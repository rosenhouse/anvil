// The shape a kind must have before the sync controller takes it on
// (doc/widget_sync_fanout_design.md, section 2.2). `check_shape` is the pure
// check over a CustomResourceDefinition; `check_crd` fetches the CRD by name
// and runs it. Every error names the row of the design's table that failed,
// so a refused kind produces a usage error a person can act on.
//
// The rows, as checked here, against the schema served for the configured
// version:
//   metadata               scope is Namespaced
//   status subresource     enabled for the version
//   status.observedGeneration   integer
//   status.conditions      array of objects: type (string, required), status
//                          (string, required), reason, message (strings),
//                          observedGeneration (integer)
//   spec                   for a `field` selector: the path is a required
//                          string, every step of it required in its parent,
//                          with the rule `self == oldSelf` on the field or
//                          `self.<path> == oldSelf.<path>` on the object that
//                          holds it or on spec (has_immutability_rule), in
//                          every served version of the CRD and not only in the
//                          configured one
// x-kubernetes-preserve-unknown-fields does not excuse a status (or a
// conditions item) from declaring these fields: it makes the API server keep
// what it does not know, not check it, and what makes "every stored status
// unmarshals" -- the model's installed type -- true of what other writers store
// is the CRD's schema. The rest of a status is opaque and needs no declaration;
// preserve-unknown-fields is how a CRD keeps it.
use crate::shim_layer::kind_config::{ClusterSelector, KindConfig};
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::{
    CustomResourceDefinition, JSONSchemaProps, JSONSchemaPropsOrArray,
};
use kube::{Api, Client};
use std::fmt;

/// One failing row of the table in design section 2.2.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShapeError {
    /// The configured version is not in the CRD, or not served.
    VersionNotServed { version: String },
    /// `metadata` row: the CRD is not namespaced.
    NotNamespaced { scope: String },
    /// The status subresource row.
    NoStatusSubresource,
    /// The served version has no openAPIV3Schema at all.
    NoSchema,
    /// `status.observedGeneration` row.
    StatusObservedGeneration(String),
    /// `status.conditions` row.
    StatusConditions(String),
    /// The status schema requires a field the controller does not always write,
    /// so the API server would reject every status write with 422.
    StatusRequires(String),
    /// `spec` row, for a `field` selector: `path` is the dotted path.
    SelectorField { path: String, reason: String },
    /// The `spec` row on another served version of the CRD: an update sent
    /// through that version is an update, so the immutability rule has to be
    /// there too.
    SelectorFieldInVersion { version: String, path: String, reason: String },
}

impl fmt::Display for ShapeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ShapeError::VersionNotServed { version } => {
                write!(f, "version {} is not served by the CRD", version)
            }
            ShapeError::NotNamespaced { scope } => {
                write!(f, "metadata: scope is {}, must be Namespaced", scope)
            }
            ShapeError::NoStatusSubresource => write!(f, "status subresource: not enabled"),
            ShapeError::StatusRequires(reason) => write!(f, "status: {}", reason),
            ShapeError::NoSchema => write!(f, "schema: the served version has no openAPIV3Schema"),
            ShapeError::StatusObservedGeneration(reason) => {
                write!(f, "status.observedGeneration: {}", reason)
            }
            ShapeError::StatusConditions(reason) => write!(f, "status.conditions: {}", reason),
            ShapeError::SelectorField { path, reason } => {
                write!(f, "spec: selector field {}: {}", path, reason)
            }
            ShapeError::SelectorFieldInVersion { version, path, reason } => write!(
                f,
                "spec of the served version {}: selector field {}: {} (an update sent through \
                 another served version is an update, so every served version must guard the field)",
                version, path, reason
            ),
        }
    }
}

impl std::error::Error for ShapeError {}

/// Check that `crd` has the shape the sync controller needs for `kind`.
/// All failing rows are reported, not only the first.
pub fn check_shape(crd: &CustomResourceDefinition, kind: &KindConfig) -> Result<(), Vec<ShapeError>> {
    let mut errors = Vec::new();

    let version = match crd.spec.versions.iter().find(|v| v.name == kind.version && v.served) {
        Some(v) => v,
        None => {
            // Nothing else can be checked without the served version.
            return Err(vec![ShapeError::VersionNotServed { version: kind.version.clone() }]);
        }
    };

    if crd.spec.scope != "Namespaced" {
        errors.push(ShapeError::NotNamespaced { scope: crd.spec.scope.clone() });
    }
    if version.subresources.as_ref().and_then(|s| s.status.as_ref()).is_none() {
        errors.push(ShapeError::NoStatusSubresource);
    }

    let schema = match version.schema.as_ref().and_then(|s| s.open_api_v3_schema.as_ref()) {
        Some(schema) => schema,
        None => {
            errors.push(ShapeError::NoSchema);
            return Err(errors);
        }
    };

    check_status(schema, &mut errors);
    if let ClusterSelector::Field(path) = &kind.selector {
        if let Err(reason) = check_selector_field(schema, path) {
            errors.push(ShapeError::SelectorField { path: kind.selector.dotted_path(), reason });
        }
        // Every other served version too. An object is one object whichever
        // version it is written through, so a version that does not guard the
        // selector field is a way to move an object between inner clusters,
        // which is what the rule is there to prevent (design section 1.1).
        for other in crd.spec.versions.iter().filter(|v| v.served && v.name != version.name) {
            let reason = match other.schema.as_ref().and_then(|s| s.open_api_v3_schema.as_ref()) {
                Some(schema) => check_selector_field(schema, path),
                None => Err("the version has no openAPIV3Schema".to_string()),
            };
            if let Err(reason) = reason {
                errors.push(ShapeError::SelectorFieldInVersion {
                    version: other.name.clone(),
                    path: kind.selector.dotted_path(),
                    reason,
                });
            }
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn property<'a>(schema: &'a JSONSchemaProps, name: &str) -> Option<&'a JSONSchemaProps> {
    schema.properties.as_ref().and_then(|p| p.get(name))
}

fn is_required(schema: &JSONSchemaProps, name: &str) -> bool {
    schema.required.as_ref().is_some_and(|r| r.iter().any(|n| n == name))
}

fn type_of(schema: &JSONSchemaProps) -> &str {
    schema.type_.as_deref().unwrap_or("(untyped)")
}

// A field of `parent` named `name` must be declared with type `expected`.
//
// `x-kubernetes-preserve-unknown-fields` on the parent is not an excuse for
// leaving it out: it only makes the API server keep a field it does not know,
// it does not make the server check its type. The model's installed type says
// that every stored status unmarshals -- observedGeneration an integer,
// conditions a list of conditions -- and the only thing that makes that true of
// what other writers store is the CRD's own schema. An undeclared
// observedGeneration accepts the string "three", which the controller would
// then fail to unmarshal.
fn check_typed_field(parent: &JSONSchemaProps, name: &str, expected: &str) -> Result<(), String> {
    match property(parent, name) {
        Some(field) if type_of(field) == expected => Ok(()),
        Some(field) => Err(format!("{} has type {}, must be {}", name, type_of(field), expected)),
        None => Err(format!("{} is not declared", name)),
    }
}

fn check_status(schema: &JSONSchemaProps, errors: &mut Vec<ShapeError>) {
    let status = match property(schema, "status") {
        Some(status) => status,
        None => {
            errors.push(ShapeError::StatusObservedGeneration("status has no schema".to_string()));
            errors.push(ShapeError::StatusConditions("status has no schema".to_string()));
            return;
        }
    };
    if let Err(reason) = check_typed_field(status, "observedGeneration", "integer") {
        errors.push(ShapeError::StatusObservedGeneration(reason));
    }
    if let Err(reason) = check_conditions(status) {
        errors.push(ShapeError::StatusConditions(reason));
    }
    if let Err(reason) = check_no_unwritten_required(status, &STATUS_ALWAYS_WRITTEN, "status") {
        errors.push(ShapeError::StatusRequires(reason));
    }
}

// Every field the sync controller always writes, at the two levels of the status
// it writes. A schema may require these and nothing else: the API server rejects
// a write missing a required field, and a rejected status write is discarded
// rather than reported (the reconcile ends in Error and requeues on the backoff),
// so the object would carry no status at all and the only signal would be a WARN
// per attempt.
//
// The controller writes no lastTransitionTime -- it reads no clocks -- and omits
// reason and message when the condition it is mirroring has none. A CRD generated
// from metav1.Condition marks all of lastTransitionTime, message and reason
// required, and would otherwise pass every other row here.
const STATUS_ALWAYS_WRITTEN: [&str; 2] = ["observedGeneration", "conditions"];
const CONDITION_ALWAYS_WRITTEN: [&str; 3] = ["type", "status", "observedGeneration"];

// `observedGeneration` is in both lists because the API server sets
// metadata.generation on every CRD with the status subresource, and the
// controller stamps whatever it read; it is omitted only for an object that has
// no generation, which such a CRD does not produce.
fn check_no_unwritten_required(schema: &JSONSchemaProps, written: &[&str], what: &str) -> Result<(), String> {
    let required = match &schema.required {
        Some(required) => required,
        None => return Ok(()),
    };
    let mut unwritten: Vec<&str> = required
        .iter()
        .map(|name| name.as_str())
        .filter(|name| !written.contains(name))
        .collect();
    if unwritten.is_empty() {
        return Ok(());
    }
    unwritten.sort_unstable();
    Err(format!(
        "{} requires {}, which the controller does not always write, so the API server would reject every status write",
        what,
        unwritten.join(", ")
    ))
}

fn check_conditions(status: &JSONSchemaProps) -> Result<(), String> {
    let conditions = match property(status, "conditions") {
        Some(c) => c,
        None => return Err("conditions is not declared".to_string()),
    };
    if type_of(conditions) != "array" {
        return Err(format!("conditions has type {}, must be array", type_of(conditions)));
    }
    let item = match &conditions.items {
        Some(JSONSchemaPropsOrArray::Schema(item)) => item.as_ref(),
        Some(JSONSchemaPropsOrArray::Schemas(_)) => {
            return Err("conditions items must be one schema, not a tuple".to_string())
        }
        None => return Err("conditions has no items schema".to_string()),
    };
    if type_of(item) != "object" {
        return Err(format!("conditions items have type {}, must be object", type_of(item)));
    }
    for (name, expected) in [
        ("type", "string"),
        ("status", "string"),
        ("reason", "string"),
        ("message", "string"),
        ("observedGeneration", "integer"),
    ] {
        check_typed_field(item, name, expected).map_err(|e| format!("conditions items: {}", e))?;
    }
    for name in ["type", "status"] {
        if property(item, name).is_some() && !is_required(item, name) {
            return Err(format!("conditions items: {} must be required", name));
        }
    }
    check_no_unwritten_required(item, &CONDITION_ALWAYS_WRITTEN, "conditions items")?;
    Ok(())
}

// The selector field: walk `spec` along `path`; every step must be a declared
// property, required in its parent; the last must be a string guarded by an
// immutability rule, on the field or on spec.
fn check_selector_field(schema: &JSONSchemaProps, path: &[String]) -> Result<(), String> {
    let spec = property(schema, "spec").ok_or_else(|| "spec has no schema".to_string())?;
    let mut parent = spec;
    let mut field = spec;
    for (i, segment) in path.iter().enumerate() {
        let here = format!("spec.{}", path[..=i].join("."));
        field = property(parent, segment)
            .ok_or_else(|| format!("{} is not declared in the schema", here))?;
        if !is_required(parent, segment) {
            return Err(format!("{} must be required", here));
        }
        if i + 1 < path.len() {
            if type_of(field) != "object" {
                return Err(format!("{} has type {}, must be object", here, type_of(field)));
            }
            parent = field;
        }
    }
    if type_of(field) != "string" {
        return Err(format!("has type {}, must be string", type_of(field)));
    }
    let dotted = path.join(".");
    // The rule may sit on the field itself, on the object that holds it, or on
    // `spec`; on an object it names the field by the path from that object.
    // `parent` is `spec` for a one-segment path, so the two coincide there.
    let last = path[path.len() - 1].as_str();
    let on_field = has_immutability_rule(field, "");
    let on_parent = has_immutability_rule(parent, last);
    let on_spec = has_immutability_rule(spec, &dotted);
    if on_field || on_parent || on_spec {
        Ok(())
    } else {
        Err(format!(
            "must carry the x-kubernetes-validations rule `self == oldSelf` \
             (or spec the rule `self.{0} == oldSelf.{0}`; either side may come \
             first and the spacing does not matter)",
            dotted
        ))
    }
}

// Whether `schema` carries an immutability rule for the field at `field_path`
// relative to it; the empty path is the field itself, whose rule is
// `self == oldSelf`.
//
// A CEL rule is text, and the same rule has several spellings: the two sides
// may be written either way round and the spacing is free (`self==oldSelf` is
// the rule that `self  ==  oldSelf` is). Comparing the text as written refused
// CRDs that are in fact guarded, which matters more than the brittleness of a
// text comparison suggests: this rule is what the janitor's delete-soundness
// invariant rests on (design section 1.1), so whether a kind is accepted must
// not depend on how a person typed it. Everything beyond these spellings is
// still refused: recognising an arbitrary CEL expression would mean evaluating
// CEL, which this deliberately does not.
fn has_immutability_rule(schema: &JSONSchemaProps, field_path: &str) -> bool {
    let (new, old) = if field_path.is_empty() {
        ("self".to_string(), "oldSelf".to_string())
    } else {
        (format!("self.{}", field_path), format!("oldSelf.{}", field_path))
    };
    let accepted = [format!("{}=={}", new, old), format!("{}=={}", old, new)];
    schema.x_kubernetes_validations.as_ref().is_some_and(|rules| {
        rules.iter().any(|r| {
            let written: String = r.rule.chars().filter(|c| !c.is_whitespace()).collect();
            accepted.contains(&written)
        })
    })
}

/// What `check_crd` can report: the CRD could not be read, or it has the wrong shape.
#[derive(Debug)]
pub enum CrdCheckError {
    Fetch { name: String, source: kube::Error },
    Shape { name: String, errors: Vec<ShapeError> },
}

impl fmt::Display for CrdCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CrdCheckError::Fetch { name, source } => {
                write!(f, "reading CRD {} failed: {}", name, source)
            }
            CrdCheckError::Shape { name, errors } => {
                write!(f, "CRD {} does not have the shape the sync controller needs:", name)?;
                for e in errors {
                    write!(f, "\n  - {}", e)?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for CrdCheckError {}

/// The name of the CRD for a kind, `<plural>.<group>`; `plural` comes from discovery.
pub fn crd_name(kind: &KindConfig, plural: &str) -> String {
    format!("{}.{}", plural, kind.group)
}

/// check_kind_name holds a kind's CRD name to what the model assumes of it.
/// The model kind of an object is the CRD name for an outer copy and
/// `<crd name>@<namespace>/<clusterName>` for a mirror, and the theorems'
/// distinctness hypotheses are discharged by that map being injective, which
/// rests on the CRD name being free of `@` (spec::model_kind::kind_name_ok);
/// `/` is refused with it, since it separates the binding's two parts.
///
/// A DNS name has neither, but the proofs assume it, so it is checked.
pub fn check_kind_name(name: &str) -> Result<(), String> {
    if name.contains('@') || name.contains('/') {
        return Err(format!(
            "the CRD name {:?} contains '@' or '/', which the model kind of a mirror uses as \
             separators (`<kind>@<namespace>/<clusterName>`)",
            name
        ));
    }
    Ok(())
}

/// Fetch the CRD of `kind` from the cluster `client` talks to and run `check_shape`.
pub async fn check_crd(client: &Client, kind: &KindConfig, plural: &str) -> Result<(), CrdCheckError> {
    let name = crd_name(kind, plural);
    let crd = Api::<CustomResourceDefinition>::all(client.clone())
        .get(&name)
        .await
        .map_err(|source| CrdCheckError::Fetch { name: name.clone(), source })?;
    check_shape(&crd, kind).map_err(|errors| CrdCheckError::Shape { name, errors })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    // The status schema of deploy/widget_sync/crd.yaml, without the descriptions.
    fn widget_status() -> Value {
        json!({
            "type": "object", "nullable": true,
            "properties": {
                "observedGeneration": { "type": "integer", "format": "int64", "nullable": true },
                "ready": { "type": "boolean", "nullable": true },
                "observedCount": { "type": "integer", "format": "int32", "nullable": true },
                "conditions": {
                    "type": "array", "nullable": true,
                    "items": {
                        "type": "object",
                        "required": ["status", "type"],
                        "properties": {
                            "type": { "type": "string" },
                            "status": { "type": "string" },
                            "reason": { "type": "string", "nullable": true },
                            "message": { "type": "string", "nullable": true },
                            "observedGeneration": { "type": "integer", "format": "int64", "nullable": true }
                        }
                    }
                }
            }
        })
    }

    // The spec schema of crd.yaml before clusterName was added.
    fn old_widget_spec() -> Value {
        json!({
            "type": "object",
            "required": ["count"],
            "properties": {
                "count": { "type": "integer", "format": "int32" },
                "message": { "type": "string", "nullable": true }
            }
        })
    }

    fn with_cluster_name(mut spec: Value, rule_on_field: bool) -> Value {
        let mut field = json!({ "type": "string" });
        if rule_on_field {
            field["x-kubernetes-validations"] =
                json!([{ "rule": "self == oldSelf", "message": "clusterName is immutable" }]);
        }
        spec["properties"]["clusterName"] = field;
        spec["required"].as_array_mut().unwrap().push(json!("clusterName"));
        spec
    }

    fn crd(scope: &str, status_subresource: bool, spec: Value, status: Value) -> CustomResourceDefinition {
        let mut version = json!({
            "name": "v1", "served": true, "storage": true,
            "schema": { "openAPIV3Schema": {
                "type": "object",
                "required": ["spec"],
                "properties": { "spec": spec, "status": status }
            } }
        });
        if status_subresource {
            version["subresources"] = json!({ "status": {} });
        }
        serde_json::from_value(json!({
            "apiVersion": "apiextensions.k8s.io/v1",
            "kind": "CustomResourceDefinition",
            "metadata": { "name": "widgets.anvil.dev" },
            "spec": {
                "group": "anvil.dev",
                "names": { "kind": "Widget", "plural": "widgets" },
                "scope": scope,
                "versions": [version]
            }
        }))
        .unwrap()
    }

    fn good_crd(spec: Value, status: Value) -> CustomResourceDefinition {
        crd("Namespaced", true, spec, status)
    }

    fn by_field() -> KindConfig {
        "anvil.dev/v1/Widget:field:spec.clusterName".parse().unwrap()
    }

    fn by_name() -> KindConfig {
        "anvil.dev/v1/Widget:name".parse().unwrap()
    }

    #[test]
    fn the_old_widget_crd_lacks_only_the_selector_field() {
        let crd = good_crd(old_widget_spec(), widget_status());
        let errors = check_shape(&crd, &by_field()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        match &errors[0] {
            ShapeError::SelectorField { path, reason } => {
                assert_eq!(path, "spec.clusterName");
                assert!(reason.contains("not declared"), "{}", reason);
            }
            other => panic!("unexpected error {:?}", other),
        }
        assert_eq!(check_shape(&crd, &by_name()), Ok(()));
    }

    #[test]
    fn a_required_string_with_the_rule_on_the_field_passes() {
        let crd = good_crd(with_cluster_name(old_widget_spec(), true), widget_status());
        assert_eq!(check_shape(&crd, &by_field()), Ok(()));
        assert_eq!(check_shape(&crd, &by_name()), Ok(()));
    }

    #[test]
    fn the_rule_may_sit_on_spec_instead() {
        let mut spec = with_cluster_name(old_widget_spec(), false);
        spec["x-kubernetes-validations"] =
            json!([{ "rule": "  self.clusterName == oldSelf.clusterName ", "message": "immutable" }]);
        let crd = good_crd(spec, widget_status());
        assert_eq!(check_shape(&crd, &by_field()), Ok(()));
    }

    // The same rule, spelled the other ways a person writes it: either side
    // first, and any spacing. All of them guard the field, so all of them are
    // accepted, on the field and on the object that holds it.
    #[test]
    fn the_rule_is_recognised_however_it_is_spelled() {
        for rule in ["self == oldSelf", "oldSelf == self", "self==oldSelf", "oldSelf\t==\n self"] {
            let mut spec = with_cluster_name(old_widget_spec(), false);
            spec["properties"]["clusterName"]["x-kubernetes-validations"] = json!([{ "rule": rule }]);
            assert_eq!(check_shape(&good_crd(spec, widget_status()), &by_field()), Ok(()), "{:?}", rule);
        }
        for rule in [
            "self.clusterName == oldSelf.clusterName",
            "oldSelf.clusterName == self.clusterName",
            "self.clusterName==oldSelf.clusterName",
        ] {
            let mut spec = with_cluster_name(old_widget_spec(), false);
            spec["x-kubernetes-validations"] = json!([{ "rule": rule }]);
            assert_eq!(check_shape(&good_crd(spec, widget_status()), &by_field()), Ok(()), "{:?}", rule);
        }
    }

    // For a nested field the rule may also sit on the object that holds it,
    // where it names the field by that object's path, not spec's.
    #[test]
    fn the_rule_may_sit_on_the_field_s_own_object() {
        let kind: KindConfig = "anvil.dev/v1/Widget:field:spec.placement.clusterName".parse().unwrap();
        let mut spec = old_widget_spec();
        spec["properties"]["placement"] = json!({
            "type": "object",
            "required": ["clusterName"],
            "x-kubernetes-validations": [{ "rule": "oldSelf.clusterName == self.clusterName" }],
            "properties": { "clusterName": { "type": "string" } }
        });
        spec["required"] = json!(["count", "placement"]);
        assert_eq!(check_shape(&good_crd(spec.clone(), widget_status()), &kind), Ok(()));

        // The path is the one from that object: spec's spelling on the parent
        // guards nothing here and is refused.
        spec["properties"]["placement"]["x-kubernetes-validations"] =
            json!([{ "rule": "self.placement.clusterName == oldSelf.placement.clusterName" }]);
        let errors = check_shape(&good_crd(spec, widget_status()), &kind).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
    }

    #[test]
    fn a_rule_with_other_text_does_not_count() {
        let mut spec = with_cluster_name(old_widget_spec(), false);
        spec["properties"]["clusterName"]["x-kubernetes-validations"] =
            json!([{ "rule": "self != oldSelf" }, { "rule": "self.size() > 0" }]);
        spec["x-kubernetes-validations"] = json!([{ "rule": "self.count == oldSelf.count" }]);
        let crd = good_crd(spec, widget_status());
        let errors = check_shape(&crd, &by_field()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(errors[0].to_string().contains("self == oldSelf"), "{}", errors[0]);
    }

    // A CRD generated from metav1.Condition passes every other row: it declares
    // all five fields with the types the shape check demands, and marks type and
    // status required. It also marks lastTransitionTime, message and reason
    // required, and the controller writes none of them reliably, so every status
    // write would be rejected 422 and the outer copy would carry no status at all.
    #[test]
    fn a_condition_schema_may_not_require_a_field_the_controller_omits() {
        let mut status = widget_status();
        status["properties"]["conditions"]["items"]["properties"]["lastTransitionTime"] =
            json!({ "type": "string", "format": "date-time" });
        status["properties"]["conditions"]["items"]["required"] =
            json!(["lastTransitionTime", "message", "reason", "status", "type"]);
        let errors =
            check_shape(&good_crd(with_cluster_name(old_widget_spec(), true), status), &by_field()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        let text = errors[0].to_string();
        assert!(text.contains("lastTransitionTime, message, reason"), "{}", text);
        assert!(text.contains("reject every status write"), "{}", text);
    }

    // observedGeneration is written whenever the object has a generation, which
    // a CRD with the status subresource always gives it, so requiring it is fine.
    #[test]
    fn a_condition_schema_may_require_observed_generation() {
        let mut status = widget_status();
        status["properties"]["conditions"]["items"]["required"] =
            json!(["observedGeneration", "status", "type"]);
        check_shape(&good_crd(with_cluster_name(old_widget_spec(), true), status), &by_field()).unwrap();
    }

    // The same at the status level: the controller writes observedGeneration, the
    // conditions and the mirrored remainder, and the remainder is empty on every
    // failure path, so a required field outside the first two breaks those writes.
    #[test]
    fn a_status_schema_may_not_require_a_field_the_controller_omits() {
        let mut status = widget_status();
        status["required"] = json!(["conditions", "observedCount", "observedGeneration"]);
        let errors =
            check_shape(&good_crd(with_cluster_name(old_widget_spec(), true), status), &by_field()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(errors[0].to_string().contains("observedCount"), "{}", errors[0]);
    }

    #[test]
    fn the_selector_field_must_be_a_required_string() {
        let mut optional = with_cluster_name(old_widget_spec(), true);
        optional["required"] = json!(["count"]);
        let errors = check_shape(&good_crd(optional, widget_status()), &by_field()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(errors[0].to_string().contains("must be required"), "{}", errors[0]);

        let mut integer = with_cluster_name(old_widget_spec(), true);
        integer["properties"]["clusterName"]["type"] = json!("integer");
        let errors = check_shape(&good_crd(integer, widget_status()), &by_field()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(errors[0].to_string().contains("must be string"), "{}", errors[0]);
    }

    #[test]
    fn a_nested_selector_field_walks_required_objects() {
        let kind: KindConfig = "anvil.dev/v1/Widget:field:spec.placement.clusterName".parse().unwrap();
        let mut spec = old_widget_spec();
        spec["properties"]["placement"] = json!({
            "type": "object",
            "required": ["clusterName"],
            "properties": { "clusterName": {
                "type": "string",
                "x-kubernetes-validations": [{ "rule": "self == oldSelf" }]
            } }
        });
        spec["required"] = json!(["count", "placement"]);
        assert_eq!(check_shape(&good_crd(spec.clone(), widget_status()), &kind), Ok(()));

        // The rule on spec names the whole path.
        spec["properties"]["placement"]["properties"]["clusterName"] = json!({ "type": "string" });
        spec["x-kubernetes-validations"] =
            json!([{ "rule": "self.placement.clusterName == oldSelf.placement.clusterName" }]);
        assert_eq!(check_shape(&good_crd(spec.clone(), widget_status()), &kind), Ok(()));

        // An optional step on the way is refused.
        spec["required"] = json!(["count"]);
        let errors = check_shape(&good_crd(spec, widget_status()), &kind).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(errors[0].to_string().contains("spec.placement must be required"), "{}", errors[0]);
    }

    // A second served version is a second way to write the object, so the rule
    // has to be there too; a version that is not served is not.
    #[test]
    fn every_served_version_must_guard_the_selector_field() {
        let with_versions = |v2_served: bool, v2_guarded: bool| {
            let spec = with_cluster_name(old_widget_spec(), true);
            let mut crd = crd("Namespaced", true, spec.clone(), widget_status());
            let v2_spec = with_cluster_name(old_widget_spec(), v2_guarded);
            let mut v2 = crd.spec.versions[0].clone();
            v2.name = "v2".to_string();
            v2.served = v2_served;
            v2.storage = false;
            v2.schema = serde_json::from_value(json!({ "openAPIV3Schema": {
                "type": "object",
                "required": ["spec"],
                "properties": { "spec": v2_spec, "status": widget_status() }
            } }))
            .unwrap();
            crd.spec.versions.push(v2);
            crd
        };
        assert_eq!(check_shape(&with_versions(true, true), &by_field()), Ok(()));
        // Not served: nothing can be written through it.
        assert_eq!(check_shape(&with_versions(false, false), &by_field()), Ok(()));
        let errors = check_shape(&with_versions(true, false), &by_field()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(errors[0].to_string().contains("served version v2"), "{}", errors[0]);
        assert!(errors[0].to_string().contains("self == oldSelf"), "{}", errors[0]);
        // A `name` selector needs no rule in any version.
        assert_eq!(check_shape(&with_versions(true, false), &by_name()), Ok(()));
    }

    #[test]
    fn a_crd_without_the_status_subresource_is_refused() {
        let crd = crd("Namespaced", false, with_cluster_name(old_widget_spec(), true), widget_status());
        assert_eq!(check_shape(&crd, &by_field()), Err(vec![ShapeError::NoStatusSubresource]));
        assert_eq!(check_shape(&crd, &by_name()), Err(vec![ShapeError::NoStatusSubresource]));
    }

    #[test]
    fn a_cluster_scoped_crd_is_refused() {
        let crd = crd("Cluster", true, old_widget_spec(), widget_status());
        assert_eq!(
            check_shape(&crd, &by_name()),
            Err(vec![ShapeError::NotNamespaced { scope: "Cluster".to_string() }])
        );
    }

    // preserve-unknown-fields keeps a field the API server does not know; it
    // does not check its type, so it does not stand in for declaring the fields
    // the controller reads and writes. Their absence is a failing row wherever
    // it appears.
    #[test]
    fn a_preserve_unknown_fields_status_must_still_declare_the_fields() {
        let status = json!({ "type": "object", "x-kubernetes-preserve-unknown-fields": true });
        let crd = good_crd(with_cluster_name(old_widget_spec(), true), status);
        let errors = check_shape(&crd, &by_field()).unwrap_err();
        assert_eq!(
            errors,
            vec![
                ShapeError::StatusObservedGeneration("observedGeneration is not declared".to_string()),
                ShapeError::StatusConditions("conditions is not declared".to_string()),
            ]
        );

        // Declared with the wrong type is refused as it was: a string
        // observedGeneration would reject the controller's integer.
        let status = json!({
            "type": "object", "x-kubernetes-preserve-unknown-fields": true,
            "properties": { "observedGeneration": { "type": "string" } }
        });
        let crd = good_crd(with_cluster_name(old_widget_spec(), true), status);
        let errors = check_shape(&crd, &by_field()).unwrap_err();
        assert_eq!(errors.len(), 2, "{:?}", errors);
        assert!(matches!(errors[0], ShapeError::StatusObservedGeneration(_)), "{:?}", errors);

        // A conditions item that preserves unknown fields but declares only
        // type and status: the fields the controller reads off a condition are
        // still required.
        let status = json!({
            "type": "object",
            "properties": {
                "observedGeneration": { "type": "integer" },
                "conditions": { "type": "array", "items": {
                    "type": "object",
                    "x-kubernetes-preserve-unknown-fields": true,
                    "required": ["type", "status"],
                    "properties": { "type": { "type": "string" }, "status": { "type": "string" } }
                } }
            }
        });
        let crd = good_crd(with_cluster_name(old_widget_spec(), true), status);
        let errors = check_shape(&crd, &by_field()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(errors[0].to_string().contains("reason is not declared"), "{}", errors[0]);

        // The whole status declared, with preserve-unknown-fields for the rest
        // the controller mirrors verbatim, passes.
        let mut status = widget_status();
        status["x-kubernetes-preserve-unknown-fields"] = json!(true);
        let crd = good_crd(with_cluster_name(old_widget_spec(), true), status);
        assert_eq!(check_shape(&crd, &by_field()), Ok(()));
    }

    #[test]
    fn a_status_without_the_fields_fails_both_status_rows() {
        let status = json!({ "type": "object", "properties": { "ready": { "type": "boolean" } } });
        let crd = good_crd(with_cluster_name(old_widget_spec(), true), status);
        let errors = check_shape(&crd, &by_field()).unwrap_err();
        assert_eq!(
            errors,
            vec![
                ShapeError::StatusObservedGeneration("observedGeneration is not declared".to_string()),
                ShapeError::StatusConditions("conditions is not declared".to_string()),
            ]
        );

        let no_status = json!({
            "apiVersion": "apiextensions.k8s.io/v1", "kind": "CustomResourceDefinition",
            "metadata": { "name": "widgets.anvil.dev" },
            "spec": {
                "group": "anvil.dev", "names": { "kind": "Widget", "plural": "widgets" },
                "scope": "Namespaced",
                "versions": [{
                    "name": "v1", "served": true, "storage": true,
                    "subresources": { "status": {} },
                    "schema": { "openAPIV3Schema": { "type": "object", "properties": {} } }
                }]
            }
        });
        let crd: CustomResourceDefinition = serde_json::from_value(no_status).unwrap();
        let errors = check_shape(&crd, &by_name()).unwrap_err();
        assert_eq!(errors.len(), 2, "{:?}", errors);
    }

    #[test]
    fn conditions_items_are_checked_field_by_field() {
        let mut status = widget_status();
        status["properties"]["conditions"]["items"]["properties"]["observedGeneration"]["type"] = json!("string");
        let crd = good_crd(old_widget_spec(), status);
        let errors = check_shape(&crd, &by_name()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(errors[0].to_string().contains("observedGeneration has type string"), "{}", errors[0]);

        let mut status = widget_status();
        status["properties"]["conditions"]["items"]["required"] = json!(["type"]);
        let errors = check_shape(&good_crd(old_widget_spec(), status), &by_name()).unwrap_err();
        assert!(errors[0].to_string().contains("status must be required"), "{}", errors[0]);

        let mut status = widget_status();
        status["properties"]["conditions"]["items"]["properties"].as_object_mut().unwrap().remove("reason");
        let errors = check_shape(&good_crd(old_widget_spec(), status), &by_name()).unwrap_err();
        assert!(errors[0].to_string().contains("reason is not declared"), "{}", errors[0]);

        let mut status = widget_status();
        status["properties"]["conditions"] = json!({ "type": "object" });
        let errors = check_shape(&good_crd(old_widget_spec(), status), &by_name()).unwrap_err();
        assert!(errors[0].to_string().contains("must be array"), "{}", errors[0]);
    }

    #[test]
    fn an_unserved_version_stops_the_check() {
        let kind: KindConfig = "anvil.dev/v2/Widget:name".parse().unwrap();
        let crd = crd("Cluster", false, old_widget_spec(), widget_status());
        assert_eq!(
            check_shape(&crd, &kind),
            Err(vec![ShapeError::VersionNotServed { version: "v2".to_string() }])
        );
    }

    // The demo manifests must pass with the selectors the demo configures.
    #[test]
    fn the_demo_crd_manifests_have_the_shape() {
        let widget: CustomResourceDefinition =
            serde_yaml::from_str(include_str!("../../deploy/widget_sync/crd.yaml")).unwrap();
        assert_eq!(check_shape(&widget, &by_field()), Ok(()));
        assert_eq!(check_shape(&widget, &by_name()), Ok(()));

        let gadget: CustomResourceDefinition =
            serde_yaml::from_str(include_str!("../../deploy/widget_sync/crd_gadget.yaml")).unwrap();
        let gadget_by_name: KindConfig = "anvil.dev/v1/Gadget:name".parse().unwrap();
        assert_eq!(check_shape(&gadget, &gadget_by_name), Ok(()));
        // Gadget has no cluster field, so a field selector is refused on the spec row alone.
        let gadget_by_field: KindConfig = "anvil.dev/v1/Gadget:field:spec.clusterName".parse().unwrap();
        let errors = check_shape(&gadget, &gadget_by_field).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(matches!(errors[0], ShapeError::SelectorField { .. }), "{:?}", errors);
    }

    #[test]
    fn every_failing_row_is_reported() {
        let crd = crd("Cluster", false, old_widget_spec(), json!({ "type": "object", "properties": {} }));
        let errors = check_shape(&crd, &by_field()).unwrap_err();
        assert_eq!(errors.len(), 5, "{:?}", errors);
        assert_eq!(crd_name(&by_field(), "widgets"), "widgets.anvil.dev");
    }
}
