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
//                          `self.<path> == oldSelf.<path>` on spec
// A status (or a conditions item) with x-kubernetes-preserve-unknown-fields
// passes the rows for the fields it does not declare; the ones it declares
// must still have the right type, since a declared string would reject the
// controller's integer.
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
    /// `spec` row, for a `field` selector: `path` is the dotted path.
    SelectorField { path: String, reason: String },
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
            ShapeError::NoSchema => write!(f, "schema: the served version has no openAPIV3Schema"),
            ShapeError::StatusObservedGeneration(reason) => {
                write!(f, "status.observedGeneration: {}", reason)
            }
            ShapeError::StatusConditions(reason) => write!(f, "status.conditions: {}", reason),
            ShapeError::SelectorField { path, reason } => {
                write!(f, "spec: selector field {}: {}", path, reason)
            }
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

fn preserves_unknown_fields(schema: &JSONSchemaProps) -> bool {
    schema.x_kubernetes_preserve_unknown_fields == Some(true)
}

fn type_of(schema: &JSONSchemaProps) -> &str {
    schema.type_.as_deref().unwrap_or("(untyped)")
}

// A field of `parent` named `name` must have type `expected`; when the parent
// preserves unknown fields the field may also be absent.
fn check_typed_field(parent: &JSONSchemaProps, name: &str, expected: &str) -> Result<(), String> {
    match property(parent, name) {
        Some(field) if type_of(field) == expected => Ok(()),
        Some(field) => Err(format!("{} has type {}, must be {}", name, type_of(field), expected)),
        None if preserves_unknown_fields(parent) => Ok(()),
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
}

fn check_conditions(status: &JSONSchemaProps) -> Result<(), String> {
    let conditions = match property(status, "conditions") {
        Some(c) => c,
        None if preserves_unknown_fields(status) => return Ok(()),
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

    #[test]
    fn a_preserve_unknown_fields_status_passes_the_status_rows() {
        let status = json!({ "type": "object", "x-kubernetes-preserve-unknown-fields": true });
        let crd = good_crd(with_cluster_name(old_widget_spec(), true), status);
        assert_eq!(check_shape(&crd, &by_field()), Ok(()));

        // Declared fields are still checked: a string observedGeneration would
        // reject the controller's integer.
        let status = json!({
            "type": "object", "x-kubernetes-preserve-unknown-fields": true,
            "properties": { "observedGeneration": { "type": "string" } }
        });
        let crd = good_crd(with_cluster_name(old_widget_spec(), true), status);
        let errors = check_shape(&crd, &by_field()).unwrap_err();
        assert_eq!(errors.len(), 1, "{:?}", errors);
        assert!(matches!(errors[0], ShapeError::StatusObservedGeneration(_)), "{:?}", errors);

        // So is a conditions item that preserves unknown fields but declares
        // only type and status.
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
