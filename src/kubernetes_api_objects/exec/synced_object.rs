// The exec twin of the shape (doc/widget_sync_fanout_design.md, section 2.3):
// SyncedObject wraps a kube DynamicObject of a configured kind together with the
// cluster it lives in. Its unmarshal, marshal, has_kind and api_resource are
// external_body with the postconditions of the typed wrapper macro
// (exec::resource::implement_object_wrapper_type), restated over the registry's
// model kind and the shape's unmarshal; the status accessors are external_body
// over serde_json::Value, as the typed wrappers' are over the typed status.
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{api_resource::*, dynamic::*, object_meta::*, registry::*, resource::*};
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::kubernetes_api_objects::spec::resource::Value;
use crate::kubernetes_api_objects::spec::synced_object as spec;
use crate::kubernetes_api_objects::spec::synced_object::{ClusterSelector, SyncedConditionView, SyncedObjectView, SyncedStatusView};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// The view of an exec Option<i64> as the model's Option<int>.
pub open spec fn opt_i64_as_int(g: Option<i64>) -> Option<int> {
    match g {
        Some(x) => Some(x as int),
        None => None,
    }
}

// RawValue is an opaque marshalled value: a spec, or the mirrored remainder of a
// status. Its view is the model's Value. Exec code copies and compares it, and
// reads the selector field off it; nothing else.
#[verifier(external_body)]
pub struct RawValue {
    inner: serde_json::Value,
}

implement_view_trait!(RawValue, Value);
implement_deep_view_trait!(RawValue, Value);

impl std::clone::Clone for RawValue {
    #[verifier(external_body)]
    fn clone(&self) -> (res: RawValue)
        ensures res@ == self@,
    {
        RawValue { inner: self.inner.clone() }
    }
}

impl RawValue {
    #[verifier(external_body)]
    pub fn eq(&self, other: &RawValue) -> (b: bool)
        ensures b == (self@ == other@),
    {
        self.inner == other.inner
    }

    // The remainder of a status that has none: the empty object, which carries
    // neither of the two members a status keeps apart from its rest. It is what
    // a status the outer copy has never carried is built from.
    #[verifier(external_body)]
    pub fn empty_rest() -> (rest: RawValue)
        ensures rest@ == spec::empty_status_rest(),
    {
        RawValue { inner: serde_json::Value::Object(serde_json::Map::new()) }
    }

    // The string at `path` (a sequence of object keys from the root of the
    // value), None if the path does not lead to a string. The exec twin of
    // spec::spec_field.
    #[verifier(external_body)]
    pub fn field(&self, path: &Vec<String>) -> (res: Option<String>)
        ensures res.deep_view() == spec::spec_field(self@, path.deep_view()),
    {
        let mut cur = &self.inner;
        for key in path.iter() {
            match cur.get(key) {
                Some(next) => cur = next,
                None => return None,
            }
        }
        cur.as_str().map(|s| s.to_string())
    }
}

#[verifier(external)]
impl RawValue {
    pub fn from_json(inner: serde_json::Value) -> RawValue {
        RawValue { inner }
    }

    pub fn into_json(self) -> serde_json::Value {
        self.inner
    }

    pub fn as_json(&self) -> &serde_json::Value {
        &self.inner
    }
}

#[verifier(external)]
impl std::fmt::Debug for RawValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.inner.fmt(f) }
}

// The exec twin of spec::ClusterSelector.
pub enum ClusterSelectorExec {
    Name,
    Field(Vec<String>),
}

impl View for ClusterSelectorExec {
    type V = ClusterSelector;

    open spec fn view(&self) -> ClusterSelector {
        match self {
            ClusterSelectorExec::Name => ClusterSelector::Name,
            ClusterSelectorExec::Field(path) => ClusterSelector::Field(path.deep_view()),
        }
    }
}

// A condition of a status of the shape: a JSON object with a string `type` and
// `status`, and optional integer `observedGeneration` and string `reason` and
// `message` (the fields of spec::SyncedConditionView). Other fields are kept
// but have no view.
#[verifier(external_body)]
pub struct SyncedCondition {
    inner: serde_json::Value,
}

implement_view_trait!(SyncedCondition, SyncedConditionView);
implement_deep_view_trait!(SyncedCondition, SyncedConditionView);

impl std::clone::Clone for SyncedCondition {
    #[verifier(external_body)]
    fn clone(&self) -> (res: SyncedCondition)
        ensures res@ == self@,
    {
        SyncedCondition { inner: self.inner.clone() }
    }
}

impl SyncedCondition {
    #[verifier(external_body)]
    pub fn new(type_: String, status: String, observed_generation: Option<i64>, reason: Option<String>, message: Option<String>) -> (c: SyncedCondition)
        ensures c@ == (SyncedConditionView {
            type_: type_@,
            status: status@,
            observed_generation: opt_i64_as_int(observed_generation),
            reason: reason.deep_view(),
            message: message.deep_view(),
        }),
    {
        let mut object = serde_json::Map::new();
        object.insert("type".to_string(), serde_json::Value::String(type_));
        object.insert("status".to_string(), serde_json::Value::String(status));
        if let Some(g) = observed_generation {
            object.insert("observedGeneration".to_string(), serde_json::json!(g));
        }
        if let Some(r) = reason {
            object.insert("reason".to_string(), serde_json::Value::String(r));
        }
        if let Some(m) = message {
            object.insert("message".to_string(), serde_json::Value::String(m));
        }
        SyncedCondition { inner: serde_json::Value::Object(object) }
    }

    #[verifier(external_body)]
    pub fn type_(&self) -> (type_: String)
        ensures type_@ == self@.type_,
    {
        json_string(&self.inner, "type").unwrap_or_default()
    }

    #[verifier(external_body)]
    pub fn status(&self) -> (status: String)
        ensures status@ == self@.status,
    {
        json_string(&self.inner, "status").unwrap_or_default()
    }

    #[verifier(external_body)]
    pub fn observed_generation(&self) -> (observed_generation: Option<i64>)
        ensures opt_i64_as_int(observed_generation) == self@.observed_generation,
    {
        self.inner.get("observedGeneration").and_then(|v| v.as_i64())
    }

    #[verifier(external_body)]
    pub fn reason(&self) -> (reason: Option<String>)
        ensures reason.deep_view() == self@.reason,
    {
        json_string(&self.inner, "reason")
    }

    #[verifier(external_body)]
    pub fn message(&self) -> (message: Option<String>)
        ensures message.deep_view() == self@.message,
    {
        json_string(&self.inner, "message")
    }
}

#[verifier(external)]
impl SyncedCondition {
    // parse is the shape check of one condition: an object whose `type` and
    // `status` are strings, whose `observedGeneration` is an integer if present
    // and whose `reason` and `message` are strings if present.
    //
    // A JSON `null` is absent, for every optional field. A CRD declares these
    // fields `nullable: true` (deploy/widget_sync/crd.yaml does), and a client
    // that serializes a Go struct with an empty pointer or slice writes
    // `"reason": null` rather than leaving the key out; refusing that would
    // refuse the status of an ordinary inner implementation. The accessors
    // already read a null as absent (`as_str`, `as_i64` answer None), so this is
    // what makes parse agree with them.
    pub fn parse(value: &serde_json::Value) -> Result<SyncedCondition, UnmarshalError> {
        let object = value.as_object().ok_or(())?;
        let is_string = |key: &str| object.get(key).map_or(false, |v| v.is_string());
        let is_string_or_null = |key: &str| object.get(key).map_or(true, |v| v.is_string() || v.is_null());
        // type and status are required: a null there is a condition that says
        // nothing, not a condition with a default.
        if !is_string("type") || !is_string("status") {
            return Err(());
        }
        if !object.get("observedGeneration").map_or(true, |v| v.as_i64().is_some() || v.is_null()) {
            return Err(());
        }
        if !is_string_or_null("reason") || !is_string_or_null("message") {
            return Err(());
        }
        Ok(SyncedCondition { inner: value.clone() })
    }

    pub fn as_json(&self) -> &serde_json::Value {
        &self.inner
    }
}

#[verifier(external)]
impl std::fmt::Debug for SyncedCondition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.inner.fmt(f) }
}

// A status of the shape: a JSON object whose `observedGeneration` is an integer
// if present and whose `conditions` is a list of conditions if present. The
// rest of the object is the mirrored remainder, spec::SyncedStatusView::rest.
#[verifier(external_body)]
pub struct SyncedStatus {
    inner: serde_json::Value,
}

implement_view_trait!(SyncedStatus, SyncedStatusView);
implement_deep_view_trait!(SyncedStatus, SyncedStatusView);

impl std::clone::Clone for SyncedStatus {
    #[verifier(external_body)]
    fn clone(&self) -> (res: SyncedStatus)
        ensures res@ == self@,
    {
        SyncedStatus { inner: self.inner.clone() }
    }
}

impl SyncedStatus {
    // new builds a status from its three parts: the explicit fields, written
    // over the mirrored remainder.
    //
    // `rest` must be a remainder (`status_rest_ok`): the value another status's
    // rest() gave, or empty_rest(). That is a precondition and not something
    // the body arranges, because the postcondition says the view's rest is the
    // value it was given -- for a value carrying an `observedGeneration` of its
    // own there is no status of which that is true, whatever the body does with
    // it. The two callers pass a rest() or an empty_rest():
    // widget_sync_controller's outer_status_for, and the tests below.
    #[verifier(external_body)]
    pub fn new(observed_generation: Option<i64>, conditions: Option<Vec<SyncedCondition>>, rest: RawValue) -> (s: SyncedStatus)
        requires spec::status_rest_ok(rest@),
        ensures s@ == (SyncedStatusView {
            observed_generation: opt_i64_as_int(observed_generation),
            conditions: conditions.deep_view(),
            rest: rest@,
        }),
    {
        let mut object = match rest.inner {
            serde_json::Value::Object(o) => o,
            // Outside the precondition; the fields the postcondition names are
            // kept authoritative rather than a value that is no remainder.
            _ => serde_json::Map::new(),
        };
        if let Some(g) = observed_generation {
            object.insert("observedGeneration".to_string(), serde_json::json!(g));
        }
        if let Some(cs) = conditions {
            object.insert("conditions".to_string(), serde_json::Value::Array(cs.into_iter().map(|c| c.inner).collect()));
        }
        SyncedStatus { inner: serde_json::Value::Object(object) }
    }

    #[verifier(external_body)]
    pub fn observed_generation(&self) -> (observed_generation: Option<i64>)
        ensures opt_i64_as_int(observed_generation) == self@.observed_generation,
    {
        self.inner.get("observedGeneration").and_then(|v| v.as_i64())
    }

    #[verifier(external_body)]
    pub fn conditions(&self) -> (conditions: Option<Vec<SyncedCondition>>)
        ensures conditions.deep_view() == self@.conditions,
    {
        self.inner.get("conditions").and_then(|v| v.as_array()).map(|items| {
            items.iter().map(|c| SyncedCondition { inner: c.clone() }).collect()
        })
    }

    // The mirrored remainder: the status without observedGeneration and
    // conditions, which is what makes it a `status_rest_ok` value and so an
    // argument SyncedStatus::new accepts.
    #[verifier(external_body)]
    pub fn rest(&self) -> (rest: RawValue)
        ensures
            rest@ == self@.rest,
            spec::status_rest_ok(rest@),
    {
        let mut object = self.inner.as_object().cloned().unwrap_or_default();
        object.remove("observedGeneration");
        object.remove("conditions");
        RawValue { inner: serde_json::Value::Object(object) }
    }
}

impl SyncedStatus {
    // Equality of the *view*: the two statuses have the same observedGeneration,
    // the same conditions field by viewed field, and the same mirrored remainder.
    // Trusted, like the accessors it is spelled out from.
    #[verifier(external_body)]
    pub fn eq(&self, other: &SyncedStatus) -> (b: bool)
        ensures b == (self@ == other@),
    {
        Self::view_eq(&self.inner, &other.inner)
    }
}

#[verifier(external)]
impl SyncedStatus {
    // parse is the shape check of a status value, the exec twin of
    // spec::unmarshal_status: an absent status (None, or JSON null) is Ok(None).
    //
    // A null `observedGeneration` or `conditions` is absent, as it is in a
    // condition (SyncedCondition::parse): the CRD declares them `nullable:
    // true`, and a Go controller that serializes a status with no conditions
    // writes `"conditions": null`. Refusing it would make an ordinary inner
    // implementation's status unreadable. Everything else stays strict: a
    // string observedGeneration or an object `conditions` is still refused.
    pub fn parse(value: Option<&serde_json::Value>) -> Result<Option<SyncedStatus>, UnmarshalError> {
        let value = match value {
            None | Some(serde_json::Value::Null) => return Ok(None),
            Some(v) => v,
        };
        let object = value.as_object().ok_or(())?;
        if !object.get("observedGeneration").map_or(true, |v| v.as_i64().is_some() || v.is_null()) {
            return Err(());
        }
        if let Some(conditions) = object.get("conditions").filter(|v| !v.is_null()) {
            let items = conditions.as_array().ok_or(())?;
            for item in items {
                SyncedCondition::parse(item)?;
            }
        }
        Ok(Some(SyncedStatus { inner: value.clone() }))
    }

    pub fn as_json(&self) -> &serde_json::Value {
        &self.inner
    }

    // The fields SyncedStatusView reads: observedGeneration, the five fields of
    // each condition, and the remainder of the object.
    fn view_eq(a: &serde_json::Value, b: &serde_json::Value) -> bool {
        let og = |v: &serde_json::Value| v.get("observedGeneration").and_then(|x| x.as_i64());
        if og(a) != og(b) {
            return false;
        }
        let conditions = |v: &serde_json::Value| v.get("conditions").and_then(|x| x.as_array()).cloned();
        match (conditions(a), conditions(b)) {
            (None, None) => {}
            (Some(ca), Some(cb)) => {
                if ca.len() != cb.len() {
                    return false;
                }
                let field = |c: &serde_json::Value, key: &str| c.get(key).and_then(|x| x.as_str()).map(|s| s.to_string());
                let gen = |c: &serde_json::Value| c.get("observedGeneration").and_then(|x| x.as_i64());
                for (x, y) in ca.iter().zip(cb.iter()) {
                    if field(x, "type") != field(y, "type")
                        || field(x, "status") != field(y, "status")
                        || gen(x) != gen(y)
                        || field(x, "reason") != field(y, "reason")
                        || field(x, "message") != field(y, "message") {
                        return false;
                    }
                }
            }
            _ => return false,
        }
        let rest = |v: &serde_json::Value| {
            let mut o = v.as_object().cloned().unwrap_or_default();
            o.remove("observedGeneration");
            o.remove("conditions");
            o
        };
        rest(a) == rest(b)
    }
}

#[verifier(external)]
impl std::fmt::Debug for SyncedStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.inner.fmt(f) }
}

// The exec twin of spec::marshal_status: the value a status is stored as; an
// absent status is JSON null.
#[verifier(external_body)]
pub fn marshal_status(status: Option<SyncedStatus>) -> (v: RawValue)
    ensures v@ == spec::marshal_status(status.deep_view()),
{
    match status {
        Some(s) => RawValue { inner: s.inner },
        None => RawValue { inner: serde_json::Value::Null },
    }
}

// The cluster name the selector picks off a stored object, whatever its shape:
// the exec twin of spec::cluster_of_dynamic, for a controller that scans a List
// response. Trusted, and reading the same two places as SyncedObject::cluster_of.
#[verifier(external_body)]
pub fn cluster_of_dynamic(selector: &ClusterSelectorExec, obj: &DynamicObject) -> (res: Option<String>)
    ensures res.deep_view() == spec::cluster_of_dynamic(selector@, obj@),
{
    match selector {
        ClusterSelectorExec::Name => obj.as_kube_ref().metadata.name.clone(),
        ClusterSelectorExec::Field(path) => {
            let mut cur = obj.as_kube_ref().data.get("spec")?;
            for key in path.iter() {
                cur = cur.get(key)?;
            }
            cur.as_str().map(|s| s.to_string())
        }
    }
}

// An object of the shape, in the cluster it came from or is bound for. The
// ApiResource it was unmarshalled through is kept so that api_resource() can
// name the object's own kind.
#[verifier(external_body)]
pub struct SyncedObject {
    inner: kube::api::DynamicObject,
    cluster: ClusterId,
    api_resource: kube::api::ApiResource,
}

implement_view_trait!(SyncedObject, SyncedObjectView);
implement_deep_view_trait!(SyncedObject, SyncedObjectView);


impl std::clone::Clone for SyncedObject {
    #[verifier(external_body)]
    fn clone(&self) -> (res: SyncedObject)
        ensures res@ == self@,
    {
        SyncedObject { inner: self.inner.clone(), cluster: self.cluster.clone(), api_resource: self.api_resource.clone() }
    }
}

impl SyncedObject {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures final(self)@ == old(self)@.with_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    // The ApiResource of this object's kind in its cluster; the counterpart of
    // the typed wrappers' api_resource(), whose kind is the view's.
    #[verifier(external_body)]
    pub fn api_resource(&self) -> (res: ApiResource)
        ensures res@.kind == self@.kind,
    {
        ApiResource::from_kube_in(self.api_resource.clone(), self.cluster.clone())
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == spec::marshal(self@),
    {
        DynamicObject::from_kube_in(self.inner, self.cluster)
    }

    // Whether obj has the model kind of `entry` in `cluster`: it carries the
    // cluster's tag and the kube apiVersion and kind of the entry's resource.
    // The exec counterpart of `obj@.kind == model_kind(entry@, cluster@)`, as
    // the typed wrappers' has_kind is of `obj@.kind == View::kind()`; trusted like
    // unmarshal, with which it agrees.
    #[verifier(external_body)]
    pub fn has_kind(entry: &RegistryEntry, cluster: &ClusterId, obj: &DynamicObject) -> (b: bool)
        ensures b == (obj@.kind == model_kind(entry@, cluster@)),
    {
        obj.cluster().eq(cluster) && kube_types_match(entry.kube_api_resource(), obj.as_kube_ref())
    }

    // unmarshal accepts an object of the entry's kind in `cluster` whose status
    // has the shape, and nothing else.
    #[verifier(external_body)]
    pub fn unmarshal(entry: &RegistryEntry, cluster: &ClusterId, obj: DynamicObject) -> (res: Result<SyncedObject, UnmarshalError>)
        ensures
            res is Ok == spec::unmarshal(model_kind(entry@, cluster@), obj@) is Ok,
            res is Ok ==> res->Ok_0@ == spec::unmarshal(model_kind(entry@, cluster@), obj@)->Ok_0,
    {
        if !Self::has_kind(entry, cluster, &obj) {
            return Err(());
        }
        let inner = obj.into_kube();
        SyncedStatus::parse(inner.data.get("status"))?;
        Ok(SyncedObject { inner, cluster: cluster.clone(), api_resource: entry.kube_api_resource().clone() })
    }

    // A new object of the entry's kind in `cluster`, with this metadata and spec
    // and no status: what a controller builds when it creates an object of a kind
    // it was given at boot. Trusted like unmarshal, and the counterpart of the
    // typed wrappers' default().
    #[verifier(external_body)]
    pub fn new(entry: &RegistryEntry, cluster: &ClusterId, metadata: ObjectMeta, spec: RawValue) -> (o: SyncedObject)
        ensures o@ == (SyncedObjectView {
            kind: model_kind(entry@, cluster@),
            metadata: metadata@,
            spec: spec@,
            status: None,
        }),
    {
        let api_resource = entry.kube_api_resource().clone();
        let mut inner = kube::api::DynamicObject::new("", &api_resource);
        inner.metadata = metadata.into_kube();
        inner.data = serde_json::Value::Object(serde_json::Map::new());
        set_data_member(&mut inner, "spec", spec.inner);
        SyncedObject { inner, cluster: cluster.clone(), api_resource }
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: RawValue)
        ensures spec@ == self@.spec,
    {
        RawValue { inner: self.inner.data.get("spec").cloned().unwrap_or(serde_json::Value::Null) }
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: RawValue)
        ensures final(self)@ == old(self)@.with_spec(spec@),
    {
        set_data_member(&mut self.inner, "spec", spec.inner);
    }

    #[verifier(external_body)]
    pub fn status(&self) -> (status: Option<SyncedStatus>)
        ensures
            status is Some == self@.status is Some,
            status is Some ==> status->0@ == self@.status->0,
    {
        // The shape was checked by unmarshal, and set_status writes a status of
        // the shape; a failure here cannot happen and reads as no status.
        SyncedStatus::parse(self.inner.data.get("status")).unwrap_or(None)
    }

    #[verifier(external_body)]
    pub fn set_status(&mut self, status: SyncedStatus)
        ensures final(self)@ == old(self)@.with_status(Some(status@)),
    {
        set_data_member(&mut self.inner, "status", status.inner);
    }

    pub fn well_formed(&self) -> (b: bool)
        ensures b == self@.metadata.well_formed_for_namespaced(),
    {
        self.metadata().well_formed_for_namespaced()
    }

    // The cluster name the selector picks off this object (spec::cluster_of).
    pub fn cluster_of(&self, selector: &ClusterSelectorExec) -> (res: Option<String>)
        ensures res.deep_view() == spec::cluster_of(selector@, self@),
    {
        match selector {
            ClusterSelectorExec::Name => self.metadata().name(),
            ClusterSelectorExec::Field(path) => self.spec().field(path),
        }
    }
}

#[verifier(external)]
impl SyncedObject {
    pub fn as_kube_ref(&self) -> &kube::api::DynamicObject {
        &self.inner
    }

    pub fn into_kube(self) -> kube::api::DynamicObject {
        self.inner
    }

    pub fn cluster(&self) -> &ClusterId {
        &self.cluster
    }
}

#[verifier(external)]
impl std::fmt::Debug for SyncedObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.inner.fmt(f) }
}

// kube_types_match reports whether obj's type metadata names the resource:
// the same apiVersion and kind. An object without type metadata (a list item
// the shim did not stamp) matches nothing.
#[verifier(external)]
fn kube_types_match(api_resource: &kube::api::ApiResource, obj: &kube::api::DynamicObject) -> bool {
    match obj.types.as_ref() {
        Some(types) => types.api_version == api_resource.api_version && types.kind == api_resource.kind,
        None => false,
    }
}

#[verifier(external)]
fn json_string(value: &serde_json::Value, key: &str) -> Option<String> {
    value.get(key).and_then(|v| v.as_str()).map(|s| s.to_string())
}

// set_data_member replaces the top-level member `key` of the object's data; a
// null value removes it, which is how an absent status is written.
#[verifier(external)]
fn set_data_member(obj: &mut kube::api::DynamicObject, key: &str, value: serde_json::Value) {
    if !obj.data.is_object() {
        obj.data = serde_json::Value::Object(serde_json::Map::new());
    }
    let object = obj.data.as_object_mut().unwrap();
    if value.is_null() {
        object.remove(key);
    } else {
        object.insert(key.to_string(), value);
    }
}

}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn widget_resource() -> kube::api::ApiResource {
        kube::api::ApiResource::from_gvk_with_plural(
            &kube::api::GroupVersionKind::gvk("anvil.dev", "v1", "Widget"),
            "widgets",
        )
    }

    fn entry() -> RegistryEntry {
        RegistryEntry::new(widget_resource())
    }

    fn remote() -> ClusterId {
        ClusterId::remote("default".to_string(), "a".to_string())
    }

    // An object of the Widget kind with the given spec and status, tagged with the cluster.
    fn object(kind: Option<&str>, cluster: ClusterId, spec: serde_json::Value, status: Option<serde_json::Value>) -> DynamicObject {
        let mut obj = kube::api::DynamicObject::new("w", &widget_resource()).within("ns");
        obj.metadata.resource_version = Some("1".to_string());
        obj.metadata.uid = Some("u".to_string());
        obj.types = kind.map(|k| kube::api::TypeMeta { api_version: "anvil.dev/v1".to_string(), kind: k.to_string() });
        let mut data = serde_json::Map::new();
        data.insert("spec".to_string(), spec);
        if let Some(s) = status {
            data.insert("status".to_string(), s);
        }
        obj.data = serde_json::Value::Object(data);
        DynamicObject::from_kube_in(obj, cluster)
    }

    #[test]
    fn crd_name_is_plural_dot_group() {
        assert_eq!(entry().crd_name(), "widgets.anvil.dev");
        let core = RegistryEntry::new(kube::api::ApiResource::erase::<k8s_openapi::api::core::v1::ConfigMap>(&()));
        assert_eq!(core.crd_name(), "configmaps");
    }

    #[test]
    fn api_resource_carries_the_cluster() {
        let e = entry();
        assert_eq!(e.api_resource(&ClusterId::Primary).cluster(), ClusterId::Primary);
        assert_eq!(e.api_resource(&remote()).cluster(), remote());
        assert_eq!(e.api_resource(&remote()).as_kube_ref().plural, "widgets");
        let mut registry = Registry::new();
        registry.push(e);
        assert_eq!(registry.len(), 1);
        assert_eq!(registry.api_resource(0, &remote()).cluster(), remote());
    }

    // The kind test follows the cluster tag and the kube type metadata, and does
    // not panic on a list item without type metadata.
    #[test]
    fn has_kind_follows_tag_and_kube_kind() {
        let e = entry();
        let spec = json!({});
        assert!(SyncedObject::has_kind(&e, &ClusterId::Primary, &object(Some("Widget"), ClusterId::Primary, spec.clone(), None)));
        assert!(!SyncedObject::has_kind(&e, &remote(), &object(Some("Widget"), ClusterId::Primary, spec.clone(), None)));
        assert!(SyncedObject::has_kind(&e, &remote(), &object(Some("Widget"), remote(), spec.clone(), None)));
        assert!(!SyncedObject::has_kind(&e, &ClusterId::Primary, &object(Some("Widget"), remote(), spec.clone(), None)));
        assert!(!SyncedObject::has_kind(&e, &remote(), &object(Some("Widget"), ClusterId::remote("default".to_string(), "b".to_string()), spec.clone(), None)));
        assert!(!SyncedObject::has_kind(&e, &ClusterId::Primary, &object(Some("widget"), ClusterId::Primary, spec.clone(), None)));
        assert!(!SyncedObject::has_kind(&e, &ClusterId::Primary, &object(Some("Gadget"), ClusterId::Primary, spec.clone(), None)));
        assert!(!SyncedObject::has_kind(&e, &ClusterId::Primary, &object(None, ClusterId::Primary, spec, None)));
    }

    // A status with fields beyond the shape round-trips: the extra fields are the
    // rest, and rebuilding the status from its parts gives the same value.
    #[test]
    fn status_with_extra_fields_round_trips() {
        let status = json!({
            "observedGeneration": 3,
            "conditions": [
                {"type": "Ready", "status": "True", "observedGeneration": 3, "reason": "Up", "message": "all good"},
                {"type": "Stalled", "status": "False"}
            ],
            "ready": true,
            "observedCount": 2,
            "nested": {"a": [1, 2]}
        });
        let obj = object(Some("Widget"), ClusterId::Primary, json!({"count": 2}), Some(status.clone()));
        let synced = SyncedObject::unmarshal(&entry(), &ClusterId::Primary, obj).unwrap();
        let s = synced.status().expect("a status");
        assert_eq!(s.observed_generation(), Some(3));
        assert_eq!(s.rest().as_json(), &json!({"ready": true, "observedCount": 2, "nested": {"a": [1, 2]}}));
        let rebuilt = SyncedStatus::new(s.observed_generation(), s.conditions(), s.rest());
        assert_eq!(rebuilt.as_json(), &status);
        assert_eq!(marshal_status(Some(rebuilt)).as_json(), &status);
        assert!(marshal_status(None).as_json().is_null());

        // The object marshals back to what it was, tag included.
        let back = synced.clone().marshal();
        assert_eq!(back.cluster(), ClusterId::Primary);
        assert_eq!(back.as_kube_ref().data, json!({"spec": {"count": 2}, "status": status}));

        // set_status replaces the status; rest from another status is carried over
        // without its own observedGeneration and conditions.
        let mut edited = synced.clone();
        let outer = SyncedStatus::new(Some(7), Some(vec![SyncedCondition::new("Synced".to_string(), "True".to_string(), Some(7), Some("Synced".to_string()), None)]), s.rest());
        edited.set_status(outer);
        let edited_status = edited.status().unwrap();
        assert_eq!(edited_status.observed_generation(), Some(7));
        assert_eq!(edited_status.conditions().unwrap().len(), 1);
        assert_eq!(edited_status.rest().as_json(), s.rest().as_json());
        // A status of the explicit fields alone: empty_rest() is the remainder
        // of a status that carries nothing else, and the fields are written
        // over it.
        let bare = SyncedStatus::new(None, None, RawValue::empty_rest());
        assert_eq!(bare.as_json(), &json!({}));
        assert_eq!(bare.observed_generation(), None);
        assert!(bare.conditions().is_none());
        assert_eq!(bare.rest().as_json(), &json!({}));
        let generation_only = SyncedStatus::new(Some(9), None, RawValue::empty_rest());
        assert_eq!(generation_only.as_json(), &json!({"observedGeneration": 9}));
        assert_eq!(generation_only.rest().as_json(), &json!({}));
    }

    #[test]
    fn missing_status_is_none() {
        let obj = object(Some("Widget"), remote(), json!({"count": 1}), None);
        let synced = SyncedObject::unmarshal(&entry(), &remote(), obj).unwrap();
        assert!(synced.status().is_none());
        let null = object(Some("Widget"), remote(), json!({"count": 1}), Some(serde_json::Value::Null));
        assert!(SyncedObject::unmarshal(&entry(), &remote(), null).unwrap().status().is_none());
        // A status outside the shape is refused, as is the wrong tag or kind.
        let bad = object(Some("Widget"), remote(), json!({}), Some(json!({"observedGeneration": "three"})));
        assert!(SyncedObject::unmarshal(&entry(), &remote(), bad).is_err());
        let bad = object(Some("Widget"), remote(), json!({}), Some(json!({"conditions": [{"type": "Ready"}]})));
        assert!(SyncedObject::unmarshal(&entry(), &remote(), bad).is_err());
        let bad = object(Some("Widget"), remote(), json!({}), Some(json!({"conditions": {}})));
        assert!(SyncedObject::unmarshal(&entry(), &remote(), bad).is_err());
        let bad = object(Some("Widget"), remote(), json!({}), Some(json!("up")));
        assert!(SyncedObject::unmarshal(&entry(), &remote(), bad).is_err());
        let wrong_tag = object(Some("Widget"), ClusterId::Primary, json!({}), None);
        assert!(SyncedObject::unmarshal(&entry(), &remote(), wrong_tag).is_err());
        let wrong_kind = object(Some("Gadget"), remote(), json!({}), None);
        assert!(SyncedObject::unmarshal(&entry(), &remote(), wrong_kind).is_err());
    }

    // The CRD declares observedGeneration, conditions, reason and message
    // `nullable: true`, and a Go controller that serializes an empty pointer or
    // slice writes `null` rather than leaving the key out. A null is absent,
    // wherever it appears, and the status is otherwise as strict as it was.
    #[test]
    fn null_is_absent_in_a_status_and_in_a_condition() {
        let null_fields = json!({
            "observedGeneration": null,
            "conditions": null,
            "ready": true
        });
        let obj = object(Some("Widget"), remote(), json!({}), Some(null_fields));
        let synced = SyncedObject::unmarshal(&entry(), &remote(), obj).expect("nulls read as absent");
        let s = synced.status().expect("a status");
        assert_eq!(s.observed_generation(), None);
        assert!(s.conditions().is_none());
        assert_eq!(s.rest().as_json(), &json!({"ready": true}));

        let null_in_condition = json!({
            "conditions": [
                {"type": "Ready", "status": "True", "observedGeneration": null, "reason": null, "message": null}
            ]
        });
        let obj = object(Some("Widget"), remote(), json!({}), Some(null_in_condition));
        let synced = SyncedObject::unmarshal(&entry(), &remote(), obj).expect("nulls read as absent");
        let conditions = synced.status().unwrap().conditions().expect("the conditions");
        assert_eq!(conditions[0].observed_generation(), None);
        assert_eq!(conditions[0].reason(), None);
        assert_eq!(conditions[0].message(), None);

        // A null `type` or `status` is not a condition with a default: those two
        // are required, and the other wrong types are refused as before.
        for bad in [
            json!({"conditions": [{"type": null, "status": "True"}]}),
            json!({"conditions": [{"type": "Ready", "status": null}]}),
            json!({"conditions": [{"type": "Ready", "status": "True", "reason": 7}]}),
            json!({"conditions": [{"type": "Ready", "status": "True", "observedGeneration": "three"}]}),
            json!({"observedGeneration": "three"}),
            json!({"conditions": {}}),
        ] {
            let obj = object(Some("Widget"), remote(), json!({}), Some(bad.clone()));
            assert!(SyncedObject::unmarshal(&entry(), &remote(), obj).is_err(), "{}", bad);
        }
    }

    // eq is equality of the view, and a null field is absent in the view, so a
    // status that writes its nulls equals one that leaves the keys out.
    #[test]
    fn a_status_with_null_fields_equals_one_without_the_keys() {
        let parse = |v: serde_json::Value| SyncedStatus::parse(Some(&v)).unwrap().unwrap();
        let with_nulls = parse(json!({"observedGeneration": null, "conditions": null, "ready": true}));
        let without = parse(json!({"ready": true}));
        assert!(with_nulls.eq(&without));
        assert!(without.eq(&with_nulls));
        assert!(with_nulls.rest().eq(&without.rest()));

        let null_in_condition = parse(json!({
            "conditions": [{"type": "Ready", "status": "True", "reason": null, "message": null}]
        }));
        let without_keys = parse(json!({"conditions": [{"type": "Ready", "status": "True"}]}));
        assert!(null_in_condition.eq(&without_keys));

        // A present value is still not an absent one.
        assert!(!with_nulls.eq(&parse(json!({"observedGeneration": 1, "ready": true}))));
        assert!(!with_nulls.eq(&parse(json!({"conditions": [], "ready": true}))));
    }

    #[test]
    fn conditions_parse() {
        let status = json!({
            "conditions": [
                {"type": "Ready", "status": "True", "observedGeneration": 4, "reason": "Up", "message": "m", "lastTransitionTime": "t"},
                {"type": "Stalled", "status": "False"}
            ]
        });
        let obj = object(Some("Widget"), ClusterId::Primary, json!({}), Some(status));
        let synced = SyncedObject::unmarshal(&entry(), &ClusterId::Primary, obj).unwrap();
        let s = synced.status().unwrap();
        assert_eq!(s.observed_generation(), None);
        let conditions = s.conditions().unwrap();
        assert_eq!(conditions.len(), 2);
        assert_eq!(conditions[0].type_(), "Ready");
        assert_eq!(conditions[0].status(), "True");
        assert_eq!(conditions[0].observed_generation(), Some(4));
        assert_eq!(conditions[0].reason(), Some("Up".to_string()));
        assert_eq!(conditions[0].message(), Some("m".to_string()));
        assert_eq!(conditions[1].type_(), "Stalled");
        assert_eq!(conditions[1].observed_generation(), None);
        assert_eq!(conditions[1].reason(), None);
        assert_eq!(conditions[1].message(), None);
        let built = SyncedCondition::new("Synced".to_string(), "False".to_string(), None, Some("NotSynced".to_string()), None);
        assert_eq!(built.as_json(), &json!({"type": "Synced", "status": "False", "reason": "NotSynced"}));
    }

    #[test]
    fn spec_field_on_a_nested_path() {
        let spec = json!({"clusterName": "a", "placement": {"cluster": {"name": "b"}, "count": 3}});
        let obj = object(Some("Widget"), ClusterId::Primary, spec.clone(), None);
        let synced = SyncedObject::unmarshal(&entry(), &ClusterId::Primary, obj).unwrap();
        let path = |keys: &[&str]| keys.iter().map(|k| k.to_string()).collect::<Vec<_>>();
        assert_eq!(synced.spec().field(&path(&["clusterName"])), Some("a".to_string()));
        assert_eq!(synced.spec().field(&path(&["placement", "cluster", "name"])), Some("b".to_string()));
        assert_eq!(synced.spec().field(&path(&["placement", "count"])), None);
        assert_eq!(synced.spec().field(&path(&["missing"])), None);
        assert_eq!(synced.spec().field(&path(&["clusterName", "deeper"])), None);
        assert_eq!(synced.cluster_of(&ClusterSelectorExec::Field(path(&["placement", "cluster", "name"]))), Some("b".to_string()));
        assert_eq!(synced.cluster_of(&ClusterSelectorExec::Name), Some("w".to_string()));
        assert!(synced.spec().eq(&RawValue::from_json(spec.clone())));
        let mut edited = synced.clone();
        edited.set_spec(RawValue::from_json(json!({"clusterName": "c"})));
        assert_eq!(edited.cluster_of(&ClusterSelectorExec::Field(path(&["clusterName"]))), Some("c".to_string()));
        assert!(!edited.spec().eq(&RawValue::from_json(spec)));
        assert!(edited.well_formed());
    }
}
