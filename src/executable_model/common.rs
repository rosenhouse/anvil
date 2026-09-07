use crate::executable_model::string_set::*;
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{api_resource::ApiResource, prelude::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine as model, api_server::types as model_types,
};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::string::*;

// We use ExternalObjectRef, instead of KubeObjectRef, as the key of the ObjectMap
// because the key has to implement a few traits including Ord and PartialOrd.
// It's easy to implement such traits for ExternalObjectRef but hard for KubeObjectRef
// because it internally uses vstd::string::String, which does not implement such traits.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct ExternalObjectRef {
    pub kind: KindExec,
    pub name: std::string::String,
    pub namespace: std::string::String,
}

impl KubeObjectRef {
    pub fn into_external_object_ref(self) -> ExternalObjectRef {
        ExternalObjectRef {
            kind: self.kind.clone(),
            name: self.name,
            namespace: self.namespace,
        }
    }
}

verus! {

pub struct KubeObjectRef {
    pub kind: KindExec,
    pub name: String,
    pub namespace: String,
}

impl View for KubeObjectRef {
    type V = ObjectRef;
    open spec fn view(&self) -> ObjectRef {
        ObjectRef {
            kind: self.kind@,
            name: self.name@,
            namespace: self.namespace@,
        }
    }
}

impl std::clone::Clone for KubeObjectRef {
    fn clone(&self) -> (result: Self)
        ensures result == self
    {
        KubeObjectRef {
            kind: self.kind.clone(),
            name: self.name.clone(),
            namespace: self.namespace.clone(),
        }
    }
}

// Maps a kind string to KindExec. Any kind that is not built in is a custom
// resource whose spec-level kind is the string itself, which is what the tests
// of the executable model rely on (SimpleCRView::kind() is "simple").
// Not a perfect implementation but sufficient for conformance tests.
#[verifier(external)]
fn kind_exec_from_str(kind: &str) -> KindExec {
    match kind {
        "ConfigMap" => KindExec::ConfigMapKind,
        "DaemonSet" => KindExec::DaemonSetKind,
        "PersistentVolumeClaim" => KindExec::PersistentVolumeClaimKind,
        "Pod" => KindExec::PodKind,
        "Role" => KindExec::RoleKind,
        "RoleBinding" => KindExec::RoleBindingKind,
        "StatefulSet" => KindExec::StatefulSetKind,
        "Service" => KindExec::ServiceKind,
        "ServiceAccount" => KindExec::ServiceAccountKind,
        "Secret" => KindExec::SecretKind,
        custom => KindExec::CustomResourceKind(custom.to_string()),
    }
}

impl ApiResource {
    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: KindExec)
        ensures kind@ == self@.kind,
    {
        kind_exec_from_str(self.as_kube_ref().kind.as_str())
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (res: ApiResource)
        ensures res@ == self@,
    {
        ApiResource::from_kube_in(self.as_kube_ref().clone(), self.cluster())
    }
}

impl PatchTests {
    // pass checks the `test` operations against the stored object, the way the
    // API server evaluates them before applying the rest of the JSON patch.
    #[verifier(external_body)]
    pub fn pass(&self, obj: &DynamicObject) -> (b: bool)
        ensures b == self@.pass(obj@),
    {
        let metadata = &obj.as_kube_ref().metadata;
        (self.uid_value().is_none() || self.uid_value() == metadata.uid)
        && (self.generation_value().is_none() || self.generation_value() == metadata.generation)
    }
}

impl Preconditions {
    #[verifier(external_body)]
    pub fn has_some_uid(&self) -> (b: bool)
        ensures b == self@.uid is Some,
    {
        self.as_kube_ref().uid.is_some()
    }

    #[verifier(external_body)]
    pub fn uid_eq(&self, metadata: &ObjectMeta) -> (b: bool)
        ensures b == (self@.uid == metadata@.uid),
    {
        self.as_kube_ref().uid == metadata.as_kube_ref().uid
    }

    #[verifier(external_body)]
    pub fn has_some_resource_version(&self) -> (b: bool)
        ensures b == self@.resource_version is Some,
    {
        self.as_kube_ref().resource_version.is_some()
    }

    #[verifier(external_body)]
    pub fn resource_version_eq(&self, metadata: &ObjectMeta) -> (b: bool)
        ensures b == (self@.resource_version == metadata@.resource_version),
    {
        self.as_kube_ref().resource_version == metadata.as_kube_ref().resource_version
    }
}

impl ObjectMeta {
    pub fn finalizers_as_set(&self) -> (ret: StringSet)
        ensures ret@ == self@.finalizers_as_set()
    {
        if self.finalizers().is_none() {
            StringSet::empty()
        } else {
            string_vec_to_string_set(self.finalizers().unwrap())
        }
    }
}

impl DynamicObjectView {
    pub open spec fn without_deletion_timestamp(self) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                deletion_timestamp: None,
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn overwrite_deletion_stamp(self, deletion_timestamp: Option<StringView>) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                deletion_timestamp: deletion_timestamp,
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn overwrite_uid(self, uid: Option<int>) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                uid: uid,
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn overwrite_resource_version(self, resource_version: Option<int>) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                resource_version: resource_version,
                ..self.metadata
            },
            ..self
        }
    }

    // with_spec and with_status: see kubernetes_api_objects::spec::dynamic.
}

impl DynamicObject {
    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: KindExec)
        ensures kind@ == self@.kind,
    {
        if self.as_kube_ref().types.is_none() {
            panic!();
        }
        kind_exec_from_str(self.as_kube_ref().types.as_ref().unwrap().kind.as_str())
    }

    // We implement getter and setter functions of the DynamicObject
    // which are used by the exec API server model.

    #[verifier(external_body)]
    pub fn object_ref(&self) -> (object_ref: KubeObjectRef)
        requires
            self@.metadata.name is Some,
            self@.metadata.namespace is Some,
        ensures object_ref@ == self@.object_ref(),
    {
        KubeObjectRef {
            kind: self.kind(),
            name: self.metadata().name().unwrap(),
            namespace: self.metadata().namespace().unwrap(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures final(self)@ == old(self)@.with_name(name@),
    {
        self.as_kube_mut_ref().metadata.name = Some(name);
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures final(self)@ == old(self)@.with_namespace(namespace@),
    {
        self.as_kube_mut_ref().metadata.namespace = Some(namespace);
    }

    #[verifier(external_body)]
    pub fn set_resource_version(&mut self, resource_version: i64)
        ensures final(self)@ == old(self)@.with_resource_version(resource_version as int),
    {
        self.as_kube_mut_ref().metadata.resource_version = Some(resource_version.to_string());
    }

    #[verifier(external_body)]
    pub fn set_resource_version_from(&mut self, other: &DynamicObject)
        ensures final(self)@ == old(self)@.overwrite_resource_version(other@.metadata.resource_version),
    {
        self.as_kube_mut_ref().metadata.resource_version = other.as_kube_ref().metadata.resource_version.clone();
    }

    #[verifier(external_body)]
    pub fn set_uid(&mut self, uid: i64)
        ensures final(self)@ == old(self)@.with_uid(uid as int),
    {
        self.as_kube_mut_ref().metadata.uid = Some(uid.to_string());
    }

    #[verifier(external_body)]
    pub fn set_uid_from(&mut self, other: &DynamicObject)
        ensures final(self)@ == old(self)@.overwrite_uid(other@.metadata.uid),
    {
        self.as_kube_mut_ref().metadata.uid = other.as_kube_ref().metadata.uid.clone();
    }

    #[verifier(external_body)]
    pub fn unset_deletion_timestamp(&mut self)
        ensures final(self)@ == old(self)@.without_deletion_timestamp(),
    {
        self.as_kube_mut_ref().metadata.deletion_timestamp = None;
    }

    // Built-in kinds keep generation unmodeled (None); custom resources follow the model's rules.
    // Mirrors the kind list in kind() above.
    #[verifier(external)]
    fn is_builtin_kind(&self) -> bool {
        match self.as_kube_ref().types.as_ref().map(|t| t.kind.as_str()) {
            Some("ConfigMap") | Some("DaemonSet") | Some("PersistentVolumeClaim") | Some("Pod")
            | Some("Role") | Some("RoleBinding") | Some("StatefulSet") | Some("Service")
            | Some("ServiceAccount") | Some("Secret") => true,
            _ => false,
        }
    }

    #[verifier(external)]
    fn spec_json(&self) -> Option<&serde_json::Value> {
        self.as_kube_ref().data.get("spec")
    }

    #[verifier(external_body)]
    pub fn set_initial_generation(&mut self)
        ensures final(self)@ == old(self)@.with_generation(model::initial_generation(old(self)@.kind)),
    {
        self.as_kube_mut_ref().metadata.generation = if self.is_builtin_kind() { None } else { Some(1) };
    }

    #[verifier(external_body)]
    pub fn set_bumped_generation(&mut self)
        ensures final(self)@ == old(self)@.with_generation(model::bumped_generation(old(self)@)),
    {
        self.as_kube_mut_ref().metadata.generation = if self.is_builtin_kind() {
            None
        } else {
            Some(self.as_kube_ref().metadata.generation.unwrap_or(0) + 1)
        };
    }

    // Sets this object's generation to what the API server assigns when this object's spec
    // replaces other's spec: bumped iff the spec changed.
    #[verifier(external_body)]
    pub fn set_next_generation_from(&mut self, other: &DynamicObject)
        ensures final(self)@ == old(self)@.with_generation(model::next_generation(other@, old(self)@.spec)),
    {
        self.as_kube_mut_ref().metadata.generation = if self.is_builtin_kind() {
            None
        } else if self.spec_json() != other.spec_json() {
            Some(other.as_kube_ref().metadata.generation.unwrap_or(0) + 1)
        } else {
            other.as_kube_ref().metadata.generation
        };
    }

    #[verifier(external_body)]
    pub fn set_deletion_timestamp_from(&mut self, other: &DynamicObject)
        ensures final(self)@ == old(self)@.overwrite_deletion_stamp(other@.metadata.deletion_timestamp),
    {
        self.as_kube_mut_ref().metadata.deletion_timestamp = other.as_kube_ref().metadata.deletion_timestamp.clone();
    }


    // This function sets the deletion timestamp to the current time.
    // This seems a bit inconsistent with the model's behavior which
    // always sets it to the return value of deletion_timestamp().
    // However, this function is actually closer to Kubernetes' real behavior.
    #[verifier(external_body)]
    pub fn set_current_deletion_timestamp(&mut self)
        ensures final(self)@ == old(self)@.with_deletion_timestamp(model::deletion_timestamp()),
    {
        self.as_kube_mut_ref().metadata.deletion_timestamp = Some(k8s_openapi::apimachinery::pkg::apis::meta::v1::Time(chrono::Utc::now()));
    }

    #[verifier(external_body)]
    pub fn eq(&self, other: &DynamicObject) -> (ret: bool)
        ensures ret == (self@ == other@)
    {
        self.as_kube_ref() == other.as_kube_ref()
    }

    #[verifier(external_body)]
    pub fn set_metadata_from(&mut self, other: &DynamicObject)
        ensures final(self)@ == old(self)@.with_metadata(other@.metadata)
    {
        self.as_kube_mut_ref().metadata = other.as_kube_ref().metadata.clone()
    }

    // In a kube DynamicObject everything but the type and object metadata lives
    // in `data`, a JSON object. The model's `status` is data["status"] and the
    // model's `spec` is everything else in data (a built-in kind such as
    // ConfigMap has no "spec" key; its payload is still the model's spec).
    #[verifier(external)]
    fn status_json(&self) -> Option<serde_json::Value> {
        self.as_kube_ref().data.get("status").cloned()
    }

    #[verifier(external)]
    fn set_status_json(&mut self, status: Option<serde_json::Value>) {
        let data = &mut self.as_kube_mut_ref().data;
        match status {
            // serde_json turns a Null `data` into an object on insertion
            Some(status) => data["status"] = status,
            None => if let Some(data) = data.as_object_mut() { data.remove("status"); },
        }
    }

    #[verifier(external_body)]
    pub fn set_spec_from(&mut self, other: &DynamicObject)
        ensures final(self)@ == old(self)@.with_spec(other@.spec)
    {
        let status = self.status_json();
        self.as_kube_mut_ref().data = other.as_kube_ref().data.clone();
        self.set_status_json(status);
    }

    #[verifier(external_body)]
    pub fn set_status_from(&mut self, other: &DynamicObject)
        ensures final(self)@ == old(self)@.with_status(other@.status)
    {
        self.set_status_json(other.status_json());
    }

    #[verifier(external_body)]
    pub fn set_default_status(&mut self, Ghost(installed_types): Ghost<model_types::InstalledTypes>)
        ensures
            final(self)@ == old(self)@.with_status(model::marshalled_default_status(old(self)@.kind, installed_types)),
            model::unmarshallable_status(final(self)@, installed_types),
    {}
}

// We implement the validation logic in exec code for different k8s object types below
// which are called by the exec API server model.
// These validation functions must conform to their correspondences of the spec-level objects.

impl ConfigMap {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { true }

    pub fn transition_validation(&self, old_obj: &ConfigMap) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl DaemonSet {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }

    pub fn transition_validation(&self, old_obj: &DaemonSet) -> (ret: bool)
        requires
            self@.state_validation(),
            old_obj@.state_validation(),
        ensures ret == self@.transition_validation(old_obj@)
    {
        self.spec().unwrap().selector().eq(&old_obj.spec().unwrap().selector())
    }
}

impl Pod {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }

    pub fn transition_validation(&self, old_obj: &Pod) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl PersistentVolumeClaim {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }

    pub fn transition_validation(&self, old_obj: &PersistentVolumeClaim) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl PolicyRule {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        self.api_groups().is_some()
        && self.api_groups().as_ref().unwrap().len() > 0
        && self.resources().is_some()
        && self.resources().as_ref().unwrap().len() > 0
        && self.verbs().len() > 0
    }
}

impl Role {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        if self.rules().is_some() {
            let policy_rules = self.rules().unwrap();
            let mut all_valid = true;
            for i in 0..policy_rules.len()
                invariant
                    all_valid == (forall |j| 0 <= j < i ==> #[trigger] policy_rules.deep_view()[j].state_validation()),
            {
                let valid = policy_rules[i].state_validation();
                proof { assert(policy_rules.deep_view()[i as int] == policy_rules@[i as int]@); }
                all_valid = all_valid && valid;
            }
            all_valid
        } else {
            true
        }
    }

    pub fn transition_validation(&self, old_obj: &Role) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl RoleBinding {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        self.role_ref().api_group().eq(&"rbac.authorization.k8s.io".to_string())
        && (self.role_ref().kind().eq(&"Role".to_string())
            || self.role_ref().kind().eq(&"ClusterRole".to_string()))
    }

    pub fn transition_validation(&self, old_obj: &RoleBinding) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    {
        self.role_ref().eq(&old_obj.role_ref())
    }
}

impl Secret {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { true }


    pub fn transition_validation(&self, old_obj: &Secret) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl Service {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }

    pub fn transition_validation(&self, old_obj: &Service) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl ServiceAccount {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { true }

    pub fn transition_validation(&self, old_obj: &ServiceAccount) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl StatefulSet {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        self.spec().is_some() && if self.spec().unwrap().replicas().is_some() {
            self.spec().unwrap().replicas().unwrap() >= 0
        } else {
            true
        }
    }

    pub fn transition_validation(&self, old_obj: &StatefulSet) -> (ret: bool)
        requires
            self@.state_validation(),
            old_obj@.state_validation(),
        ensures ret == self@.transition_validation(old_obj@)
    {
        self.spec().unwrap().immutable_fields_eq(&old_obj.spec().unwrap())
    }
}

impl StatefulSetSpec {
    // Every field other than replicas, template and
    // persistent_volume_claim_retention_policy is immutable (see
    // StatefulSetView::_transition_validation): the check is that old_spec
    // equals self with those three fields taken from old_spec.
    #[verifier(external_body)]
    pub fn immutable_fields_eq(&self, old_spec: &StatefulSetSpec) -> (b: bool)
        ensures b == (old_spec@ == StatefulSetSpecView {
            replicas: old_spec@.replicas,
            template: old_spec@.template,
            persistent_volume_claim_retention_policy: old_spec@.persistent_volume_claim_retention_policy,
            ..self@
        }),
    {
        let mut normalized = self.as_kube_ref().clone();
        normalized.replicas = old_spec.as_kube_ref().replicas.clone();
        normalized.template = old_spec.as_kube_ref().template.clone();
        normalized.persistent_volume_claim_retention_policy = old_spec.as_kube_ref().persistent_volume_claim_retention_policy.clone();
        normalized == *old_spec.as_kube_ref()
    }
}

// CustomResource is the trait that associates the exec methods (e.g., unmarshal)
// with their spec correspondences, and is only used for proving the executable API server model
// conforms to the spec model.
pub trait CustomResource: View
where Self::V: CustomResourceView, Self: std::marker::Sized
{
    fn unmarshal(obj: DynamicObject) -> (res: Result<Self, UnmarshalError>)
        ensures
            res is Ok == Self::V::unmarshal(obj@) is Ok,
            res is Ok ==> res->Ok_0@ == Self::V::unmarshal(obj@)->Ok_0;

    fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation();

    fn transition_validation(&self, old_obj: &Self) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@);
}

// SimpleCRView and SimpleCR are types only used for instantiating the executable API server model,
// which is only used for conformance tests, so we keep the two types minimal.

pub struct SimpleCRView {
    pub metadata: ObjectMetaView,
    pub spec: SimpleCRSpecView,
    pub status: Option<SimpleCRStatusView>,
}

pub struct SimpleCRSpecView {}

pub struct SimpleCRStatusView {}

impl ResourceView for SimpleCRView {
    type Spec = SimpleCRSpecView;
    type Status = Option<SimpleCRStatusView>;

    open spec fn default() -> SimpleCRView {
        SimpleCRView {
            metadata: ObjectMetaView::default(),
            spec: arbitrary(),
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView { self.metadata }

    open spec fn kind() -> Kind { Kind::CustomResourceKind("simple"@) }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> SimpleCRSpecView { self.spec }

    open spec fn status(self) -> Option<SimpleCRStatusView> { self.status }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: SimpleCRView::marshal_spec(self.spec),
            status: SimpleCRView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<SimpleCRView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !(SimpleCRView::unmarshal_spec(obj.spec) is Ok) {
            Err(())
        } else if !(SimpleCRView::unmarshal_status(obj.status) is Ok) {
            Err(())
        } else {
            Ok(SimpleCRView {
                metadata: obj.metadata,
                spec: SimpleCRView::unmarshal_spec(obj.spec)->Ok_0,
                status: SimpleCRView::unmarshal_status(obj.status)->Ok_0,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        SimpleCRView::marshal_spec_preserves_integrity();
        SimpleCRView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    uninterp spec fn marshal_spec(s: SimpleCRSpecView) -> Value;

    uninterp spec fn unmarshal_spec(v: Value) -> Result<SimpleCRSpecView, UnmarshalError>;

    uninterp spec fn marshal_status(s: Option<SimpleCRStatusView>) -> Value;

    uninterp spec fn unmarshal_status(v: Value) -> Result<Option<SimpleCRStatusView>, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool { true }

    open spec fn transition_validation(self, old_obj: SimpleCRView) -> bool { true }
}

impl CustomResourceView for SimpleCRView {
    proof fn kind_is_custom_resource() {}

    open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool { true }

    proof fn validation_result_determined_by_spec_and_status()
        ensures forall |obj: Self| #[trigger] obj.state_validation() == Self::spec_status_validation(obj.spec(), obj.status())
    {}
}

#[verifier(external_body)]
pub struct SimpleCR {}

impl View for SimpleCR {
    type V = SimpleCRView;

    uninterp spec fn view(&self) -> SimpleCRView;
}

impl CustomResource for SimpleCR {
    #[verifier(external_body)]
    fn unmarshal(obj: DynamicObject) -> (res: Result<SimpleCR, UnmarshalError>)
        ensures
            res is Ok == SimpleCRView::unmarshal(obj@) is Ok,
            res is Ok ==> res->Ok_0@ == SimpleCRView::unmarshal(obj@)->Ok_0,
    {
        Ok(SimpleCR {})
    }

    fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        true
    }

    fn transition_validation(&self, old_obj: &Self) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    {
        true
    }
}

#[verifier(external_body)]
pub fn filter_controller_references(owner_references: Vec<OwnerReference>) -> (ret: Vec<OwnerReference>)
    ensures ret.deep_view() == owner_references.deep_view().filter(|o: OwnerReferenceView| o.controller is Some && o.controller->0)
{
    // TODO: is there a way to prove postconditions involving filter?
    // TODO: clone the entire Vec instead of clone in map()
    owner_references.iter().map(|o: &OwnerReference| o.clone()).filter(|o: &OwnerReference| o.controller().is_some() && o.controller().unwrap()).collect()
}

#[verifier(external_body)]
pub fn string_vec_to_string_set(s: Vec<String>) -> (ret: StringSet)
    ensures ret@ == s.deep_view().to_set()
{
    StringSet::from_rust_set(s.into_iter().collect())
}

}
