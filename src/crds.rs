#![cfg_attr(verus_keep_ghost, verifier::allow(unknown_automatic_derive))]
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("ShimLayerError: {0}")]
    ShimLayerError(String),
    #[error("ReconcileCoreError")]
    ReconcileCoreError,
}

#[derive(
    kube::CustomResource,
    Default,
    Debug,
    Clone,
    serde::Deserialize,
    serde::Serialize,
    schemars::JsonSchema,
    PartialEq,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "VReplicaSet")]
#[kube(shortname = "vrs", namespaced)]
#[kube(status = "VReplicaSetStatus")]
pub struct VReplicaSetSpec {
    pub replicas: Option<i32>,
    pub selector: k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector,
    pub template: Option<k8s_openapi::api::core::v1::PodTemplateSpec>,
}

#[derive(Clone, Debug, Default, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct VReplicaSetStatus {
    pub replicas: i32,
}

impl Default for VReplicaSet {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: VReplicaSetSpec::default(),
            status: None,
        }
    }
}

#[derive(
    kube::CustomResource,
    Default,
    Debug,
    Clone,
    serde::Deserialize,
    serde::Serialize,
    schemars::JsonSchema,
    PartialEq,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "VDeployment")]
#[kube(shortname = "vd", namespaced)]
pub struct VDeploymentSpec {
    pub replicas: Option<i32>,
    pub selector: k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector,
    pub template: k8s_openapi::api::core::v1::PodTemplateSpec,
    #[serde(rename = "minReadySeconds")]
    pub min_ready_seconds: Option<i32>,
    pub strategy: Option<k8s_openapi::api::apps::v1::DeploymentStrategy>,
    #[serde(rename = "revisionHistoryLimit")]
    pub revision_history_limit: Option<i32>,
    #[serde(rename = "progressDeadlineSeconds")]
    pub progress_deadline_seconds: Option<i32>,
    pub paused: Option<bool>,
}

impl Default for VDeployment {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: VDeploymentSpec::default(),
        }
    }
}

#[derive(
    kube::CustomResource,
    Default,
    Debug,
    Clone,
    serde::Deserialize,
    serde::Serialize,
    schemars::JsonSchema,
    PartialEq,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "VStatefulSet")]
#[kube(shortname = "vsts", namespaced)]
#[kube(status = "VStatefulSetStatus")]
pub struct VStatefulSetSpec {
    #[serde(rename = "serviceName")]
    pub service_name: String,
    pub selector: k8s_openapi::apimachinery::pkg::apis::meta::v1::LabelSelector,
    pub template: k8s_openapi::api::core::v1::PodTemplateSpec,
    pub replicas: Option<i32>,
    #[serde(rename = "updateStrategy")]
    pub update_strategy: Option<k8s_openapi::api::apps::v1::StatefulSetUpdateStrategy>,
    #[serde(rename = "podManagementPolicy")]
    pub pod_management_policy: Option<String>,
    #[serde(rename = "revisionHistoryLimit")]
    pub revision_history_limit: Option<i32>,
    #[serde(rename = "volumeClaimTemplates")]
    pub volume_claim_templates: Option<Vec<k8s_openapi::api::core::v1::PersistentVolumeClaim>>,
    #[serde(rename = "minReadySeconds")]
    pub min_ready_seconds: Option<i32>,
    #[serde(rename = "persistentVolumeClaimRetentionPolicy")]
    pub persistent_volume_claim_retention_policy:
        Option<k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy>,
    pub ordinals: Option<k8s_openapi::api::apps::v1::StatefulSetOrdinals>,
}

#[derive(
    Clone, Debug, Default, serde::Deserialize, serde::Serialize, schemars::JsonSchema, PartialEq,
)]
pub struct VStatefulSetStatus {
    pub replicas: i32,
    #[serde(rename = "readyReplicas")]
    pub ready_replicas: Option<i32>,
    #[serde(rename = "currentReplicas")]
    pub current_replicas: Option<i32>,
    #[serde(rename = "updatedReplicas")]
    pub updated_replicas: Option<i32>,
    #[serde(rename = "availableReplicas")]
    pub available_replicas: Option<i32>,
    #[serde(rename = "collisionCount")]
    pub collision_count: Option<i32>,
    pub conditions: Option<Vec<k8s_openapi::api::apps::v1::StatefulSetCondition>>,
    #[serde(rename = "currentRevision")]
    pub current_revision: Option<String>,
    #[serde(rename = "updateRevision")]
    pub update_revision: Option<String>,
    #[serde(rename = "observedGeneration")]
    pub observed_generation: Option<i64>,
}

impl Default for VStatefulSet {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: VStatefulSetSpec::default(),
            status: None,
        }
    }
}

impl VStatefulSetSpec {
    // (1) create VStatefulSet through VStatefulSetSpec using macros from k8s_openapi,
    // (2) reuse the wrapper type of k8s_openapi::api::apps::v1::StatefulSetSpec for VStatefulSet
    //     instead of creating a new wrapper type for VStatefulSetSpec.
    pub fn to_native(&self) -> k8s_openapi::api::apps::v1::StatefulSetSpec {
        k8s_openapi::api::apps::v1::StatefulSetSpec {
            service_name: self.service_name.clone(),
            selector: self.selector.clone(),
            template: self.template.clone(),
            replicas: self.replicas.clone(),
            update_strategy: self.update_strategy.clone(),
            pod_management_policy: self.pod_management_policy.clone(),
            revision_history_limit: self.revision_history_limit.clone(),
            volume_claim_templates: self.volume_claim_templates.clone(),
            min_ready_seconds: self.min_ready_seconds.clone(),
            persistent_volume_claim_retention_policy: self
                .persistent_volume_claim_retention_policy
                .clone(),
            ordinals: self.ordinals.clone(),
        }
    }
}

// Widget is the custom resource the widget sync controller mirrors from the
// outer cluster into an inner one. The same kind is installed in both: the outer copy is
// reconciled by the widget sync controller, the inner copy by whatever
// implementation the inner cluster runs (in the demo, the widget echo controller).
// `clusterName` selects the cluster (the kind's selector is `field:spec.clusterName`);
// `count` and `message` are opaque payload as far as the sync controller is concerned.
#[derive(
    kube::CustomResource,
    Default,
    Debug,
    Clone,
    serde::Deserialize,
    serde::Serialize,
    schemars::JsonSchema,
    PartialEq,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "Widget")]
#[kube(shortname = "wdg", namespaced)]
#[kube(status = "WidgetStatus")]
pub struct WidgetSpec {
    /// The name of the binding whose cluster receives the mirror. Immutable.
    // The immutability is the CEL rule `self == oldSelf` on the field in
    // deploy/widget_sync/crd.yaml; kube-derive 0.91 cannot express it, so the
    // YAML is checked against the export by crd_manifest_tests below.
    #[serde(rename = "clusterName")]
    pub cluster_name: String,
    pub count: i32,
    pub message: Option<String>,
}

/// The status of a Widget. On an inner copy it is written by the inner implementation;
/// on an outer copy it is written by the sync controller, which mirrors the inner
/// copy's data fields and combines its conditions with its own.
#[derive(
    Clone, Debug, Default, serde::Deserialize, serde::Serialize, schemars::JsonSchema, PartialEq,
)]
pub struct WidgetStatus {
    /// The generation of this object that the writer of this status last processed.
    /// On an outer copy the sync controller stamps the generation it reconciled on
    /// every write, including the ones that report a failure.
    #[serde(rename = "observedGeneration")]
    pub observed_generation: Option<i64>,
    /// Mirrored from the inner copy while Synced is True; otherwise kept as last reported.
    /// A data field, not the Ready condition: while Synced is False the two can disagree.
    pub ready: Option<bool>,
    /// Mirrored from the inner copy while Synced is True; otherwise kept as last reported.
    #[serde(rename = "observedCount")]
    pub observed_count: Option<i32>,
    /// On an outer copy: Synced, Ready and Stalled first, all with observedGeneration
    /// equal to the generation the sync controller reconciled; then the inner copy's
    /// conditions of other types, in the inner order, the first of each type, with
    /// status, reason and message as the inner copy wrote them and observedGeneration
    /// equal to the outer generation at which it was read (while Synced is False they
    /// are kept as last reported, with the stamp they were read at). An inner Synced
    /// condition is dropped. No condition carries lastTransitionTime. The rules:
    /// doc/widget_sync_design.md, section 1.4. Synced is True when the spec is in the
    /// inner cluster and the inner status observes it; otherwise False with the reason
    /// of the case, which deploy/widget_sync/README.md tabulates with the Ready and
    /// Stalled each one reads. While Synced is True, Ready is the inner copy's own
    /// Ready condition (status, reason and message; an inner status that is none of
    /// True, False and Unknown reads Unknown), except that an inner Stalled=True forces
    /// Ready=False with that condition's reason and message, and a mirror with no Ready
    /// condition reads Unknown with reason NoInnerReadyCondition. While Synced is
    /// False, Ready has reason NotSynced, and is Unknown where the controller has no
    /// caught-up inner status for the current spec and False where it knows no mirror
    /// runs that spec. Stalled is True with the sync controller's reason in a case
    /// nothing the controller does again gets out of; otherwise, while Synced is True,
    /// it is the inner copy's own Stalled condition, and False with Synced's reason
    /// when the inner copy has no Stalled condition or Synced is False. Ready and
    /// Stalled are never both True.
    pub conditions: Option<Vec<WidgetCondition>>,
}

/// A condition in the usual metav1.Condition shape. `lastTransitionTime` is omitted
/// because the verified controller does not read clocks.
#[derive(
    Clone, Debug, Default, serde::Deserialize, serde::Serialize, schemars::JsonSchema, PartialEq,
)]
pub struct WidgetCondition {
    /// On an outer copy: Synced, Ready or Stalled, or a type copied from the inner copy.
    /// On an inner copy: whatever the inner implementation reports; the sync controller
    /// merges Ready and Stalled, drops Synced, and copies the rest.
    #[serde(rename = "type")]
    pub type_: String,
    /// On an outer copy: Synced is True or False; Ready and Stalled are True, False or
    /// Unknown; a copied condition's status is the inner copy's, as written. On an inner
    /// copy, whatever the inner implementation writes.
    pub status: String,
    /// The generation of the object the condition was computed for.
    #[serde(rename = "observedGeneration")]
    pub observed_generation: Option<i64>,
    /// A CamelCase word saying why the condition has its status; absent on an outer
    /// copy when the inner condition it repeats carries none.
    pub reason: Option<String>,
    /// Free text; on an outer copy, copied from the inner condition when the reason is.
    pub message: Option<String>,
}

impl Default for Widget {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: WidgetSpec::default(),
            status: None,
        }
    }
}

// Gadget is the second kind of the demo, there to show the sync controller is
// generic over kinds (doc/widget_sync_fanout_design.md, section 4). Its spec has
// nothing in common with Widget's and no cluster field: its selector is `name`,
// so the object's name is the binding whose cluster receives the mirror. The
// status has the shape of section 2.2 (observedGeneration and conditions) plus
// its own payload, observedSize.
#[derive(
    kube::CustomResource,
    Default,
    Debug,
    Clone,
    serde::Deserialize,
    serde::Serialize,
    schemars::JsonSchema,
    PartialEq,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "Gadget")]
#[kube(namespaced)]
#[kube(status = "GadgetStatus")]
pub struct GadgetSpec {
    pub size: i32,
    pub labels: Option<Vec<String>>,
}

/// The status of a Gadget; written like a Widget's, by the inner implementation
/// on an inner copy and by the sync controller on an outer copy.
#[derive(
    Clone, Debug, Default, serde::Deserialize, serde::Serialize, schemars::JsonSchema, PartialEq,
)]
pub struct GadgetStatus {
    /// The generation of this object that the writer of this status last processed.
    #[serde(rename = "observedGeneration")]
    pub observed_generation: Option<i64>,
    /// The conditions of a Widget's status, with the same meaning.
    pub conditions: Option<Vec<WidgetCondition>>,
    /// Mirrored from the inner copy while Synced is True; otherwise kept as last reported.
    #[serde(rename = "observedSize")]
    pub observed_size: Option<i32>,
}

impl Default for Gadget {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: GadgetSpec::default(),
            status: None,
        }
    }
}

/// The CRDs of the demo kinds of the sync controller, in the order they are
/// installed, and exactly what `widget_sync_controller export` prints and what
/// the manifests under deploy/widget_sync hold (crd_manifest_tests).
///
/// The derive cannot express the CEL immutability rule on the selector field
/// or the map list type on `status.conditions`, so both are added here.
/// Without the rule, `export` would print a Widget CRD that this binary
/// refuses at boot.
pub fn demo_crds(
) -> Vec<k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition> {
    vec![with_conditions_as_map(widget_crd()), with_conditions_as_map(<Gadget as kube::CustomResourceExt>::crd())]
}

/// `status.conditions` as a map list keyed by `type`, set on every version the
/// CRD serves. A server-side apply by another writer then merges by condition
/// type instead of replacing the list, and the API server rejects a write with
/// two conditions of one type -- which the sync controller never sends: its own
/// three types are distinct and the conditions it copies are the first of each
/// type (widget_sync_controller::trusted::spec_types::copied_conditions). The
/// controller's own write is a JSON patch that replaces the list; the map type
/// does not make it merge.
fn with_conditions_as_map(
    mut crd: k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition,
) -> k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition {
    for version in crd.spec.versions.iter_mut() {
        let conditions = version
            .schema
            .as_mut()
            .and_then(|schema| schema.open_api_v3_schema.as_mut())
            .and_then(|schema| schema.properties.as_mut())
            .and_then(|properties| properties.get_mut("status"))
            .and_then(|status| status.properties.as_mut())
            .and_then(|properties| properties.get_mut("conditions"))
            .expect("the derived CRD declares status.conditions");
        conditions.x_kubernetes_list_type = Some("map".to_string());
        conditions.x_kubernetes_list_map_keys = Some(vec!["type".to_string()]);
    }
    crd
}

/// The name of the Widget field that selects an object's inner cluster, and
/// the rule the sync controller requires on it
/// (`--kind anvil.dev/v1/Widget:field:spec.clusterName`).
const WIDGET_SELECTOR_FIELD: &str = "clusterName";
const IMMUTABLE_RULE: &str = "self == oldSelf";
const IMMUTABLE_MESSAGE: &str = "clusterName is immutable";

// The derive's Widget CRD with the immutability rule on spec.clusterName, in
// every version it serves.
fn widget_crd(
) -> k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition {
    use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::ValidationRule;
    let mut crd = <Widget as kube::CustomResourceExt>::crd();
    for version in crd.spec.versions.iter_mut() {
        let field = version
            .schema
            .as_mut()
            .and_then(|schema| schema.open_api_v3_schema.as_mut())
            .and_then(|schema| schema.properties.as_mut())
            .and_then(|properties| properties.get_mut("spec"))
            .and_then(|spec| spec.properties.as_mut())
            .and_then(|properties| properties.get_mut(WIDGET_SELECTOR_FIELD))
            .expect("the derived Widget CRD declares spec.clusterName");
        field.x_kubernetes_validations = Some(vec![ValidationRule {
            rule: IMMUTABLE_RULE.to_string(),
            message: Some(IMMUTABLE_MESSAGE.to_string()),
            ..ValidationRule::default()
        }]);
    }
    crd
}

#[derive(
    kube::CustomResource,
    Default,
    Debug,
    Clone,
    serde::Deserialize,
    serde::Serialize,
    schemars::JsonSchema,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "RabbitmqCluster")]
#[kube(shortname = "rbmq", namespaced)]
pub struct RabbitmqClusterSpec {
    pub replicas: i32,
    pub image: String,
    #[serde(default = "default_persistence")]
    pub persistence: RabbitmqClusterPersistenceSpec,
    #[serde(rename = "rabbitmqConfig")]
    pub rabbitmq_config: Option<RabbitmqConfig>,
    pub affinity: Option<k8s_openapi::api::core::v1::Affinity>,
    pub tolerations: Option<Vec<k8s_openapi::api::core::v1::Toleration>>,
    #[serde(default)]
    pub labels: std::collections::BTreeMap<String, String>,
    #[serde(default)]
    pub annotations: std::collections::BTreeMap<String, String>,
    pub resources: Option<k8s_openapi::api::core::v1::ResourceRequirements>,
    #[serde(
        rename = "podManagementPolicy",
        default = "default_pod_management_policy"
    )]
    pub pod_management_policy: String,
    #[serde(rename = "persistentVolumeClaimRetentionPolicy")]
    pub persistent_volume_claim_retention_policy:
        Option<k8s_openapi::api::apps::v1::StatefulSetPersistentVolumeClaimRetentionPolicy>,
}

pub fn default_pod_management_policy() -> String {
    "Parallel".to_string()
}

impl Default for RabbitmqCluster {
    fn default() -> Self {
        Self {
            metadata: k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta::default(),
            spec: RabbitmqClusterSpec::default(),
        }
    }
}

pub fn default_persistence() -> RabbitmqClusterPersistenceSpec {
    RabbitmqClusterPersistenceSpec {
        storage_class_name: default_storage_class_name(),
        storage: default_storage(),
    }
}

#[derive(Default, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct RabbitmqConfig {
    #[serde(rename = "additionalConfig")]
    pub additional_config: Option<String>,
    #[serde(rename = "advancedConfig")]
    pub advanced_config: Option<String>,
    #[serde(rename = "envConfig")]
    pub env_config: Option<String>,
}

pub fn default_storage_class_name() -> String {
    "standard".to_string()
}

pub fn default_storage() -> k8s_openapi::apimachinery::pkg::api::resource::Quantity {
    k8s_openapi::apimachinery::pkg::api::resource::Quantity("10Gi".to_string())
}

#[derive(Default, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema)]
pub struct RabbitmqClusterPersistenceSpec {
    #[serde(rename = "storageClassName", default = "default_storage_class_name")]
    pub storage_class_name: String,
    #[serde(default = "default_storage")]
    pub storage: k8s_openapi::apimachinery::pkg::api::resource::Quantity,
}

// `widget_sync_controller export` prints demo_crds(), and the manifests under
// deploy/widget_sync are what it prints -- the derive's output plus the CEL
// immutability rule kube-derive 0.91 cannot express, which demo_crds() puts
// back. These tests hold the two to being the same document, so that what
// `export` prints is installable and passes the boot check, and so that a
// change to a spec type reaches the manifests. On a mismatch the message
// carries the export, to paste into the YAML.
#[cfg(test)]
mod crd_manifest_tests {
    use serde_yaml::Value;

    fn assert_manifest_is_exported(
        path: &str,
        manifest: &str,
        crd: &k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition,
    ) {
        let in_manifest: Value = serde_yaml::from_str(manifest).unwrap();
        let exported = serde_yaml::to_value(crd).unwrap();
        assert!(
            in_manifest == exported,
            "{} is not what `widget_sync_controller export` prints; the export is:\n{}",
            path,
            serde_yaml::to_string(crd).unwrap()
        );
    }

    #[test]
    fn widget_crd_yaml_is_what_export_prints() {
        assert_manifest_is_exported(
            "deploy/widget_sync/crd.yaml",
            include_str!("../deploy/widget_sync/crd.yaml"),
            &super::demo_crds()[0],
        );
    }

    #[test]
    fn gadget_crd_yaml_is_what_export_prints() {
        assert_manifest_is_exported(
            "deploy/widget_sync/crd_gadget.yaml",
            include_str!("../deploy/widget_sync/crd_gadget.yaml"),
            &super::demo_crds()[1],
        );
    }

    #[test]
    fn demo_crds_are_widget_then_gadget() {
        let names: Vec<String> = super::demo_crds().into_iter().map(|c| c.metadata.name.unwrap()).collect();
        assert_eq!(names, vec!["widgets.anvil.dev", "gadgets.anvil.dev"]);
    }

    // What `export` prints must boot: the shape check of the configured
    // selector, run on the exported CRD itself.
    #[test]
    fn what_export_prints_passes_the_boot_check() {
        use crate::shim_layer::crd_shape::check_shape;
        let widget = "anvil.dev/v1/Widget:field:spec.clusterName".parse().unwrap();
        assert_eq!(check_shape(&super::demo_crds()[0], &widget), Ok(()));
        let gadget = "anvil.dev/v1/Gadget:name".parse().unwrap();
        assert_eq!(check_shape(&super::demo_crds()[1], &gadget), Ok(()));
    }

    // The rule the design requires on the selector field (section 1.1) is in
    // the YAML by hand; make sure it stays.
    #[test]
    fn widget_crd_yaml_has_the_immutability_rule() {
        let manifest: Value = serde_yaml::from_str(include_str!("../deploy/widget_sync/crd.yaml")).unwrap();
        let rules = &manifest["spec"]["versions"][0]["schema"]["openAPIV3Schema"]["properties"]["spec"]
            ["properties"]["clusterName"]["x-kubernetes-validations"];
        assert_eq!(rules[0]["rule"], Value::String("self == oldSelf".to_string()), "{:?}", rules);
    }
}
