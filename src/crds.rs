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

// Widget is the custom resource mirrored between two clusters by the widget sync
// controller. The same kind is installed in both clusters: the outer copy is
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
    pub ready: Option<bool>,
    /// Mirrored from the inner copy while Synced is True; otherwise kept as last reported.
    #[serde(rename = "observedCount")]
    pub observed_count: Option<i32>,
    /// On an outer copy, exactly Synced, Ready and Stalled, all with observedGeneration
    /// equal to the generation the sync controller reconciled. Synced is True when the
    /// spec is in the inner cluster and the inner status observes it; otherwise False
    /// with reason InnerConverging, InnerTerminating, StaleMirror, ForeignObject, or,
    /// after a failed request, Forbidden, InnerUnreachable, CreateFailed, Rejected or
    /// RequestFailed. Ready is True exactly when Synced is True and the inner copy's own
    /// Ready condition, if present, is True and its own Stalled condition, if present,
    /// is not True; otherwise False, with reason NotSynced when not synced, else with
    /// the inner condition's reason and message. Stalled is True when the sync
    /// controller is in a permanent case (ForeignObject, Forbidden, Rejected) or the
    /// inner copy's own Stalled condition is True, with the sync controller's reason
    /// when it has one, else the inner condition's. Ready and Stalled are never both
    /// True.
    pub conditions: Option<Vec<WidgetCondition>>,
}

/// A condition in the usual metav1.Condition shape. `lastTransitionTime` is omitted
/// because the verified controller does not read clocks.
#[derive(
    Clone, Debug, Default, serde::Deserialize, serde::Serialize, schemars::JsonSchema, PartialEq,
)]
pub struct WidgetCondition {
    /// Synced, Ready or Stalled on an outer copy; whatever the inner implementation
    /// reports on an inner copy (the sync controller reads Ready and Stalled).
    #[serde(rename = "type")]
    pub type_: String,
    /// True or False.
    pub status: String,
    /// The generation of the object the condition was computed for.
    #[serde(rename = "observedGeneration")]
    pub observed_generation: Option<i64>,
    /// A CamelCase word saying why the condition has its status.
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
/// installed. The manifests under deploy/widget_sync are these plus the CEL
/// rules the derive cannot express (see crd_manifest_tests).
pub fn demo_crds(
) -> Vec<k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition> {
    vec![
        <Widget as kube::CustomResourceExt>::crd(),
        <Gadget as kube::CustomResourceExt>::crd(),
    ]
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

// The CRD manifests under deploy/widget_sync are the derive's export plus what
// kube-derive 0.91 cannot express: the CEL immutability rule on the selector
// field. These tests keep the two from drifting: the YAML, with every
// x-kubernetes-validations block removed, must equal the export. On a
// mismatch the message carries the export, to paste into the YAML and then
// put the rule back.
#[cfg(test)]
mod crd_manifest_tests {
    use kube::CustomResourceExt;
    use serde_yaml::Value;

    fn strip_validations(value: &mut Value) {
        match value {
            Value::Mapping(map) => {
                map.remove(Value::String("x-kubernetes-validations".to_string()));
                for (_, v) in map.iter_mut() {
                    strip_validations(v);
                }
            }
            Value::Sequence(seq) => seq.iter_mut().for_each(strip_validations),
            _ => {}
        }
    }

    fn assert_manifest_matches_export(
        path: &str,
        manifest: &str,
        crd: &k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition,
    ) {
        let mut in_manifest: Value = serde_yaml::from_str(manifest).unwrap();
        strip_validations(&mut in_manifest);
        let exported = serde_yaml::to_value(crd).unwrap();
        assert!(
            in_manifest == exported,
            "{} differs from the derive's export (x-kubernetes-validations ignored); \
             the export is:\n{}",
            path,
            serde_yaml::to_string(crd).unwrap()
        );
    }

    #[test]
    fn widget_crd_yaml_matches_the_derive() {
        assert_manifest_matches_export(
            "deploy/widget_sync/crd.yaml",
            include_str!("../deploy/widget_sync/crd.yaml"),
            &super::Widget::crd(),
        );
    }

    #[test]
    fn gadget_crd_yaml_matches_the_derive() {
        assert_manifest_matches_export(
            "deploy/widget_sync/crd_gadget.yaml",
            include_str!("../deploy/widget_sync/crd_gadget.yaml"),
            &super::Gadget::crd(),
        );
    }

    #[test]
    fn demo_crds_are_widget_then_gadget() {
        let names: Vec<String> = super::demo_crds().into_iter().map(|c| c.metadata.name.unwrap()).collect();
        assert_eq!(names, vec!["widgets.anvil.dev", "gadgets.anvil.dev"]);
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
