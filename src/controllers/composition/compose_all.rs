
// The whole-repository composition: the four framework controllers beside the
// Widget sync controller and janitors (doc/widget_sync_design.md, section 3.4).
use verus_temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::rabbitmq_controller::model::install::*;
use crate::rabbitmq_controller::trusted::{rely_guarantee::*, spec_types::*};
use crate::vdeployment_controller::model::install::*;
use crate::vdeployment_controller::trusted::{rely_guarantee::*, spec_types::*};
use crate::vreplicaset_controller::model::install::*;
use crate::vreplicaset_controller::model::reconciler::*;
use crate::vreplicaset_controller::trusted::{rely_guarantee::*, spec_types::*};
use crate::vstatefulset_controller::model::install::*;
use crate::vstatefulset_controller::proof::predicate::*;
use crate::vstatefulset_controller::trusted::{rely_guarantee::*, spec_types::*};
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::trusted::rely_guarantee::*;
use crate::widget_sync_controller::trusted::spec_types::*;
use crate::widget_sync_controller::proof::liveness::spec::*;
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use crate::composition::{rabbitmq_reconciler::*, vdeployment_reconciler::*, vreplicaset_reconciler::*, vstatefulset_reconciler::*};
use crate::composition::{widget_janitor_reconciler::*, widget_sync_reconciler::*};
use crate::composition::widget_sync_reconciler;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

// ============================================================
// Concrete id assignment and cluster instantiation
// ============================================================

pub open spec fn vrs_id() -> int { 1 }
pub open spec fn vd_id() -> int { 2 }
pub open spec fn vsts_id() -> int { 3 }
pub open spec fn rmq_id() -> int { 4 }
pub open spec fn janitor_id() -> int { 5 }
pub open spec fn sync_id() -> int { 6 }

// ============================================================
// The four framework controllers beside a Widget configuration
// ============================================================
//
// Nothing below fixes the configured kind: `core_holds_for` composes the four
// controllers of the repository with the sync controller of any `k` and the
// janitors of its bindings. What the composition needs of `k` is stated as
// hypotheses -- `sync_kind_ok`, `binding_ok` of each binding, and that the outer
// kind is none of the four framework kinds -- and the demo at the end of the file
// is one application of the statement to `widgets.anvil.dev`.

// The outer kind of the configuration is none of the four framework kinds. The
// mirror kinds need no hypothesis: a mirror kind name carries an '@' and the four
// framework names do not (framework_kind_names_ok).
pub open spec fn widget_kinds_off_framework(k: SyncKind) -> bool {
    &&& k.outer_kind != VReplicaSetView::kind()
    &&& k.outer_kind != VDeploymentView::kind()
    &&& k.outer_kind != VStatefulSetView::kind()
    &&& k.outer_kind != RabbitmqClusterView::kind()
}

// The Widget controllers run at ids of their own.
pub open spec fn widget_ids_off_framework(bs: Set<Binding>, ids: Map<Binding, int>, sync_id: int) -> bool {
    &&& sync_id != vrs_id() && sync_id != vd_id() && sync_id != vsts_id() && sync_id != rmq_id()
    &&& forall |b: Binding| #[trigger] bs.contains(b)
        ==> ids[b] != vrs_id() && ids[b] != vd_id() && ids[b] != vsts_id() && ids[b] != rmq_id()
}

// The cluster: the four framework types and controllers, plus the model kinds and
// controllers of the configuration (composition::widget_sync_reconciler).
pub open spec fn cluster_instance_for(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>) -> Cluster {
    Cluster {
        installed_types: widget_installed_types(k, spec_ok)
            .insert(VReplicaSetView::kind()->CustomResourceKind_0, Cluster::installed_type::<VReplicaSetView>())
            .insert(VDeploymentView::kind()->CustomResourceKind_0, Cluster::installed_type::<VDeploymentView>())
            .insert(VStatefulSetView::kind()->CustomResourceKind_0, Cluster::installed_type::<VStatefulSetView>())
            .insert(RabbitmqClusterView::kind()->CustomResourceKind_0, Cluster::installed_type::<RabbitmqClusterView>()),
        controller_models: widget_cluster_for(k, spec_ok, sync_id, ids).controller_models
            .insert(vrs_id(), vrs_controller_model())
            .insert(vd_id(), vd_controller_model())
            .insert(vsts_id(), vsts_controller_model())
            .insert(rmq_id(), rabbitmq_controller_model()),
    }
}

pub open spec fn core_cluster_for(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>) -> CoreCluster {
    CoreCluster {
        cluster: cluster_instance_for(k, spec_ok, sync_id, ids),
        registry: widget_core_cluster_for(k, spec_ok, sync_id, ids).registry
            .insert(vrs_id(), vrs_controller_spec(vrs_id()))
            .insert(vd_id(), vd_controller_spec(vd_id()))
            .insert(vsts_id(), vsts_controller_spec(vsts_id()))
            .insert(rmq_id(), rmq_controller_spec(rmq_id())),
    }
}

// Helper: vsts and vrs name prefixes are disjoint (kind names differ).
proof fn vsts_prefix_not_vrs_prefix(name: StringView)
    ensures
        !(has_vsts_prefix(name) && has_vrs_prefix(name)),
{
    if has_vsts_prefix(name) && has_vrs_prefix(name) {
        let vsts_suffix = choose |suffix| name == VStatefulSetView::kind()->CustomResourceKind_0 + "-"@ + suffix;
        let vrs_suffix = choose |suffix| name == VReplicaSetView::kind()->CustomResourceKind_0 + "-"@ + suffix;
        assert(VStatefulSetView::kind()->CustomResourceKind_0 == "vstatefulset"@);
        assert(VReplicaSetView::kind()->CustomResourceKind_0 == "vreplicaset"@);
        assert(name.take(VStatefulSetView::kind()->CustomResourceKind_0.len() as int) == VStatefulSetView::kind()->CustomResourceKind_0);
        assert(name.take(VReplicaSetView::kind()->CustomResourceKind_0.len() as int) == VReplicaSetView::kind()->CustomResourceKind_0);
        vrs_vsts_str_neq();
        assert(VStatefulSetView::kind()->CustomResourceKind_0.len() > VReplicaSetView::kind()->CustomResourceKind_0.len());
        assert(VStatefulSetView::kind()->CustomResourceKind_0.take(VReplicaSetView::kind()->CustomResourceKind_0.len() as int) == VReplicaSetView::kind()->CustomResourceKind_0);
        assert(false);
    }
}

// The four framework kind names are pairwise distinct, and none of them carries
// an '@'. The second half is what tells them from every mirror kind of every
// configuration: a mirror kind name is `<crd name>@<namespace>/<cluster>`.
// Revealing these four literals is not a configuration-dependent argument -- they
// are the framework's own fixed kinds.
pub proof fn framework_kind_names_ok()
    ensures
        "vreplicaset"@ != "vdeployment"@,
        "vreplicaset"@ != "vstatefulset"@,
        "vreplicaset"@ != "rabbitmq"@,
        "vdeployment"@ != "vstatefulset"@,
        "vdeployment"@ != "rabbitmq"@,
        "vstatefulset"@ != "rabbitmq"@,
        kind_name_ok("vreplicaset"@),
        kind_name_ok("vdeployment"@),
        kind_name_ok("vstatefulset"@),
        kind_name_ok("rabbitmq"@),
{
    reveal_strlit("vreplicaset");
    reveal_strlit("vdeployment");
    reveal_strlit("vstatefulset");
    reveal_strlit("rabbitmq");
    assert("vreplicaset"@ != "vdeployment"@) by {
        assert("vreplicaset"@[1] != "vdeployment"@[1]);
    };
    assert("vreplicaset"@.len() != "vstatefulset"@.len());
    assert("vreplicaset"@.len() != "rabbitmq"@.len());
    assert("vdeployment"@.len() != "vstatefulset"@.len());
    assert("vdeployment"@.len() != "rabbitmq"@.len());
    assert("vstatefulset"@.len() != "rabbitmq"@.len());
}

// No model kind of the configuration is a framework kind. For the outer kind that
// is the hypothesis; for every mirror kind it is lemma_remote_kind_name_is_not_primary,
// the '@' argument, applied to each of the four names.
pub proof fn widget_kinds_distinct_from_framework(k: SyncKind)
    requires sync_kind_ok(k), widget_kinds_off_framework(k),
    ensures
        forall |b: Binding| #![trigger inner_kind(k, b)] {
            &&& inner_kind(k, b) != VReplicaSetView::kind()
            &&& inner_kind(k, b) != VDeploymentView::kind()
            &&& inner_kind(k, b) != VStatefulSetView::kind()
            &&& inner_kind(k, b) != RabbitmqClusterView::kind()
        },
        forall |b: Binding| #[trigger] inner_kind(k, b) != k.outer_kind,
{
    framework_kind_names_ok();
    assert(VReplicaSetView::kind()->CustomResourceKind_0 == "vreplicaset"@);
    assert(VDeploymentView::kind()->CustomResourceKind_0 == "vdeployment"@);
    assert(VStatefulSetView::kind()->CustomResourceKind_0 == "vstatefulset"@);
    assert(RabbitmqClusterView::kind()->CustomResourceKind_0 == "rabbitmq"@);
    assert forall |b: Binding| #![trigger inner_kind(k, b)] {
        &&& inner_kind(k, b) != VReplicaSetView::kind()
        &&& inner_kind(k, b) != VDeploymentView::kind()
        &&& inner_kind(k, b) != VStatefulSetView::kind()
        &&& inner_kind(k, b) != RabbitmqClusterView::kind()
    } by {
        lemma_remote_kind_name_is_not_primary("vreplicaset"@, k.name, b);
        lemma_remote_kind_name_is_not_primary("vdeployment"@, k.name, b);
        lemma_remote_kind_name_is_not_primary("vstatefulset"@, k.name, b);
        lemma_remote_kind_name_is_not_primary("rabbitmq"@, k.name, b);
    }
    assert forall |b: Binding| #[trigger] inner_kind(k, b) != k.outer_kind by {
        lemma_outer_kind_is_not_inner(k, b);
    }
}

// VRS and VSTS both manage Pods, so name-prefix disambiguation is required.
// The other 6 cross-group pairs have disjoint request types so Verus derives
// guarantee to rely automatically (same as in VRS/VD).

proof fn vrs_guarantee_implies_vsts_rely(id: int)
    ensures lift_state(vrs_guarantee(id)).entails(lift_state(vsts_rely(id))),
{
    assert forall |s: ClusterState| #[trigger] vrs_guarantee(id)(s) implies vsts_rely(id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => vsts_rely_create_req(req),
                APIRequest::UpdateRequest(req) => vsts_rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => vsts_rely_get_then_update_req(req),
                APIRequest::DeleteRequest(req) => vsts_rely_delete_req(req)(s),
                APIRequest::GetThenDeleteRequest(req) => vsts_rely_get_then_delete_req(req),
                _ => true,
            }) by {
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(r) => {
                    assert(vrs_guarantee_create_req(r)(s));
                    vsts_prefix_not_vrs_prefix(r.obj.metadata.generate_name->0);
                }
                APIRequest::GetThenDeleteRequest(r) => {
                    assert(vrs_guarantee_get_then_delete_req(r)(s));
                    vsts_prefix_not_vrs_prefix(r.key.name);
                }
                _ => {}
            }
        };
    };
}

proof fn vsts_guarantee_implies_vrs_rely(id: int)
    ensures lift_state(vsts_guarantee(id)).entails(lift_state(vrs_rely(id))),
{
    assert forall |s: ClusterState| #[trigger] vsts_guarantee(id)(s) implies vrs_rely(id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => vrs_rely_create_req(req)(s),
                APIRequest::UpdateRequest(req) => vrs_rely_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => vrs_rely_get_then_update_req(req)(s),
                APIRequest::UpdateStatusRequest(req) => vrs_rely_update_status_req(req)(s),
                APIRequest::DeleteRequest(req) => vrs_rely_delete_req(req)(s),
                APIRequest::GetThenDeleteRequest(req) => vrs_rely_get_then_delete_req(req)(s),
                APIRequest::GetThenUpdateStatusRequest(req) => vrs_rely_get_then_update_status_req(req)(s),
                _ => true,
            }) by {
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(r) => {
                    assert(vsts_guarantee_create_req(r));
                    vsts_prefix_not_vrs_prefix(r.obj.metadata.name->0);
                }
                APIRequest::GetThenUpdateRequest(r) => {
                    assert(vsts_guarantee_get_then_update_req(r));
                    vsts_prefix_not_vrs_prefix(r.name);
                }
                APIRequest::GetThenDeleteRequest(r) => {
                    assert(vsts_guarantee_get_then_delete_req(r));
                    vsts_prefix_not_vrs_prefix(r.key.name);
                }
                _ => {}
            }
        };
    };
}

// ============================================================
// Compatibility of the Widget pair with the other four controllers
// ============================================================
//
// The Widget pair sends requests to the two Widget kinds only, and the other
// four controllers send requests to Pods, PVCs, VReplicaSets and the
// RabbitMQ-managed kinds only. Every cross implication is kind disjointness once
// the custom kind names are known to differ (kind_strings_distinct).

// The kinds the sync reconciler's requests target. This is the part of
// widget_sync_guarantee the other controllers' relies need; the Create case is
// stated there through make_inner, whose marshalled kind is the inner kind.
pub open spec fn widget_sync_touches_widget_kinds_only(k: SyncKind, id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::GetRequest(req) => is_inner_kind(k, req.key.kind),
            APIRequest::CreateRequest(req) => is_inner_kind(k, req.obj.kind),
            APIRequest::PatchRequest(req) => is_inner_kind(k, req.kind),
            APIRequest::PatchStatusRequest(req) => req.kind == k.outer_kind,
            _ => false,
        }
    }
}

proof fn widget_sync_guarantee_implies_widget_kinds_only(k: SyncKind, id: int)
    ensures lift_state(widget_sync_guarantee(k, id)).entails(lift_state(widget_sync_touches_widget_kinds_only(k, id))),
{
    assert forall |s: ClusterState| #[trigger] widget_sync_guarantee(k, id)(s) implies widget_sync_touches_widget_kinds_only(k, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::GetRequest(req) => is_inner_kind(k, req.key.kind),
                APIRequest::CreateRequest(req) => is_inner_kind(k, req.obj.kind),
                APIRequest::PatchRequest(req) => is_inner_kind(k, req.kind),
                APIRequest::PatchStatusRequest(req) => req.kind == k.outer_kind,
                _ => false,
            }) by {
            let outer_key = msg.src->Controller_1;
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => {
                    assert(mirror_create_req(k, req, outer_key)(s));
                    let outer = choose |outer: SyncedObjectView| {
                        &&& outer.kind == k.outer_kind
                        &&& outer.object_ref() == outer_key
                        &&& outer.metadata.uid is Some
                        &&& cluster_of(k.selector, outer) is Some
                        &&& req.namespace == outer_key.namespace
                        &&& req.obj == #[trigger] marshal(make_inner(k, outer))
                        &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s)
                    };
                    assert(req.obj.kind == make_inner(k, outer).kind);
                    assert(is_inner_kind(k, req.obj.kind)) by {
                        assert(req.obj.kind == inner_kind(k, binding_of(k, outer)));
                    }
                }
                _ => {}
            }
        };
    };
}

// The sync reconciler's guarantee implies the relies of the other four
// controllers on it: it only touches the model kinds of its own configuration.
proof fn widget_sync_guarantee_implies_relies(k: SyncKind, id: int)
    requires sync_kind_ok(k), widget_kinds_off_framework(k),
    ensures
        lift_state(widget_sync_guarantee(k, id)).entails(lift_state(vrs_rely(id))),
        lift_state(widget_sync_guarantee(k, id)).entails(lift_state(vd_rely(id))),
        lift_state(widget_sync_guarantee(k, id)).entails(lift_state(vsts_rely(id))),
        lift_state(widget_sync_guarantee(k, id)).entails(lift_state(rmq_rely(id))),
{
    widget_kinds_distinct_from_framework(k);
    widget_sync_guarantee_implies_widget_kinds_only(k, id);
    let kinds_only = lift_state(widget_sync_touches_widget_kinds_only(k, id));

    assert forall |s: ClusterState| #[trigger] widget_sync_touches_widget_kinds_only(k, id)(s) implies vrs_rely(id)(s) by {}
    entails_trans(lift_state(widget_sync_guarantee(k, id)), kinds_only, lift_state(vrs_rely(id)));

    assert forall |s: ClusterState| #[trigger] widget_sync_touches_widget_kinds_only(k, id)(s) implies vd_rely(id)(s) by {}
    entails_trans(lift_state(widget_sync_guarantee(k, id)), kinds_only, lift_state(vd_rely(id)));

    assert forall |s: ClusterState| #[trigger] widget_sync_touches_widget_kinds_only(k, id)(s) implies vsts_rely(id)(s) by {}
    entails_trans(lift_state(widget_sync_guarantee(k, id)), kinds_only, lift_state(vsts_rely(id)));

    assert forall |s: ClusterState| #[trigger] widget_sync_touches_widget_kinds_only(k, id)(s) implies rmq_rely(id)(s) by {}
    entails_trans(lift_state(widget_sync_guarantee(k, id)), kinds_only, lift_state(rmq_rely(id)));
}

// The janitor's guarantee implies the relies of the other four controllers on
// it: it lists outer copies and deletes mirrors, nothing else.
proof fn widget_janitor_guarantee_implies_relies(k: SyncKind, b: Binding, id: int)
    requires sync_kind_ok(k), widget_kinds_off_framework(k),
    ensures
        lift_state(widget_janitor_guarantee(k, b, id)).entails(lift_state(vrs_rely(id))),
        lift_state(widget_janitor_guarantee(k, b, id)).entails(lift_state(vd_rely(id))),
        lift_state(widget_janitor_guarantee(k, b, id)).entails(lift_state(vsts_rely(id))),
        lift_state(widget_janitor_guarantee(k, b, id)).entails(lift_state(rmq_rely(id))),
{
    widget_kinds_distinct_from_framework(k);
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(k, b, id)(s) implies vrs_rely(id)(s) by {}
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(k, b, id)(s) implies vd_rely(id)(s) by {}
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(k, b, id)(s) implies vsts_rely(id)(s) by {}
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(k, b, id)(s) implies rmq_rely(id)(s) by {}
}

// Each of the other four controllers' guarantees implies both Widget relies on
// it: none of them creates, updates or deletes a Widget kind, and none writes
// the status of an outer copy.
proof fn vrs_guarantee_implies_widget_relies(k: SyncKind, id: int)
    requires sync_kind_ok(k), widget_kinds_off_framework(k),
    ensures
        lift_state(vrs_guarantee(id)).entails(lift_state(widget_sync_rely(k, id))),
        lift_state(vrs_guarantee(id)).entails(lift_state(widget_janitor_rely(k, id))),
{
    widget_kinds_distinct_from_framework(k);
    assert forall |s: ClusterState| #[trigger] vrs_guarantee(id)(s) implies widget_sync_rely(k, id)(s) by {}
    assert forall |s: ClusterState| #[trigger] vrs_guarantee(id)(s) implies widget_janitor_rely(k, id)(s) by {}
}

proof fn vd_guarantee_implies_widget_relies(k: SyncKind, id: int)
    requires sync_kind_ok(k), widget_kinds_off_framework(k),
    ensures
        lift_state(vd_guarantee(id)).entails(lift_state(widget_sync_rely(k, id))),
        lift_state(vd_guarantee(id)).entails(lift_state(widget_janitor_rely(k, id))),
{
    widget_kinds_distinct_from_framework(k);
    assert forall |s: ClusterState| #[trigger] vd_guarantee(id)(s) implies widget_sync_rely(k, id)(s) by {}
    assert forall |s: ClusterState| #[trigger] vd_guarantee(id)(s) implies widget_janitor_rely(k, id)(s) by {}
}

proof fn vsts_guarantee_implies_widget_relies(k: SyncKind, id: int)
    requires sync_kind_ok(k), widget_kinds_off_framework(k),
    ensures
        lift_state(vsts_guarantee(id)).entails(lift_state(widget_sync_rely(k, id))),
        lift_state(vsts_guarantee(id)).entails(lift_state(widget_janitor_rely(k, id))),
{
    widget_kinds_distinct_from_framework(k);
    assert forall |s: ClusterState| #[trigger] vsts_guarantee(id)(s) implies widget_sync_rely(k, id)(s) by {}
    assert forall |s: ClusterState| #[trigger] vsts_guarantee(id)(s) implies widget_janitor_rely(k, id)(s) by {}
}

proof fn rmq_guarantee_implies_widget_relies(k: SyncKind, id: int)
    requires sync_kind_ok(k), widget_kinds_off_framework(k),
    ensures
        lift_state(rmq_guarantee(id)).entails(lift_state(widget_sync_rely(k, id))),
        lift_state(rmq_guarantee(id)).entails(lift_state(widget_janitor_rely(k, id))),
{
    widget_kinds_distinct_from_framework(k);
    assert forall |s: ClusterState| #[trigger] rmq_guarantee(id)(s) implies widget_sync_rely(k, id)(s) by {}
    assert forall |s: ClusterState| #[trigger] rmq_guarantee(id)(s) implies widget_janitor_rely(k, id)(s) by {}
}

// ============================================================
// Pairwise CORE proofs: {VRS,VD} and {VSTS,RMQ}
// ============================================================

pub proof fn vrs_vd_core_holds(cluster: CoreCluster)
    requires
        cluster.registry.contains_pair(vrs_id(), vrs_controller_spec(vrs_id())),
        cluster.registry.contains_pair(vd_id(), vd_controller_spec(vd_id())),
        well_formed(cluster, vrs_core_set(vrs_id())),
        well_formed(cluster, vd_core_set(vd_id())),
    ensures
        well_formed(cluster, union_coreset(vrs_core_set(vrs_id()), vd_core_set(vd_id()), true_pred())),
        core(cluster, union_coreset(vrs_core_set(vrs_id()), vd_core_set(vd_id()), true_pred())),
{
    let s1 = vrs_core_set(vrs_id());
    let s2 = vd_core_set(vd_id());
    let spec = cluster_model(cluster);

    vrs_singleton_core_holds(cluster, vrs_id());
    vd_singleton_core_holds(cluster, vd_id());

    assert(satisfies_dependency(cluster, s1, s2)) by {
        let esr_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
        let esr_s1 = tla_forall(esr_fn_s1);
        assert(s1.members.contains(vrs_id()));
        tla_forall_apply(esr_fn_s1, vrs_id());
        entails_trans(spec.and(esr_s1), esr_s1, s2.liveness_dependency);
        entails_implies(spec, esr_s1, s2.liveness_dependency);
    }

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(vd_rely(vrs_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(vrs_rely(vd_id())));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                tla_forall_apply(g_fn_s1, vrs_id());
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(vrs_guarantee(vrs_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(vd_rely(vrs_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                tla_forall_apply(g_fn_s2, vd_id());
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(vd_guarantee(vd_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(vd_guarantee(vd_id()))), always(lift_state(vrs_rely(vd_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));

        entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose_dep(cluster, s1, s2);
}

pub proof fn vsts_rmq_core_holds(cluster: CoreCluster)
    requires
        cluster.registry.contains_pair(vsts_id(), vsts_controller_spec(vsts_id())),
        cluster.registry.contains_pair(rmq_id(), rmq_controller_spec(rmq_id())),
        well_formed(cluster, vsts_core_set(vsts_id())),
        well_formed(cluster, rmq_core_set(rmq_id())),
    ensures
        well_formed(cluster, union_coreset(vsts_core_set(vsts_id()), rmq_core_set(rmq_id()), true_pred())),
        core(cluster, union_coreset(vsts_core_set(vsts_id()), rmq_core_set(rmq_id()), true_pred())),
{
    let s1 = vsts_core_set(vsts_id());
    let s2 = rmq_core_set(rmq_id());
    let spec = cluster_model(cluster);

    vsts_singleton_core_holds(cluster, vsts_id());
    rmq_singleton_core_holds(cluster, rmq_id());

    assert(satisfies_dependency(cluster, s1, s2)) by {
        let esr_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
        let esr_s1 = tla_forall(esr_fn_s1);
        assert(s1.members.contains(vsts_id()));
        tla_forall_apply(esr_fn_s1, vsts_id());
        entails_trans(spec.and(esr_s1), esr_s1, s2.liveness_dependency);
        entails_implies(spec, esr_s1, s2.liveness_dependency);
    }

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(rmq_rely(vsts_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(vsts_rely(rmq_id())));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                tla_forall_apply(g_fn_s1, vsts_id());
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(vsts_guarantee(vsts_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(rmq_rely(vsts_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                tla_forall_apply(g_fn_s2, rmq_id());
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(rmq_guarantee(rmq_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(vsts_rely(rmq_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));

        entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose_dep(cluster, s1, s2);
}

// ============================================================
// Joint CORE proof: compose {VRS, VD} with {VSTS, RMQ}
// ============================================================

pub open spec fn vrs_vd_set() -> CoreSet {
    union_coreset(vrs_core_set(vrs_id()), vd_core_set(vd_id()), true_pred())
}

pub open spec fn vsts_rmq_set() -> CoreSet {
    union_coreset(vsts_core_set(vsts_id()), rmq_core_set(rmq_id()), true_pred())
}

pub open spec fn vrs_vd_vsts_rmq_set() -> CoreSet {
    union_coreset(vrs_vd_set(), vsts_rmq_set(), true_pred())
}

proof fn vrs_vd_vsts_rmq_core_holds(cluster: CoreCluster)
    requires
        cluster.registry.contains_pair(vrs_id(), vrs_controller_spec(vrs_id())),
        cluster.registry.contains_pair(vd_id(), vd_controller_spec(vd_id())),
        cluster.registry.contains_pair(vsts_id(), vsts_controller_spec(vsts_id())),
        cluster.registry.contains_pair(rmq_id(), rmq_controller_spec(rmq_id())),
        well_formed(cluster, vrs_core_set(vrs_id())),
        well_formed(cluster, vd_core_set(vd_id())),
        well_formed(cluster, vsts_core_set(vsts_id())),
        well_formed(cluster, rmq_core_set(rmq_id())),
    ensures
        well_formed(cluster, vrs_vd_vsts_rmq_set()),
        core(cluster, vrs_vd_vsts_rmq_set()),
{
    let s1 = vrs_vd_set();
    let s2 = vsts_rmq_set();
    let spec = cluster_model(cluster);

    vrs_vd_core_holds(cluster);
    vsts_rmq_core_holds(cluster);

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        assert(s1.members =~= set![vrs_id(), vd_id()]);
        assert(s2.members =~= set![vsts_id(), rmq_id()]);

        // VRS and VSTS need explicit prefix reasoning.
        vrs_guarantee_implies_vsts_rely(vrs_id());
        vsts_guarantee_implies_vrs_rely(vsts_id());

        // Ambient fact for kinds used across is_rmq_managed_kind checks.
        framework_kind_names_ok();

        // Lift pointwise implications through always(...). Verus derives the
        // 6 cross-kind implications directly (same pattern as VRS/VD).
        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(vsts_rely(vrs_id())));
        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(rmq_rely(vrs_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(vsts_rely(vd_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(rmq_rely(vd_id())));
        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(vrs_rely(vsts_id())));
        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(vd_rely(vsts_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(vrs_rely(rmq_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(vd_rely(rmq_id())));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                tla_forall_apply(g_fn_s1, vrs_id());
                tla_forall_apply(g_fn_s1, vd_id());
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(vrs_guarantee(vrs_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(vsts_rely(vrs_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(rmq_rely(vrs_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(vd_guarantee(vd_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vd_guarantee(vd_id()))), always(lift_state(vsts_rely(vd_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(vd_guarantee(vd_id()))), always(lift_state(rmq_rely(vd_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                tla_forall_apply(g_fn_s2, vsts_id());
                tla_forall_apply(g_fn_s2, rmq_id());
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(vsts_guarantee(vsts_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(vrs_rely(vsts_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(vd_rely(vsts_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(rmq_guarantee(rmq_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(vrs_rely(rmq_id()))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(vd_rely(rmq_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));
        entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose(cluster, s1, s2);
}

// ============================================================
// Joint CORE proof: compose {VRS, VD, VSTS, RMQ} with a Widget configuration
// ============================================================

// The Widget controllers of the configuration, composed by widget_fanout_core_holds
// (through widget_core_set_for): the janitors' ESRs discharge the sync
// reconciler's liveness dependency inside the set, so the set as a whole has none.
pub open spec fn widget_set_for(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>) -> CoreSet {
    widget_core_set_for(k, spec_ok, sync_id, ids)
}

pub open spec fn core_set_for(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>) -> CoreSet {
    union_coreset(vrs_vd_vsts_rmq_set(), widget_set_for(k, spec_ok, sync_id, ids), true_pred())
}

proof fn all_core_holds(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>, cluster: CoreCluster)
    requires
        sync_kind_ok(k),
        forall |b: Binding| #[trigger] k.bindings.contains(b) ==> binding_ok(b),
        widget_kinds_off_framework(k),
        ids_ok(k.bindings, ids, sync_id),
        widget_ids_off_framework(k.bindings, ids, sync_id),
        cluster.registry.contains_pair(vrs_id(), vrs_controller_spec(vrs_id())),
        cluster.registry.contains_pair(vd_id(), vd_controller_spec(vd_id())),
        cluster.registry.contains_pair(vsts_id(), vsts_controller_spec(vsts_id())),
        cluster.registry.contains_pair(rmq_id(), rmq_controller_spec(rmq_id())),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, k.bindings, spec_ok, sync_id, ids)),
        janitors_registered(k, k.bindings, spec_ok, cluster, ids),
        (widget_sync_controller_spec(k, k.bindings, spec_ok, sync_id, ids).membership)(cluster.cluster, sync_id),
        well_formed(cluster, vrs_core_set(vrs_id())),
        well_formed(cluster, vd_core_set(vd_id())),
        well_formed(cluster, vsts_core_set(vsts_id())),
        well_formed(cluster, rmq_core_set(rmq_id())),
    ensures
        well_formed(cluster, core_set_for(k, spec_ok, sync_id, ids)),
        core(cluster, core_set_for(k, spec_ok, sync_id, ids)),
{
    broadcast use Set::lemma_map_contains;
    let s1 = vrs_vd_vsts_rmq_set();
    let s2 = widget_set_for(k, spec_ok, sync_id, ids);
    let spec = cluster_model(cluster);

    vrs_vd_vsts_rmq_core_holds(cluster);
    widget_fanout_core_holds(k, k.bindings, spec_ok, cluster, ids, sync_id);

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        assert(s1.members =~= set![vrs_id(), vd_id(), vsts_id(), rmq_id()]);
        assert(s2.members =~= janitor_ids_of(k.bindings, ids).insert(sync_id));

        // A framework id is never one of the Widget controllers'.
        assert forall |i: int| s1.members.contains(i) implies !is_janitor_id(k.bindings, ids, i) && i != sync_id by {
            if is_janitor_id(k.bindings, ids, i) {
                let b = binding_at(k.bindings, ids, i);
                assert(k.bindings.contains(b) && ids[b] == i);
            }
        }

        vrs_guarantee_implies_widget_relies(k, vrs_id());
        vd_guarantee_implies_widget_relies(k, vd_id());
        vsts_guarantee_implies_widget_relies(k, vsts_id());
        rmq_guarantee_implies_widget_relies(k, rmq_id());
        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(widget_sync_rely(k, vrs_id())));
        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(widget_janitor_rely(k, vrs_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(widget_sync_rely(k, vd_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(widget_janitor_rely(k, vd_id())));
        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(widget_sync_rely(k, vsts_id())));
        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(widget_janitor_rely(k, vsts_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(widget_sync_rely(k, rmq_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(widget_janitor_rely(k, rmq_id())));

        // r_21: what the Widget controllers rely on from the other four. The sync
        // reconciler's partial rely on a non-janitor id is widget_sync_rely, and a
        // janitor's is widget_janitor_rely whatever its binding.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                let spec_g1 = spec.and(tla_forall(g_fn_s1));
                tla_forall_apply(g_fn_s1, vrs_id());
                tla_forall_apply(g_fn_s1, vd_id());
                tla_forall_apply(g_fn_s1, vsts_id());
                tla_forall_apply(g_fn_s1, rmq_id());
                entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(vrs_guarantee(vrs_id()))));
                entails_trans(spec_g1, always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(widget_sync_rely(k, vrs_id()))));
                entails_trans(spec_g1, always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(widget_janitor_rely(k, vrs_id()))));
                entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(vd_guarantee(vd_id()))));
                entails_trans(spec_g1, always(lift_state(vd_guarantee(vd_id()))), always(lift_state(widget_sync_rely(k, vd_id()))));
                entails_trans(spec_g1, always(lift_state(vd_guarantee(vd_id()))), always(lift_state(widget_janitor_rely(k, vd_id()))));
                entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(vsts_guarantee(vsts_id()))));
                entails_trans(spec_g1, always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(widget_sync_rely(k, vsts_id()))));
                entails_trans(spec_g1, always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(widget_janitor_rely(k, vsts_id()))));
                entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(rmq_guarantee(rmq_id()))));
                entails_trans(spec_g1, always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(widget_sync_rely(k, rmq_id()))));
                entails_trans(spec_g1, always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(widget_janitor_rely(k, rmq_id()))));
                if pair.0 == sync_id {
                    assert(!is_janitor_id(k.bindings, ids, pair.1));
                    assert(r21_fn(pair) == always(lift_state(widget_sync_rely(k, pair.1))));
                } else {
                    lemma_janitor_id_is_a_binding(k.bindings, k.bindings, ids, sync_id, pair.0);
                    assert(r21_fn(pair) == always(lift_state(widget_janitor_rely(k, pair.1))));
                }
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        // r_12: what the other four rely on from the Widget controllers.
        widget_sync_guarantee_implies_relies(k, sync_id);
        entails_preserved_by_always(lift_state(widget_sync_guarantee(k, sync_id)), lift_state(vrs_rely(sync_id)));
        entails_preserved_by_always(lift_state(widget_sync_guarantee(k, sync_id)), lift_state(vd_rely(sync_id)));
        entails_preserved_by_always(lift_state(widget_sync_guarantee(k, sync_id)), lift_state(vsts_rely(sync_id)));
        entails_preserved_by_always(lift_state(widget_sync_guarantee(k, sync_id)), lift_state(rmq_rely(sync_id)));
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                let spec_g2 = spec.and(tla_forall(g_fn_s2));
                tla_forall_apply(g_fn_s2, pair.1);
                if pair.1 == sync_id {
                    assert(g_fn_s2(sync_id) == always(lift_state(widget_sync_guarantee(k, sync_id))));
                    entails_trans(spec_g2, tla_forall(g_fn_s2), always(lift_state(widget_sync_guarantee(k, sync_id))));
                    entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(k, sync_id))), always(lift_state(vrs_rely(sync_id))));
                    entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(k, sync_id))), always(lift_state(vd_rely(sync_id))));
                    entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(k, sync_id))), always(lift_state(vsts_rely(sync_id))));
                    entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(k, sync_id))), always(lift_state(rmq_rely(sync_id))));
                } else {
                    lemma_janitor_id_is_a_binding(k.bindings, k.bindings, ids, sync_id, pair.1);
                    let b2 = binding_at(k.bindings, ids, pair.1);
                    assert(cluster.registry.contains_pair(pair.1, widget_janitor_controller_spec(k, b2, k.bindings, spec_ok, pair.1)));
                    assert(g_fn_s2(pair.1) == always(lift_state(widget_janitor_guarantee(k, b2, pair.1))));
                    widget_janitor_guarantee_implies_relies(k, b2, pair.1);
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k, b2, pair.1)), lift_state(vrs_rely(pair.1)));
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k, b2, pair.1)), lift_state(vd_rely(pair.1)));
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k, b2, pair.1)), lift_state(vsts_rely(pair.1)));
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k, b2, pair.1)), lift_state(rmq_rely(pair.1)));
                    entails_trans(spec_g2, tla_forall(g_fn_s2), always(lift_state(widget_janitor_guarantee(k, b2, pair.1))));
                    entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(k, b2, pair.1))), always(lift_state(vrs_rely(pair.1))));
                    entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(k, b2, pair.1))), always(lift_state(vd_rely(pair.1))));
                    entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(k, b2, pair.1))), always(lift_state(vsts_rely(pair.1))));
                    entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(k, b2, pair.1))), always(lift_state(rmq_rely(pair.1))));
                }
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));
        entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose(cluster, s1, s2);
}

// The four controllers of the repository beside the sync controller of ANY
// configured kind and the janitors of its bindings. The configuration enters only
// through the hypotheses: its name is one model_kind is injective on, its
// bindings are well formed, its outer kind is none of the four framework kinds
// (from which no mirror kind is either, by the '@' argument), and its controllers
// run at ids of their own.
pub proof fn core_holds_for(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>)
    requires
        sync_kind_ok(k),
        forall |b: Binding| #[trigger] k.bindings.contains(b) ==> binding_ok(b),
        widget_kinds_off_framework(k),
        ids_ok(k.bindings, ids, sync_id),
        widget_ids_off_framework(k.bindings, ids, sync_id),
    ensures
        well_formed(core_cluster_for(k, spec_ok, sync_id, ids), core_set_for(k, spec_ok, sync_id, ids)),
        core(core_cluster_for(k, spec_ok, sync_id, ids), core_set_for(k, spec_ok, sync_id, ids)),
{
    broadcast use Set::lemma_map_contains;
    let cluster = core_cluster_for(k, spec_ok, sync_id, ids);
    let inner = cluster.cluster;
    framework_kind_names_ok();
    widget_kinds_distinct_from_framework(k);
    lemma_widget_installed_types(k, spec_ok);
    lemma_widget_cluster_for_models(k, spec_ok, sync_id, ids);

    // The Widget kinds survive the four framework inserts, and the Widget ids the
    // four framework controllers.
    assert(inner.synced_type_is_installed(k.outer_kind, spec_ok, k.selector));
    assert forall |b: Binding| #[trigger] k.bindings.contains(b)
        implies inner.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector) by {
        assert(inner_kind(k, b) == Kind::CustomResourceKind(remote_kind_name(k.name, b)));
    }
    assert(inner.controller_models.contains_pair(sync_id, widget_sync_controller_model(k)));
    assert(cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, k.bindings, spec_ok, sync_id, ids)));
    assert(janitors_registered(k, k.bindings, spec_ok, cluster, ids)) by {
        assert forall |b: Binding| #[trigger] k.bindings.contains(b) implies {
            &&& cluster.registry.contains_pair(ids[b], widget_janitor_controller_spec(k, b, k.bindings, spec_ok, ids[b]))
            &&& (widget_janitor_controller_spec(k, b, k.bindings, spec_ok, ids[b]).membership)(inner, ids[b])
        } by {
            lemma_binding_id_is_a_member(k.bindings, k.bindings, ids, sync_id, b);
            assert(ids[b] != sync_id);
            assert(binding_at(k.bindings, ids, ids[b]) == b);
            assert(inner.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector));
        }
    }
    assert((widget_sync_controller_spec(k, k.bindings, spec_ok, sync_id, ids).membership)(inner, sync_id)) by {
        assert forall |b: Binding| #[trigger] k.bindings.contains(b)
            implies sync_membership(k, b, k.bindings, spec_ok, inner, sync_id, ids[b]) by {
            lemma_binding_id_is_a_member(k.bindings, k.bindings, ids, sync_id, b);
            assert(ids[b] != sync_id);
            assert(inner.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector));
        }
    }
    all_core_holds(k, spec_ok, sync_id, ids, cluster);
}

// ============================================================
// The demo configuration
// ============================================================

// The one configured kind and its one binding of the demo cluster.
pub open spec fn wk() -> SyncKind { widget_sync_reconciler::widget_kind() }
pub open spec fn wb() -> Binding { widget_sync_reconciler::widget_binding() }
pub open spec fn wbs() -> Set<Binding> { Set::empty().insert(wb()) }
pub open spec fn wids() -> Map<Binding, int> { Map::empty().insert(wb(), janitor_id()) }
pub open spec fn wspec_ok() -> spec_fn(Value) -> bool { widget_sync_reconciler::widget_spec_ok() }

pub open spec fn cluster_instance() -> Cluster { cluster_instance_for(wk(), wspec_ok(), sync_id(), wids()) }

pub open spec fn core_cluster() -> CoreCluster { core_cluster_for(wk(), wspec_ok(), sync_id(), wids()) }

pub open spec fn widget_set() -> CoreSet { widget_set_for(wk(), wspec_ok(), sync_id(), wids()) }

pub open spec fn core_set() -> CoreSet { core_set_for(wk(), wspec_ok(), sync_id(), wids()) }

// The demo is one application of core_holds_for. The only thing the literal
// strings are used for is the four inequalities of widget_kinds_off_framework and
// the well-formedness of the kind name and the binding.
pub proof fn core_holds()
    ensures
        well_formed(core_cluster(), core_set()),
        core(core_cluster(), core_set()),
{
    widget_sync_reconciler::widget_demo_config_ok();
    framework_kind_names_ok();
    assert(wk().bindings =~= wbs());
    assert(widget_kinds_off_framework(wk())) by {
        reveal_strlit("widgets.anvil.dev");
        reveal_strlit("vreplicaset");
        reveal_strlit("vdeployment");
        reveal_strlit("vstatefulset");
        reveal_strlit("rabbitmq");
        assert(widget_sync_reconciler::widget_kind_name().len() == 17);
    }
    assert(ids_ok(wbs(), wids(), sync_id())) by {
        assert forall |x: Binding, y: Binding| #![trigger wids()[x], wids()[y]]
            wbs().contains(x) && wbs().contains(y) && wids()[x] == wids()[y] implies x == y by {
            assert(x == wb() && y == wb());
        }
    }
    assert(widget_ids_off_framework(wbs(), wids(), sync_id())) by {
        assert forall |b: Binding| #[trigger] wbs().contains(b) implies wids()[b] == janitor_id() by {
            assert(b == wb());
        }
    }
    core_holds_for(wk(), wspec_ok(), sync_id(), wids());
}

}
