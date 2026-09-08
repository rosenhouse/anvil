
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
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use crate::composition::{rabbitmq_reconciler::*, vdeployment_reconciler::*, vreplicaset_reconciler::*, vstatefulset_reconciler::*};
use crate::composition::{widget_janitor_reconciler::*, widget_sync_reconciler::*};
use crate::composition::widget_sync_reconciler;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

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

// The one configured kind and its one binding of this cluster.
pub open spec fn wk() -> SyncKind { widget_sync_reconciler::widget_kind() }
pub open spec fn wb() -> Binding { widget_sync_reconciler::widget_binding() }
pub open spec fn wbs() -> Set<Binding> { Set::empty().insert(wb()) }
pub open spec fn wids() -> Map<Binding, int> { Map::empty().insert(wb(), janitor_id()) }
pub open spec fn wspec_ok() -> spec_fn(Value) -> bool { widget_sync_reconciler::widget_spec_ok() }

pub open spec fn cluster_instance() -> Cluster {
    Cluster {
        installed_types: Map::empty()
            .insert(VReplicaSetView::kind()->CustomResourceKind_0, Cluster::installed_type::<VReplicaSetView>())
            .insert(VDeploymentView::kind()->CustomResourceKind_0, Cluster::installed_type::<VDeploymentView>())
            .insert(VStatefulSetView::kind()->CustomResourceKind_0, Cluster::installed_type::<VStatefulSetView>())
            .insert(RabbitmqClusterView::kind()->CustomResourceKind_0, Cluster::installed_type::<RabbitmqClusterView>())
            .insert(wk().outer_kind->CustomResourceKind_0, Cluster::synced_installed_type(wspec_ok(), wk().selector))
            .insert(inner_kind(wk(), wb())->CustomResourceKind_0, Cluster::synced_installed_type(wspec_ok(), wk().selector)),
        controller_models: Map::empty()
            .insert(vrs_id(), vrs_controller_model())
            .insert(vd_id(), vd_controller_model())
            .insert(vsts_id(), vsts_controller_model())
            .insert(rmq_id(), rabbitmq_controller_model())
            .insert(janitor_id(), widget_janitor_controller_model(wk(), wb()))
            .insert(sync_id(), widget_sync_controller_model(wk())),
    }
}

pub open spec fn core_cluster() -> CoreCluster {
    CoreCluster {
        cluster: cluster_instance(),
        registry: Map::empty()
            .insert(vrs_id(), vrs_controller_spec(vrs_id()))
            .insert(vd_id(), vd_controller_spec(vd_id()))
            .insert(vsts_id(), vsts_controller_spec(vsts_id()))
            .insert(rmq_id(), rmq_controller_spec(rmq_id()))
            .insert(janitor_id(), widget_janitor_controller_spec(wk(), wb(), wbs(), wspec_ok(), janitor_id()))
            .insert(sync_id(), widget_sync_controller_spec(wk(), wbs(), wspec_ok(), sync_id(), wids())),
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

// The four built-in-controller kind names are pairwise distinct, and none of
// them is a model kind of the configured Widget kind: the outer kind name is the
// CRD name, 17 characters, and a mirror kind name is that plus at least two
// separators, so both are longer than any of the four.
proof fn kind_strings_distinct()
    ensures
        "vreplicaset"@ != "vdeployment"@,
        "vreplicaset"@ != "vstatefulset"@,
        "vreplicaset"@ != "rabbitmq"@,
        "vdeployment"@ != "vstatefulset"@,
        "vdeployment"@ != "rabbitmq"@,
        "vstatefulset"@ != "rabbitmq"@,
        forall |name: StringView| #[trigger] name.len() <= 12 ==> wk().outer_kind != Kind::CustomResourceKind(name),
        forall |name: StringView, b: Binding| #![trigger name.len(), inner_kind(wk(), b)] name.len() <= 12 ==> inner_kind(wk(), b) != Kind::CustomResourceKind(name),
        wk().outer_kind != inner_kind(wk(), wb()),
        "vreplicaset"@.len() <= 12,
        "vdeployment"@.len() <= 12,
        "vstatefulset"@.len() <= 12,
        "rabbitmq"@.len() <= 12,
{
    reveal_strlit("vreplicaset");
    reveal_strlit("vdeployment");
    reveal_strlit("vstatefulset");
    reveal_strlit("rabbitmq");
    reveal_strlit("widgets.anvil.dev");
    reveal_strlit("@");
    reveal_strlit("/");
    reveal_strlit("default");
    reveal_strlit("inner");

    assert("vreplicaset"@ != "vdeployment"@) by {
        assert("vreplicaset"@[1] != "vdeployment"@[1]);
    };
    assert("vreplicaset"@.len() != "vstatefulset"@.len());
    assert("vreplicaset"@.len() != "rabbitmq"@.len());
    assert("vdeployment"@.len() != "vstatefulset"@.len());
    assert("vdeployment"@.len() != "rabbitmq"@.len());
    assert("vstatefulset"@.len() != "rabbitmq"@.len());

    assert(widget_sync_reconciler::widget_kind_name().len() == 17);
    assert forall |name: StringView| #[trigger] name.len() <= 12 implies wk().outer_kind != Kind::CustomResourceKind(name) by {}
    assert forall |name: StringView, b: Binding| #![trigger name.len(), inner_kind(wk(), b)] name.len() <= 12 implies inner_kind(wk(), b) != Kind::CustomResourceKind(name) by {
        assert(remote_kind_name(widget_sync_reconciler::widget_kind_name(), b).len()
            == 17 + at_sign().len() + b.namespace.len() + slash().len() + b.name.len());
    }
    widget_sync_reconciler::widget_kind_strings_distinct();
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
// controllers on it: it only touches Widget kinds.
proof fn widget_sync_guarantee_implies_relies(id: int)
    ensures
        lift_state(widget_sync_guarantee(wk(), id)).entails(lift_state(vrs_rely(id))),
        lift_state(widget_sync_guarantee(wk(), id)).entails(lift_state(vd_rely(id))),
        lift_state(widget_sync_guarantee(wk(), id)).entails(lift_state(vsts_rely(id))),
        lift_state(widget_sync_guarantee(wk(), id)).entails(lift_state(rmq_rely(id))),
{
    kind_strings_distinct();
    widget_sync_guarantee_implies_widget_kinds_only(wk(), id);
    let kinds_only = lift_state(widget_sync_touches_widget_kinds_only(wk(), id));

    assert forall |s: ClusterState| #[trigger] widget_sync_touches_widget_kinds_only(wk(), id)(s) implies vrs_rely(id)(s) by {}
    entails_trans(lift_state(widget_sync_guarantee(wk(), id)), kinds_only, lift_state(vrs_rely(id)));

    assert forall |s: ClusterState| #[trigger] widget_sync_touches_widget_kinds_only(wk(), id)(s) implies vd_rely(id)(s) by {}
    entails_trans(lift_state(widget_sync_guarantee(wk(), id)), kinds_only, lift_state(vd_rely(id)));

    assert forall |s: ClusterState| #[trigger] widget_sync_touches_widget_kinds_only(wk(), id)(s) implies vsts_rely(id)(s) by {}
    entails_trans(lift_state(widget_sync_guarantee(wk(), id)), kinds_only, lift_state(vsts_rely(id)));

    assert forall |s: ClusterState| #[trigger] widget_sync_touches_widget_kinds_only(wk(), id)(s) implies rmq_rely(id)(s) by {}
    entails_trans(lift_state(widget_sync_guarantee(wk(), id)), kinds_only, lift_state(rmq_rely(id)));
}

// The janitor's guarantee implies the relies of the other four controllers on
// it: it lists outer copies and deletes mirrors, nothing else.
proof fn widget_janitor_guarantee_implies_relies(id: int)
    ensures
        lift_state(widget_janitor_guarantee(wk(), wb(), id)).entails(lift_state(vrs_rely(id))),
        lift_state(widget_janitor_guarantee(wk(), wb(), id)).entails(lift_state(vd_rely(id))),
        lift_state(widget_janitor_guarantee(wk(), wb(), id)).entails(lift_state(vsts_rely(id))),
        lift_state(widget_janitor_guarantee(wk(), wb(), id)).entails(lift_state(rmq_rely(id))),
{
    kind_strings_distinct();
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(wk(), wb(), id)(s) implies vrs_rely(id)(s) by {}
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(wk(), wb(), id)(s) implies vd_rely(id)(s) by {}
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(wk(), wb(), id)(s) implies vsts_rely(id)(s) by {}
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(wk(), wb(), id)(s) implies rmq_rely(id)(s) by {}
}

// Each of the other four controllers' guarantees implies both Widget relies on
// it: none of them creates, updates or deletes a Widget kind, and none writes
// the status of an outer copy.
proof fn vrs_guarantee_implies_widget_relies(id: int)
    ensures
        lift_state(vrs_guarantee(id)).entails(lift_state(widget_sync_rely(wk(), id))),
        lift_state(vrs_guarantee(id)).entails(lift_state(widget_janitor_rely(wk(), id))),
{
    kind_strings_distinct();
    assert forall |s: ClusterState| #[trigger] vrs_guarantee(id)(s) implies widget_sync_rely(wk(), id)(s) by {}
    assert forall |s: ClusterState| #[trigger] vrs_guarantee(id)(s) implies widget_janitor_rely(wk(), id)(s) by {}
}

proof fn vd_guarantee_implies_widget_relies(id: int)
    ensures
        lift_state(vd_guarantee(id)).entails(lift_state(widget_sync_rely(wk(), id))),
        lift_state(vd_guarantee(id)).entails(lift_state(widget_janitor_rely(wk(), id))),
{
    kind_strings_distinct();
    assert forall |s: ClusterState| #[trigger] vd_guarantee(id)(s) implies widget_sync_rely(wk(), id)(s) by {}
    assert forall |s: ClusterState| #[trigger] vd_guarantee(id)(s) implies widget_janitor_rely(wk(), id)(s) by {}
}

proof fn vsts_guarantee_implies_widget_relies(id: int)
    ensures
        lift_state(vsts_guarantee(id)).entails(lift_state(widget_sync_rely(wk(), id))),
        lift_state(vsts_guarantee(id)).entails(lift_state(widget_janitor_rely(wk(), id))),
{
    kind_strings_distinct();
    assert forall |s: ClusterState| #[trigger] vsts_guarantee(id)(s) implies widget_sync_rely(wk(), id)(s) by {}
    assert forall |s: ClusterState| #[trigger] vsts_guarantee(id)(s) implies widget_janitor_rely(wk(), id)(s) by {}
}

proof fn rmq_guarantee_implies_widget_relies(id: int)
    ensures
        lift_state(rmq_guarantee(id)).entails(lift_state(widget_sync_rely(wk(), id))),
        lift_state(rmq_guarantee(id)).entails(lift_state(widget_janitor_rely(wk(), id))),
{
    kind_strings_distinct();
    assert forall |s: ClusterState| #[trigger] rmq_guarantee(id)(s) implies widget_sync_rely(wk(), id)(s) by {}
    assert forall |s: ClusterState| #[trigger] rmq_guarantee(id)(s) implies widget_janitor_rely(wk(), id)(s) by {}
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
        kind_strings_distinct();

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
// Joint CORE proof: compose {VRS, VD, VSTS, RMQ} with the Widget pair
// ============================================================

// The Widget pair, composed by widget_pair_core_holds: the janitor's ESR
// discharges the sync reconciler's liveness dependency inside the pair, so the
// pair as a whole has none.
pub open spec fn widget_set() -> CoreSet {
    union_coreset(
        widget_janitor_core_set(wk(), wb(), wbs(), wspec_ok(), janitor_id()),
        widget_sync_core_set(wk(), wbs(), wspec_ok(), sync_id(), wids()),
        true_pred())
}

pub open spec fn core_set() -> CoreSet {
    union_coreset(vrs_vd_vsts_rmq_set(), widget_set(), true_pred())
}

proof fn all_core_holds(cluster: CoreCluster)
    requires
        cluster.registry.contains_pair(vrs_id(), vrs_controller_spec(vrs_id())),
        cluster.registry.contains_pair(vd_id(), vd_controller_spec(vd_id())),
        cluster.registry.contains_pair(vsts_id(), vsts_controller_spec(vsts_id())),
        cluster.registry.contains_pair(rmq_id(), rmq_controller_spec(rmq_id())),
        cluster.registry.contains_pair(janitor_id(), widget_janitor_controller_spec(wk(), wb(), wbs(), wspec_ok(), janitor_id())),
        cluster.registry.contains_pair(sync_id(), widget_sync_controller_spec(wk(), wbs(), wspec_ok(), sync_id(), wids())),
        well_formed(cluster, vrs_core_set(vrs_id())),
        well_formed(cluster, vd_core_set(vd_id())),
        well_formed(cluster, vsts_core_set(vsts_id())),
        well_formed(cluster, rmq_core_set(rmq_id())),
        well_formed(cluster, widget_janitor_core_set(wk(), wb(), wbs(), wspec_ok(), janitor_id())),
        well_formed(cluster, widget_sync_core_set(wk(), wbs(), wspec_ok(), sync_id(), wids())),
    ensures
        well_formed(cluster, core_set()),
        core(cluster, core_set()),
{
    let s1 = vrs_vd_vsts_rmq_set();
    let s2 = widget_set();
    let spec = cluster_model(cluster);

    vrs_vd_vsts_rmq_core_holds(cluster);
    widget_pair_core_holds(wk(), wb(), wspec_ok(), cluster, janitor_id(), sync_id());

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        assert(s1.members =~= set![vrs_id(), vd_id(), vsts_id(), rmq_id()]);
        assert(s2.members =~= set![janitor_id(), sync_id()]);

        // The sixteen pointwise implications, lifted through always(...).
        vrs_guarantee_implies_widget_relies(vrs_id());
        vd_guarantee_implies_widget_relies(vd_id());
        vsts_guarantee_implies_widget_relies(vsts_id());
        rmq_guarantee_implies_widget_relies(rmq_id());
        widget_janitor_guarantee_implies_relies(janitor_id());
        widget_sync_guarantee_implies_relies(sync_id());

        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(widget_sync_rely(wk(), vrs_id())));
        entails_preserved_by_always(lift_state(vrs_guarantee(vrs_id())), lift_state(widget_janitor_rely(wk(), vrs_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(widget_sync_rely(wk(), vd_id())));
        entails_preserved_by_always(lift_state(vd_guarantee(vd_id())), lift_state(widget_janitor_rely(wk(), vd_id())));
        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(widget_sync_rely(wk(), vsts_id())));
        entails_preserved_by_always(lift_state(vsts_guarantee(vsts_id())), lift_state(widget_janitor_rely(wk(), vsts_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(widget_sync_rely(wk(), rmq_id())));
        entails_preserved_by_always(lift_state(rmq_guarantee(rmq_id())), lift_state(widget_janitor_rely(wk(), rmq_id())));
        entails_preserved_by_always(lift_state(widget_janitor_guarantee(wk(), wb(), janitor_id())), lift_state(vrs_rely(janitor_id())));
        entails_preserved_by_always(lift_state(widget_janitor_guarantee(wk(), wb(), janitor_id())), lift_state(vd_rely(janitor_id())));
        entails_preserved_by_always(lift_state(widget_janitor_guarantee(wk(), wb(), janitor_id())), lift_state(vsts_rely(janitor_id())));
        entails_preserved_by_always(lift_state(widget_janitor_guarantee(wk(), wb(), janitor_id())), lift_state(rmq_rely(janitor_id())));
        entails_preserved_by_always(lift_state(widget_sync_guarantee(wk(), sync_id())), lift_state(vrs_rely(sync_id())));
        entails_preserved_by_always(lift_state(widget_sync_guarantee(wk(), sync_id())), lift_state(vd_rely(sync_id())));
        entails_preserved_by_always(lift_state(widget_sync_guarantee(wk(), sync_id())), lift_state(vsts_rely(sync_id())));
        entails_preserved_by_always(lift_state(widget_sync_guarantee(wk(), sync_id())), lift_state(rmq_rely(sync_id())));

        // r_21: what the Widget pair relies on from the other four. The sync
        // reconciler's partial rely on a non-janitor id is widget_sync_rely.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                let spec_g1 = spec.and(tla_forall(g_fn_s1));
                tla_forall_apply(g_fn_s1, vrs_id());
                tla_forall_apply(g_fn_s1, vd_id());
                tla_forall_apply(g_fn_s1, vsts_id());
                tla_forall_apply(g_fn_s1, rmq_id());
                entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(vrs_guarantee(vrs_id()))));
                entails_trans(spec_g1, always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(widget_sync_rely(wk(), vrs_id()))));
                entails_trans(spec_g1, always(lift_state(vrs_guarantee(vrs_id()))), always(lift_state(widget_janitor_rely(wk(), vrs_id()))));
                entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(vd_guarantee(vd_id()))));
                entails_trans(spec_g1, always(lift_state(vd_guarantee(vd_id()))), always(lift_state(widget_sync_rely(wk(), vd_id()))));
                entails_trans(spec_g1, always(lift_state(vd_guarantee(vd_id()))), always(lift_state(widget_janitor_rely(wk(), vd_id()))));
                entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(vsts_guarantee(vsts_id()))));
                entails_trans(spec_g1, always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(widget_sync_rely(wk(), vsts_id()))));
                entails_trans(spec_g1, always(lift_state(vsts_guarantee(vsts_id()))), always(lift_state(widget_janitor_rely(wk(), vsts_id()))));
                entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(rmq_guarantee(rmq_id()))));
                entails_trans(spec_g1, always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(widget_sync_rely(wk(), rmq_id()))));
                entails_trans(spec_g1, always(lift_state(rmq_guarantee(rmq_id()))), always(lift_state(widget_janitor_rely(wk(), rmq_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        // r_12: what the other four rely on from the Widget pair.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                let spec_g2 = spec.and(tla_forall(g_fn_s2));
                tla_forall_apply(g_fn_s2, janitor_id());
                tla_forall_apply(g_fn_s2, sync_id());
                entails_trans(spec_g2, tla_forall(g_fn_s2), always(lift_state(widget_janitor_guarantee(wk(), wb(), janitor_id()))));
                entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(wk(), wb(), janitor_id()))), always(lift_state(vrs_rely(janitor_id()))));
                entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(wk(), wb(), janitor_id()))), always(lift_state(vd_rely(janitor_id()))));
                entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(wk(), wb(), janitor_id()))), always(lift_state(vsts_rely(janitor_id()))));
                entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(wk(), wb(), janitor_id()))), always(lift_state(rmq_rely(janitor_id()))));
                entails_trans(spec_g2, tla_forall(g_fn_s2), always(lift_state(widget_sync_guarantee(wk(), sync_id()))));
                entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(wk(), sync_id()))), always(lift_state(vrs_rely(sync_id()))));
                entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(wk(), sync_id()))), always(lift_state(vd_rely(sync_id()))));
                entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(wk(), sync_id()))), always(lift_state(vsts_rely(sync_id()))));
                entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(wk(), sync_id()))), always(lift_state(rmq_rely(sync_id()))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));
        entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose(cluster, s1, s2);
}

pub proof fn core_holds()
    ensures
        well_formed(core_cluster(), core_set()),
        core(core_cluster(), core_set()),
{
    let cluster = core_cluster();
    kind_strings_distinct();
    assert(cluster.cluster.synced_type_is_installed(wk().outer_kind, wspec_ok(), wk().selector));
    assert(cluster.cluster.synced_type_is_installed(inner_kind(wk(), wb()), wspec_ok(), wk().selector));
    assert(wbs().contains(wb()));
    assert(ids_ok(wbs(), wids(), sync_id()));
    assert(well_formed(cluster, widget_janitor_core_set(wk(), wb(), wbs(), wspec_ok(), janitor_id())));
    assert(well_formed(cluster, widget_sync_core_set(wk(), wbs(), wspec_ok(), sync_id(), wids())));
    all_core_holds(cluster);
}

}
