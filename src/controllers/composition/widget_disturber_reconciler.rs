// The disturber (widget_sync_controller/model/disturber_reconciler.rs) as a
// Welder controller spec, and the Widget pair composed with it: a cluster running
// the janitor, the sync reconciler and a controller that edits and deletes
// mirrors at will still has R1, R2, R3 and R3s. Nothing is assumed about the
// disturber beyond the shape of its requests: no fairness, no rely, no ESR. The
// premises of R1 and R2 are what say when its disturbance has stopped.
use crate::composition::widget_janitor_reconciler::*;
use crate::composition::widget_sync_reconciler::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::proof::disturber::*;
use crate::widget_sync_controller::proof::liveness::spec::*;
use crate::widget_sync_controller::trusted::{rely_guarantee::*, spec_types::*};
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

pub open spec fn widget_disturber_controller_spec(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, id: int) -> ControllerSpec {
    ControllerSpec {
        esr: true_pred(),
        liveness_dependency: true_pred(),
        safety_guarantee: always(lift_state(widget_disturber_guarantee(id))),
        environment_rely: true_pred(),
        safety_partial_rely: |other_id: int| true_pred(),
        fairness: |cluster: Cluster| true_pred(),
        membership: |cluster: Cluster, c_id: int| {
            &&& cluster.controller_models.contains_pair(c_id, widget_disturber_controller_model(inner_kind(k, b)))
            &&& cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector)
        },
    }
}

pub open spec fn widget_disturber_core_set(id: int) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: true_pred(),
    }
}

// The disturber's core: its guarantee holds, and its (empty) ESR follows.
pub proof fn widget_disturber_singleton_core_holds(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, id: int)
    requires
        cluster.registry.contains_pair(id, widget_disturber_controller_spec(k, b, spec_ok, id)),
        well_formed(cluster, widget_disturber_core_set(id)),
    ensures
        core(cluster, widget_disturber_core_set(id)),
{
    let s = widget_disturber_core_set(id);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    assert(s.members.contains(id));
    assert((cluster.registry[id].membership)(inner, id));

    lemma_always_widget_disturber_guarantee(spec, inner, inner_kind(k, b), spec_ok, k.selector, id);

    let G_fn = |c: int| if s.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
    let R_fn = |pair: (int, int)| if s.members.contains(pair.0) && !s.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let ESR_fn = |c: int| if s.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
    let env_fn = |c: int| if s.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred::<ClusterState>() };

    assert forall |c: int| spec.entails(#[trigger] G_fn(c)) by {
        if s.members.contains(c) {
            tla_forall_apply(G_fn, c);
        }
    }
    spec_entails_tla_forall(spec, G_fn);

    let assumption_rde = tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn));
    let spec_rde = spec.and(assumption_rde);
    assert forall |c: int| spec_rde.entails(#[trigger] ESR_fn(c)) by {
        if s.members.contains(c) {
            assert(ESR_fn(c) == true_pred::<ClusterState>());
        }
    }
    spec_entails_tla_forall(spec_rde, ESR_fn);
    entails_implies(spec, assumption_rde, tla_forall(ESR_fn));
    entails_and(spec, tla_forall(G_fn), assumption_rde.implies(tla_forall(ESR_fn)));
}

// ---------------------------------------------------------------------------
// The pair with the disturber.
// ---------------------------------------------------------------------------


pub open spec fn widget_disturbed_core_set(k: SyncKind, b: Binding, janitor_id: int, sync_id: int, disturber_id: int) -> CoreSet {
    union_coreset(widget_pair_core_set(k, b, janitor_id, sync_id), widget_disturber_core_set(disturber_id), true_pred())
}

// The pair and the disturber are compatible: the disturber relies on nothing,
// and its guarantee implies both members' relies on it.
pub proof fn widget_pair_with_disturber_core_holds(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, janitor_id: int, sync_id: int, disturber_id: int)
    requires
        k.bindings == Set::<Binding>::empty().insert(b),
        cluster.registry.contains_pair(janitor_id, widget_janitor_controller_spec(k, b, spec_ok, janitor_id)),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, Map::empty().insert(b, janitor_id))),
        cluster.registry.contains_pair(disturber_id, widget_disturber_controller_spec(k, b, spec_ok, disturber_id)),
        janitor_id != sync_id,
        janitor_id != disturber_id,
        sync_id != disturber_id,
        well_formed(cluster, widget_janitor_core_set(janitor_id)),
        well_formed(cluster, widget_sync_core_set(k, sync_id, Map::empty().insert(b, janitor_id))),
        well_formed(cluster, widget_disturber_core_set(disturber_id)),
    ensures
        well_formed(cluster, widget_disturbed_core_set(k, b, janitor_id, sync_id, disturber_id)),
        core(cluster, widget_disturbed_core_set(k, b, janitor_id, sync_id, disturber_id)),
{
    let s1 = widget_pair_core_set(k, b, janitor_id, sync_id);
    let s2 = widget_disturber_core_set(disturber_id);
    let spec = cluster_model(cluster);

    widget_pair_core_holds(k, b, spec_ok, cluster, janitor_id, sync_id);
    widget_disturber_singleton_core_holds(k, b, spec_ok, cluster, disturber_id);

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        assert(s1.members =~= set![janitor_id, sync_id]);
        assert(s2.members =~= set![disturber_id]);

        // r_21: the disturber relies on nothing.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                assert(pair.0 == disturber_id);
                assert(r21_fn(pair) == true_pred::<ClusterState>());
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        // r_12: both members' relies on the disturber follow from its guarantee.
        disturber_guarantee_implies_relies(k, disturber_id);
        entails_preserved_by_always(lift_state(widget_disturber_guarantee(disturber_id)), lift_state(widget_sync_rely(k, disturber_id)));
        entails_preserved_by_always(lift_state(widget_disturber_guarantee(disturber_id)), lift_state(widget_janitor_rely(k, disturber_id)));
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                assert(pair.1 == disturber_id);
                tla_forall_apply(g_fn_s2, disturber_id);
                assert(g_fn_s2(disturber_id) == always(lift_state(widget_disturber_guarantee(disturber_id))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(widget_disturber_guarantee(disturber_id))));
                if pair.0 == janitor_id {
                    assert(r12_fn(pair) == always(lift_state(widget_janitor_rely(k, disturber_id))));
                    entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(widget_disturber_guarantee(disturber_id))), always(lift_state(widget_janitor_rely(k, disturber_id))));
                } else {
                    assert(pair.0 == sync_id);
                    assert(r12_fn(pair) == always(lift_state(widget_sync_rely(k, disturber_id))));
                    entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(widget_disturber_guarantee(disturber_id))), always(lift_state(widget_sync_rely(k, disturber_id))));
                }
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));

        entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose(cluster, s1, s2);
}

// ---------------------------------------------------------------------------
// The pair with the disturber, for any configuration.
// ---------------------------------------------------------------------------

// The cluster of a configuration with the disturber beside the pair: the model
// kinds of `k` installed, the sync controller, the janitor of `b`, and the
// disturber on `b`'s mirror kind. A function of the configuration, like
// widget_pair_cluster_for.
pub open spec fn widget_disturbed_cluster_for(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int, disturber_id: int) -> Cluster {
    Cluster {
        installed_types: widget_installed_types(k, spec_ok),
        controller_models: widget_pair_cluster_for(k, b, spec_ok, sync_id, janitor_id).controller_models
            .insert(disturber_id, widget_disturber_controller_model(inner_kind(k, b))),
    }
}

pub open spec fn widget_disturbed_core_cluster_for(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int, disturber_id: int) -> CoreCluster {
    CoreCluster {
        cluster: widget_disturbed_cluster_for(k, b, spec_ok, sync_id, janitor_id, disturber_id),
        registry: Map::empty()
            .insert(janitor_id, widget_janitor_controller_spec(k, b, spec_ok, janitor_id))
            .insert(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, Map::empty().insert(b, janitor_id)))
            .insert(disturber_id, widget_disturber_controller_spec(k, b, spec_ok, disturber_id)),
    }
}

// The closed statement, for ANY one-binding configuration: the pair and the
// disturber satisfy `core`. As in widget_core_holds, the model kinds are told
// apart by the injectivity of model_kind, from `sync_kind_ok` and `binding_ok`.
pub proof fn widget_disturbed_core_holds_for(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int, disturber_id: int)
    requires
        sync_kind_ok(k),
        binding_ok(b),
        k.bindings == Set::<Binding>::empty().insert(b),
        janitor_id != sync_id,
        janitor_id != disturber_id,
        sync_id != disturber_id,
    ensures
        well_formed(widget_disturbed_core_cluster_for(k, b, spec_ok, sync_id, janitor_id, disturber_id),
            widget_disturbed_core_set(k, b, janitor_id, sync_id, disturber_id)),
        core(widget_disturbed_core_cluster_for(k, b, spec_ok, sync_id, janitor_id, disturber_id),
            widget_disturbed_core_set(k, b, janitor_id, sync_id, disturber_id)),
{
    let bs = Set::<Binding>::empty().insert(b);
    let ids = Map::<Binding, int>::empty().insert(b, janitor_id);
    let cluster = widget_disturbed_core_cluster_for(k, b, spec_ok, sync_id, janitor_id, disturber_id);
    let inner = cluster.cluster;

    lemma_widget_types_installed(k, spec_ok, inner);
    lemma_outer_kind_is_not_inner(k, b);
    assert(bs.contains(b));
    assert(inner.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector));
    assert(ids_ok(bs, ids, sync_id)) by {
        assert forall |x: Binding, y: Binding| #![trigger ids[x], ids[y]] bs.contains(x) && bs.contains(y) && ids[x] == ids[y] implies x == y by {
            assert(x == b && y == b);
        }
    }
    assert(well_formed(cluster, widget_janitor_core_set(janitor_id)));
    assert(well_formed(cluster, widget_disturber_core_set(disturber_id)));
    assert(well_formed(cluster, widget_sync_core_set(k, sync_id, ids))) by {
        assert forall |b2: Binding| #[trigger] bs.contains(b2)
            implies sync_membership(k, b2, spec_ok, inner, sync_id, ids[b2]) by {
            assert(b2 == b);
        }
    }
    widget_pair_with_disturber_core_holds(k, b, spec_ok, cluster, janitor_id, sync_id, disturber_id);
}

// ---------------------------------------------------------------------------
// The demo configuration with the disturber: three controllers.
// ---------------------------------------------------------------------------

pub open spec fn widget_disturber_id() -> int { 3 }

pub open spec fn widget_disturbed_cluster_instance() -> Cluster {
    widget_disturbed_cluster_for(widget_kind(), widget_binding(), widget_spec_ok(), widget_sync_id(), widget_janitor_id(), widget_disturber_id())
}

pub open spec fn widget_disturbed_core_cluster() -> CoreCluster {
    widget_disturbed_core_cluster_for(widget_kind(), widget_binding(), widget_spec_ok(), widget_sync_id(), widget_janitor_id(), widget_disturber_id())
}

// The demo is one line of the generic statement.
pub proof fn widget_disturbed_core_holds()
    ensures
        well_formed(widget_disturbed_core_cluster(), widget_disturbed_core_set(widget_kind(), widget_binding(), widget_janitor_id(), widget_sync_id(), widget_disturber_id())),
        core(widget_disturbed_core_cluster(), widget_disturbed_core_set(widget_kind(), widget_binding(), widget_janitor_id(), widget_sync_id(), widget_disturber_id())),
{
    widget_demo_config_ok();
    assert(widget_kind().bindings =~= Set::<Binding>::empty().insert(widget_binding()));
    widget_disturbed_core_holds_for(widget_kind(), widget_binding(), widget_spec_ok(), widget_sync_id(), widget_janitor_id(), widget_disturber_id());
}

}
