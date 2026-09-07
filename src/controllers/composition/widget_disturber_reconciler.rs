// The disturber (widget_sync_controller/model/disturber_reconciler.rs) as a
// Welder controller spec, and the Widget pair composed with it: a cluster running
// the janitor, the sync reconciler and a controller that edits and deletes
// mirrors at will still has R1, R2, R3 and R3s. Nothing is assumed about the
// disturber beyond the shape of its requests: no fairness, no rely, no ESR. The
// premises of R1 and R2 are what say when its disturbance has stopped.
use crate::composition::widget_janitor_reconciler::*;
use crate::composition::widget_sync_reconciler::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::proof::disturber::*;
use crate::widget_sync_controller::trusted::{rely_guarantee::*, spec_types::*};
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

pub open spec fn widget_disturber_controller_spec(id: int) -> ControllerSpec {
    ControllerSpec {
        esr: true_pred(),
        liveness_dependency: true_pred(),
        safety_guarantee: always(lift_state(widget_disturber_guarantee(id))),
        environment_rely: true_pred(),
        safety_partial_rely: |other_id: int| true_pred(),
        fairness: |cluster: Cluster| true_pred(),
        membership: |cluster: Cluster, c_id: int| {
            &&& cluster.controller_models.contains_pair(c_id, widget_disturber_controller_model())
            &&& cluster.type_is_installed_in_cluster::<InnerWidgetView>()
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
pub proof fn widget_disturber_singleton_core_holds(cluster: CoreCluster, id: int)
    requires
        cluster.registry.contains_pair(id, widget_disturber_controller_spec(id)),
        well_formed(cluster, widget_disturber_core_set(id)),
    ensures
        core(cluster, widget_disturber_core_set(id)),
{
    let s = widget_disturber_core_set(id);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    assert(s.members.contains(id));
    assert((cluster.registry[id].membership)(inner, id));

    lemma_always_widget_disturber_guarantee(spec, inner, id);

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

pub open spec fn widget_pair_core_set(janitor_id: int, sync_id: int) -> CoreSet {
    union_coreset(widget_janitor_core_set(janitor_id), widget_sync_core_set(sync_id, janitor_id), true_pred())
}

pub open spec fn widget_disturbed_core_set(janitor_id: int, sync_id: int, disturber_id: int) -> CoreSet {
    union_coreset(widget_pair_core_set(janitor_id, sync_id), widget_disturber_core_set(disturber_id), true_pred())
}

// The pair and the disturber are compatible: the disturber relies on nothing,
// and its guarantee implies both members' relies on it.
pub proof fn widget_pair_with_disturber_core_holds(cluster: CoreCluster, janitor_id: int, sync_id: int, disturber_id: int)
    requires
        cluster.registry.contains_pair(janitor_id, widget_janitor_controller_spec(janitor_id)),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(sync_id, janitor_id)),
        cluster.registry.contains_pair(disturber_id, widget_disturber_controller_spec(disturber_id)),
        janitor_id != sync_id,
        janitor_id != disturber_id,
        sync_id != disturber_id,
        well_formed(cluster, widget_janitor_core_set(janitor_id)),
        well_formed(cluster, widget_sync_core_set(sync_id, janitor_id)),
        well_formed(cluster, widget_disturber_core_set(disturber_id)),
    ensures
        well_formed(cluster, widget_disturbed_core_set(janitor_id, sync_id, disturber_id)),
        core(cluster, widget_disturbed_core_set(janitor_id, sync_id, disturber_id)),
{
    let s1 = widget_pair_core_set(janitor_id, sync_id);
    let s2 = widget_disturber_core_set(disturber_id);
    let spec = cluster_model(cluster);

    widget_pair_core_holds(cluster, janitor_id, sync_id);
    widget_disturber_singleton_core_holds(cluster, disturber_id);

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
        disturber_guarantee_implies_relies(disturber_id);
        entails_preserved_by_always(lift_state(widget_disturber_guarantee(disturber_id)), lift_state(widget_sync_rely(disturber_id)));
        entails_preserved_by_always(lift_state(widget_disturber_guarantee(disturber_id)), lift_state(widget_janitor_rely(disturber_id)));
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                assert(pair.1 == disturber_id);
                tla_forall_apply(g_fn_s2, disturber_id);
                assert(g_fn_s2(disturber_id) == always(lift_state(widget_disturber_guarantee(disturber_id))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(widget_disturber_guarantee(disturber_id))));
                if pair.0 == janitor_id {
                    assert(r12_fn(pair) == always(lift_state(widget_janitor_rely(disturber_id))));
                    entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(widget_disturber_guarantee(disturber_id))), always(lift_state(widget_janitor_rely(disturber_id))));
                } else {
                    assert(pair.0 == sync_id);
                    assert(r12_fn(pair) == always(lift_state(widget_sync_rely(disturber_id))));
                    entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(widget_disturber_guarantee(disturber_id))), always(lift_state(widget_sync_rely(disturber_id))));
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
// A concrete three-controller cluster: the pair and the disturber.
// ---------------------------------------------------------------------------

pub open spec fn widget_disturber_id() -> int { 3 }

pub open spec fn widget_disturbed_cluster_instance() -> Cluster {
    Cluster {
        installed_types: Map::empty()
            .insert(OuterWidgetView::kind()->CustomResourceKind_0, Cluster::installed_type::<OuterWidgetView>())
            .insert(InnerWidgetView::kind()->CustomResourceKind_0, Cluster::installed_type::<InnerWidgetView>()),
        controller_models: Map::empty()
            .insert(widget_janitor_id(), widget_janitor_controller_model())
            .insert(widget_sync_id(), widget_sync_controller_model())
            .insert(widget_disturber_id(), widget_disturber_controller_model()),
    }
}

pub open spec fn widget_disturbed_core_cluster() -> CoreCluster {
    CoreCluster {
        cluster: widget_disturbed_cluster_instance(),
        registry: Map::empty()
            .insert(widget_janitor_id(), widget_janitor_controller_spec(widget_janitor_id()))
            .insert(widget_sync_id(), widget_sync_controller_spec(widget_sync_id(), widget_janitor_id()))
            .insert(widget_disturber_id(), widget_disturber_controller_spec(widget_disturber_id())),
    }
}

proof fn widget_kind_strings_distinct()
    ensures OuterWidgetView::kind()->CustomResourceKind_0 != InnerWidgetView::kind()->CustomResourceKind_0,
{
    reveal_strlit("widget");
    reveal_strlit("widget@inner");
    assert("widget"@.len() != "widget@inner"@.len());
}

pub proof fn widget_disturbed_core_holds()
    ensures
        well_formed(widget_disturbed_core_cluster(), widget_disturbed_core_set(widget_janitor_id(), widget_sync_id(), widget_disturber_id())),
        core(widget_disturbed_core_cluster(), widget_disturbed_core_set(widget_janitor_id(), widget_sync_id(), widget_disturber_id())),
{
    let cluster = widget_disturbed_core_cluster();
    widget_kind_strings_distinct();
    assert(cluster.cluster.type_is_installed_in_cluster::<OuterWidgetView>());
    assert(cluster.cluster.type_is_installed_in_cluster::<InnerWidgetView>());
    assert(well_formed(cluster, widget_janitor_core_set(widget_janitor_id())));
    assert(well_formed(cluster, widget_sync_core_set(widget_sync_id(), widget_janitor_id())));
    assert(well_formed(cluster, widget_disturber_core_set(widget_disturber_id())));
    widget_pair_with_disturber_core_holds(cluster, widget_janitor_id(), widget_sync_id(), widget_disturber_id());
}

}
