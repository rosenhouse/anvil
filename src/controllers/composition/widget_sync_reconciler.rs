// The Widget sync reconciler as a Welder controller spec, its singleton core, and
// the composition of the sync reconciler with the janitor.
//
// The sync reconciler depends on the janitor only through the janitor's
// ControllerSpec: on its guarantee (the partial rely for the janitor's id) and on
// its ESR (the liveness dependency: R3, and that the janitor's Deletes are sound).
// Its environment rely is D3 (the inner side releases terminating mirrors).
// compose_dep discharges the dependency with the janitor's proved ESR.
use crate::composition::widget_janitor_reconciler::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::proof::{guarantee::*, liveness::cleanup_proof::*, liveness::spec::*, liveness::sync_spec_proof::*, liveness::sync_status_proof::*};
use crate::widget_sync_controller::trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*};
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

// R1, R2 and R3s together.
pub open spec fn widget_sync_esr() -> TempPred<ClusterState> {
    widget_spec_eventually_synced().and(widget_status_eventually_mirrored()).and(widget_mirrors_stably_collected())
}

pub open spec fn widget_sync_partial_rely(janitor_id: int) -> spec_fn(int) -> TempPred<ClusterState> {
    |other_id: int| if other_id == janitor_id {
        always(lift_state(widget_janitor_guarantee(other_id)))
    } else {
        always(lift_state(widget_sync_rely(other_id)))
    }
}

pub open spec fn widget_sync_controller_spec(id: int, janitor_id: int) -> ControllerSpec {
    ControllerSpec {
        esr: widget_sync_esr(),
        // The janitor's ESR: R3 and sound deletes.
        liveness_dependency: widget_janitor_esr(janitor_id),
        safety_guarantee: always(lift_state(widget_sync_guarantee(id))),
        // D3: the inner side releases terminating mirrors.
        environment_rely: inner_releases_terminating_objects(),
        safety_partial_rely: widget_sync_partial_rely(janitor_id),
        fairness: |cluster: Cluster| sync_next_with_wf(cluster, id),
        membership: |cluster: Cluster, c_id: int| sync_membership(cluster, c_id, janitor_id),
    }
}

pub open spec fn widget_sync_core_set(id: int, janitor_id: int) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: widget_janitor_esr(janitor_id),
    }
}

// The per-controller rely facts, lifted into the one always-predicate the liveness
// proofs take.
pub proof fn sync_rely_facts_imply_lifted_condition(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int)
    requires
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(#[trigger] widget_sync_partial_rely(janitor_id)(other_id)),
    ensures spec.entails(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))),
{
    assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
        spec.satisfied_by(ex)
        && cluster.controller_models.remove(controller_id).contains_key(other_id)
        implies (if other_id == janitor_id { widget_janitor_guarantee(janitor_id)(ex.suffix(n).head()) } else { widget_sync_rely(other_id)(ex.suffix(n).head()) }) by {
        let p = widget_sync_partial_rely(janitor_id)(other_id);
        assert(valid(spec.implies(p)));
        assert(spec.implies(p).satisfied_by(ex));
        assert(p.satisfied_by(ex));
        if other_id == janitor_id {
            assert(always(lift_state(widget_janitor_guarantee(other_id))).satisfied_by(ex));
            assert(lift_state(widget_janitor_guarantee(other_id)).satisfied_by(ex.suffix(n)));
        } else {
            assert(always(lift_state(widget_sync_rely(other_id))).satisfied_by(ex));
            assert(lift_state(widget_sync_rely(other_id)).satisfied_by(ex.suffix(n)));
        }
    }
}

pub proof fn widget_sync_singleton_core_holds(cluster: CoreCluster, id: int, janitor_id: int)
    requires
        cluster.registry.contains_pair(id, widget_sync_controller_spec(id, janitor_id)),
        well_formed(cluster, widget_sync_core_set(id, janitor_id)),
    ensures
        core(cluster, widget_sync_core_set(id, janitor_id)),
{
    let s = widget_sync_core_set(id, janitor_id);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    assert(s.members.contains(id));
    assert((cluster.registry[id].membership)(inner, id));
    assert(sync_membership(inner, id, janitor_id));

    let fairness_fn = |i: int| if cluster.registry.contains_key(i) {
        (cluster.registry[i].fairness)(inner)
    } else { true_pred::<ClusterState>() };
    assert(spec.entails(sync_next_with_wf(inner, id))) by {
        tla_forall_apply(fairness_fn, id);
    }
    assert(sync_next_with_wf(inner, id).entails(always(lift_action(inner.next()))));
    entails_trans(spec, sync_next_with_wf(inner, id), always(lift_action(inner.next())));

    // Guarantee.
    lemma_always_widget_sync_guarantee(spec, inner, id);

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

    // R, D (R3) and the environment rely (D3) all feed the liveness proofs.
    let assumption_rde = tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn));
    let spec_rde = spec.and(assumption_rde);

    assert forall |c: int| spec_rde.entails(#[trigger] ESR_fn(c)) by {
        if s.members.contains(c) {
            assert forall |other_id: int| #[trigger] inner.controller_models.remove(id).contains_key(other_id)
                implies spec_rde.entails(widget_sync_partial_rely(janitor_id)(other_id)) by {
                tla_forall_apply(R_fn, (id, other_id));
                assert(R_fn((id, other_id)) == widget_sync_partial_rely(janitor_id)(other_id));
                entails_trans(spec_rde, tla_forall(R_fn), R_fn((id, other_id)));
            }
            sync_rely_facts_imply_lifted_condition(spec_rde, inner, id, janitor_id);
            tla_forall_apply(env_fn, id);
            entails_trans(spec_rde, tla_forall(env_fn), env_fn(id));
            assert(env_fn(id) == inner_releases_terminating_objects());
            assert(s.liveness_dependency == widget_janitor_esr(janitor_id));
            entails_trans(spec_rde, spec, lift_state(inner.init()));
            entails_trans(spec_rde, spec, sync_next_with_wf(inner, id));
            sync_eventually_synced(spec_rde, inner, id, janitor_id);
            sync_eventually_mirrors_status(spec_rde, inner, id, janitor_id);
            sync_mirrors_stably_collected(spec_rde, inner, id, janitor_id);
            entails_and(spec_rde, widget_spec_eventually_synced(), widget_status_eventually_mirrored());
            entails_and(spec_rde, widget_spec_eventually_synced().and(widget_status_eventually_mirrored()), widget_mirrors_stably_collected());
            assert(ESR_fn(c) == widget_sync_esr());
        }
    }
    spec_entails_tla_forall(spec_rde, ESR_fn);
    entails_implies(spec, assumption_rde, tla_forall(ESR_fn));
    entails_and(spec, tla_forall(G_fn), assumption_rde.implies(tla_forall(ESR_fn)));
}

// ---------------------------------------------------------------------------
// Composing the janitor with the sync reconciler.
// ---------------------------------------------------------------------------

// The sync reconciler's guarantee implies the janitor's rely on it: the only mirror
// it creates is make_inner(outer) for an outer copy at the request's namespace and
// name, and it never sends Update or GetThenUpdate.
pub proof fn sync_guarantee_implies_janitor_rely(id: int)
    ensures lift_state(widget_sync_guarantee(id)).entails(lift_state(widget_janitor_rely(id))),
{
    assert forall |s: ClusterState| #[trigger] widget_sync_guarantee(id)(s) implies widget_janitor_rely(id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => req.obj.kind == InnerWidgetView::kind() ==> {
                    &&& req.obj.metadata.name is Some
                    &&& mirror_create_req(req, ObjectRef {
                        kind: OuterWidgetView::kind(),
                        namespace: req.namespace,
                        name: req.obj.metadata.name->0,
                    })(s)
                },
                APIRequest::UpdateRequest(req) => mirror_update_req(req)(s),
                APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(req)(s),
                _ => true,
            }) by {
            let outer_key = msg.src->Controller_1;
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => {
                    assert(mirror_create_req(req, outer_key)(s));
                    let outer = choose |outer: OuterWidgetView| {
                        &&& outer.object_ref() == outer_key
                        &&& outer.metadata.uid is Some
                        &&& req.namespace == outer_key.namespace
                        &&& req.obj == #[trigger] make_inner(outer).marshal()
                        &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s)
                    };
                    InnerWidgetView::marshal_preserves_metadata();
                    assert(req.obj.metadata == make_inner(outer).metadata);
                    assert(req.obj.metadata.name == Some(outer.metadata.name->0));
                    let key2 = ObjectRef { kind: OuterWidgetView::kind(), namespace: req.namespace, name: req.obj.metadata.name->0 };
                    assert(key2 == outer_key);
                }
                _ => {}
            }
        }
    }
}

// The pair {janitor, sync}: the janitor's ESR discharges the sync reconciler's
// liveness dependency, the two guarantees discharge each other's relies.
pub proof fn widget_pair_core_holds(cluster: CoreCluster, janitor_id: int, sync_id: int)
    requires
        cluster.registry.contains_pair(janitor_id, widget_janitor_controller_spec(janitor_id)),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(sync_id, janitor_id)),
        janitor_id != sync_id,
        well_formed(cluster, widget_janitor_core_set(janitor_id)),
        well_formed(cluster, widget_sync_core_set(sync_id, janitor_id)),
    ensures
        well_formed(cluster, union_coreset(widget_janitor_core_set(janitor_id), widget_sync_core_set(sync_id, janitor_id), true_pred())),
        core(cluster, union_coreset(widget_janitor_core_set(janitor_id), widget_sync_core_set(sync_id, janitor_id), true_pred())),
{
    let s1 = widget_janitor_core_set(janitor_id);
    let s2 = widget_sync_core_set(sync_id, janitor_id);
    let spec = cluster_model(cluster);

    widget_janitor_singleton_core_holds(cluster, janitor_id);
    widget_sync_singleton_core_holds(cluster, sync_id, janitor_id);

    assert(satisfies_dependency(cluster, s1, s2)) by {
        let esr_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
        let esr_s1 = tla_forall(esr_fn_s1);
        assert(s1.members.contains(janitor_id));
        tla_forall_apply(esr_fn_s1, janitor_id);
        assert(esr_fn_s1(janitor_id) == widget_janitor_esr(janitor_id));
        entails_trans(spec.and(esr_s1), esr_s1, s2.liveness_dependency);
        entails_implies(spec, esr_s1, s2.liveness_dependency);
    }

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        sync_guarantee_implies_janitor_rely(sync_id);
        entails_preserved_by_always(lift_state(widget_sync_guarantee(sync_id)), lift_state(widget_janitor_rely(sync_id)));

        // r_21: what the sync reconciler relies on from the janitor is the janitor's
        // guarantee itself.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                assert(pair == (sync_id, janitor_id));
                tla_forall_apply(g_fn_s1, janitor_id);
                assert(g_fn_s1(janitor_id) == always(lift_state(widget_janitor_guarantee(janitor_id))));
                assert(r21_fn(pair) == always(lift_state(widget_janitor_guarantee(janitor_id))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(widget_janitor_guarantee(janitor_id))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        // r_12: the janitor's rely on the sync reconciler follows from the sync
        // reconciler's guarantee.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                assert(pair == (janitor_id, sync_id));
                tla_forall_apply(g_fn_s2, sync_id);
                assert(g_fn_s2(sync_id) == always(lift_state(widget_sync_guarantee(sync_id))));
                assert(r12_fn(pair) == always(lift_state(widget_janitor_rely(sync_id))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(widget_sync_guarantee(sync_id))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(widget_sync_guarantee(sync_id))), always(lift_state(widget_janitor_rely(sync_id))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));

        entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose_dep(cluster, s1, s2);
}

// ---------------------------------------------------------------------------
// A concrete two-controller cluster, instantiating the pair.
// ---------------------------------------------------------------------------

pub open spec fn widget_janitor_id() -> int { 1 }
pub open spec fn widget_sync_id() -> int { 2 }

pub open spec fn widget_cluster_instance() -> Cluster {
    Cluster {
        installed_types: Map::empty()
            .insert(OuterWidgetView::kind()->CustomResourceKind_0, Cluster::installed_type::<OuterWidgetView>())
            .insert(InnerWidgetView::kind()->CustomResourceKind_0, Cluster::installed_type::<InnerWidgetView>()),
        controller_models: Map::empty()
            .insert(widget_janitor_id(), widget_janitor_controller_model())
            .insert(widget_sync_id(), widget_sync_controller_model()),
    }
}

pub open spec fn widget_core_cluster() -> CoreCluster {
    CoreCluster {
        cluster: widget_cluster_instance(),
        registry: Map::empty()
            .insert(widget_janitor_id(), widget_janitor_controller_spec(widget_janitor_id()))
            .insert(widget_sync_id(), widget_sync_controller_spec(widget_sync_id(), widget_janitor_id())),
    }
}

pub open spec fn widget_core_set() -> CoreSet {
    union_coreset(widget_janitor_core_set(widget_janitor_id()), widget_sync_core_set(widget_sync_id(), widget_janitor_id()), true_pred())
}

proof fn widget_kind_strings_distinct()
    ensures OuterWidgetView::kind()->CustomResourceKind_0 != InnerWidgetView::kind()->CustomResourceKind_0,
{
    reveal_strlit("widget");
    reveal_strlit("widget@inner");
    assert("widget"@.len() != "widget@inner"@.len());
}

pub proof fn widget_core_holds()
    ensures
        well_formed(widget_core_cluster(), widget_core_set()),
        core(widget_core_cluster(), widget_core_set()),
{
    let cluster = widget_core_cluster();
    widget_kind_strings_distinct();
    assert(cluster.cluster.type_is_installed_in_cluster::<OuterWidgetView>());
    assert(cluster.cluster.type_is_installed_in_cluster::<InnerWidgetView>());
    assert(well_formed(cluster, widget_janitor_core_set(widget_janitor_id())));
    assert(well_formed(cluster, widget_sync_core_set(widget_sync_id(), widget_janitor_id())));
    widget_pair_core_holds(cluster, widget_janitor_id(), widget_sync_id());
}

}
