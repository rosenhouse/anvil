// The Widget janitor as a Welder controller spec, and its singleton core.
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::proof::{guarantee::*, liveness::janitor_proof::*, liveness::spec::*, predicate::*};
use crate::widget_sync_controller::trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*};
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

pub open spec fn widget_janitor_controller_spec(id: int) -> ControllerSpec {
    ControllerSpec {
        esr: widget_janitor_esr(id),
        liveness_dependency: true_pred(),
        safety_guarantee: always(lift_state(widget_janitor_guarantee(id))),
        // D3: the inner side releases terminating mirrors.
        environment_rely: inner_releases_terminating_objects(),
        safety_partial_rely: |other_id: int| always(lift_state(widget_janitor_rely(other_id))),
        fairness: |cluster: Cluster| janitor_next_with_wf(cluster, id),
        membership: |cluster: Cluster, c_id: int| {
            &&& cluster.controller_models.contains_pair(c_id, widget_janitor_controller_model())
            &&& cluster.type_is_installed_in_cluster::<InnerWidgetView>()
            &&& cluster.type_is_installed_in_cluster::<OuterWidgetView>()
        },
    }
}

pub open spec fn widget_janitor_core_set(id: int) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: true_pred(),
    }
}

// The per-controller rely facts, lifted into one always-predicate.
pub proof fn janitor_rely_facts_imply_lifted_condition(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(always(lift_state(#[trigger] widget_janitor_rely(other_id)))),
    ensures spec.entails(always(lifted_janitor_rely_condition(cluster, controller_id))),
{
    assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
        spec.satisfied_by(ex)
        && cluster.controller_models.remove(controller_id).contains_key(other_id)
        implies widget_janitor_rely(other_id)(ex.suffix(n).head()) by {
        assert(valid(spec.implies(always(lift_state(widget_janitor_rely(other_id))))));
        assert(spec.implies(always(lift_state(widget_janitor_rely(other_id)))).satisfied_by(ex));
        assert(always(lift_state(widget_janitor_rely(other_id))).satisfied_by(ex));
        assert(lift_state(widget_janitor_rely(other_id)).satisfied_by(ex.suffix(n)));
    }
}

pub proof fn widget_janitor_singleton_core_holds(cluster: CoreCluster, id: int)
    requires
        cluster.registry.contains_pair(id, widget_janitor_controller_spec(id)),
        well_formed(cluster, widget_janitor_core_set(id)),
    ensures
        core(cluster, widget_janitor_core_set(id)),
{
    let s = widget_janitor_core_set(id);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    assert(s.members.contains(id));
    assert((cluster.registry[id].membership)(inner, id));

    let fairness_fn = |i: int| if cluster.registry.contains_key(i) {
        (cluster.registry[i].fairness)(inner)
    } else { true_pred::<ClusterState>() };
    assert(spec.entails(janitor_next_with_wf(inner, id))) by {
        tla_forall_apply(fairness_fn, id);
    }
    assert(janitor_next_with_wf(inner, id).entails(always(lift_action(inner.next()))));
    entails_trans(spec, janitor_next_with_wf(inner, id), always(lift_action(inner.next())));

    // Guarantee.
    lemma_always_widget_janitor_guarantee(spec, inner, id);

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

    // R and the environment rely (D3) feed the liveness proof; D is true_pred.
    let assumption_re = tla_forall(R_fn).and(tla_forall(env_fn));
    let spec_re = spec.and(assumption_re);

    assert forall |c: int| spec_re.entails(#[trigger] ESR_fn(c)) by {
        if s.members.contains(c) {
            assert forall |other_id: int| #[trigger] inner.controller_models.remove(id).contains_key(other_id)
                implies spec_re.entails(always(lift_state(widget_janitor_rely(other_id)))) by {
                tla_forall_apply(R_fn, (id, other_id));
                entails_trans(spec_re, tla_forall(R_fn), R_fn((id, other_id)));
            }
            janitor_rely_facts_imply_lifted_condition(spec_re, inner, id);
            tla_forall_apply(env_fn, id);
            entails_trans(spec_re, tla_forall(env_fn), env_fn(id));
            assert(env_fn(id) == inner_releases_terminating_objects());
            entails_trans(spec_re, spec, lift_state(inner.init()));
            entails_trans(spec_re, spec, janitor_next_with_wf(inner, id));
            janitor_satisfies_its_spec(spec_re, inner, id);
            assert(ESR_fn(c) == widget_janitor_esr(id));
        }
    }
    spec_entails_tla_forall(spec_re, ESR_fn);
    entails_implies(spec, assumption_re, tla_forall(ESR_fn));

    assert(spec.entails(tla_forall(G_fn).and(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn))))) by {
        temp_pred_equality(tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)), assumption_re);
        entails_and(spec, tla_forall(G_fn), tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(ESR_fn)));
    }
}

}
