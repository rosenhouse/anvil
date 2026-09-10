// The round trip: R1 and R2 chained across D4.
//
// R2's premise, inner_settled, is R1's conclusion plus two facts about the
// implementation running in the inner cluster, which Anvil does not model: that
// the inner status observes the mirror's current generation, and that it is the
// status R2 is stated for. D4 assumes that step.
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::widget_sync_controller::trusted::{liveness_theorem::*, spec_types::*};
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

// R1 and R2 for one outer copy, plus D4 for it, give the round trip for it. The
// chain is: always(outer_stable) gives itself and, by R1 on the weaker premise,
// always(spec_synced); D4 turns the pair into some status the inner side keeps;
// R2 turns each such status into the outer copy stably carrying it.
pub proof fn lemma_round_trip_per_cr(spec: TempPred<ClusterState>, k: SyncKind, b: Binding, outer: SyncedObjectView)
    requires
        spec.entails(widget_spec_eventually_synced_per_cr(k, b, outer)),
        spec.entails(inner_impl_settles_per_cr(k, b, outer)),
        forall |settled: SyncedStatusView| #[trigger] spec.entails(widget_status_eventually_mirrored_per_cr(k, b, outer, settled)),
    ensures spec.entails(widget_round_trip_per_cr(k, b, outer)),
{
    let stable = lift_state(outer_stable(k, b, outer));
    let spec_stable = lift_state(outer_spec_stable(k, b, outer));
    let synced = lift_state(spec_synced(k, outer));
    let settled_and_stable = |settled: SyncedStatusView|
        always(stable.and(lift_state(inner_settled(k, outer, settled))));
    let reported = |settled: SyncedStatusView|
        always(lift_state(status_synced(k, outer, settled)).and(lift_state(inner_settled(k, outer, settled))));

    // always(outer_stable) leads to itself.
    leads_to_self::<ClusterState>(always(stable));
    assert(spec.entails(always(stable).leads_to(always(stable))));

    // R1's premise is weaker than always(outer_stable), which pins the generation
    // on top of it, so R1 applies.
    assert(stable.entails(spec_stable));
    entails_preserved_by_always::<ClusterState>(stable, spec_stable);
    entails_implies_leads_to::<ClusterState>(spec, always(stable), always(spec_stable));
    leads_to_trans::<ClusterState>(spec, always(stable), always(spec_stable), always(synced));

    // Together: the outer copy stays stable and the mirror carries its spec.
    leads_to_always_and::<ClusterState>(spec, always(stable), stable, synced);

    // D4 turns that into some status the inner side settles on and keeps.
    leads_to_trans::<ClusterState>(spec, always(stable), always(stable.and(synced)), tla_exists(settled_and_stable));

    // R2 turns each such status into the outer copy stably carrying it.
    assert forall |settled: SyncedStatusView| #[trigger] spec.entails(settled_and_stable(settled).leads_to(tla_exists(reported))) by {
        // R2 for this status, with the closure beta-reduced onto its shape.
        assert(spec.entails(widget_status_eventually_mirrored_per_cr(k, b, outer, settled)));
        assert(settled_and_stable(settled) == always(stable.and(lift_state(inner_settled(k, outer, settled)))));

        // The premise is itself an always, so it leads to itself; carrying it
        // through is what keeps inner_settled beside status_synced.
        leads_to_self::<ClusterState>(settled_and_stable(settled));
        assert(spec.entails(settled_and_stable(settled).leads_to(settled_and_stable(settled))));
        leads_to_always_and::<ClusterState>(spec, settled_and_stable(settled),
            lift_state(status_synced(k, outer, settled)), stable.and(lift_state(inner_settled(k, outer, settled))));
        assert(lift_state(status_synced(k, outer, settled))
            .and(stable.and(lift_state(inner_settled(k, outer, settled))))
            .entails(lift_state(status_synced(k, outer, settled)).and(lift_state(inner_settled(k, outer, settled)))));
        entails_preserved_by_always::<ClusterState>(
            lift_state(status_synced(k, outer, settled)).and(stable.and(lift_state(inner_settled(k, outer, settled)))),
            lift_state(status_synced(k, outer, settled)).and(lift_state(inner_settled(k, outer, settled))));
        entails_implies_leads_to::<ClusterState>(spec,
            always(lift_state(status_synced(k, outer, settled)).and(stable.and(lift_state(inner_settled(k, outer, settled))))),
            reported(settled));
        leads_to_trans::<ClusterState>(spec, settled_and_stable(settled),
            always(lift_state(status_synced(k, outer, settled)).and(stable.and(lift_state(inner_settled(k, outer, settled))))),
            reported(settled));

        entails_exists_intro::<ClusterState, SyncedStatusView>(reported, settled);
        entails_implies_leads_to::<ClusterState>(spec, reported(settled), tla_exists(reported));
        leads_to_trans::<ClusterState>(spec, settled_and_stable(settled), reported(settled), tla_exists(reported));
    }
    leads_to_exists_intro::<ClusterState, SyncedStatusView>(spec, settled_and_stable, tla_exists(reported));
    leads_to_trans::<ClusterState>(spec, always(stable), tla_exists(settled_and_stable), tla_exists(reported));
}

// The round trip for every outer copy of the kind in the binding.
pub proof fn lemma_round_trip(spec: TempPred<ClusterState>, k: SyncKind, b: Binding)
    requires
        spec.entails(widget_spec_eventually_synced(k, b)),
        spec.entails(widget_status_eventually_mirrored(k, b)),
        spec.entails(inner_impl_settles(k, b)),
    ensures spec.entails(widget_round_trip(k, b)),
{
    assert forall |outer: SyncedObjectView| #[trigger] spec.entails(widget_round_trip_per_cr(k, b, outer)) by {
        spec_entails_tla_forall_apply::<ClusterState, SyncedObjectView>(spec, |o: SyncedObjectView| widget_spec_eventually_synced_per_cr(k, b, o), outer);
        spec_entails_tla_forall_apply::<ClusterState, SyncedObjectView>(spec, |o: SyncedObjectView| inner_impl_settles_per_cr(k, b, o), outer);
        assert forall |settled: SyncedStatusView| #[trigger] spec.entails(widget_status_eventually_mirrored_per_cr(k, b, outer, settled)) by {
            spec_entails_tla_forall_apply::<ClusterState, (SyncedObjectView, SyncedStatusView)>(
                spec, |i: (SyncedObjectView, SyncedStatusView)| widget_status_eventually_mirrored_per_cr(k, b, i.0, i.1), (outer, settled));
        }
        lemma_round_trip_per_cr(spec, k, b, outer);
    }
    spec_entails_tla_forall::<ClusterState, SyncedObjectView>(spec, |o: SyncedObjectView| widget_round_trip_per_cr(k, b, o));
}

}
