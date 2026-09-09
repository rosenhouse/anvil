// The round trip: R1 and R2 chained across D4.
//
// R1 promises the mirror carries the outer copy's spec. R2 promises the outer copy
// carries the status the inner side settled on. R2's premise, inner_settled,
// contains R1's conclusion, spec_synced, and two things besides: that the inner
// status observes the mirror's current generation, and that it is the particular
// `settled` R2 is stated for. R1 supplies neither, and no proof about the sync
// controller can -- both are facts about the implementation running in the inner
// cluster, which Anvil does not model. D4 assumes exactly that step.
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::spec::cluster::*;
use crate::widget_sync_controller::trusted::{liveness_theorem::*, spec_types::*};
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

// A predicate that holds of every execution holds always, under any spec.
proof fn lemma_valid_entails_always(spec: TempPred<ClusterState>, p: TempPred<ClusterState>)
    requires valid(p),
    ensures spec.entails(always(p)),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies always(p).satisfied_by(ex) by {
        assert forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)) by {}
    }
}

// Modus ponens under a spec: the shape core's conclusion is stated in.
pub proof fn lemma_entails_modus_ponens(spec: TempPred<ClusterState>, p: TempPred<ClusterState>, q: TempPred<ClusterState>)
    requires
        spec.entails(p.implies(q)),
        spec.entails(p),
    ensures spec.entails(q),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies q.satisfied_by(ex) by {
        assert(spec.implies(p.implies(q)).satisfied_by(ex));
        assert(spec.implies(p).satisfied_by(ex));
    }
}

// Both halves of a conjunction a spec entails.
pub proof fn lemma_entails_and_elim(spec: TempPred<ClusterState>, p: TempPred<ClusterState>, q: TempPred<ClusterState>)
    requires spec.entails(p.and(q)),
    ensures
        spec.entails(p),
        spec.entails(q),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex) implies p.satisfied_by(ex) && q.satisfied_by(ex) by {
        assert(spec.implies(p.and(q)).satisfied_by(ex));
    }
}

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
    let reported = |settled: SyncedStatusView| always(lift_state(status_synced(k, outer, settled)));

    // always(outer_stable) leads to itself.
    leads_to_self::<ClusterState>(always(stable));
    assert(spec.entails(always(stable).leads_to(always(stable))));

    // R1's premise is weaker than always(outer_stable), which pins the generation
    // on top of it, so R1 applies.
    assert(stable.entails(spec_stable));
    entails_preserved_by_always::<ClusterState>(stable, spec_stable);
    lemma_valid_entails_always(spec, always(stable).implies(always(spec_stable)));
    lemma_valid_entails_always(spec, always(synced).implies(always(synced)));
    leads_to_weaken::<ClusterState>(spec, always(spec_stable), always(synced), always(stable), always(synced));

    // Together: the outer copy stays stable and the mirror carries its spec.
    leads_to_always_and::<ClusterState>(spec, always(stable), stable, synced);

    // D4 turns that into some status the inner side settles on and keeps.
    leads_to_trans::<ClusterState>(spec, always(stable), always(stable.and(synced)), tla_exists(settled_and_stable));

    // R2 turns each such status into the outer copy stably carrying it.
    assert forall |settled: SyncedStatusView| #[trigger] spec.entails(settled_and_stable(settled).leads_to(tla_exists(reported))) by {
        // R2 for this status, with the closures beta-reduced onto its shape.
        assert(spec.entails(widget_status_eventually_mirrored_per_cr(k, b, outer, settled)));
        assert(settled_and_stable(settled) == always(stable.and(lift_state(inner_settled(k, outer, settled)))));
        assert(reported(settled) == always(lift_state(status_synced(k, outer, settled))));
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
