// R3s, stable cleanup, the pair's property: once no outer copy with uid `a`
// exists at the parent key of `k`, eventually no mirror at `k` points at `a`,
// and none does again.
//
// R3 (the janitor's ESR) removes each mirror object that points at `a`. This
// proof adds that the sync reconciler stops creating them: after the outer copy
// with uid `a` is gone, the snapshots the sync reconciler still holds for the
// parent key (one scheduled, one in an ongoing reconcile) drain, every later
// snapshot carries another uid, and every Create it sends for `k` is built from
// such a snapshot. The layers are: failures disabled (phase I); snapshots of the
// parent key avoid `a`; every request from the parent key is the pending request
// of its reconcile; then each object pointing at `a` is removed and nothing
// pointing at `a` replaces it.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::{api_server::*, temporal_rules::*};
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{set_lib::*, string_view::*};
use crate::widget_sync_controller::{
    model::{install::*, sync_reconciler::*},
    proof::{
        guarantee::*, helper_invariants::*, janitor_invariants::*,
        liveness::{api_actions::*, spec::*},
        predicate::*, sync_invariants::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The eventual facts and the layered specs.
// ---------------------------------------------------------------------------

// The snapshot scheduled for the parent key, if any, does not carry uid `a`.
pub open spec fn scheduled_avoids(controller_id: int, ok: ObjectRef, a: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.scheduled_reconciles(controller_id).contains_key(ok)
            ==> s.scheduled_reconciles(controller_id)[ok].metadata.uid != Some(a)
    }
}

// The snapshot of the ongoing reconcile of the parent key, if any, does not carry uid `a`.
pub open spec fn ongoing_avoids(controller_id: int, ok: ObjectRef, a: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.ongoing_reconciles(controller_id).contains_key(ok)
            ==> s.ongoing_reconciles(controller_id)[ok].triggering_cr.metadata.uid != Some(a)
    }
}

pub open spec fn snapshots_avoid(controller_id: int, ok: ObjectRef, a: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& scheduled_avoids(controller_id, ok, a)(s)
        &&& ongoing_avoids(controller_id, ok, a)(s)
    }
}

// Requests and responses of the reconcile of the parent key are consistent, and
// every request from that key is its pending request.
pub open spec fn key_msgs_ok(controller_id: int, ok: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, ok)(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, ok)(s)
    }
}

pub open spec fn cleanup_spec_l0(cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid) -> TempPred<ClusterState> {
    sync_stable_spec(cluster, controller_id, janitor_id).and(always(lift_state(parent_absent(key, a))))
}

pub open spec fn cleanup_spec_l1(cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid) -> TempPred<ClusterState> {
    cleanup_spec_l0(cluster, controller_id, janitor_id, key, a).and(always(lift_state(phase_i(controller_id))))
}

pub open spec fn cleanup_spec_l2(cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid) -> TempPred<ClusterState> {
    cleanup_spec_l1(cluster, controller_id, janitor_id, key, a).and(always(lift_state(snapshots_avoid(controller_id, outer_key_of(key), a))))
}

pub open spec fn cleanup_spec_l3(cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid) -> TempPred<ClusterState> {
    cleanup_spec_l2(cluster, controller_id, janitor_id, key, a).and(always(lift_state(key_msgs_ok(controller_id, outer_key_of(key)))))
}

pub proof fn cleanup_spec_l0_is_stable(cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    ensures valid(stable(cleanup_spec_l0(cluster, controller_id, janitor_id, key, a))),
{
    sync_stable_spec_is_stable(cluster, controller_id, janitor_id);
    always_p_is_stable(lift_state(parent_absent(key, a)));
    stable_and_n!(sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(parent_absent(key, a))));
}

pub proof fn cleanup_spec_l1_is_stable(cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    ensures valid(stable(cleanup_spec_l1(cluster, controller_id, janitor_id, key, a))),
{
    cleanup_spec_l0_is_stable(cluster, controller_id, janitor_id, key, a);
    always_p_is_stable(lift_state(phase_i(controller_id)));
    stable_and_n!(cleanup_spec_l0(cluster, controller_id, janitor_id, key, a), always(lift_state(phase_i(controller_id))));
}

pub proof fn cleanup_spec_l2_is_stable(cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    ensures valid(stable(cleanup_spec_l2(cluster, controller_id, janitor_id, key, a))),
{
    cleanup_spec_l1_is_stable(cluster, controller_id, janitor_id, key, a);
    always_p_is_stable(lift_state(snapshots_avoid(controller_id, outer_key_of(key), a)));
    stable_and_n!(cleanup_spec_l1(cluster, controller_id, janitor_id, key, a), always(lift_state(snapshots_avoid(controller_id, outer_key_of(key), a))));
}

// What the layers give, down to the stable spec.
pub proof fn lemma_cleanup_l1_facts(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    requires spec.entails(cleanup_spec_l1(cluster, controller_id, janitor_id, key, a)),
    ensures
        spec.entails(sync_stable_spec(cluster, controller_id, janitor_id)),
        spec.entails(always(lift_state(parent_absent(key, a)))),
        spec.entails(always(lift_state(phase_i(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
{
    entails_and_split(spec, cleanup_spec_l0(cluster, controller_id, janitor_id, key, a), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(parent_absent(key, a))));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
}

pub proof fn lemma_cleanup_l3_facts(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    requires spec.entails(cleanup_spec_l3(cluster, controller_id, janitor_id, key, a)),
    ensures
        spec.entails(cleanup_spec_l1(cluster, controller_id, janitor_id, key, a)),
        spec.entails(always(lift_state(snapshots_avoid(controller_id, outer_key_of(key), a)))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer_key_of(key))))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer_key_of(key))))),
{
    let ok = outer_key_of(key);
    entails_and_split(spec, cleanup_spec_l2(cluster, controller_id, janitor_id, key, a), always(lift_state(key_msgs_ok(controller_id, ok))));
    entails_and_split(spec, cleanup_spec_l1(cluster, controller_id, janitor_id, key, a), always(lift_state(snapshots_avoid(controller_id, ok, a))));
    always_weaken(spec, lift_state(key_msgs_ok(controller_id, ok)), lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, ok)));
    always_weaken(spec, lift_state(key_msgs_ok(controller_id, ok)), lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, ok)));
}

// ---------------------------------------------------------------------------
// Snapshots of the parent key eventually avoid `a`.
// ---------------------------------------------------------------------------

// The step relation these facts are preserved under.
pub open spec fn cleanup_snapshot_next(cluster: Cluster, controller_id: int, key: ObjectRef, a: Uid) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& parent_absent(key, a)(s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    }
}

pub proof fn lemma_always_cleanup_snapshot_next(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    requires spec.entails(cleanup_spec_l1(cluster, controller_id, janitor_id, key, a)),
    ensures spec.entails(always(lift_action(cleanup_snapshot_next(cluster, controller_id, key, a)))),
{
    lemma_cleanup_l1_facts(spec, cluster, controller_id, janitor_id, key, a);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    always_to_always_later(spec, lift_state(parent_absent(key, a)));
    combine_spec_entails_always_n!(
        spec, lift_action(cleanup_snapshot_next(cluster, controller_id, key, a)),
        lift_action(cluster.next()),
        later(lift_state(parent_absent(key, a))),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
}

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_true_leads_to_always_scheduled_avoids(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    requires
        key.kind == InnerWidgetView::kind(),
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(cleanup_spec_l1(cluster, controller_id, janitor_id, key, a)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(scheduled_avoids(controller_id, outer_key_of(key), a))))),
{
    let ok = outer_key_of(key);
    lemma_cleanup_l1_facts(spec, cluster, controller_id, janitor_id, key, a);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_cleanup_snapshot_next(spec, cluster, controller_id, janitor_id, key, a);
    lemma_sync_terminates(spec, cluster, controller_id, janitor_id, ok);
    let next = cleanup_snapshot_next(cluster, controller_id, key, a);
    let sched_ok = scheduled_avoids(controller_id, ok, a);
    let idle = Cluster::reconcile_idle(controller_id, ok);

    // sched_ok is stable: a new schedule copies the stored object, which does not have uid a.
    assert forall |s, s_prime: ClusterState| sched_ok(s) && #[trigger] next(s, s_prime) implies sched_ok(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ScheduleControllerReconcileStep(input) => {
                if input.0 == controller_id && input.1 == ok {
                    assert(s_prime.scheduled_reconciles(controller_id)[ok] == s.resources()[ok]);
                    assert(s_prime.api_server == s.api_server);
                }
            },
            _ => {},
        }
    }

    // A scheduled snapshot with uid a at an idle key is consumed (or replaced).
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(ok)
        &&& s.scheduled_reconciles(controller_id).contains_key(ok)
        &&& s.scheduled_reconciles(controller_id)[ok].metadata.uid == Some(a)
    };
    let input = (None::<Message>, Some(ok));
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || sched_ok(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ScheduleControllerReconcileStep(i) => {
                if i.0 == controller_id && i.1 == ok {
                    assert(s_prime.scheduled_reconciles(controller_id)[ok] == s.resources()[ok]);
                    assert(s_prime.api_server == s.api_server);
                }
            },
            _ => {},
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies sched_ok(s_prime) by {}
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::RunScheduledReconcile, (controller_id, input.0, input.1))(s) by {
        assert(ok.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, next, ControllerStep::RunScheduledReconcile, pre, sched_ok);

    // idle ~> sched_ok, hence true ~> sched_ok, hence true ~> []sched_ok.
    let idle_ok = |s: ClusterState| idle(s) && sched_ok(s);
    entails_implies_leads_to(spec, lift_state(idle_ok), lift_state(sched_ok));
    or_leads_to(spec, lift_state(pre), lift_state(idle_ok), lift_state(sched_ok));
    temp_pred_equality(lift_state(pre).or(lift_state(idle_ok)), lift_state(idle));
    leads_to_trans(spec, true_pred(), lift_state(idle), lift_state(sched_ok));
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(sched_ok));
}

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_true_leads_to_always_snapshots_avoid(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    requires
        key.kind == InnerWidgetView::kind(),
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(cleanup_spec_l1(cluster, controller_id, janitor_id, key, a)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(snapshots_avoid(controller_id, outer_key_of(key), a))))),
{
    let ok = outer_key_of(key);
    let l1 = cleanup_spec_l1(cluster, controller_id, janitor_id, key, a);
    let sched_ok = lift_state(scheduled_avoids(controller_id, ok, a));
    let target = snapshots_avoid(controller_id, ok, a);
    assert(l1.entails(l1));
    lemma_true_leads_to_always_scheduled_avoids(l1, cluster, controller_id, janitor_id, key, a);

    // Under l1 /\ []sched_ok: the ongoing snapshot is eventually good too, and stays so.
    let spec_a = l1.and(always(sched_ok));
    assert(spec_a.entails(spec_a));
    entails_and_split(spec_a, l1, always(sched_ok));
    lemma_cleanup_l1_facts(spec_a, cluster, controller_id, janitor_id, key, a);
    lemma_sync_stable_spec_facts(spec_a, cluster, controller_id, janitor_id);
    lemma_always_cleanup_snapshot_next(spec_a, cluster, controller_id, janitor_id, key, a);
    lemma_sync_terminates(spec_a, cluster, controller_id, janitor_id, ok);
    let next = cleanup_snapshot_next(cluster, controller_id, key, a);
    let idle = Cluster::reconcile_idle(controller_id, ok);
    assert forall |s, s_prime: ClusterState| target(s) && #[trigger] next(s, s_prime) implies target(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ScheduleControllerReconcileStep(i) => {
                if i.0 == controller_id && i.1 == ok {
                    assert(s_prime.scheduled_reconciles(controller_id)[ok] == s.resources()[ok]);
                    assert(s_prime.api_server == s.api_server);
                }
            },
            Step::ControllerStep(i) => {
                if i.0 == controller_id && i.2 == Some(ok) {
                    if s_prime.ongoing_reconciles(controller_id).contains_key(ok) {
                        if s.ongoing_reconciles(controller_id).contains_key(ok) {
                            assert(s_prime.ongoing_reconciles(controller_id)[ok].triggering_cr == s.ongoing_reconciles(controller_id)[ok].triggering_cr);
                        } else {
                            assert(s_prime.ongoing_reconciles(controller_id)[ok].triggering_cr == s.scheduled_reconciles(controller_id)[ok]);
                        }
                    }
                }
            },
            _ => {},
        }
    }
    entails_implies_leads_to(spec_a, lift_state(idle).and(sched_ok), lift_state(target));
    leads_to_by_borrowing_inv(spec_a, lift_state(idle), lift_state(target), sched_ok);
    leads_to_trans(spec_a, true_pred(), lift_state(idle), lift_state(target));
    leads_to_stable(spec_a, lift_action(next), true_pred(), lift_state(target));

    // Back to l1.
    cleanup_spec_l1_is_stable(cluster, controller_id, janitor_id, key, a);
    unpack_conditions_from_spec(l1, always(sched_ok), true_pred(), always(lift_state(target)));
    temp_pred_equality(true_pred().and(always(sched_ok)), always(sched_ok));
    leads_to_trans(l1, true_pred(), always(sched_ok), always(lift_state(target)));
    entails_trans(spec, l1, true_pred().leads_to(always(lift_state(target))));
}

// ---------------------------------------------------------------------------
// Requests from the parent key are eventually its pending request.
// ---------------------------------------------------------------------------

pub proof fn lemma_true_leads_to_always_key_msgs_ok(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(cleanup_spec_l2(cluster, controller_id, janitor_id, key, a)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(key_msgs_ok(controller_id, outer_key_of(key)))))),
{
    let ok = outer_key_of(key);
    let l2 = cleanup_spec_l2(cluster, controller_id, janitor_id, key, a);
    let xor = lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, ok));
    let msg_fact = lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, ok));
    assert(l2.entails(l2));
    entails_and_split(l2, cleanup_spec_l1(cluster, controller_id, janitor_id, key, a), always(lift_state(snapshots_avoid(controller_id, ok, a))));
    lemma_cleanup_l1_facts(l2, cluster, controller_id, janitor_id, key, a);
    lemma_sync_stable_spec_facts(l2, cluster, controller_id, janitor_id);
    lemma_sync_terminates(l2, cluster, controller_id, janitor_id, ok);
    always_tla_forall_apply(l2, |k: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, k)), ok);
    cluster.lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(l2, controller_id, ok);

    let spec_b = l2.and(always(xor));
    assert(spec_b.entails(spec_b));
    entails_and_split(spec_b, l2, always(xor));
    entails_and_split(spec_b, cleanup_spec_l1(cluster, controller_id, janitor_id, key, a), always(lift_state(snapshots_avoid(controller_id, ok, a))));
    lemma_cleanup_l1_facts(spec_b, cluster, controller_id, janitor_id, key, a);
    lemma_sync_stable_spec_facts(spec_b, cluster, controller_id, janitor_id);
    always_tla_forall_apply(spec_b, |k: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, k)), ok);
    always_tla_forall_apply(spec_b, |k: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, k, cluster.reconcile_model(controller_id).done)), ok);
    always_tla_forall_apply(spec_b, |k: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, k, cluster.reconcile_model(controller_id).error)), ok);
    cluster.lemma_true_leads_to_always_every_msg_from_key_is_pending_req_msg_of(spec_b, controller_id, ok);

    cleanup_spec_l2_is_stable(cluster, controller_id, janitor_id, key, a);
    unpack_conditions_from_spec(l2, always(xor), true_pred(), always(msg_fact));
    temp_pred_equality(true_pred().and(always(xor)), always(xor));
    leads_to_trans(l2, true_pred(), always(xor), always(msg_fact));
    leads_to_always_and(l2, true_pred(), xor, msg_fact);
    temp_pred_equality(lift_state(key_msgs_ok(controller_id, ok)), xor.and(msg_fact));
    entails_trans(spec, l2, true_pred().leads_to(always(lift_state(key_msgs_ok(controller_id, ok)))));
}

// ---------------------------------------------------------------------------
// Nothing pointing at `a` appears at `key` any more.
// ---------------------------------------------------------------------------

// The store facts one step keeps: a collected key stays collected, and an object
// with uid `m` at the key either stays (with its identity) or the key is collected.
#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_mirror_collected_after_step(
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, key: ObjectRef, a: Uid, m: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        sync_membership(cluster, controller_id, janitor_id),
        cluster.next()(s, s_prime),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime),
        cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s_prime),
        every_mirror_is_bound()(s),
        every_in_flight_inner_update_preserves_identity()(s),
        sync_rely_with_janitor(cluster, controller_id, janitor_id)(s),
        widget_sync_guarantee(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s),
        Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s),
        Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s),
        Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id)(s),
        Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id)(s),
        Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer_key_of(key), at_sync_step_closure(WidgetSyncStepView::Init))(s),
        Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer_key_of(key), cluster.reconcile_model(controller_id).done)(s),
        Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer_key_of(key), cluster.reconcile_model(controller_id).error)(s),
        sync_triggering_crs_are_bound(controller_id)(s),
        sync_pending_requests_match_snapshots(controller_id)(s),
        Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer_key_of(key))(s),
        ongoing_avoids(controller_id, outer_key_of(key), a)(s),
    ensures
        mirror_collected(key, a)(s) ==> mirror_collected(key, a)(s_prime),
        (s.resources().contains_key(key) && s.resources()[key].metadata.uid == Some(m))
            ==> mirror_collected(key, a)(s_prime) || (s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == Some(m)),
{
    let ok = outer_key_of(key);
    int_to_string_view_injectivity();
    OuterWidgetView::marshal_preserves_integrity();
    OuterWidgetView::marshal_preserves_metadata();
    InnerWidgetView::marshal_preserves_integrity();
    InnerWidgetView::marshal_preserves_metadata();
    InnerWidgetView::marshal_preserves_kind();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            assert(msg.dst is APIServer);
            assert(msg.content is APIRequest);
            lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
            if s_prime.resources().contains_key(key) {
                if s.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == s.resources()[key].metadata.uid {
                    // The same object: its identity is preserved.
                    assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                    let m0 = s.resources()[key].metadata.uid->0;
                    lemma_well_formed_inner_unmarshals(cluster, s, key);
                    let inner = InnerWidgetView::unmarshal(s.resources()[key])->Ok_0;
                    assert(mirror_is_bound(key)(s));
                    let p = choose |p: Uid| parent_uid_annotation(inner) == #[trigger] int_to_string_view(p);
                    assert(mirror_object_is(key, p, m0)(s));
                    lemma_mirror_object_after_step(cluster, s, s_prime, key, p, m0);
                    assert(mirror_object_is(key, p, m0)(s_prime));
                    if mirror_collected(key, a)(s) {
                        assert(p != a);
                        let new_inner = InnerWidgetView::unmarshal(s_prime.resources()[key])->Ok_0;
                        assert(parent_uid_annotation(new_inner) == int_to_string_view(p));
                        assert(!mirror_of_parent(s_prime.resources()[key], a));
                    }
                } else {
                    // A new object at the key: created by this request, by the sync
                    // reconciler, from a snapshot whose uid is not a.
                    lemma_new_object_comes_from_create(cluster, s, s_prime, msg, key);
                    let req = msg.content.get_create_request();
                    let new_obj = s_prime.resources()[key];
                    match msg.src {
                        HostId::Controller(id, ck) => {
                            assert(cluster.controller_models.contains_key(id));
                            if id == controller_id {
                                assert(sync_request_is_guaranteed(msg, s));
                                assert(mirror_create_req(req, ck)(s));
                                let outer = choose |outer: OuterWidgetView| {
                                    &&& outer.object_ref() == ck
                                    &&& outer.metadata.uid is Some
                                    &&& req.namespace == ck.namespace
                                    &&& req.obj == #[trigger] make_inner(outer).marshal()
                                    &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, ck)(s)
                                };
                                assert(req.obj.metadata == make_inner(outer).metadata);
                                assert(req.obj.metadata.name == Some(outer.metadata.name->0));
                                assert(ck.kind == OuterWidgetView::kind());
                                assert(ck == ok);
                                // The Create is the pending request of the reconcile of ok.
                                assert(s.ongoing_reconciles(controller_id).contains_key(ok));
                                let reconcile = s.ongoing_reconciles(controller_id)[ok];
                                assert(reconcile.pending_req_msg == Some(msg));
                                assert(sync_pending_request_is(controller_id, ok, reconcile));
                                let snap = OuterWidgetView::unmarshal(reconcile.triggering_cr)->Ok_0;
                                let state = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0;
                                assert(outer_snapshot_is_bound(reconcile.triggering_cr, ok)(s));
                                assert(snap.metadata == reconcile.triggering_cr.metadata);
                                match state.reconcile_step {
                                    WidgetSyncStepView::Init => { assert(false); },
                                    WidgetSyncStepView::AfterGetInner => { assert(false); },
                                    WidgetSyncStepView::AfterCreateInner => {},
                                    WidgetSyncStepView::AfterPatchInner => { assert(false); },
                                    WidgetSyncStepView::AfterPatchOuterStatus => { assert(false); },
                                    WidgetSyncStepView::Done => { assert(false); },
                                    WidgetSyncStepView::Error => { assert(false); },
                                }
                                assert(req.obj == make_inner(snap).marshal());
                                assert(make_inner(outer) == make_inner(snap));
                                assert(new_obj.metadata.annotations == make_inner(snap).metadata.annotations);
                                assert(snap.metadata.uid != Some(a));
                                assert(snap.metadata.uid is Some);
                                assert(parent_uid_of(snap) != int_to_string_view(a));
                                if InnerWidgetView::unmarshal(new_obj) is Ok {
                                    let new_inner = InnerWidgetView::unmarshal(new_obj)->Ok_0;
                                    assert(new_inner.metadata == new_obj.metadata);
                                    assert(parent_uid_annotation(new_inner) == parent_uid_of(snap));
                                }
                                assert(!mirror_of_parent(new_obj, a));
                            } else if id == janitor_id {
                                assert(janitor_request_is_guaranteed(msg));
                                assert(false);
                            } else {
                                assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                assert(widget_sync_rely(id)(s));
                                assert(req.obj.kind != InnerWidgetView::kind());
                                assert(false);
                            }
                        },
                        HostId::BuiltinController => { assert(false); },
                        HostId::PodMonkey => {
                            assert(req.key().kind == Kind::PodKind);
                            assert(false);
                        },
                        _ => { assert(false); },
                    }
                }
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// The step relation of the last layer.
pub open spec fn cleanup_step_next(cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s_prime)
        &&& every_mirror_is_bound()(s)
        &&& every_in_flight_inner_update_preserves_identity()(s)
        &&& sync_rely_with_janitor(cluster, controller_id, janitor_id)(s)
        &&& widget_sync_guarantee(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id)(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer_key_of(key), at_sync_step_closure(WidgetSyncStepView::Init))(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer_key_of(key), cluster.reconcile_model(controller_id).done)(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer_key_of(key), cluster.reconcile_model(controller_id).error)(s)
        &&& sync_triggering_crs_are_bound(controller_id)(s)
        &&& sync_pending_requests_match_snapshots(controller_id)(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer_key_of(key))(s)
        &&& ongoing_avoids(controller_id, outer_key_of(key), a)(s)
    }
}

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_always_cleanup_step_next(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    requires spec.entails(cleanup_spec_l3(cluster, controller_id, janitor_id, key, a)),
    ensures spec.entails(always(lift_action(cleanup_step_next(cluster, controller_id, janitor_id, key, a)))),
{
    let ok = outer_key_of(key);
    lemma_cleanup_l3_facts(spec, cluster, controller_id, janitor_id, key, a);
    lemma_cleanup_l1_facts(spec, cluster, controller_id, janitor_id, key, a);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    always_to_always_later(spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_to_always_later(spec, lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()));
    always_tla_forall_apply(spec, |k: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, k, at_sync_step_closure(WidgetSyncStepView::Init))), ok);
    always_tla_forall_apply(spec, |k: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, k, cluster.reconcile_model(controller_id).done)), ok);
    always_tla_forall_apply(spec, |k: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, k, cluster.reconcile_model(controller_id).error)), ok);
    always_weaken(spec, lift_state(snapshots_avoid(controller_id, ok, a)), lift_state(ongoing_avoids(controller_id, ok, a)));
    combine_spec_entails_always_n!(
        spec, lift_action(cleanup_step_next(cluster, controller_id, janitor_id, key, a)),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        later(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()),
        later(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>())),
        lift_state(every_mirror_is_bound()),
        lift_state(every_in_flight_inner_update_preserves_identity()),
        lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)),
        lift_state(widget_sync_guarantee(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id)),
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, ok, at_sync_step_closure(WidgetSyncStepView::Init))),
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, ok, cluster.reconcile_model(controller_id).done)),
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, ok, cluster.reconcile_model(controller_id).error)),
        lift_state(sync_triggering_crs_are_bound(controller_id)),
        lift_state(sync_pending_requests_match_snapshots(controller_id)),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, ok)),
        lift_state(ongoing_avoids(controller_id, ok, a))
    );
}

#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_true_leads_to_always_mirror_collected(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    requires
        key.kind == InnerWidgetView::kind(),
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(cleanup_spec_l3(cluster, controller_id, janitor_id, key, a)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(mirror_collected(key, a))))),
{
    let ok = outer_key_of(key);
    lemma_cleanup_l3_facts(spec, cluster, controller_id, janitor_id, key, a);
    lemma_cleanup_l1_facts(spec, cluster, controller_id, janitor_id, key, a);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_cleanup_step_next(spec, cluster, controller_id, janitor_id, key, a);
    let next = cleanup_step_next(cluster, controller_id, janitor_id, key, a);
    let collected = mirror_collected(key, a);
    let p_absent = lift_state(parent_absent(key, a));
    assert(outer_key_of(key) == ok);

    // collected is stable.
    assert forall |s, s_prime: ClusterState| collected(s) && #[trigger] next(s, s_prime) implies collected(s_prime) by {
        lemma_mirror_collected_after_step(cluster, controller_id, janitor_id, s, s_prime, key, a, 0);
    }

    // An object with uid m pointing at a is removed (R3), and nothing pointing at a
    // takes its place.
    let bad_m = |m: Uid| lift_state(|s: ClusterState| {
        &&& !collected(s)
        &&& s.resources()[key].metadata.uid == Some(m)
    });
    assert forall |m: Uid| spec.entails(#[trigger] bad_m(m).leads_to(lift_state(collected))) by {
        let has_m = |s: ClusterState| s.resources().contains_key(key) && s.resources()[key].metadata.uid == Some(m);
        let j = |s: ClusterState| collected(s) || has_m(s);
        let m_pm = lift_state(mirror_object_is(key, a, m));
        let gone_m = lift_state(object_is_gone(key, m));
        // R3 for this object.
        spec_entails_tla_forall_apply(
            spec,
            |i: (ObjectRef, Uid, Uid)| widget_mirror_eventually_collected_per_object(i.0, i.1, i.2),
            (key, a, m)
        );
        always_double_equality(p_absent);
        temp_pred_equality(always(p_absent).and(m_pm), m_pm.and(always(p_absent)));
        leads_to_by_borrowing_inv(spec, m_pm, gone_m, always(p_absent));
        entails_implies_leads_to(spec, bad_m(m), m_pm);
        leads_to_trans(spec, bad_m(m), m_pm, gone_m);
        // j holds from now on.
        assert forall |s, s_prime: ClusterState| #[trigger] next(s, s_prime) && j(s) implies j(s_prime) by {
            lemma_mirror_collected_after_step(cluster, controller_id, janitor_id, s, s_prime, key, a, m);
        }
        next_to_stable(next, j);
        entails_preserved_by_always(always(lift_action(next)), stable(lift_state(j)));
        always_double_equality(lift_action(next));
        entails_trans(spec, always(lift_action(next)), always(stable(lift_state(j))));
        let bj = bad_m(m).and(always(lift_state(j)));
        assert(stable(lift_state(j)).entails(bad_m(m).implies(bj)));
        entails_preserved_by_always(stable(lift_state(j)), bad_m(m).implies(bj));
        entails_trans(spec, always(stable(lift_state(j))), always(bad_m(m).implies(bj)));
        always_implies_to_leads_to(spec, bad_m(m), bj);
        leads_to_with_always(spec, bad_m(m), gone_m, lift_state(j));
        always_entails_current(lift_state(j));
        assert forall |ex: Execution<ClusterState>| #[trigger] gone_m.and(always(lift_state(j))).satisfied_by(ex)
        implies lift_state(collected).satisfied_by(ex) by {
            assert(always(lift_state(j)).satisfied_by(ex));
            assert(always(lift_state(j)).implies(lift_state(j)).satisfied_by(ex));
            assert(lift_state(j).satisfied_by(ex));
        }
        entails_implies_leads_to(spec, gone_m.and(always(lift_state(j))), lift_state(collected));
        leads_to_trans_n!(spec, bad_m(m), bj, gone_m.and(always(lift_state(j))), lift_state(collected));
    }
    leads_to_exists_intro(spec, bad_m, lift_state(collected));
    // Every uncollected state has such an m (stored objects have uids).
    let wf = lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed());
    let bad_wf = |s: ClusterState| !collected(s) && Cluster::each_object_in_etcd_is_weakly_well_formed()(s);
    assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(bad_wf).satisfied_by(ex) implies tla_exists(bad_m).satisfied_by(ex) by {
        let s = ex.head();
        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
        let m = s.resources()[key].metadata.uid->0;
        assert(bad_m(m).satisfied_by(ex));
    }
    entails_implies_leads_to(spec, lift_state(bad_wf), tla_exists(bad_m));
    leads_to_trans(spec, lift_state(bad_wf), tla_exists(bad_m), lift_state(collected));
    temp_pred_equality(lift_state(|s: ClusterState| !collected(s)).and(wf), lift_state(bad_wf));
    leads_to_by_borrowing_inv(spec, lift_state(|s: ClusterState| !collected(s)), lift_state(collected), wf);
    entails_implies_leads_to(spec, lift_state(collected), lift_state(collected));
    or_leads_to(spec, lift_state(|s: ClusterState| !collected(s)), lift_state(collected), lift_state(collected));
    temp_pred_equality(lift_state(|s: ClusterState| !collected(s)).or(lift_state(collected)), true_pred());
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(collected));
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

pub proof fn lemma_parent_absent_leads_to_always_collected(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef, a: Uid)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_stable_spec(cluster, controller_id, janitor_id)),
    ensures spec.entails(widget_mirror_stably_collected_per_key(key, a)),
{
    let stable_spec = sync_stable_spec(cluster, controller_id, janitor_id);
    let p_absent = lift_state(parent_absent(key, a));
    let collected = lift_state(mirror_collected(key, a));
    assert(stable_spec.entails(stable_spec));
    lemma_sync_stable_spec_facts(stable_spec, cluster, controller_id, janitor_id);
    if key.kind != InnerWidgetView::kind() {
        // A mirror never sits at a key of another kind, so the key is always collected.
        InnerWidgetView::marshal_preserves_kind();
        assert forall |s: ClusterState| #[trigger] Cluster::each_object_in_etcd_is_weakly_well_formed()(s) implies mirror_collected(key, a)(s) by {
            if s.resources().contains_key(key) {
                assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                assert(s.resources()[key].kind == key.kind);
            }
        }
        always_weaken(stable_spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()), collected);
        always_double_equality(collected);
        assert forall |ex: Execution<ClusterState>| #[trigger] always(collected).satisfied_by(ex)
        implies always(p_absent).implies(always(collected)).satisfied_by(ex) by {}
        always_weaken(stable_spec, always(collected), always(p_absent).implies(always(collected)));
        always_implies_to_leads_to(stable_spec, always(p_absent), always(collected));
    } else {
        let l0 = cleanup_spec_l0(cluster, controller_id, janitor_id, key, a);
        let l1 = cleanup_spec_l1(cluster, controller_id, janitor_id, key, a);
        let l2 = cleanup_spec_l2(cluster, controller_id, janitor_id, key, a);
        let l3 = cleanup_spec_l3(cluster, controller_id, janitor_id, key, a);
        let ph1 = always(lift_state(phase_i(controller_id)));
        let snaps = always(lift_state(snapshots_avoid(controller_id, outer_key_of(key), a)));
        let msgs = always(lift_state(key_msgs_ok(controller_id, outer_key_of(key))));
        assert(l0.entails(l0));
        assert(l1.entails(l1));
        assert(l2.entails(l2));
        assert(l3.entails(l3));
        // Phase I under l0.
        entails_and_split(l0, stable_spec, always(p_absent));
        lemma_sync_stable_spec_facts(l0, cluster, controller_id, janitor_id);
        lemma_true_leads_to_always_phase_i(l0, cluster, controller_id);
        // The layers.
        lemma_true_leads_to_always_snapshots_avoid(l1, cluster, controller_id, janitor_id, key, a);
        lemma_true_leads_to_always_key_msgs_ok(l2, cluster, controller_id, janitor_id, key, a);
        lemma_true_leads_to_always_mirror_collected(l3, cluster, controller_id, janitor_id, key, a);
        // Unpack them one by one.
        cleanup_spec_l2_is_stable(cluster, controller_id, janitor_id, key, a);
        unpack_conditions_from_spec(l2, msgs, true_pred(), always(collected));
        temp_pred_equality(true_pred().and(msgs), msgs);
        leads_to_trans(l2, true_pred(), msgs, always(collected));
        cleanup_spec_l1_is_stable(cluster, controller_id, janitor_id, key, a);
        unpack_conditions_from_spec(l1, snaps, true_pred(), always(collected));
        temp_pred_equality(true_pred().and(snaps), snaps);
        leads_to_trans(l1, true_pred(), snaps, always(collected));
        cleanup_spec_l0_is_stable(cluster, controller_id, janitor_id, key, a);
        unpack_conditions_from_spec(l0, ph1, true_pred(), always(collected));
        temp_pred_equality(true_pred().and(ph1), ph1);
        leads_to_trans(l0, true_pred(), ph1, always(collected));
        sync_stable_spec_is_stable(cluster, controller_id, janitor_id);
        unpack_conditions_from_spec(stable_spec, always(p_absent), true_pred(), always(collected));
        temp_pred_equality(true_pred().and(always(p_absent)), always(p_absent));
    }
    entails_trans(spec, stable_spec, always(p_absent).leads_to(always(collected)));
}

// R3s: the sync reconciler, given the janitor's ESR, keeps every parent key clean of
// mirrors pointing at a departed parent.
pub proof fn sync_mirrors_stably_collected(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(sync_next_with_wf(cluster, controller_id)),
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))),
        spec.entails(inner_releases_terminating_objects()),
        spec.entails(widget_janitor_esr(janitor_id)),
    ensures spec.entails(widget_mirrors_stably_collected()),
{
    entails_and_split(spec, widget_mirrors_eventually_collected(), always(lift_state(janitor_deletes_are_sound(janitor_id))));
    assert(sync_next_with_wf(cluster, controller_id).entails(always(lift_action(cluster.next()))));
    entails_trans(spec, sync_next_with_wf(cluster, controller_id), always(lift_action(cluster.next())));
    sync_invariants_hold(spec, cluster, controller_id, janitor_id);
    entails_and_n!(
        spec,
        sync_next_with_wf(cluster, controller_id),
        always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id))),
        inner_releases_terminating_objects(),
        widget_mirrors_eventually_collected(),
        sync_invariants(cluster, controller_id, janitor_id)
    );
    let per_key = |i: (ObjectRef, Uid)| widget_mirror_stably_collected_per_key(i.0, i.1);
    assert forall |i: (ObjectRef, Uid)| spec.entails(#[trigger] per_key(i)) by {
        lemma_parent_absent_leads_to_always_collected(spec, cluster, controller_id, janitor_id, i.0, i.1);
    }
    spec_entails_tla_forall(spec, per_key);
}

}
