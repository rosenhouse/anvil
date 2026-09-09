// Weak fairness of the one-store actions on the abstract execution follows from
// weak fairness of the multi-store actions on the execution. The one point of
// care is a message: a one-store action waits on a relabeled message, and the
// multi-store message behind it must be the same one for as long as the wait
// lasts. It is, because a message leaves the network only when a step consumes
// it, that step consumes the relabeled message too, and the one-store network
// never holds two copies of a message.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::multi_cluster::{api_server::*, execution::*, relabel::*, steps::*};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, api_server::types::*, builtin_controllers::types::*, cluster::*,
    controller::state_machine::*, controller::types::*, message::*, network::types::*, multi_cluster::*,
};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use verus_temporal_logic::defs::*;
use vstd::{map_lib::*, multiset::*, prelude::*};

verus! {

// ---------------------------------------------------------------------------
// Messages and steps.
// ---------------------------------------------------------------------------

// The steps that take m out of the network.
pub open spec fn consumes(step: Step, m: Message) -> bool {
    match step {
        Step::APIServerStep(input) => input == Some(m),
        Step::ControllerStep(input) => input.1 == Some(m),
        Step::DropReqStep(input) => input.0 == m,
        Step::ExternalStep(input) => input.1 == Some(m),
        _ => false,
    }
}

pub proof fn lemma_consumes_relabel<S>(tc: MultiCluster<S>, r: Relabeling<S>, step: Step, m: Message)
    requires consumes(step, m),
    ensures consumes(relabel_step(tc, r, step), relabel_msg(tc, r, m)),
{
}

// A multi-store step that does not consume m keeps it in flight.
pub proof fn lemma_kept<S>(tc: MultiCluster<S>, s: MultiClusterState<S>, s_prime: MultiClusterState<S>, side: S, step: Step, m: Message)
    requires
        tc.next_step(s, s_prime, side, step),
        s.in_flight().contains(m),
        !consumes(step, m),
    ensures s_prime.in_flight().contains(m),
{
    broadcast use group_multiset_axioms;
    match step {
        Step::APIServerStep(input) => {},
        Step::BuiltinControllersStep(input) => {},
        Step::ControllerStep(input) => {},
        Step::ScheduleControllerReconcileStep(input) => {},
        Step::RestartControllerStep(input) => {},
        Step::DisableCrashStep(input) => {},
        Step::DropReqStep(input) => {},
        Step::DisableReqDropStep => {},
        Step::PodMonkeyStep(input) => {},
        Step::DisablePodMonkeyStep => {},
        Step::ExternalStep(input) => {},
        Step::StutterStep => {},
    }
}

// The one-store invariants the argument uses.
pub open spec fn m1_msg_invs(a: ClusterState) -> bool {
    &&& Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()(a)
    &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(a)
}

pub open spec fn no_externals(cluster: Cluster) -> bool {
    forall |id: int| #[trigger] cluster.controller_models.contains_key(id) ==> cluster.controller_models[id].external_model is None
}

// A one-store step that consumes m1 leaves it out of flight: what it sends is
// a response to a request or a request with a fresh id, never m1 again.
pub proof fn lemma_consumed_gone(cluster: Cluster, a: ClusterState, a_prime: ClusterState, step: Step, m1: Message)
    requires
        no_externals(cluster),
        cluster.next_step(a, a_prime, step),
        consumes(step, m1),
        m1_msg_invs(a),
    ensures !a_prime.in_flight().contains(m1),
{
    broadcast use group_multiset_axioms;
    assert(a.in_flight().count(m1) == 1);
    match step {
        Step::APIServerStep(input) => {
            let resp = transition_by_etcd(cluster.installed_types, m1, a.api_server).1;
            assert(resp_msg_matches_req_msg(resp, m1));
            assert(resp != m1);
            assert(a_prime.in_flight() == a.in_flight().remove(m1).add(Multiset::singleton(resp)));
        },
        Step::ControllerStep(input) => {
            let id = input.0;
            let key_o = input.2;
            let key = key_o->0;
            let sm = cluster.controller(id);
            let c = a.controller_and_externals[id].controller;
            let cin = ControllerActionInput { recv: Some(m1), scheduled_cr_key: key_o, rpc_id_allocator: a.rpc_id_allocator };
            let st = choose |step: ControllerStep| (#[trigger] (sm.step_to_action)(step).precondition)((sm.action_input)(step, cin), c);
            let host = sm.next_result(cin, c);
            let sent = host->Enabled_1.send;
            assert(a_prime.in_flight() == a.in_flight().remove(m1).add(sent));
            match st {
                ControllerStep::RunScheduledReconcile => { assert(false); },
                ControllerStep::ContinueReconcile => {
                    let rs = c.ongoing_reconciles[key];
                    let resp_o = if m1.content is APIResponse {
                        Some(ResponseContent::KubernetesResponse(m1.content->APIResponse_0))
                    } else {
                        Some(ResponseContent::ExternalResponse(m1.content->ExternalResponse_0))
                    };
                    let (ls, req_o) = (cluster.reconcile_model(id).transition)(rs.triggering_cr, resp_o, rs.local_state);
                    if req_o is Some {
                        let pending = match req_o->0 {
                            RequestContent::KubernetesRequest(req) => controller_req_msg(id, key, a.rpc_id_allocator.allocate().1, req),
                            RequestContent::ExternalRequest(req) => controller_external_req_msg(id, key, a.rpc_id_allocator.allocate().1, req),
                        };
                        assert(sent == Multiset::singleton(pending));
                        assert(pending.rpc_id == a.rpc_id_allocator.rpc_id_counter);
                        assert(pending != m1);
                    } else {
                        assert(sent == Multiset::<Message>::empty());
                    }
                },
                ControllerStep::EndReconcile => { assert(false); },
            }
        },
        Step::DropReqStep(input) => {
            let resp = form_matched_err_resp_msg(m1, input.1);
            assert(resp_msg_matches_req_msg(resp, m1));
            assert(resp != m1);
            assert(a_prime.in_flight() == a.in_flight().remove(m1).add(Multiset::singleton(resp)));
        },
        Step::ExternalStep(input) => {
            assert(cluster.controller_models.contains_key(input.0));
            assert(false);
        },
        _ => { assert(false); },
    }
}

// ---------------------------------------------------------------------------
// The abstract execution satisfies the one-store message invariants.
// ---------------------------------------------------------------------------

pub open spec fn fair_sim<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>) -> bool {
    &&& simulation(tc, r, ex)
    &&& forall |i: nat| m1_msg_invs(#[trigger] abs_at(tc, r, ex, i))
}

// An always-property of the abstract execution, read at position i.
proof fn lemma_always_at<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, p: StatePred<ClusterState>, i: nat)
    requires always(lift_state(p)).satisfied_by(alpha(tc, r, ex)),
    ensures p(abs_at(tc, r, ex, i)),
{
    let ex1 = alpha(tc, r, ex);
    assert(lift_state(p).satisfied_by(ex1.suffix(i)));
    assert(ex1.suffix(i).head() == abs_at(tc, r, ex, i));
}

#[verifier::rlimit(50)]
pub proof fn lemma_fair_sim<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>)
    requires
        simulation(tc, r, ex),
        lift_state(tc.cluster.init()).satisfied_by(alpha(tc, r, ex)),
        always(lift_action(tc.cluster.next())).satisfied_by(alpha(tc, r, ex)),
    ensures fair_sim(tc, r, ex),
{
    let cluster = tc.cluster;
    let ex1 = alpha(tc, r, ex);
    let spec = lift_state(cluster.init()).and(always(lift_action(cluster.next())));
    let p1 = Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id();
    let p2 = Cluster::every_in_flight_msg_has_lower_id_than_allocator();
    assert(spec.entails(lift_state(cluster.init())));
    assert(spec.entails(always(lift_action(cluster.next()))));
    cluster.lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    assert(spec.satisfied_by(ex1));
    assert(spec.implies(always(lift_state(p1))).satisfied_by(ex1));
    assert(spec.implies(always(lift_state(p2))).satisfied_by(ex1));
    assert forall |i: nat| m1_msg_invs(#[trigger] abs_at(tc, r, ex, i)) by {
        lemma_always_at(tc, r, ex, p1, i);
        lemma_always_at(tc, r, ex, p2, i);
    }
}

// The relabeled message m1 is in flight at every abstract state from t on.
pub open spec fn in_flight_from<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, t: nat, m1: Message) -> bool {
    forall |k: nat| abs_at(tc, r, ex, #[trigger] (t + k)).in_flight().contains(m1)
}

// One step: if m1 is still in flight afterwards, the message behind it still is.
proof fn lemma_msg_stays_step<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, i: nat, m1: Message, m2: Message)
    requires
        fair_sim(tc, r, ex),
        relabel_msg(tc, r, m2) == m1,
        state_at(ex, i).in_flight().contains(m2),
        abs_at(tc, r, ex, i + 1).in_flight().contains(m1),
    ensures state_at(ex, i + 1).in_flight().contains(m2),
{
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    assert(tc.next()(s, s_prime));
    let (side, step) = choose |side: S, step: Step| tc.next_step(s, s_prime, side, step);
    if consumes(step, m2) {
        lemma_consumes_relabel(tc, r, step, m2);
        lemma_alpha_step_of(tc, r, ex, i, side, step);
        assert(no_externals(tc.cluster));
        lemma_consumed_gone(tc.cluster, abs_at(tc, r, ex, i), abs_at(tc, r, ex, i + 1), relabel_step(tc, r, step), m1);
        assert(false);
    } else {
        lemma_kept(tc, s, s_prime, side, step, m2);
    }
}

// While m1 stays in flight in the abstract execution, the message behind it stays in flight too.
pub proof fn lemma_msg_stays<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, t: nat, m1: Message, m2: Message, d: nat)
    requires
        fair_sim(tc, r, ex),
        relabel_msg(tc, r, m2) == m1,
        state_at(ex, t).in_flight().contains(m2),
        in_flight_from(tc, r, ex, t, m1),
    ensures state_at(ex, t + d).in_flight().contains(m2),
    decreases d,
{
    if d > 0 {
        let i = (t + d - 1) as nat;
        lemma_msg_stays(tc, r, ex, t, m1, m2, (d - 1) as nat);
        assert(state_at(ex, i).in_flight().contains(m2));
        assert(abs_at(tc, r, ex, t + d).in_flight().contains(m1));
        assert(i + 1 == t + d);
        lemma_msg_stays_step(tc, r, ex, i, m1, m2);
    }
}

// ---------------------------------------------------------------------------
// Fairness of each action.
// ---------------------------------------------------------------------------

// Positions along the two executions.
proof fn lemma_suffix_heads<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, t: nat, k: nat)
    ensures
        ex.suffix(t).suffix(k).head() == state_at(ex, t + k),
        ex.suffix(t).suffix(k).head_next() == state_at(ex, t + k + 1),
        alpha(tc, r, ex).suffix(t).suffix(k).head() == abs_at(tc, r, ex, t + k),
        alpha(tc, r, ex).suffix(t).suffix(k).head_next() == abs_at(tc, r, ex, t + k + 1),
{
}

// The API server of the message's side is enabled on it when the one-store API
// server is enabled on its relabeling.
proof fn lemma_api_pre_from_abs<S>(tc: MultiCluster<S>, r: Relabeling<S>, s: MultiClusterState<S>, m2: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        s.in_flight().contains(m2),
        tc.cluster.api_server_next().pre(Some(relabel_msg(tc, r, m2)))(abs(tc, r, s, uid_next, rv_next)),
    ensures tc.api_server_next(tc.side_of_msg(m2)).pre(Some(m2))(s),
{
}

// A two-store API server step is the one-store step on the relabeled message.
proof fn lemma_api_forward_transfer<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, i: nat, side: S, m2: Message)
    requires
        fair_sim(tc, r, ex),
        tc.api_server_next(side).forward(Some(m2))(state_at(ex, i), state_at(ex, i + 1)),
    ensures tc.cluster.api_server_next().forward(Some(relabel_msg(tc, r, m2)))(abs_at(tc, r, ex, i), abs_at(tc, r, ex, i + 1)),
{
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    lemma_api_server_step(tc, r, s, s_prime, side, Some(m2), uid_sum(tc, s), rv_sum(tc, s));
    assert(uid_next_after(tc, s, s_prime, uid_sum(tc, s)) == uid_sum(tc, s_prime));
    assert(rv_next_after(tc, s, s_prime, rv_sum(tc, s)) == rv_sum(tc, s_prime));
}

// The action is enabled at every position from t on.
pub open spec fn always_enabled_from<S, I>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, act: Action<ClusterState, I, ()>, input: I, t: nat) -> bool {
    forall |k: nat| #[trigger] act.pre(input)(abs_at(tc, r, ex, t + k))
}

// The action is taken at some position from t on.
pub open spec fn step_from<S, I>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, act: Action<ClusterState, I, ()>, input: I, t: nat) -> bool {
    exists |d: nat| #[trigger] act.forward(input)(abs_at(tc, r, ex, t + d), abs_at(tc, r, ex, t + d + 1))
}

pub open spec fn two_step_from<S, I>(ex: Execution<MultiClusterState<S>>, act: Action<MultiClusterState<S>, I, ()>, input: I, t: nat) -> bool {
    exists |d: nat| #[trigger] act.forward(input)(state_at(ex, t + d), state_at(ex, t + d + 1))
}

// From a fairness premise on the two-store execution to the step it promises.
proof fn lemma_wf_apply<S, I>(act: Action<MultiClusterState<S>, I, ()>, input: I, ex: Execution<MultiClusterState<S>>, t: nat)
    requires
        act.weak_fairness(input).satisfied_by(ex),
        forall |k: nat| #[trigger] act.pre(input)(state_at(ex, t + k)),
    ensures two_step_from(ex, act, input, t),
{
    assert forall |k: nat| #[trigger] lift_state(act.pre(input)).satisfied_by(ex.suffix(t).suffix(k)) by {
        assert(ex.suffix(t).suffix(k).head() == state_at(ex, t + k));
    }
    assert(always(lift_state(act.pre(input))).satisfied_by(ex.suffix(t)));
    assert(always(lift_state(act.pre(input))).implies(eventually(lift_action(act.forward(input)))).satisfied_by(ex.suffix(t)));
    let d = choose |d: nat| #[trigger] lift_action(act.forward(input)).satisfied_by(ex.suffix(t).suffix(d));
    assert(ex.suffix(t).suffix(d).head() == state_at(ex, t + d));
    assert(ex.suffix(t).suffix(d).head_next() == state_at(ex, t + d + 1));
    assert(act.forward(input)(state_at(ex, t + d), state_at(ex, t + d + 1)));
}

// Weak fairness of a one-store action on the abstract execution, from a step at
// every position where the action is always enabled.
proof fn lemma_wf_from_steps<S, I>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, act: Action<ClusterState, I, ()>, input: I)
    requires forall |t: nat| always_enabled_from(tc, r, ex, act, input, t) ==> #[trigger] step_from(tc, r, ex, act, input, t),
    ensures act.weak_fairness(input).satisfied_by(alpha(tc, r, ex)),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |t: nat| #[trigger] always(lift_state(act.pre(input))).implies(eventually(lift_action(act.forward(input)))).satisfied_by(ex1.suffix(t)) by {
        if always(lift_state(act.pre(input))).satisfied_by(ex1.suffix(t)) {
            assert forall |k: nat| #[trigger] act.pre(input)(abs_at(tc, r, ex, t + k)) by {
                assert(lift_state(act.pre(input)).satisfied_by(ex1.suffix(t).suffix(k)));
                assert(ex1.suffix(t).suffix(k).head() == abs_at(tc, r, ex, t + k));
            }
            assert(always_enabled_from(tc, r, ex, act, input, t));
            assert(step_from(tc, r, ex, act, input, t));
            let d = choose |d: nat| #[trigger] act.forward(input)(abs_at(tc, r, ex, t + d), abs_at(tc, r, ex, t + d + 1));
            assert(ex1.suffix(t).suffix(d).head() == abs_at(tc, r, ex, t + d));
            assert(ex1.suffix(t).suffix(d).head_next() == abs_at(tc, r, ex, t + d + 1));
            assert(lift_action(act.forward(input)).satisfied_by(ex1.suffix(t).suffix(d)));
        }
    }
}

pub proof fn lemma_wf_api_server<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, input1: Option<Message>)
    requires
        fair_sim(tc, r, ex),
        forall |side: S, input: Option<Message>| tc.sides.contains(side) ==> #[trigger] tc.api_server_next(side).weak_fairness(input).satisfied_by(ex),
    ensures tc.cluster.api_server_next().weak_fairness(input1).satisfied_by(alpha(tc, r, ex)),
{
    let act1 = tc.cluster.api_server_next();
    assert forall |t: nat| always_enabled_from(tc, r, ex, act1, input1, t) implies #[trigger] step_from(tc, r, ex, act1, input1, t) by {
        assert(act1.pre(input1)(abs_at(tc, r, ex, t + 0)));
        let m1 = input1->0;
        let s_t = state_at(ex, t);
        assert(abs_at(tc, r, ex, t + 0).in_flight().contains(m1));
        lemma_relabel_msgs_contains(tc, r, s_t.network.in_flight, m1);
        let m2 = choose |m2: Message| s_t.in_flight().contains(m2) && relabel_msg(tc, r, m2) == m1;
        let side = tc.side_of_msg(m2);
        let act2 = tc.api_server_next(side);
        assert(tc.sides.contains(side));
        assert forall |k: nat| abs_at(tc, r, ex, #[trigger] (t + k)).in_flight().contains(m1) by {
            assert(act1.pre(input1)(abs_at(tc, r, ex, t + k)));
        }
        assert forall |k: nat| #[trigger] act2.pre(Some(m2))(state_at(ex, t + k)) by {
            lemma_msg_stays(tc, r, ex, t, m1, m2, k);
            let s = state_at(ex, t + k);
            assert(act1.pre(input1)(abs_at(tc, r, ex, t + k)));
            lemma_api_pre_from_abs(tc, r, s, m2, uid_sum(tc, s), rv_sum(tc, s));
        }
        lemma_wf_apply(act2, Some(m2), ex, t);
        let d = choose |d: nat| #[trigger] act2.forward(Some(m2))(state_at(ex, t + d), state_at(ex, t + d + 1));
        lemma_api_forward_transfer(tc, r, ex, t + d, side, m2);
    }
    lemma_wf_from_steps(tc, r, ex, act1, input1);
}

proof fn lemma_controller_forward_transfer<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, i: nat, input: (int, Option<Message>, Option<ObjectRef>))
    requires
        fair_sim(tc, r, ex),
        tc.controller_next().forward(input)(state_at(ex, i), state_at(ex, i + 1)),
    ensures tc.cluster.controller_next().forward((input.0, relabel_opt_msg(tc, r, input.1), input.2))(abs_at(tc, r, ex, i), abs_at(tc, r, ex, i + 1)),
{
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    lemma_controller_step(tc, r, s, s_prime, input, uid_sum(tc, s), rv_sum(tc, s));
    assert(uid_sum(tc, s_prime) == uid_sum(tc, s));
    assert(rv_sum(tc, s_prime) == rv_sum(tc, s));
}

pub proof fn lemma_wf_controller<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, id: int, input1: (Option<Message>, Option<ObjectRef>))
    requires
        fair_sim(tc, r, ex),
        forall |msg: Option<Message>, key: Option<ObjectRef>| #[trigger] tc.controller_next().weak_fairness((id, msg, key)).satisfied_by(ex),
    ensures tc.cluster.controller_next().weak_fairness((id, input1.0, input1.1)).satisfied_by(alpha(tc, r, ex)),
{
    let act1 = tc.cluster.controller_next();
    let act2 = tc.controller_next();
    let i1 = (id, input1.0, input1.1);
    let key_o = input1.1;
    assert forall |t: nat| always_enabled_from(tc, r, ex, act1, i1, t) implies #[trigger] step_from(tc, r, ex, act1, i1, t) by {
        assert(act1.pre(i1)(abs_at(tc, r, ex, t + 0)));
        // The two-store message behind the input, if any.
        let msg2: Option<Message> = if input1.0 is Some {
            let m1 = input1.0->0;
            let s_t = state_at(ex, t);
            assert(abs_at(tc, r, ex, t + 0).in_flight().contains(m1));
            lemma_relabel_msgs_contains(tc, r, s_t.network.in_flight, m1);
            Some(choose |m2: Message| s_t.in_flight().contains(m2) && relabel_msg(tc, r, m2) == m1)
        } else {
            None
        };
        let i2 = (id, msg2, key_o);
        assert(relabel_opt_msg(tc, r, msg2) == input1.0);
        if input1.0 is Some {
            assert forall |k: nat| abs_at(tc, r, ex, #[trigger] (t + k)).in_flight().contains(input1.0->0) by {
                assert(act1.pre(i1)(abs_at(tc, r, ex, t + k)));
            }
        }
        assert forall |k: nat| #[trigger] act2.pre(i2)(state_at(ex, t + k)) by {
            let s = state_at(ex, t + k);
            assert(act1.pre(i1)(abs_at(tc, r, ex, t + k)));
            if input1.0 is Some {
                lemma_msg_stays(tc, r, ex, t, input1.0->0, msg2->0, k);
            }
            lemma_controller_pre_from_abs(tc, r, s, i2, uid_sum(tc, s), rv_sum(tc, s));
        }
        lemma_wf_apply(act2, i2, ex, t);
        let d = choose |d: nat| #[trigger] act2.forward(i2)(state_at(ex, t + d), state_at(ex, t + d + 1));
        lemma_controller_forward_transfer(tc, r, ex, t + d, i2);
    }
    lemma_wf_from_steps(tc, r, ex, act1, i1);
}

// The two-store controller action is enabled when the one-store one is enabled on
// the abstraction, once the message behind the input is in flight.
pub proof fn lemma_controller_pre_from_abs<S>(tc: MultiCluster<S>, r: Relabeling<S>, s: MultiClusterState<S>, input: (int, Option<Message>, Option<ObjectRef>), uid_next: Uid, rv_next: ResourceVersion)
    requires
        inv(tc, s),
        tc.cluster.controller_next().pre((input.0, relabel_opt_msg(tc, r, input.1), input.2))(abs(tc, r, s, uid_next, rv_next)),
        input.1 is Some ==> s.in_flight().contains(input.1->0),
    ensures tc.controller_next().pre(input)(s),
{
    let id = input.0;
    let msg = input.1;
    let key_o = input.2;
    let a = abs(tc, r, s, uid_next, rv_next);
    let model = tc.cluster.controller_models[id].reconcile_model;
    let sm = tc.cluster.controller(id);
    lemma_abs_controller(tc, r, s, id, uid_next, rv_next);
    let c = s.controller_and_externals[id].controller;
    let c1 = relabel_controller(tc, r, c);
    let in2 = ControllerActionInput { recv: msg, scheduled_cr_key: key_o, rpc_id_allocator: s.rpc_id_allocator };
    let in1 = relabel_controller_input(tc, r, in2);
    let st1 = choose |step: ControllerStep| (#[trigger] (sm.step_to_action)(step).precondition)((sm.action_input)(step, in1), c1);
    assert(((sm.step_to_action)(st1).precondition)(in1, c1));
    lemma_controller_action_pre_relabel(tc, r, model, id, in2, c, st1);
    assert(((sm.step_to_action)(st1).precondition)((sm.action_input)(st1, in2), c));
    assert(sm.next_result(in2, c) is Enabled);
}

pub proof fn lemma_wf_schedule<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, id: int, key: ObjectRef)
    requires
        fair_sim(tc, r, ex),
        forall |side: S, key: ObjectRef| tc.sides.contains(side) ==> #[trigger] tc.schedule_controller_reconcile(side).weak_fairness((id, key)).satisfied_by(ex),
    ensures tc.cluster.schedule_controller_reconcile().weak_fairness((id, key)).satisfied_by(alpha(tc, r, ex)),
{
    let act1 = tc.cluster.schedule_controller_reconcile();
    let i1 = (id, key);
    let side = tc.side_of_kind(key.kind);
    let act2 = tc.schedule_controller_reconcile(side);
    assert forall |t: nat| always_enabled_from(tc, r, ex, act1, i1, t) implies #[trigger] step_from(tc, r, ex, act1, i1, t) by {
        assert forall |k: nat| #[trigger] act2.pre(i1)(state_at(ex, t + k)) by {
            let s = state_at(ex, t + k);
            assert(act1.pre(i1)(abs_at(tc, r, ex, t + k)));
            lemma_abs_store_index(tc, r, s, key);
        }
        assert(tc.sides.contains(side));
        lemma_wf_apply(act2, i1, ex, t);
        let d = choose |d: nat| #[trigger] act2.forward(i1)(state_at(ex, t + d), state_at(ex, t + d + 1));
        let s = state_at(ex, t + d);
        let s_prime = state_at(ex, t + d + 1);
        lemma_schedule_step(tc, r, s, s_prime, side, i1, uid_sum(tc, s), rv_sum(tc, s));
        assert(uid_sum(tc, s_prime) == uid_sum(tc, s));
        assert(rv_sum(tc, s_prime) == rv_sum(tc, s));
        assert(act1.forward(i1)(abs_at(tc, r, ex, t + d), abs_at(tc, r, ex, t + d + 1)));
    }
    lemma_wf_from_steps(tc, r, ex, act1, i1);
}

// The garbage collector of the key's side is enabled when the one-store one is
// enabled on the abstraction.
pub proof fn lemma_builtin_pre_from_abs<S>(tc: MultiCluster<S>, r: Relabeling<S>, s: MultiClusterState<S>, input: (BuiltinControllerChoice, ObjectRef), uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        inv(tc, s),
        tc.cluster.builtin_controllers_next().pre(input)(abs(tc, r, s, uid_next, rv_next)),
    ensures tc.builtin_controllers_next(tc.side_of_kind(input.1.kind)).pre(input)(s),
{
    let key = input.1;
    let side = tc.side_of_kind(key.kind);
    let a = abs(tc, r, s, uid_next, rv_next);
    let store = s.store(side).resources;
    lemma_abs_store_index(tc, r, s, key);
    let obj = store[key];
    lemma_relabel_obj_keeps_identity(tc, r, obj);
    let refs = obj.metadata.owner_references->0;
    let refs1 = relabel_obj(tc, r, obj).metadata.owner_references->0;
    assert(refs1 == refs.map_values(|x: OwnerReferenceView| relabel_owner_ref(tc, r, x)));
    assert forall |i: int| 0 <= i < refs.len() implies ({
        let owner_key = owner_reference_to_object_reference(#[trigger] refs[i], key.namespace);
        ||| !store.contains_key(owner_key)
        ||| store[owner_key].metadata.uid != Some(refs[i].uid)
    }) by {
        let owner_key = owner_reference_to_object_reference(refs[i], key.namespace);
        assert(tc.side_of_kind(refs[i].kind) == side);
        assert(refs1[i] == relabel_owner_ref(tc, r, refs[i]));
        assert(owner_reference_to_object_reference(refs1[i], key.namespace) == owner_key);
        lemma_abs_store_index(tc, r, s, owner_key);
        if store.contains_key(owner_key) && store[owner_key].metadata.uid == Some(refs[i].uid) {
            assert(a.api_server.resources[owner_key].metadata.uid == Some(refs1[i].uid));
            assert(false);
        }
    }
}

pub proof fn lemma_wf_builtin<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, input1: (BuiltinControllerChoice, ObjectRef))
    requires
        fair_sim(tc, r, ex),
        forall |side: S, input: (BuiltinControllerChoice, ObjectRef)| tc.sides.contains(side) ==> #[trigger] tc.builtin_controllers_next(side).weak_fairness(input).satisfied_by(ex),
    ensures tc.cluster.builtin_controllers_next().weak_fairness(input1).satisfied_by(alpha(tc, r, ex)),
{
    let act1 = tc.cluster.builtin_controllers_next();
    let side = tc.side_of_kind(input1.1.kind);
    let act2 = tc.builtin_controllers_next(side);
    assert forall |t: nat| always_enabled_from(tc, r, ex, act1, input1, t) implies #[trigger] step_from(tc, r, ex, act1, input1, t) by {
        assert forall |k: nat| #[trigger] act2.pre(input1)(state_at(ex, t + k)) by {
            let s = state_at(ex, t + k);
            assert(act1.pre(input1)(abs_at(tc, r, ex, t + k)));
            lemma_builtin_pre_from_abs(tc, r, s, input1, uid_sum(tc, s), rv_sum(tc, s));
        }
        assert(tc.sides.contains(side));
        lemma_wf_apply(act2, input1, ex, t);
        let d = choose |d: nat| #[trigger] act2.forward(input1)(state_at(ex, t + d), state_at(ex, t + d + 1));
        let s = state_at(ex, t + d);
        let s_prime = state_at(ex, t + d + 1);
        lemma_builtin_step(tc, r, s, s_prime, side, input1, uid_sum(tc, s), rv_sum(tc, s));
        assert(uid_sum(tc, s_prime) == uid_sum(tc, s));
        assert(rv_sum(tc, s_prime) == rv_sum(tc, s));
        assert(act1.forward(input1)(abs_at(tc, r, ex, t + d), abs_at(tc, r, ex, t + d + 1)));
    }
    lemma_wf_from_steps(tc, r, ex, act1, input1);
}

pub proof fn lemma_wf_disable_crash<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, id: int)
    requires
        fair_sim(tc, r, ex),
        forall |input: int| #[trigger] tc.disable_crash().weak_fairness(input).satisfied_by(ex),
    ensures tc.cluster.disable_crash().weak_fairness(id).satisfied_by(alpha(tc, r, ex)),
{
    let act1 = tc.cluster.disable_crash();
    let act2 = tc.disable_crash();
    assert forall |t: nat| always_enabled_from(tc, r, ex, act1, id, t) implies #[trigger] step_from(tc, r, ex, act1, id, t) by {
        assert forall |k: nat| #[trigger] act2.pre(id)(state_at(ex, t + k)) by {
            assert(act1.pre(id)(abs_at(tc, r, ex, t + k)));
        }
        lemma_wf_apply(act2, id, ex, t);
        let d = choose |d: nat| #[trigger] act2.forward(id)(state_at(ex, t + d), state_at(ex, t + d + 1));
        let s = state_at(ex, t + d);
        let s_prime = state_at(ex, t + d + 1);
        lemma_disable_crash_step(tc, r, s, s_prime, id, uid_sum(tc, s), rv_sum(tc, s));
        assert(act1.forward(id)(abs_at(tc, r, ex, t + d), abs_at(tc, r, ex, t + d + 1)));
    }
    lemma_wf_from_steps(tc, r, ex, act1, id);
}

pub proof fn lemma_wf_disable_req_drop<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>)
    requires
        fair_sim(tc, r, ex),
        tc.disable_req_drop().weak_fairness(()).satisfied_by(ex),
    ensures tc.cluster.disable_req_drop().weak_fairness(()).satisfied_by(alpha(tc, r, ex)),
{
    let act1 = tc.cluster.disable_req_drop();
    let act2 = tc.disable_req_drop();
    assert forall |t: nat| always_enabled_from(tc, r, ex, act1, (), t) implies #[trigger] step_from(tc, r, ex, act1, (), t) by {
        assert forall |k: nat| #[trigger] act2.pre(())(state_at(ex, t + k)) by {}
        lemma_wf_apply(act2, (), ex, t);
        let d = choose |d: nat| #[trigger] act2.forward(())(state_at(ex, t + d), state_at(ex, t + d + 1));
        let s = state_at(ex, t + d);
        let s_prime = state_at(ex, t + d + 1);
        lemma_disable_req_drop_step(tc, r, s, s_prime, uid_sum(tc, s), rv_sum(tc, s));
        assert(act1.forward(())(abs_at(tc, r, ex, t + d), abs_at(tc, r, ex, t + d + 1)));
    }
    lemma_wf_from_steps(tc, r, ex, act1, ());
}

pub proof fn lemma_wf_disable_pod_monkey<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>)
    requires
        fair_sim(tc, r, ex),
        tc.disable_pod_monkey().weak_fairness(()).satisfied_by(ex),
    ensures tc.cluster.disable_pod_monkey().weak_fairness(()).satisfied_by(alpha(tc, r, ex)),
{
    let act1 = tc.cluster.disable_pod_monkey();
    let act2 = tc.disable_pod_monkey();
    assert forall |t: nat| always_enabled_from(tc, r, ex, act1, (), t) implies #[trigger] step_from(tc, r, ex, act1, (), t) by {
        assert forall |k: nat| #[trigger] act2.pre(())(state_at(ex, t + k)) by {}
        lemma_wf_apply(act2, (), ex, t);
        let d = choose |d: nat| #[trigger] act2.forward(())(state_at(ex, t + d), state_at(ex, t + d + 1));
        let s = state_at(ex, t + d);
        let s_prime = state_at(ex, t + d + 1);
        lemma_disable_pod_monkey_step(tc, r, s, s_prime, uid_sum(tc, s), rv_sum(tc, s));
        assert(act1.forward(())(abs_at(tc, r, ex, t + d), abs_at(tc, r, ex, t + d + 1)));
    }
    lemma_wf_from_steps(tc, r, ex, act1, ());
}

// No controller has an external system, so the external action is never enabled
// and its fairness holds vacuously.
pub proof fn lemma_wf_external<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, id: int, input1: Option<Message>)
    requires fair_sim(tc, r, ex),
    ensures tc.cluster.external_next().weak_fairness((id, input1)).satisfied_by(alpha(tc, r, ex)),
{
    let act1 = tc.cluster.external_next();
    let i1 = (id, input1);
    assert forall |t: nat| always_enabled_from(tc, r, ex, act1, i1, t) implies #[trigger] step_from(tc, r, ex, act1, i1, t) by {
        assert(act1.pre(i1)(abs_at(tc, r, ex, t + 0)));
        assert(tc.cluster.controller_models.contains_key(id));
        assert(false);
    }
    lemma_wf_from_steps(tc, r, ex, act1, i1);
}

}
