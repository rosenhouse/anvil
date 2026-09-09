// From an execution of the multi-store model to an execution of the one-store
// model. The relabeling is read off the execution: the k-th value a store's
// counter allocates relabels to the number of values all stores had allocated
// by then, so that the one-store counters count every allocation once. Values a
// counter never allocates relabel to distinct negative numbers.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::multi_cluster::{api_server::*, finite::*, relabel::*, steps::*};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, api_server::types::*, cluster::*, controller::state_machine::*,
    controller::types::*, external::state_machine::*, message::*, network::types::*, multi_cluster::*,
};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::vstd_ext::string_view::*;
use verus_temporal_logic::defs::*;
use vstd::{arithmetic::div_mod::*, arithmetic::mul::*, map_lib::*, multiset::*, prelude::*};

verus! {

// ---------------------------------------------------------------------------
// The relabeling of an execution.
// ---------------------------------------------------------------------------

pub open spec fn state_at<S>(ex: Execution<MultiClusterState<S>>, i: nat) -> MultiClusterState<S> {
    (ex.nat_to_state)(i)
}

pub open spec fn uid_at<S>(ex: Execution<MultiClusterState<S>>, side: S, i: nat) -> int {
    state_at(ex, i).store(side).uid_counter
}

pub open spec fn rv_at<S>(ex: Execution<MultiClusterState<S>>, side: S, i: nat) -> int {
    state_at(ex, i).store(side).resource_version_counter
}

// The step at which the uid counter of `side` goes from k to k + 1.
pub open spec fn uid_alloc_at<S>(ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat) -> bool {
    uid_at(ex, side, i) == k && uid_at(ex, side, i + 1) == k + 1
}

pub open spec fn rv_alloc_at<S>(ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat) -> bool {
    rv_at(ex, side, i) == k && rv_at(ex, side, i + 1) == k + 1
}

// An injection of the integers into the naturals.
pub open spec fn int_code(k: int) -> int {
    if k >= 0 { 2 * k } else { -2 * k - 1 }
}

// A negative value, distinct for every side of the cluster and every k: the
// sides are numbered by their rank in the (finite) set of sides.
pub open spec fn unused_value<S>(tc: MultiCluster<S>, side: S, k: int) -> int {
    -(int_code(k) * tc.sides.len() + rank(tc.sides, side) + 1)
}

#[verifier::opaque]
pub open spec fn uid_value<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int) -> int {
    if exists |i: nat| uid_alloc_at(ex, side, k, i) {
        uid_sum(tc, state_at(ex, choose |i: nat| uid_alloc_at(ex, side, k, i)))
    } else {
        unused_value(tc, side, k)
    }
}

#[verifier::opaque]
pub open spec fn rv_value<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int) -> int {
    if exists |i: nat| rv_alloc_at(ex, side, k, i) {
        rv_sum(tc, state_at(ex, choose |i: nat| rv_alloc_at(ex, side, k, i)))
    } else {
        unused_value(tc, side, k)
    }
}

pub open spec fn uid_map<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>) -> spec_fn(S, Uid) -> Uid {
    |side: S, k: Uid| uid_value(tc, ex, side, k)
}

pub open spec fn rv_map<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>) -> spec_fn(S, ResourceVersion) -> ResourceVersion {
    |side: S, k: ResourceVersion| rv_value(tc, ex, side, k)
}

// How annotation values follow the counter maps; instantiated per controller.
pub type Hook<S> = spec_fn(spec_fn(S, Uid) -> Uid, spec_fn(S, ResourceVersion) -> ResourceVersion) -> spec_fn(Kind, StringView, StringView) -> StringView;

pub open spec fn hook_injective<S>(tc: MultiCluster<S>, hook: Hook<S>) -> bool {
    forall |u: spec_fn(S, Uid) -> Uid, v: spec_fn(S, ResourceVersion) -> ResourceVersion|
        uid_map_injective(tc.sides, u) && rv_map_injective(tc.sides, v) ==> annotation_injective(#[trigger] hook(u, v))
}

pub open spec fn relabeling_of<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, hook: Hook<S>) -> Relabeling<S> {
    Relabeling { uid: uid_map(tc, ex), rv: rv_map(tc, ex), annotation: hook(uid_map(tc, ex), rv_map(tc, ex)) }
}

// The one-store execution.
pub open spec fn alpha<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>) -> Execution<ClusterState> {
    Execution {
        nat_to_state: |i: nat| abs(tc, r, state_at(ex, i), uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i))),
    }
}

pub open spec fn abs_at<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, i: nat) -> ClusterState {
    abs(tc, r, state_at(ex, i), uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i)))
}

// An execution of the multi-store model.
pub open spec fn multi_cluster_run<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>) -> bool {
    &&& tc.init()(state_at(ex, 0))
    &&& forall |i: nat| tc.next()(#[trigger] state_at(ex, i), state_at(ex, i + 1))
}

// The hypotheses on a multi-store cluster and its controllers.
pub open spec fn refinement_hyps<S>(tc: MultiCluster<S>, hook: Hook<S>) -> bool {
    &&& tc.wf()
    &&& models_ok(tc)
    &&& installed_types_ignore_metadata(tc.cluster.installed_types)
    &&& installed_types_coherent(tc.cluster.installed_types)
    &&& hook_injective(tc, hook)
    &&& forall |r: Relabeling<S>| injective(tc, r) && r.annotation == hook(r.uid, r.rv) ==> #[trigger] models_commute(tc, r)
}

// What the simulation of an execution establishes.
pub open spec fn simulation<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>) -> bool {
    &&& tc.wf()
    &&& relabel_hyps(tc, r)
    &&& models_ok(tc)
    &&& models_commute(tc, r)
    &&& forall |i: nat| inv(tc, #[trigger] state_at(ex, i))
    &&& forall |i: nat| tc.next()(#[trigger] state_at(ex, i), state_at(ex, i + 1))
    &&& forall |i: nat| step_compatible(tc, r, #[trigger] state_at(ex, i), state_at(ex, i + 1), uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i)))
}

// ---------------------------------------------------------------------------
// Initial states.
// ---------------------------------------------------------------------------

pub proof fn lemma_init_abs<S>(tc: MultiCluster<S>, r: Relabeling<S>, s: MultiClusterState<S>)
    requires
        tc.wf(),
        models_ok(tc),
        tc.init()(s),
    ensures
        tc.cluster.init()(abs(tc, r, s, 0, 0)),
        inv(tc, s),
        uid_sum(tc, s) == 0,
        rv_sum(tc, s) == 0,
{
    let a = abs(tc, r, s, 0, 0);
    let cluster = tc.cluster;
    assert(stores_keyed(tc, s));
    assert forall |k: ObjectRef| !a.api_server.resources.contains_key(k) by {
        lemma_abs_store_index_keyed(tc, r, s, k);
    }
    assert(a.api_server.resources =~= Map::<ObjectRef, DynamicObjectView>::empty());
    lemma_set_sum_pointwise_eq(tc.sides, |side: S| s.store(side).uid_counter, |side: S| 0);
    lemma_set_sum_pointwise_eq(tc.sides, |side: S| s.store(side).resource_version_counter, |side: S| 0);
    lemma_set_sum_zero(tc.sides);
    lemma_relabel_msgs_empty(tc, r);
    assert forall |key: int| #[trigger] cluster.controller_models.contains_key(key) implies {
        let model = cluster.controller_models[key];
        &&& a.controller_and_externals.contains_key(key)
        &&& (controller(model.reconcile_model, key).init)(a.controller_and_externals[key].controller)
        &&& a.controller_and_externals[key].crash_enabled
        &&& model.external_model is Some ==> {
            &&& a.controller_and_externals[key].external is Some
            &&& (external(model.external_model->0).init)(a.controller_and_externals[key].external->0)
        }
    } by {
        let c = s.controller_and_externals[key].controller;
        lemma_map_values_empty::<ObjectRef, OngoingReconcile, OngoingReconcile>(|o: OngoingReconcile| relabel_ongoing(tc, r, o));
        lemma_map_values_empty::<ObjectRef, DynamicObjectView, DynamicObjectView>(|o: DynamicObjectView| relabel_obj(tc, r, o));
        assert(relabel_controller(tc, r, c) == c);
        assert(a.controller_and_externals[key] == relabel_cae(tc, r, s.controller_and_externals[key]));
    }
    assert(cluster.init()(a));
    assert forall |m: Message| #[trigger] s.in_flight().contains(m) && m.content is APIRequest implies tc.request_ok(m.content->APIRequest_0) by {
        assert(s.in_flight().count(m) == 0);
    }
    assert forall |id: int| #[trigger] cluster.controller_models.contains_key(id) implies controller_crs_ok(tc, s.controller_and_externals[id].controller) by {
        let c = s.controller_and_externals[id].controller;
        assert(c.scheduled_reconciles == Map::<ObjectRef, DynamicObjectView>::empty());
        assert(c.ongoing_reconciles == Map::<ObjectRef, OngoingReconcile>::empty());
    }
}

// ---------------------------------------------------------------------------
// Invariants along an execution, without a relabeling.
// ---------------------------------------------------------------------------

// A relabeling that only keeps the sides apart.
pub open spec fn split_relabeling<S>(tc: MultiCluster<S>) -> Relabeling<S> {
    Relabeling {
        uid: |side: S, k: Uid| unused_value(tc, side, k),
        rv: |side: S, k: ResourceVersion| unused_value(tc, side, k),
        annotation: |kind: Kind, key: StringView, v: StringView| v,
    }
}

pub proof fn lemma_split_relabeling_injective<S>(tc: MultiCluster<S>)
    requires tc.wf(),
    ensures injective(tc, split_relabeling(tc)),
{
    let r = split_relabeling(tc);
    assert forall |side_a: S, a: Uid, side_b: S, b: Uid|
        tc.sides.contains(side_a) && tc.sides.contains(side_b) && #[trigger] (r.uid)(side_a, a) == #[trigger] (r.uid)(side_b, b)
        implies side_a == side_b && a == b by {
        lemma_unused_value_injective(tc, side_a, a, side_b, b);
    }
    assert forall |side_a: S, a: ResourceVersion, side_b: S, b: ResourceVersion|
        tc.sides.contains(side_a) && tc.sides.contains(side_b) && #[trigger] (r.rv)(side_a, a) == #[trigger] (r.rv)(side_b, b)
        implies side_a == side_b && a == b by {
        lemma_unused_value_injective(tc, side_a, a, side_b, b);
    }
}

// The controller step keeps the invariants; unlike the simulation this needs no
// commutation of the reconciler.
proof fn lemma_controller_step_keeps_inv<S>(tc: MultiCluster<S>, s: MultiClusterState<S>, s_prime: MultiClusterState<S>, input: (int, Option<Message>, Option<ObjectRef>))
    requires
        tc.wf(),
        models_ok(tc),
        inv(tc, s),
        tc.controller_next().forward(input)(s, s_prime),
    ensures
        inv(tc, s_prime),
        s_prime.stores == s.stores,
{
    assert(s_prime.stores =~= s.stores);
    let id = input.0;
    let msg = input.1;
    let key_o = input.2;
    let key = key_o->0;
    let model = tc.cluster.controller_models[id].reconcile_model;
    let sm = tc.cluster.controller(id);
    let c = s.controller_and_externals[id].controller;
    let in2 = ControllerActionInput { recv: msg, scheduled_cr_key: key_o, rpc_id_allocator: s.rpc_id_allocator };
    let st = choose |step: ControllerStep| (#[trigger] (sm.step_to_action)(step).precondition)((sm.action_input)(step, in2), c);
    let host = sm.next_result(in2, c);
    let sent = host->Enabled_1.send;
    assert(controller_crs_ok(tc, c));
    assert(controller_crs_ok(tc, host->Enabled_0)) by {
        match st {
            ControllerStep::RunScheduledReconcile => {},
            ControllerStep::ContinueReconcile => {},
            ControllerStep::EndReconcile => {},
        }
    }
    assert forall |i: int| #[trigger] tc.cluster.controller_models.contains_key(i) implies controller_crs_ok(tc, s_prime.controller_and_externals[i].controller) by {
        if i != id { assert(s_prime.controller_and_externals[i] == s.controller_and_externals[i]); }
    }
    assert forall |m: Message| #[trigger] s_prime.in_flight().contains(m) && m.content is APIRequest implies tc.request_ok(m.content->APIRequest_0) by {
        if !s.in_flight().contains(m) {
            assert(sent.contains(m));
            match st {
                ControllerStep::RunScheduledReconcile => { assert(false); },
                ControllerStep::ContinueReconcile => {
                    let rs = c.ongoing_reconciles[key];
                    let resp_o = if msg is Some {
                        if msg->0.content is APIResponse { Some(ResponseContent::KubernetesResponse(msg->0.content->APIResponse_0)) }
                        else { Some(ResponseContent::ExternalResponse(msg->0.content->ExternalResponse_0)) }
                    } else { None };
                    let (ls, req_o) = (model.transition)(rs.triggering_cr, resp_o, rs.local_state);
                    assert(req_o is Some);
                    match req_o->0 {
                        RequestContent::KubernetesRequest(req) => {
                            assert(m == controller_req_msg(id, key, s.rpc_id_allocator.allocate().1, req));
                            assert(tc.request_ok(req));
                        },
                        RequestContent::ExternalRequest(req) => {
                            assert(m == controller_external_req_msg(id, key, s.rpc_id_allocator.allocate().1, req));
                            assert(false);
                        },
                    }
                },
                ControllerStep::EndReconcile => { assert(false); },
            }
        }
    }
}

pub proof fn lemma_next_step_keeps_inv<S>(tc: MultiCluster<S>, s: MultiClusterState<S>, s_prime: MultiClusterState<S>, side: S, step: Step)
    requires
        tc.wf(),
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        inv(tc, s),
        tc.next_step(s, s_prime, side, step),
    ensures
        inv(tc, s_prime),
        counters_step(tc, s, s_prime),
{
    let r = split_relabeling(tc);
    lemma_split_relabeling_injective(tc);
    match step {
        Step::APIServerStep(input) => {
            let uid_next = (r.uid)(side, s.store(side).uid_counter);
            let rv_next = (r.rv)(side, s.store(side).resource_version_counter);
            assert(step_compatible(tc, r, s, s_prime, uid_next, rv_next)) by {
                reveal(step_compatible);
                assert forall |x: S| #[trigger] tc.sides.contains(x) implies alloc_compatible(tc, r, s, x, s_prime.store(x), uid_next, rv_next) by {
                    if x != side { assert(s_prime.store(x) == s.store(x)); }
                }
            }
            lemma_api_server_step(tc, r, s, s_prime, side, input, uid_next, rv_next);
        },
        Step::BuiltinControllersStep(input) => { lemma_builtin_step(tc, r, s, s_prime, side, input, 0, 0); },
        Step::ControllerStep(input) => { lemma_controller_step_keeps_inv(tc, s, s_prime, input); },
        Step::ScheduleControllerReconcileStep(input) => { lemma_schedule_step(tc, r, s, s_prime, side, input, 0, 0); },
        Step::RestartControllerStep(input) => { lemma_restart_step(tc, r, s, s_prime, input, 0, 0); },
        Step::DisableCrashStep(input) => { lemma_disable_crash_step(tc, r, s, s_prime, input, 0, 0); },
        Step::DropReqStep(input) => { lemma_drop_req_step(tc, r, s, s_prime, input, 0, 0); },
        Step::DisableReqDropStep => { lemma_disable_req_drop_step(tc, r, s, s_prime, 0, 0); },
        Step::PodMonkeyStep(input) => { lemma_pod_monkey_step(tc, r, s, s_prime, input, 0, 0); },
        Step::DisablePodMonkeyStep => { lemma_disable_pod_monkey_step(tc, r, s, s_prime, 0, 0); },
        Step::ExternalStep(input) => {
            assert(tc.cluster.controller_models.contains_key(input.0));
            assert(false);
        },
        Step::StutterStep => { lemma_stutter_step(tc, r, s, s_prime, 0, 0); },
    }
}

proof fn lemma_next_keeps_inv<S>(tc: MultiCluster<S>, s: MultiClusterState<S>, s_prime: MultiClusterState<S>)
    requires
        tc.wf(),
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        inv(tc, s),
        tc.next()(s, s_prime),
    ensures
        inv(tc, s_prime),
        counters_step(tc, s, s_prime),
{
    let (side, step) = choose |side: S, step: Step| tc.next_step(s, s_prime, side, step);
    lemma_next_step_keeps_inv(tc, s, s_prime, side, step);
}

proof fn lemma_init_inv<S>(tc: MultiCluster<S>, s: MultiClusterState<S>)
    requires
        tc.wf(),
        models_ok(tc),
        tc.init()(s),
    ensures inv(tc, s),
{
    lemma_init_abs(tc, split_relabeling(tc), s);
}

pub proof fn lemma_inv_at<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, i: nat)
    requires
        tc.wf(),
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        multi_cluster_run(tc, ex),
    ensures inv(tc, state_at(ex, i)),
    decreases i,
{
    if i == 0 {
        lemma_init_inv(tc, state_at(ex, 0));
    } else {
        let j = (i - 1) as nat;
        lemma_inv_at(tc, ex, j);
        assert(tc.next()(state_at(ex, j), state_at(ex, j + 1)));
        lemma_next_keeps_inv(tc, state_at(ex, j), state_at(ex, j + 1));
    }
}

pub proof fn lemma_counters_step_at<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, i: nat)
    requires
        tc.wf(),
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        multi_cluster_run(tc, ex),
    ensures counters_step(tc, state_at(ex, i), state_at(ex, i + 1)),
{
    lemma_inv_at(tc, ex, i);
    lemma_next_keeps_inv(tc, state_at(ex, i), state_at(ex, i + 1));
}

// ---------------------------------------------------------------------------
// Counters along an execution.
// ---------------------------------------------------------------------------

// The hypotheses of every lemma about an execution below.
pub open spec fn run_hyps<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>) -> bool {
    &&& tc.wf()
    &&& models_ok(tc)
    &&& installed_types_ignore_metadata(tc.cluster.installed_types)
    &&& installed_types_coherent(tc.cluster.installed_types)
    &&& multi_cluster_run(tc, ex)
}

proof fn lemma_counters_one_step<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, k: nat)
    requires run_hyps(tc, ex),
    ensures
        forall |side: S| #[trigger] tc.sides.contains(side) ==> uid_at(ex, side, k) <= uid_at(ex, side, k + 1) && rv_at(ex, side, k) <= rv_at(ex, side, k + 1),
        uid_sum(tc, state_at(ex, k)) <= uid_sum(tc, state_at(ex, k + 1)),
        rv_sum(tc, state_at(ex, k)) <= rv_sum(tc, state_at(ex, k + 1)),
{
    lemma_counters_step_at(tc, ex, k);
    let s = state_at(ex, k);
    let s_prime = state_at(ex, k + 1);
    lemma_set_sum_pointwise_le(tc.sides, |side: S| s.store(side).uid_counter, |side: S| s_prime.store(side).uid_counter);
    lemma_set_sum_pointwise_le(tc.sides, |side: S| s.store(side).resource_version_counter, |side: S| s_prime.store(side).resource_version_counter);
}

pub proof fn lemma_counters_mono<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, i: nat, j: nat)
    requires
        run_hyps(tc, ex),
        i <= j,
    ensures
        forall |side: S| #[trigger] tc.sides.contains(side) ==> uid_at(ex, side, i) <= uid_at(ex, side, j) && rv_at(ex, side, i) <= rv_at(ex, side, j),
        uid_sum(tc, state_at(ex, i)) <= uid_sum(tc, state_at(ex, j)),
        rv_sum(tc, state_at(ex, i)) <= rv_sum(tc, state_at(ex, j)),
    decreases j - i,
{
    if i < j {
        let k = (j - 1) as nat;
        lemma_counters_mono(tc, ex, i, k);
        lemma_counters_one_step(tc, ex, k);
        assert(k + 1 == j);
    }
}

pub proof fn lemma_counters_nonneg<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, i: nat)
    requires run_hyps(tc, ex),
    ensures
        uid_sum(tc, state_at(ex, i)) >= 0,
        rv_sum(tc, state_at(ex, i)) >= 0,
{
    lemma_counters_mono(tc, ex, 0, i);
    lemma_init_abs(tc, split_relabeling(tc), state_at(ex, 0));
}

// A counter goes from k to k + 1 at most once.
pub proof fn lemma_uid_alloc_unique<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat, j: nat)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side),
        uid_alloc_at(ex, side, k, i),
        uid_alloc_at(ex, side, k, j),
    ensures i == j,
{
    if i < j {
        lemma_counters_mono(tc, ex, i + 1, j);
    } else if j < i {
        lemma_counters_mono(tc, ex, j + 1, i);
    }
}

pub proof fn lemma_rv_alloc_unique<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat, j: nat)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side),
        rv_alloc_at(ex, side, k, i),
        rv_alloc_at(ex, side, k, j),
    ensures i == j,
{
    if i < j {
        lemma_counters_mono(tc, ex, i + 1, j);
    } else if j < i {
        lemma_counters_mono(tc, ex, j + 1, i);
    }
}

// An allocation on `side` at step i moves the sum by exactly one: no other
// store moves at that step.
proof fn lemma_uid_sum_alloc_step<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side),
        uid_alloc_at(ex, side, k, i),
    ensures uid_sum(tc, state_at(ex, i + 1)) == uid_sum(tc, state_at(ex, i)) + 1,
{
    lemma_counters_step_at(tc, ex, i);
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    assert(s_prime.store(side) != s.store(side));
    assert(stores_agree_except(tc, s, s_prime, side));
    lemma_set_sum_diff_at(tc.sides, |x: S| s.store(x).uid_counter, |x: S| s_prime.store(x).uid_counter, side);
}

proof fn lemma_rv_sum_alloc_step<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side),
        rv_alloc_at(ex, side, k, i),
    ensures rv_sum(tc, state_at(ex, i + 1)) == rv_sum(tc, state_at(ex, i)) + 1,
{
    lemma_counters_step_at(tc, ex, i);
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    assert(s_prime.store(side) != s.store(side));
    assert(stores_agree_except(tc, s, s_prime, side));
    lemma_set_sum_diff_at(tc.sides, |x: S| s.store(x).resource_version_counter, |x: S| s_prime.store(x).resource_version_counter, side);
}

// After an allocation the sum has grown by one, and never shrinks.
pub proof fn lemma_uid_sum_after_alloc<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat, j: nat)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side),
        uid_alloc_at(ex, side, k, i),
        i < j,
    ensures uid_sum(tc, state_at(ex, i)) + 1 <= uid_sum(tc, state_at(ex, j)),
{
    lemma_uid_sum_alloc_step(tc, ex, side, k, i);
    lemma_counters_mono(tc, ex, i + 1, j);
}

pub proof fn lemma_rv_sum_after_alloc<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat, j: nat)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side),
        rv_alloc_at(ex, side, k, i),
        i < j,
    ensures rv_sum(tc, state_at(ex, i)) + 1 <= rv_sum(tc, state_at(ex, j)),
{
    lemma_rv_sum_alloc_step(tc, ex, side, k, i);
    lemma_counters_mono(tc, ex, i + 1, j);
}

// ---------------------------------------------------------------------------
// The relabeling of an execution is injective and compatible with its steps.
// ---------------------------------------------------------------------------

proof fn lemma_unused_value_negative<S>(tc: MultiCluster<S>, side: S, k: int)
    requires
        tc.wf(),
        tc.sides.contains(side),
    ensures unused_value(tc, side, k) < 0,
{
    lemma_rank_bounds(tc.sides, side);
    lemma_mul_nonnegative(int_code(k), tc.sides.len() as int);
}

proof fn lemma_unused_value_injective<S>(tc: MultiCluster<S>, side_a: S, a: int, side_b: S, b: int)
    requires
        tc.wf(),
        tc.sides.contains(side_a),
        tc.sides.contains(side_b),
        unused_value(tc, side_a, a) == unused_value(tc, side_b, b),
    ensures side_a == side_b && a == b,
{
    let n = tc.sides.len() as int;
    lemma_rank_bounds(tc.sides, side_a);
    lemma_rank_bounds(tc.sides, side_b);
    let x = int_code(a) * n + rank(tc.sides, side_a);
    assert(x == int_code(b) * n + rank(tc.sides, side_b));
    lemma_fundamental_div_mod_converse(x, n, int_code(a), rank(tc.sides, side_a));
    lemma_fundamental_div_mod_converse(x, n, int_code(b), rank(tc.sides, side_b));
    lemma_rank_injective(tc.sides, side_a, side_b);
}

pub proof fn lemma_uid_value_alloc<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side),
        uid_alloc_at(ex, side, k, i),
    ensures uid_value(tc, ex, side, k) == uid_sum(tc, state_at(ex, i)),
{
    reveal(uid_value);
    let j = choose |j: nat| uid_alloc_at(ex, side, k, j);
    lemma_uid_alloc_unique(tc, ex, side, k, i, j);
}

pub proof fn lemma_rv_value_alloc<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int, i: nat)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side),
        rv_alloc_at(ex, side, k, i),
    ensures rv_value(tc, ex, side, k) == rv_sum(tc, state_at(ex, i)),
{
    reveal(rv_value);
    let j = choose |j: nat| rv_alloc_at(ex, side, k, j);
    lemma_rv_alloc_unique(tc, ex, side, k, i, j);
}

proof fn lemma_uid_value_unused<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int)
    requires !(exists |i: nat| uid_alloc_at(ex, side, k, i)),
    ensures uid_value(tc, ex, side, k) == unused_value(tc, side, k),
{
    reveal(uid_value);
}

proof fn lemma_rv_value_unused<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side: S, k: int)
    requires !(exists |i: nat| rv_alloc_at(ex, side, k, i)),
    ensures rv_value(tc, ex, side, k) == unused_value(tc, side, k),
{
    reveal(rv_value);
}

// Two different (side, k) pairs relabel to different values.
proof fn lemma_uid_values_distinct<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side_a: S, a: Uid, side_b: S, b: Uid)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side_a),
        tc.sides.contains(side_b),
        uid_value(tc, ex, side_a, a) == uid_value(tc, ex, side_b, b),
    ensures side_a == side_b && a == b,
{
    if exists |i: nat| uid_alloc_at(ex, side_a, a, i) {
        let i = choose |i: nat| uid_alloc_at(ex, side_a, a, i);
        lemma_uid_value_alloc(tc, ex, side_a, a, i);
        lemma_counters_nonneg(tc, ex, i);
        if exists |j: nat| uid_alloc_at(ex, side_b, b, j) {
            let j = choose |j: nat| uid_alloc_at(ex, side_b, b, j);
            lemma_uid_value_alloc(tc, ex, side_b, b, j);
            if i < j {
                lemma_uid_sum_after_alloc(tc, ex, side_a, a, i, j);
            } else if j < i {
                lemma_uid_sum_after_alloc(tc, ex, side_b, b, j, i);
            } else {
                // The same step allocates on one side only.
                lemma_counters_step_at(tc, ex, i);
                let s = state_at(ex, i);
                let s_prime = state_at(ex, i + 1);
                assert(s_prime.store(side_a) != s.store(side_a));
                assert(stores_agree_except(tc, s, s_prime, side_a));
                assert(s_prime.store(side_b) != s.store(side_b));
            }
        } else {
            lemma_uid_value_unused(tc, ex, side_b, b);
            lemma_unused_value_negative(tc, side_b, b);
        }
    } else {
        lemma_uid_value_unused(tc, ex, side_a, a);
        lemma_unused_value_negative(tc, side_a, a);
        if exists |j: nat| uid_alloc_at(ex, side_b, b, j) {
            let j = choose |j: nat| uid_alloc_at(ex, side_b, b, j);
            lemma_uid_value_alloc(tc, ex, side_b, b, j);
            lemma_counters_nonneg(tc, ex, j);
        } else {
            lemma_uid_value_unused(tc, ex, side_b, b);
            lemma_unused_value_injective(tc, side_a, a, side_b, b);
        }
    }
}

proof fn lemma_rv_values_distinct<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, side_a: S, a: ResourceVersion, side_b: S, b: ResourceVersion)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side_a),
        tc.sides.contains(side_b),
        rv_value(tc, ex, side_a, a) == rv_value(tc, ex, side_b, b),
    ensures side_a == side_b && a == b,
{
    if exists |i: nat| rv_alloc_at(ex, side_a, a, i) {
        let i = choose |i: nat| rv_alloc_at(ex, side_a, a, i);
        lemma_rv_value_alloc(tc, ex, side_a, a, i);
        lemma_counters_nonneg(tc, ex, i);
        if exists |j: nat| rv_alloc_at(ex, side_b, b, j) {
            let j = choose |j: nat| rv_alloc_at(ex, side_b, b, j);
            lemma_rv_value_alloc(tc, ex, side_b, b, j);
            if i < j {
                lemma_rv_sum_after_alloc(tc, ex, side_a, a, i, j);
            } else if j < i {
                lemma_rv_sum_after_alloc(tc, ex, side_b, b, j, i);
            } else {
                lemma_counters_step_at(tc, ex, i);
                let s = state_at(ex, i);
                let s_prime = state_at(ex, i + 1);
                assert(s_prime.store(side_a) != s.store(side_a));
                assert(stores_agree_except(tc, s, s_prime, side_a));
                assert(s_prime.store(side_b) != s.store(side_b));
            }
        } else {
            lemma_rv_value_unused(tc, ex, side_b, b);
            lemma_unused_value_negative(tc, side_b, b);
        }
    } else {
        lemma_rv_value_unused(tc, ex, side_a, a);
        lemma_unused_value_negative(tc, side_a, a);
        if exists |j: nat| rv_alloc_at(ex, side_b, b, j) {
            let j = choose |j: nat| rv_alloc_at(ex, side_b, b, j);
            lemma_rv_value_alloc(tc, ex, side_b, b, j);
            lemma_counters_nonneg(tc, ex, j);
        } else {
            lemma_rv_value_unused(tc, ex, side_b, b);
            lemma_unused_value_injective(tc, side_a, a, side_b, b);
        }
    }
}

pub proof fn lemma_uid_map_injective<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>)
    requires run_hyps(tc, ex),
    ensures uid_map_injective(tc.sides, uid_map(tc, ex)),
{
    let u = uid_map(tc, ex);
    assert forall |side_a: S, a: Uid, side_b: S, b: Uid|
        tc.sides.contains(side_a) && tc.sides.contains(side_b) && #[trigger] u(side_a, a) == #[trigger] u(side_b, b)
        implies side_a == side_b && a == b by {
        lemma_uid_values_distinct(tc, ex, side_a, a, side_b, b);
    }
}

pub proof fn lemma_rv_map_injective<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>)
    requires run_hyps(tc, ex),
    ensures rv_map_injective(tc.sides, rv_map(tc, ex)),
{
    let v = rv_map(tc, ex);
    assert forall |side_a: S, a: ResourceVersion, side_b: S, b: ResourceVersion|
        tc.sides.contains(side_a) && tc.sides.contains(side_b) && #[trigger] v(side_a, a) == #[trigger] v(side_b, b)
        implies side_a == side_b && a == b by {
        lemma_rv_values_distinct(tc, ex, side_a, a, side_b, b);
    }
}

proof fn lemma_side_compatible_at<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, hook: Hook<S>, i: nat, side: S)
    requires
        run_hyps(tc, ex),
        tc.sides.contains(side),
    ensures alloc_compatible(tc, relabeling_of(tc, ex, hook), state_at(ex, i), side, state_at(ex, i + 1).store(side), uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i))),
{
    let r = relabeling_of(tc, ex, hook);
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    lemma_counters_step_at(tc, ex, i);
    if s_prime.store(side).uid_counter > s.store(side).uid_counter {
        let k = s.store(side).uid_counter;
        assert(uid_alloc_at(ex, side, k, i));
        lemma_uid_value_alloc(tc, ex, side, k, i);
        assert((r.uid)(side, k) == uid_sum(tc, s));
    }
    if s_prime.store(side).resource_version_counter > s.store(side).resource_version_counter {
        let k = s.store(side).resource_version_counter;
        assert(rv_alloc_at(ex, side, k, i));
        lemma_rv_value_alloc(tc, ex, side, k, i);
        assert((r.rv)(side, k) == rv_sum(tc, s));
    }
}

pub proof fn lemma_step_compatible_at<S>(tc: MultiCluster<S>, ex: Execution<MultiClusterState<S>>, hook: Hook<S>, i: nat)
    requires run_hyps(tc, ex),
    ensures step_compatible(tc, relabeling_of(tc, ex, hook), state_at(ex, i), state_at(ex, i + 1), uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i))),
{
    reveal(step_compatible);
    let r = relabeling_of(tc, ex, hook);
    assert forall |side: S| #[trigger] tc.sides.contains(side)
        implies alloc_compatible(tc, r, state_at(ex, i), side, state_at(ex, i + 1).store(side), uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i))) by {
        lemma_side_compatible_at(tc, ex, hook, i, side);
    }
}

// ---------------------------------------------------------------------------
// The abstract execution is a one-store execution.
// ---------------------------------------------------------------------------

pub proof fn lemma_simulation<S>(tc: MultiCluster<S>, hook: Hook<S>, ex: Execution<MultiClusterState<S>>)
    requires
        refinement_hyps(tc, hook),
        multi_cluster_run(tc, ex),
    ensures ({
        let r = relabeling_of(tc, ex, hook);
        &&& injective(tc, r)
        &&& r.annotation == hook(r.uid, r.rv)
        &&& simulation(tc, r, ex)
        &&& lift_state(tc.cluster.init()).satisfied_by(alpha(tc, r, ex))
        &&& always(lift_action(tc.cluster.next())).satisfied_by(alpha(tc, r, ex))
    }),
{
    let r = relabeling_of(tc, ex, hook);
    let ex1 = alpha(tc, r, ex);
    lemma_uid_map_injective(tc, ex);
    lemma_rv_map_injective(tc, ex);
    assert(annotation_injective(r.annotation));
    assert(models_commute(tc, r));
    assert forall |i: nat| inv(tc, #[trigger] state_at(ex, i)) by { lemma_inv_at(tc, ex, i); }
    assert forall |i: nat| step_compatible(tc, r, #[trigger] state_at(ex, i), state_at(ex, i + 1), uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i))) by {
        lemma_step_compatible_at(tc, ex, hook, i);
    }
    lemma_init_abs(tc, r, state_at(ex, 0));
    assert(ex1.head() == abs_at(tc, r, ex, 0));
    assert forall |i: nat| #[trigger] lift_action(tc.cluster.next()).satisfied_by(ex1.suffix(i)) by {
        lemma_alpha_step(tc, r, ex, i);
    }
}

// The step of the abstract execution at i.
pub proof fn lemma_alpha_step<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, i: nat)
    requires simulation(tc, r, ex),
    ensures
        alpha(tc, r, ex).suffix(i).head() == abs_at(tc, r, ex, i),
        alpha(tc, r, ex).suffix(i).head_next() == abs_at(tc, r, ex, i + 1),
        tc.cluster.next()(abs_at(tc, r, ex, i), abs_at(tc, r, ex, i + 1)),
{
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    let (side, step) = choose |side: S, step: Step| tc.next_step(s, s_prime, side, step);
    lemma_next_step(tc, r, s, s_prime, side, step, uid_sum(tc, s), rv_sum(tc, s));
    assert(uid_next_after(tc, s, s_prime, uid_sum(tc, s)) == uid_sum(tc, s_prime));
    assert(rv_next_after(tc, s, s_prime, rv_sum(tc, s)) == rv_sum(tc, s_prime));
    assert(tc.cluster.next_step(abs_at(tc, r, ex, i), abs_at(tc, r, ex, i + 1), relabel_step(tc, r, step)));
}

// The two-store step at i, relabeled, is the abstract step at i.
pub proof fn lemma_alpha_step_of<S>(tc: MultiCluster<S>, r: Relabeling<S>, ex: Execution<MultiClusterState<S>>, i: nat, side: S, step: Step)
    requires
        simulation(tc, r, ex),
        tc.next_step(state_at(ex, i), state_at(ex, i + 1), side, step),
    ensures tc.cluster.next_step(abs_at(tc, r, ex, i), abs_at(tc, r, ex, i + 1), relabel_step(tc, r, step)),
{
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    lemma_next_step(tc, r, s, s_prime, side, step, uid_sum(tc, s), rv_sum(tc, s));
    assert(uid_next_after(tc, s, s_prime, uid_sum(tc, s)) == uid_sum(tc, s_prime));
    assert(rv_next_after(tc, s, s_prime, rv_sum(tc, s)) == rv_sum(tc, s_prime));
}

}
