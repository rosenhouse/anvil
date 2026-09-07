// From an execution of the two-store model to an execution of the one-store
// model. The relabeling is read off the execution: the k-th value a store's
// counter allocates relabels to the number of values both stores had allocated
// by then, so that the one-store counters count every allocation once. Values a
// counter never allocates relabel to distinct negative numbers.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::two_cluster::{api_server::*, relabel::*, steps::*};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, api_server::types::*, cluster::*, controller::state_machine::*,
    controller::types::*, external::state_machine::*, message::*, network::types::*, two_cluster::*,
};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::vstd_ext::string_view::*;
use verus_temporal_logic::defs::*;
use vstd::{map_lib::*, multiset::*, prelude::*};

verus! {

// ---------------------------------------------------------------------------
// The relabeling of an execution.
// ---------------------------------------------------------------------------

pub open spec fn state_at(ex: Execution<TwoClusterState>, i: nat) -> TwoClusterState {
    (ex.nat_to_state)(i)
}

pub open spec fn uid_at(ex: Execution<TwoClusterState>, side: Side, i: nat) -> int {
    state_at(ex, i).store(side).uid_counter
}

pub open spec fn rv_at(ex: Execution<TwoClusterState>, side: Side, i: nat) -> int {
    state_at(ex, i).store(side).resource_version_counter
}

// The step at which the uid counter of `side` goes from k to k + 1.
pub open spec fn uid_alloc_at(ex: Execution<TwoClusterState>, side: Side, k: int, i: nat) -> bool {
    uid_at(ex, side, i) == k && uid_at(ex, side, i + 1) == k + 1
}

pub open spec fn rv_alloc_at(ex: Execution<TwoClusterState>, side: Side, k: int, i: nat) -> bool {
    rv_at(ex, side, i) == k && rv_at(ex, side, i + 1) == k + 1
}

// An injection of the integers into the naturals.
pub open spec fn int_code(k: int) -> int {
    if k >= 0 { 2 * k } else { -2 * k - 1 }
}

// A negative value, distinct for every side and k.
pub open spec fn unused_value(side: Side, k: int) -> int {
    if side is Primary { -(2 * int_code(k) + 1) } else { -(2 * int_code(k) + 2) }
}

#[verifier::opaque]
pub open spec fn uid_value(ex: Execution<TwoClusterState>, side: Side, k: int) -> int {
    if exists |i: nat| uid_alloc_at(ex, side, k, i) {
        uid_sum(state_at(ex, choose |i: nat| uid_alloc_at(ex, side, k, i)))
    } else {
        unused_value(side, k)
    }
}

#[verifier::opaque]
pub open spec fn rv_value(ex: Execution<TwoClusterState>, side: Side, k: int) -> int {
    if exists |i: nat| rv_alloc_at(ex, side, k, i) {
        rv_sum(state_at(ex, choose |i: nat| rv_alloc_at(ex, side, k, i)))
    } else {
        unused_value(side, k)
    }
}

pub open spec fn uid_map(ex: Execution<TwoClusterState>) -> spec_fn(Side, Uid) -> Uid {
    |side: Side, k: Uid| uid_value(ex, side, k)
}

pub open spec fn rv_map(ex: Execution<TwoClusterState>) -> spec_fn(Side, ResourceVersion) -> ResourceVersion {
    |side: Side, k: ResourceVersion| rv_value(ex, side, k)
}

// How annotation values follow the counter maps; instantiated per controller.
pub type Hook = spec_fn(spec_fn(Side, Uid) -> Uid, spec_fn(Side, ResourceVersion) -> ResourceVersion) -> spec_fn(Kind, StringView, StringView) -> StringView;

pub open spec fn hook_injective(hook: Hook) -> bool {
    forall |u: spec_fn(Side, Uid) -> Uid, v: spec_fn(Side, ResourceVersion) -> ResourceVersion|
        uid_map_injective(u) && rv_map_injective(v) ==> annotation_injective(#[trigger] hook(u, v))
}

pub open spec fn relabeling_of(ex: Execution<TwoClusterState>, hook: Hook) -> Relabeling {
    Relabeling { uid: uid_map(ex), rv: rv_map(ex), annotation: hook(uid_map(ex), rv_map(ex)) }
}

// The one-store execution.
pub open spec fn alpha(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>) -> Execution<ClusterState> {
    Execution {
        nat_to_state: |i: nat| abs(tc, r, state_at(ex, i), uid_sum(state_at(ex, i)), rv_sum(state_at(ex, i))),
    }
}

pub open spec fn abs_at(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>, i: nat) -> ClusterState {
    abs(tc, r, state_at(ex, i), uid_sum(state_at(ex, i)), rv_sum(state_at(ex, i)))
}

// An execution of the two-store model.
pub open spec fn two_cluster_run(tc: TwoCluster, ex: Execution<TwoClusterState>) -> bool {
    &&& tc.init()(state_at(ex, 0))
    &&& forall |i: nat| tc.next()(#[trigger] state_at(ex, i), state_at(ex, i + 1))
}

// The hypotheses on a two-store cluster and its controllers.
pub open spec fn refinement_hyps(tc: TwoCluster, hook: Hook) -> bool {
    &&& models_ok(tc)
    &&& installed_types_ignore_metadata(tc.cluster.installed_types)
    &&& installed_types_coherent(tc.cluster.installed_types)
    &&& hook_injective(hook)
    &&& forall |r: Relabeling| injective(r) && r.annotation == hook(r.uid, r.rv) ==> #[trigger] models_commute(tc, r)
}

// What the simulation of an execution establishes.
pub open spec fn simulation(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>) -> bool {
    &&& relabel_hyps(tc, r)
    &&& models_ok(tc)
    &&& models_commute(tc, r)
    &&& forall |i: nat| inv(tc, #[trigger] state_at(ex, i))
    &&& forall |i: nat| tc.next()(#[trigger] state_at(ex, i), state_at(ex, i + 1))
    &&& forall |i: nat| step_compatible(tc, r, #[trigger] state_at(ex, i), state_at(ex, i + 1), uid_sum(state_at(ex, i)), rv_sum(state_at(ex, i)))
}

// ---------------------------------------------------------------------------
// Initial states.
// ---------------------------------------------------------------------------

pub proof fn lemma_init_abs(tc: TwoCluster, r: Relabeling, s: TwoClusterState)
    requires
        models_ok(tc),
        tc.init()(s),
    ensures
        tc.cluster.init()(abs(tc, r, s, 0, 0)),
        inv(tc, s),
        uid_sum(s) == 0,
        rv_sum(s) == 0,
{
    let a = abs(tc, r, s, 0, 0);
    let cluster = tc.cluster;
    lemma_map_values_empty::<ObjectRef, DynamicObjectView, DynamicObjectView>(|o: DynamicObjectView| relabel_obj(tc, r, o));
    assert(a.api_server.resources =~= Map::<ObjectRef, DynamicObjectView>::empty());
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

// A relabeling that only separates the two sides.
pub open spec fn split_relabeling() -> Relabeling {
    Relabeling {
        uid: |side: Side, k: Uid| if side is Primary { 2 * k } else { 2 * k + 1 },
        rv: |side: Side, k: ResourceVersion| if side is Primary { 2 * k } else { 2 * k + 1 },
        annotation: |kind: Kind, key: StringView, v: StringView| v,
    }
}

pub proof fn lemma_split_relabeling_injective()
    ensures injective(split_relabeling()),
{
}

// The controller step keeps the invariants; unlike the simulation this needs no
// commutation of the reconciler.
proof fn lemma_controller_step_keeps_inv(tc: TwoCluster, s: TwoClusterState, s_prime: TwoClusterState, input: (int, Option<Message>, Option<ObjectRef>))
    requires
        models_ok(tc),
        inv(tc, s),
        tc.controller_next().forward(input)(s, s_prime),
    ensures
        inv(tc, s_prime),
        s_prime.primary == s.primary,
        s_prime.remote == s.remote,
{
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

pub proof fn lemma_next_step_keeps_inv(tc: TwoCluster, s: TwoClusterState, s_prime: TwoClusterState, side: Side, step: Step)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        inv(tc, s),
        tc.next_step(s, s_prime, side, step),
    ensures
        inv(tc, s_prime),
        counters_step(s, s_prime),
{
    let r = split_relabeling();
    lemma_split_relabeling_injective();
    match step {
        Step::APIServerStep(input) => {
            let uid_next = (r.uid)(side, s.store(side).uid_counter);
            let rv_next = (r.rv)(side, s.store(side).resource_version_counter);
            assert(s_prime.store(side.other()) == s.store(side.other()));
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

proof fn lemma_next_keeps_inv(tc: TwoCluster, s: TwoClusterState, s_prime: TwoClusterState)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        inv(tc, s),
        tc.next()(s, s_prime),
    ensures
        inv(tc, s_prime),
        counters_step(s, s_prime),
{
    let (side, step) = choose |side: Side, step: Step| tc.next_step(s, s_prime, side, step);
    lemma_next_step_keeps_inv(tc, s, s_prime, side, step);
}

proof fn lemma_init_inv(tc: TwoCluster, s: TwoClusterState)
    requires
        models_ok(tc),
        tc.init()(s),
    ensures inv(tc, s),
{
    lemma_init_abs(tc, split_relabeling(), s);
}

pub proof fn lemma_inv_at(tc: TwoCluster, ex: Execution<TwoClusterState>, i: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
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

pub proof fn lemma_counters_step_at(tc: TwoCluster, ex: Execution<TwoClusterState>, i: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
    ensures counters_step(state_at(ex, i), state_at(ex, i + 1)),
{
    lemma_inv_at(tc, ex, i);
    lemma_next_keeps_inv(tc, state_at(ex, i), state_at(ex, i + 1));
}

// ---------------------------------------------------------------------------
// Counters along an execution.
// ---------------------------------------------------------------------------

proof fn lemma_counters_one_step(tc: TwoCluster, ex: Execution<TwoClusterState>, k: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
    ensures
        uid_at(ex, Side::Primary, k) <= uid_at(ex, Side::Primary, k + 1),
        uid_at(ex, Side::Remote, k) <= uid_at(ex, Side::Remote, k + 1),
        rv_at(ex, Side::Primary, k) <= rv_at(ex, Side::Primary, k + 1),
        rv_at(ex, Side::Remote, k) <= rv_at(ex, Side::Remote, k + 1),
        uid_sum(state_at(ex, k)) <= uid_sum(state_at(ex, k + 1)),
        rv_sum(state_at(ex, k)) <= rv_sum(state_at(ex, k + 1)),
{
    lemma_counters_step_at(tc, ex, k);
}

#[verifier::rlimit(50)]
pub proof fn lemma_counters_mono(tc: TwoCluster, ex: Execution<TwoClusterState>, i: nat, j: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
        i <= j,
    ensures
        uid_at(ex, Side::Primary, i) <= uid_at(ex, Side::Primary, j),
        uid_at(ex, Side::Remote, i) <= uid_at(ex, Side::Remote, j),
        rv_at(ex, Side::Primary, i) <= rv_at(ex, Side::Primary, j),
        rv_at(ex, Side::Remote, i) <= rv_at(ex, Side::Remote, j),
        uid_sum(state_at(ex, i)) <= uid_sum(state_at(ex, j)),
        rv_sum(state_at(ex, i)) <= rv_sum(state_at(ex, j)),
    decreases j - i,
{
    if i < j {
        let k = (j - 1) as nat;
        lemma_counters_mono(tc, ex, i, k);
        lemma_counters_one_step(tc, ex, k);
        assert(k + 1 == j);
    }
}

pub proof fn lemma_counters_nonneg(tc: TwoCluster, ex: Execution<TwoClusterState>, i: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
    ensures
        uid_sum(state_at(ex, i)) >= 0,
        rv_sum(state_at(ex, i)) >= 0,
{
    lemma_counters_mono(tc, ex, 0, i);
}

// A counter goes from k to k + 1 at most once.
pub proof fn lemma_uid_alloc_unique(tc: TwoCluster, ex: Execution<TwoClusterState>, side: Side, k: int, i: nat, j: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
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

pub proof fn lemma_rv_alloc_unique(tc: TwoCluster, ex: Execution<TwoClusterState>, side: Side, k: int, i: nat, j: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
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

// After an allocation the sum has grown by one, and never shrinks.
pub proof fn lemma_uid_sum_after_alloc(tc: TwoCluster, ex: Execution<TwoClusterState>, side: Side, k: int, i: nat, j: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
        uid_alloc_at(ex, side, k, i),
        i < j,
    ensures uid_sum(state_at(ex, i)) + 1 <= uid_sum(state_at(ex, j)),
{
    lemma_counters_step_at(tc, ex, i);
    assert(uid_sum(state_at(ex, i + 1)) == uid_sum(state_at(ex, i)) + 1);
    lemma_counters_mono(tc, ex, i + 1, j);
}

pub proof fn lemma_rv_sum_after_alloc(tc: TwoCluster, ex: Execution<TwoClusterState>, side: Side, k: int, i: nat, j: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
        rv_alloc_at(ex, side, k, i),
        i < j,
    ensures rv_sum(state_at(ex, i)) + 1 <= rv_sum(state_at(ex, j)),
{
    lemma_counters_step_at(tc, ex, i);
    assert(rv_sum(state_at(ex, i + 1)) == rv_sum(state_at(ex, i)) + 1);
    lemma_counters_mono(tc, ex, i + 1, j);
}

// ---------------------------------------------------------------------------
// The relabeling of an execution is injective and compatible with its steps.
// ---------------------------------------------------------------------------

proof fn lemma_unused_value_negative(side: Side, k: int)
    ensures unused_value(side, k) < 0,
{
}

proof fn lemma_unused_value_injective(side_a: Side, a: int, side_b: Side, b: int)
    requires unused_value(side_a, a) == unused_value(side_b, b),
    ensures side_a == side_b && a == b,
{
}

pub proof fn lemma_uid_value_alloc(tc: TwoCluster, ex: Execution<TwoClusterState>, side: Side, k: int, i: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
        uid_alloc_at(ex, side, k, i),
    ensures uid_value(ex, side, k) == uid_sum(state_at(ex, i)),
{
    reveal(uid_value);
    let j = choose |j: nat| uid_alloc_at(ex, side, k, j);
    lemma_uid_alloc_unique(tc, ex, side, k, i, j);
}

pub proof fn lemma_rv_value_alloc(tc: TwoCluster, ex: Execution<TwoClusterState>, side: Side, k: int, i: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
        rv_alloc_at(ex, side, k, i),
    ensures rv_value(ex, side, k) == rv_sum(state_at(ex, i)),
{
    reveal(rv_value);
    let j = choose |j: nat| rv_alloc_at(ex, side, k, j);
    lemma_rv_alloc_unique(tc, ex, side, k, i, j);
}

proof fn lemma_uid_value_unused(ex: Execution<TwoClusterState>, side: Side, k: int)
    requires !(exists |i: nat| uid_alloc_at(ex, side, k, i)),
    ensures uid_value(ex, side, k) == unused_value(side, k),
{
    reveal(uid_value);
}

proof fn lemma_rv_value_unused(ex: Execution<TwoClusterState>, side: Side, k: int)
    requires !(exists |i: nat| rv_alloc_at(ex, side, k, i)),
    ensures rv_value(ex, side, k) == unused_value(side, k),
{
    reveal(rv_value);
}

// Two different (side, k) pairs relabel to different values.
proof fn lemma_uid_values_distinct(tc: TwoCluster, ex: Execution<TwoClusterState>, side_a: Side, a: Uid, side_b: Side, b: Uid)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
        uid_value(ex, side_a, a) == uid_value(ex, side_b, b),
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
            }
        } else {
            lemma_uid_value_unused(ex, side_b, b);
            lemma_unused_value_negative(side_b, b);
        }
    } else {
        lemma_uid_value_unused(ex, side_a, a);
        lemma_unused_value_negative(side_a, a);
        if exists |j: nat| uid_alloc_at(ex, side_b, b, j) {
            let j = choose |j: nat| uid_alloc_at(ex, side_b, b, j);
            lemma_uid_value_alloc(tc, ex, side_b, b, j);
            lemma_counters_nonneg(tc, ex, j);
        } else {
            lemma_uid_value_unused(ex, side_b, b);
            lemma_unused_value_injective(side_a, a, side_b, b);
        }
    }
}

proof fn lemma_rv_values_distinct(tc: TwoCluster, ex: Execution<TwoClusterState>, side_a: Side, a: ResourceVersion, side_b: Side, b: ResourceVersion)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
        rv_value(ex, side_a, a) == rv_value(ex, side_b, b),
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
            }
        } else {
            lemma_rv_value_unused(ex, side_b, b);
            lemma_unused_value_negative(side_b, b);
        }
    } else {
        lemma_rv_value_unused(ex, side_a, a);
        lemma_unused_value_negative(side_a, a);
        if exists |j: nat| rv_alloc_at(ex, side_b, b, j) {
            let j = choose |j: nat| rv_alloc_at(ex, side_b, b, j);
            lemma_rv_value_alloc(tc, ex, side_b, b, j);
            lemma_counters_nonneg(tc, ex, j);
        } else {
            lemma_rv_value_unused(ex, side_b, b);
            lemma_unused_value_injective(side_a, a, side_b, b);
        }
    }
}

pub proof fn lemma_uid_map_injective(tc: TwoCluster, ex: Execution<TwoClusterState>)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
    ensures uid_map_injective(uid_map(ex)),
{
    let u = uid_map(ex);
    assert forall |side: Side, a: Uid, b: Uid| #[trigger] u(side, a) == #[trigger] u(side, b) implies a == b by {
        lemma_uid_values_distinct(tc, ex, side, a, side, b);
    }
    assert forall |a: Uid, b: Uid| #[trigger] u(Side::Primary, a) != #[trigger] u(Side::Remote, b) by {
        if u(Side::Primary, a) == u(Side::Remote, b) {
            lemma_uid_values_distinct(tc, ex, Side::Primary, a, Side::Remote, b);
        }
    }
}

pub proof fn lemma_rv_map_injective(tc: TwoCluster, ex: Execution<TwoClusterState>)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
    ensures rv_map_injective(rv_map(ex)),
{
    let v = rv_map(ex);
    assert forall |side: Side, a: ResourceVersion, b: ResourceVersion| #[trigger] v(side, a) == #[trigger] v(side, b) implies a == b by {
        lemma_rv_values_distinct(tc, ex, side, a, side, b);
    }
    assert forall |a: ResourceVersion, b: ResourceVersion| #[trigger] v(Side::Primary, a) != #[trigger] v(Side::Remote, b) by {
        if v(Side::Primary, a) == v(Side::Remote, b) {
            lemma_rv_values_distinct(tc, ex, Side::Primary, a, Side::Remote, b);
        }
    }
}

proof fn lemma_side_compatible_at(tc: TwoCluster, ex: Execution<TwoClusterState>, hook: Hook, i: nat, side: Side)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
    ensures alloc_compatible(tc, relabeling_of(ex, hook), state_at(ex, i), side, state_at(ex, i + 1).store(side), uid_sum(state_at(ex, i)), rv_sum(state_at(ex, i))),
{
    let r = relabeling_of(ex, hook);
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    lemma_counters_step_at(tc, ex, i);
    if s_prime.store(side).uid_counter > s.store(side).uid_counter {
        let k = s.store(side).uid_counter;
        assert(uid_alloc_at(ex, side, k, i));
        lemma_uid_value_alloc(tc, ex, side, k, i);
        assert((r.uid)(side, k) == uid_sum(s));
    }
    if s_prime.store(side).resource_version_counter > s.store(side).resource_version_counter {
        let k = s.store(side).resource_version_counter;
        assert(rv_alloc_at(ex, side, k, i));
        lemma_rv_value_alloc(tc, ex, side, k, i);
        assert((r.rv)(side, k) == rv_sum(s));
    }
}

pub proof fn lemma_step_compatible_at(tc: TwoCluster, ex: Execution<TwoClusterState>, hook: Hook, i: nat)
    requires
        models_ok(tc),
        installed_types_ignore_metadata(tc.cluster.installed_types),
        installed_types_coherent(tc.cluster.installed_types),
        two_cluster_run(tc, ex),
    ensures step_compatible(tc, relabeling_of(ex, hook), state_at(ex, i), state_at(ex, i + 1), uid_sum(state_at(ex, i)), rv_sum(state_at(ex, i))),
{
    lemma_side_compatible_at(tc, ex, hook, i, Side::Primary);
    lemma_side_compatible_at(tc, ex, hook, i, Side::Remote);
    assert(state_at(ex, i + 1).store(Side::Primary) == state_at(ex, i + 1).primary);
    assert(state_at(ex, i + 1).store(Side::Remote) == state_at(ex, i + 1).remote);
}

// ---------------------------------------------------------------------------
// The abstract execution is a one-store execution.
// ---------------------------------------------------------------------------

pub proof fn lemma_simulation(tc: TwoCluster, hook: Hook, ex: Execution<TwoClusterState>)
    requires
        refinement_hyps(tc, hook),
        two_cluster_run(tc, ex),
    ensures ({
        let r = relabeling_of(ex, hook);
        &&& injective(r)
        &&& r.annotation == hook(r.uid, r.rv)
        &&& simulation(tc, r, ex)
        &&& lift_state(tc.cluster.init()).satisfied_by(alpha(tc, r, ex))
        &&& always(lift_action(tc.cluster.next())).satisfied_by(alpha(tc, r, ex))
    }),
{
    let r = relabeling_of(ex, hook);
    let ex1 = alpha(tc, r, ex);
    lemma_uid_map_injective(tc, ex);
    lemma_rv_map_injective(tc, ex);
    assert(annotation_injective(r.annotation));
    assert(models_commute(tc, r));
    assert forall |i: nat| inv(tc, #[trigger] state_at(ex, i)) by { lemma_inv_at(tc, ex, i); }
    assert forall |i: nat| step_compatible(tc, r, #[trigger] state_at(ex, i), state_at(ex, i + 1), uid_sum(state_at(ex, i)), rv_sum(state_at(ex, i))) by {
        lemma_step_compatible_at(tc, ex, hook, i);
    }
    lemma_init_abs(tc, r, state_at(ex, 0));
    assert(ex1.head() == abs_at(tc, r, ex, 0));
    assert forall |i: nat| #[trigger] lift_action(tc.cluster.next()).satisfied_by(ex1.suffix(i)) by {
        lemma_alpha_step(tc, r, ex, i);
    }
}

// The step of the abstract execution at i.
pub proof fn lemma_alpha_step(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>, i: nat)
    requires simulation(tc, r, ex),
    ensures
        alpha(tc, r, ex).suffix(i).head() == abs_at(tc, r, ex, i),
        alpha(tc, r, ex).suffix(i).head_next() == abs_at(tc, r, ex, i + 1),
        tc.cluster.next()(abs_at(tc, r, ex, i), abs_at(tc, r, ex, i + 1)),
{
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    let (side, step) = choose |side: Side, step: Step| tc.next_step(s, s_prime, side, step);
    lemma_next_step(tc, r, s, s_prime, side, step, uid_sum(s), rv_sum(s));
    assert(uid_next_after(s, s_prime, uid_sum(s)) == uid_sum(s_prime));
    assert(rv_next_after(s, s_prime, rv_sum(s)) == rv_sum(s_prime));
    assert(tc.cluster.next_step(abs_at(tc, r, ex, i), abs_at(tc, r, ex, i + 1), relabel_step(tc, r, step)));
}

// The two-store step at i, relabeled, is the abstract step at i.
pub proof fn lemma_alpha_step_of(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>, i: nat, side: Side, step: Step)
    requires
        simulation(tc, r, ex),
        tc.next_step(state_at(ex, i), state_at(ex, i + 1), side, step),
    ensures tc.cluster.next_step(abs_at(tc, r, ex, i), abs_at(tc, r, ex, i + 1), relabel_step(tc, r, step)),
{
    let s = state_at(ex, i);
    let s_prime = state_at(ex, i + 1);
    lemma_next_step(tc, r, s, s_prime, side, step, uid_sum(s), rv_sum(s));
    assert(uid_next_after(s, s_prime, uid_sum(s)) == uid_sum(s_prime));
    assert(rv_next_after(s, s_prime, rv_sum(s)) == rv_sum(s_prime));
}

}
