// Every step of the two-store model is, through the abstraction, a step of the
// one-store model: for each kind of step, the one-store action with the
// relabeled input takes abs(s) to abs(s'), and the invariants the abstraction
// relies on are kept.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::two_cluster::{api_server::*, relabel::*};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, api_server::types::*, builtin_controllers::garbage_collector::*,
    builtin_controllers::state_machine::*, builtin_controllers::types::*, cluster::*,
    controller::state_machine::*, controller::types::*, message::*, network::state_machine::*,
    network::types::*, pod_monkey::state_machine::*, pod_monkey::types::*, two_cluster::*,
};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use vstd::{map_lib::*, multiset::*, prelude::*, seq_lib::*, set_lib::*};

verus! {

// ---------------------------------------------------------------------------
// Invariants of the two-store model that the simulation relies on.
// ---------------------------------------------------------------------------

// Every in-flight request is one the refinement handles.
pub open spec fn msgs_ok(tc: TwoCluster, s: TwoClusterState) -> bool {
    forall |m: Message| #[trigger] s.in_flight().contains(m) && m.content is APIRequest ==> tc.request_ok(m.content->APIRequest_0)
}

pub open spec fn controllers_present(tc: TwoCluster, s: TwoClusterState) -> bool {
    forall |id: int| #[trigger] tc.cluster.controller_models.contains_key(id) ==> s.controller_and_externals.contains_key(id)
}

pub open spec fn inv(tc: TwoCluster, s: TwoClusterState) -> bool {
    &&& stores_sided(tc, s)
    &&& msgs_ok(tc, s)
    &&& controllers_present(tc, s)
}

// ---------------------------------------------------------------------------
// Hypotheses on the controllers.
// ---------------------------------------------------------------------------

pub open spec fn relabel_resp_content(tc: TwoCluster, r: Relabeling, c: Option<ResponseContent>) -> Option<ResponseContent> {
    match c {
        Some(ResponseContent::KubernetesResponse(x)) => Some(ResponseContent::KubernetesResponse(relabel_resp(tc, r, x))),
        _ => c,
    }
}

pub open spec fn relabel_req_content(tc: TwoCluster, r: Relabeling, c: Option<RequestContent>) -> Option<RequestContent> {
    match c {
        Some(RequestContent::KubernetesRequest(x)) => Some(RequestContent::KubernetesRequest(relabel_req(tc, r, x))),
        _ => c,
    }
}

// No controller has an external system, and every request a controller sends
// is one the refinement handles.
pub open spec fn models_ok(tc: TwoCluster) -> bool {
    forall |id: int| #[trigger] tc.cluster.controller_models.contains_key(id) ==> {
        let m = tc.cluster.controller_models[id];
        &&& m.external_model is None
        &&& forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState| {
            let req_o = (#[trigger] (m.reconcile_model.transition)(cr, resp, ls)).1;
            req_o is Some && req_o->0 is KubernetesRequest ==> tc.request_ok(req_o->0->KubernetesRequest_0)
        }
    }
}

// Every reconciler commutes with the relabeling: run on the relabeled object and
// response, it reaches the same local state and sends the relabeled request.
pub open spec fn models_commute(tc: TwoCluster, r: Relabeling) -> bool {
    forall |id: int| #[trigger] tc.cluster.controller_models.contains_key(id) ==> {
        let t = tc.cluster.controller_models[id].reconcile_model.transition;
        forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState|
            #[trigger] t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls)
                == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1))
    }
}

// ---------------------------------------------------------------------------
// Steps and counters.
// ---------------------------------------------------------------------------

pub open spec fn relabel_step(tc: TwoCluster, r: Relabeling, step: Step) -> Step {
    match step {
        Step::APIServerStep(input) => Step::APIServerStep(relabel_opt_msg(tc, r, input)),
        Step::ControllerStep(input) => Step::ControllerStep((input.0, relabel_opt_msg(tc, r, input.1), input.2)),
        Step::DropReqStep(input) => Step::DropReqStep((relabel_msg(tc, r, input.0), input.1)),
        _ => step,
    }
}

pub open spec fn uid_sum(s: TwoClusterState) -> int {
    s.primary.uid_counter + s.remote.uid_counter
}

pub open spec fn rv_sum(s: TwoClusterState) -> int {
    s.primary.resource_version_counter + s.remote.resource_version_counter
}

// The global counters after the step from s to s_prime.
pub open spec fn uid_next_after(s: TwoClusterState, s_prime: TwoClusterState, uid_next: Uid) -> Uid {
    uid_next + uid_sum(s_prime) - uid_sum(s)
}

pub open spec fn rv_next_after(s: TwoClusterState, s_prime: TwoClusterState, rv_next: ResourceVersion) -> ResourceVersion {
    rv_next + rv_sum(s_prime) - rv_sum(s)
}

// Whatever a step allocates on either side relabels to the global counter.
pub open spec fn step_compatible(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, uid_next: Uid, rv_next: ResourceVersion) -> bool {
    &&& alloc_compatible(tc, r, s, Side::Primary, s_prime.primary, uid_next, rv_next)
    &&& alloc_compatible(tc, r, s, Side::Remote, s_prime.remote, uid_next, rv_next)
}

pub open spec fn counter_step(a: int, b: int) -> bool {
    b == a || b == a + 1
}

// A step moves the counters of at most one store, each by at most one.
pub open spec fn counters_step(s: TwoClusterState, s_prime: TwoClusterState) -> bool {
    &&& counter_step(s.primary.uid_counter, s_prime.primary.uid_counter)
    &&& counter_step(s.primary.resource_version_counter, s_prime.primary.resource_version_counter)
    &&& counter_step(s.remote.uid_counter, s_prime.remote.uid_counter)
    &&& counter_step(s.remote.resource_version_counter, s_prime.remote.resource_version_counter)
    &&& s_prime.primary == s.primary || s_prime.remote == s.remote
}

// ---------------------------------------------------------------------------
// Generic map and message facts.
// ---------------------------------------------------------------------------

pub proof fn lemma_map_values_insert<K, V, W>(m: Map<K, V>, f: spec_fn(V) -> W, k: K, v: V)
    ensures m.insert(k, v).map_values(f) == m.map_values(f).insert(k, f(v)),
{
    assert(m.insert(k, v).map_values(f) =~= m.map_values(f).insert(k, f(v)));
}

pub proof fn lemma_map_values_remove<K, V, W>(m: Map<K, V>, f: spec_fn(V) -> W, k: K)
    ensures m.remove(k).map_values(f) == m.map_values(f).remove(k),
{
    assert(m.remove(k).map_values(f) =~= m.map_values(f).remove(k));
}

pub proof fn lemma_map_values_empty<K, V, W>(f: spec_fn(V) -> W)
    ensures Map::<K, V>::empty().map_values(f) == Map::<K, W>::empty(),
{
    assert(Map::<K, V>::empty().map_values(f) =~= Map::<K, W>::empty());
}

pub proof fn lemma_resp_matches_relabel(tc: TwoCluster, r: Relabeling, resp: Message, req: Message)
    ensures resp_msg_matches_req_msg(relabel_msg(tc, r, resp), relabel_msg(tc, r, req)) == resp_msg_matches_req_msg(resp, req),
{
}

pub proof fn lemma_err_resp_relabel(tc: TwoCluster, r: Relabeling, m: Message, err: APIError)
    requires m.content is APIRequest,
    ensures relabel_msg(tc, r, form_matched_err_resp_msg(m, err)) == form_matched_err_resp_msg(relabel_msg(tc, r, m), err),
{
    match m.content->APIRequest_0 {
        APIRequest::GetRequest(_) => {},
        APIRequest::ListRequest(_) => {},
        APIRequest::CreateRequest(_) => {},
        APIRequest::DeleteRequest(_) => {},
        APIRequest::UpdateRequest(_) => {},
        APIRequest::UpdateStatusRequest(_) => {},
        APIRequest::GetThenDeleteRequest(_) => {},
        APIRequest::GetThenUpdateRequest(_) => {},
        APIRequest::GetThenUpdateStatusRequest(_) => {},
        APIRequest::PatchRequest(_) => {},
        APIRequest::PatchStatusRequest(_) => {},
    }
}

// The controller state of `id` in the abstraction is the relabeled controller state.
pub proof fn lemma_abs_controller(tc: TwoCluster, r: Relabeling, s: TwoClusterState, id: int, uid_next: Uid, rv_next: ResourceVersion)
    requires s.controller_and_externals.contains_key(id),
    ensures
        abs(tc, r, s, uid_next, rv_next).controller_and_externals.contains_key(id),
        abs(tc, r, s, uid_next, rv_next).controller_and_externals[id] == relabel_cae(tc, r, s.controller_and_externals[id]),
{
}

// ---------------------------------------------------------------------------
// The API server step.
// ---------------------------------------------------------------------------

pub proof fn lemma_api_server_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, side: Side, input: Option<Message>, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        inv(tc, s),
        tc.api_server_next(side).forward(input)(s, s_prime),
        step_compatible(tc, r, s, s_prime, uid_next, rv_next),
    ensures
        tc.cluster.api_server_next().forward(relabel_opt_msg(tc, r, input))(
            abs(tc, r, s, uid_next, rv_next),
            abs(tc, r, s_prime, uid_next_after(s, s_prime, uid_next), rv_next_after(s, s_prime, rv_next))
        ),
        inv(tc, s_prime),
        counters_step(s, s_prime),
{
    let it = tc.cluster.installed_types;
    let msg = input->0;
    let msg1 = relabel_msg(tc, r, msg);
    let st = s.store(side);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let a = abs(tc, r, s, uid_next, rv_next);
    let u1 = uid_next_after(s, s_prime, uid_next);
    let v1 = rv_next_after(s, s_prime, rv_next);
    let a_prime = abs(tc, r, s_prime, u1, v1);
    assert(s_prime.store(side) == s1);
    assert(s_prime.store(side.other()) == s.store(side.other()));
    lemma_etcd_counters(it, msg, st);
    lemma_transition_by_etcd_relabel(tc, r, s, side, msg, uid_next, rv_next);
    assert(a_prime.api_server == abs_after(tc, r, s, side, s1, uid_next, rv_next)) by {
        lemma_abs_store_unchanged(tc, r, s_prime, with_store(s, side, s1));
    }
    let in_flight = s.network.in_flight;
    lemma_relabel_msgs_contains(tc, r, in_flight, msg);
    lemma_relabel_msgs_remove(tc, r, in_flight, msg);
    lemma_relabel_msgs_insert(tc, r, in_flight.remove(msg), resp);
    assert(s_prime.network.in_flight == in_flight.remove(msg).insert(resp));
    assert(a_prime.network.in_flight == a.network.in_flight.remove(msg1).insert(relabel_msg(tc, r, resp)));
    assert(a_prime.controller_and_externals == a.controller_and_externals);
    // The one-store step.
    assert(tc.cluster.api_server_next().forward(Some(msg1))(a, a_prime));
    // Invariants.
    assert(stores_sided(tc, s_prime));
    assert forall |m: Message| #[trigger] s_prime.in_flight().contains(m) && m.content is APIRequest implies tc.request_ok(m.content->APIRequest_0) by {
        if m != resp { assert(s.in_flight().contains(m)); }
    }
}

// Each handler moves each counter of its store by at most one.
proof fn lemma_etcd_counters(it: InstalledTypes, msg: Message, st: APIServerState)
    requires msg.content is APIRequest,
    ensures
        counter_step(st.uid_counter, transition_by_etcd(it, msg, st).0.uid_counter),
        counter_step(st.resource_version_counter, transition_by_etcd(it, msg, st).0.resource_version_counter),
{
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(_) => {},
        APIRequest::ListRequest(_) => {},
        APIRequest::CreateRequest(_) => {},
        APIRequest::DeleteRequest(_) => {},
        APIRequest::UpdateRequest(_) => {},
        APIRequest::UpdateStatusRequest(_) => {},
        APIRequest::GetThenDeleteRequest(_) => {},
        APIRequest::GetThenUpdateRequest(_) => {},
        APIRequest::GetThenUpdateStatusRequest(_) => {},
        APIRequest::PatchRequest(_) => {},
        APIRequest::PatchStatusRequest(_) => {},
    }
}

// ---------------------------------------------------------------------------
// The controller step.
// ---------------------------------------------------------------------------

pub open spec fn relabel_controller_input(tc: TwoCluster, r: Relabeling, input: ControllerActionInput) -> ControllerActionInput {
    ControllerActionInput { recv: relabel_opt_msg(tc, r, input.recv), ..input }
}

// Each controller action is enabled on the relabeled state and input exactly
// when it is enabled on the original ones.
pub proof fn lemma_controller_action_pre_relabel(tc: TwoCluster, r: Relabeling, model: ReconcileModel, id: int, input: ControllerActionInput, c: ControllerState, step: ControllerStep)
    ensures ({
        let sm = controller(model, id);
        ((sm.step_to_action)(step).precondition)(relabel_controller_input(tc, r, input), relabel_controller(tc, r, c))
            == ((sm.step_to_action)(step).precondition)(input, c)
    }),
{
    let c1 = relabel_controller(tc, r, c);
    match step {
        ControllerStep::RunScheduledReconcile => {},
        ControllerStep::ContinueReconcile => {
            if input.scheduled_cr_key is Some {
                let key = input.scheduled_cr_key->0;
                if c.ongoing_reconciles.contains_key(key) {
                    assert(c1.ongoing_reconciles[key] == relabel_ongoing(tc, r, c.ongoing_reconciles[key]));
                    if c.ongoing_reconciles[key].pending_req_msg is Some && input.recv is Some {
                        lemma_resp_matches_relabel(tc, r, input.recv->0, c.ongoing_reconciles[key].pending_req_msg->0);
                    }
                }
            }
        },
        ControllerStep::EndReconcile => {},
    }
}

pub proof fn lemma_controller_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, input: (int, Option<Message>, Option<ObjectRef>), uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        models_ok(tc),
        models_commute(tc, r),
        inv(tc, s),
        tc.controller_next().forward(input)(s, s_prime),
    ensures
        tc.cluster.controller_next().forward((input.0, relabel_opt_msg(tc, r, input.1), input.2))(
            abs(tc, r, s, uid_next, rv_next),
            abs(tc, r, s_prime, uid_next, rv_next)
        ),
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
    let a = abs(tc, r, s, uid_next, rv_next);
    let a_prime = abs(tc, r, s_prime, uid_next, rv_next);
    let c = s.controller_and_externals[id].controller;
    let c1 = relabel_controller(tc, r, c);
    lemma_abs_controller(tc, r, s, id, uid_next, rv_next);
    let in2 = ControllerActionInput { recv: msg, scheduled_cr_key: key_o, rpc_id_allocator: s.rpc_id_allocator };
    let in1 = relabel_controller_input(tc, r, in2);
    let msg1 = relabel_opt_msg(tc, r, msg);
    let st2 = choose |step: ControllerStep| (#[trigger] (sm.step_to_action)(step).precondition)((sm.action_input)(step, in2), c);
    assert(((sm.step_to_action)(st2).precondition)(in2, c));
    lemma_controller_action_pre_relabel(tc, r, model, id, in2, c, st2);
    assert(((sm.step_to_action)(st2).precondition)((sm.action_input)(st2, in1), c1));
    let st1 = choose |step: ControllerStep| (#[trigger] (sm.step_to_action)(step).precondition)((sm.action_input)(step, in1), c1);
    assert(((sm.step_to_action)(st1).precondition)(in1, c1));
    lemma_controller_action_pre_relabel(tc, r, model, id, in2, c, st1);
    assert(((sm.step_to_action)(st1).precondition)(in2, c));
    assert(st1 == st2) by {
        match (st1, st2) {
            (ControllerStep::RunScheduledReconcile, ControllerStep::RunScheduledReconcile) => {},
            (ControllerStep::ContinueReconcile, ControllerStep::ContinueReconcile) => {},
            (ControllerStep::EndReconcile, ControllerStep::EndReconcile) => {},
            _ => { assert(false); },
        }
    }
    let host2 = sm.next_result(in2, c);
    let host1 = sm.next_result(in1, c1);
    assert(host2 == ActionResult::Enabled(((sm.step_to_action)(st2).transition)(in2, c).0, ((sm.step_to_action)(st2).transition)(in2, c).1));
    assert(host1 == ActionResult::Enabled(((sm.step_to_action)(st2).transition)(in1, c1).0, ((sm.step_to_action)(st2).transition)(in1, c1).1));
    let in_flight = s.network.in_flight;
    let f_ongoing = |o: OngoingReconcile| relabel_ongoing(tc, r, o);
    let f_sched = |o: DynamicObjectView| relabel_obj(tc, r, o);
    let f_cae = |x: ControllerAndExternalState| relabel_cae(tc, r, x);
    match st2 {
        ControllerStep::RunScheduledReconcile => {
            let (alloc, rid) = c.reconcile_id_allocator.allocate();
            let init2 = OngoingReconcile { triggering_cr: c.scheduled_reconciles[key], pending_req_msg: None, local_state: (model.init)(), reconcile_id: rid };
            let init1 = OngoingReconcile { triggering_cr: c1.scheduled_reconciles[key], pending_req_msg: None, local_state: (model.init)(), reconcile_id: rid };
            assert(init1 == relabel_ongoing(tc, r, init2));
            lemma_map_values_insert(c.ongoing_reconciles, f_ongoing, key, init2);
            lemma_map_values_remove(c.scheduled_reconciles, f_sched, key);
            let c2_prime = host2->Enabled_0;
            assert(host1->Enabled_0 == relabel_controller(tc, r, c2_prime));
            lemma_add_empty(in_flight);
            lemma_add_empty(a.network.in_flight);
        },
        ControllerStep::ContinueReconcile => {
            let rs = c.ongoing_reconciles[key];
            assert(c1.ongoing_reconciles[key] == relabel_ongoing(tc, r, rs));
            let resp_o2 = if msg is Some {
                if msg->0.content is APIResponse { Some(ResponseContent::KubernetesResponse(msg->0.content->APIResponse_0)) }
                else { Some(ResponseContent::ExternalResponse(msg->0.content->ExternalResponse_0)) }
            } else { None };
            let resp_o1 = if msg1 is Some {
                if msg1->0.content is APIResponse { Some(ResponseContent::KubernetesResponse(msg1->0.content->APIResponse_0)) }
                else { Some(ResponseContent::ExternalResponse(msg1->0.content->ExternalResponse_0)) }
            } else { None };
            assert(resp_o1 == relabel_resp_content(tc, r, resp_o2));
            let t = model.transition;
            let (ls2, req_o2) = t(rs.triggering_cr, resp_o2, rs.local_state);
            assert(t(relabel_obj(tc, r, rs.triggering_cr), relabel_resp_content(tc, r, resp_o2), rs.local_state) == (ls2, relabel_req_content(tc, r, req_o2)));
            let (pending2, send2, alloc2) = if req_o2 is Some {
                let pending = match req_o2->0 {
                    RequestContent::KubernetesRequest(req) => Some(controller_req_msg(id, key, s.rpc_id_allocator.allocate().1, req)),
                    RequestContent::ExternalRequest(req) => Some(controller_external_req_msg(id, key, s.rpc_id_allocator.allocate().1, req)),
                };
                (pending, Multiset::singleton(pending->0), s.rpc_id_allocator.allocate().0)
            } else { (None::<Message>, Multiset::<Message>::empty(), s.rpc_id_allocator) };
            let rs2_prime = OngoingReconcile { pending_req_msg: pending2, local_state: ls2, ..rs };
            let rs1_prime = OngoingReconcile { pending_req_msg: relabel_opt_msg(tc, r, pending2), local_state: ls2, ..relabel_ongoing(tc, r, rs) };
            assert(rs1_prime == relabel_ongoing(tc, r, rs2_prime));
            lemma_map_values_insert(c.ongoing_reconciles, f_ongoing, key, rs2_prime);
            let c2_prime = host2->Enabled_0;
            assert(c2_prime == ControllerState { ongoing_reconciles: c.ongoing_reconciles.insert(key, rs2_prime), ..c });
            assert(host1->Enabled_0 == relabel_controller(tc, r, c2_prime));
            assert(host2->Enabled_1.send == send2);
            if msg is Some {
                lemma_relabel_msgs_contains(tc, r, in_flight, msg->0);
                lemma_relabel_msgs_remove(tc, r, in_flight, msg->0);
                if req_o2 is Some {
                    lemma_relabel_msgs_insert(tc, r, in_flight.remove(msg->0), pending2->0);
                } else {
                    lemma_add_empty(in_flight.remove(msg->0));
                    lemma_add_empty(a.network.in_flight.remove(msg1->0));
                }
            } else {
                if req_o2 is Some {
                    lemma_relabel_msgs_insert(tc, r, in_flight, pending2->0);
                } else {
                    lemma_add_empty(in_flight);
                    lemma_add_empty(a.network.in_flight);
                }
            }
            if req_o2 is Some && req_o2->0 is KubernetesRequest {
                assert(tc.request_ok(req_o2->0->KubernetesRequest_0));
            }
        },
        ControllerStep::EndReconcile => {
            lemma_map_values_remove(c.ongoing_reconciles, f_ongoing, key);
            let c2_prime = host2->Enabled_0;
            assert(host1->Enabled_0 == relabel_controller(tc, r, c2_prime));
            lemma_add_empty(in_flight);
            lemma_add_empty(a.network.in_flight);
        },
    }
    let cae2_prime = ControllerAndExternalState { controller: host2->Enabled_0, ..s.controller_and_externals[id] };
    lemma_map_values_insert(s.controller_and_externals, f_cae, id, cae2_prime);
    assert(a_prime.controller_and_externals == a.controller_and_externals.insert(id, relabel_cae(tc, r, cae2_prime)));
    assert(tc.cluster.controller_next().forward((id, msg1, key_o))(a, a_prime));
    assert forall |m: Message| #[trigger] s_prime.in_flight().contains(m) && m.content is APIRequest implies tc.request_ok(m.content->APIRequest_0) by {
        if !s.in_flight().contains(m) {
            assert(host2->Enabled_1.send.contains(m));
        }
    }
}

// ---------------------------------------------------------------------------
// Scheduling, the garbage collector, and the environment steps.
// ---------------------------------------------------------------------------

pub proof fn lemma_schedule_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, side: Side, input: (int, ObjectRef), uid_next: Uid, rv_next: ResourceVersion)
    requires
        inv(tc, s),
        tc.schedule_controller_reconcile(side).forward(input)(s, s_prime),
    ensures
        tc.cluster.schedule_controller_reconcile().forward(input)(abs(tc, r, s, uid_next, rv_next), abs(tc, r, s_prime, uid_next, rv_next)),
        inv(tc, s_prime),
        s_prime.primary == s.primary,
        s_prime.remote == s.remote,
{
    let id = input.0;
    let key = input.1;
    let a = abs(tc, r, s, uid_next, rv_next);
    let a_prime = abs(tc, r, s_prime, uid_next, rv_next);
    lemma_abs_store_index(tc, r, s, key);
    lemma_abs_controller(tc, r, s, id, uid_next, rv_next);
    let cae = s.controller_and_externals[id];
    let obj = s.store(side).resources[key];
    let f_sched = |o: DynamicObjectView| relabel_obj(tc, r, o);
    let f_cae = |x: ControllerAndExternalState| relabel_cae(tc, r, x);
    lemma_map_values_insert(cae.controller.scheduled_reconciles, f_sched, key, obj);
    let cae_prime = ControllerAndExternalState {
        controller: ControllerState { scheduled_reconciles: cae.controller.scheduled_reconciles.insert(key, obj), ..cae.controller },
        ..cae
    };
    lemma_map_values_insert(s.controller_and_externals, f_cae, id, cae_prime);
    assert(a_prime.controller_and_externals == a.controller_and_externals.insert(id, relabel_cae(tc, r, cae_prime)));
    assert(tc.cluster.schedule_controller_reconcile().forward(input)(a, a_prime));
}

pub proof fn lemma_builtin_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, side: Side, input: (BuiltinControllerChoice, ObjectRef), uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        inv(tc, s),
        tc.builtin_controllers_next(side).forward(input)(s, s_prime),
    ensures
        tc.cluster.builtin_controllers_next().forward(input)(abs(tc, r, s, uid_next, rv_next), abs(tc, r, s_prime, uid_next, rv_next)),
        inv(tc, s_prime),
        s_prime.primary == s.primary,
        s_prime.remote == s.remote,
{
    let key = input.1;
    let a = abs(tc, r, s, uid_next, rv_next);
    let a_prime = abs(tc, r, s_prime, uid_next, rv_next);
    let store = s.store(side).resources;
    let obj = store[key];
    lemma_abs_store_index(tc, r, s, key);
    lemma_relabel_obj_keeps_identity(tc, r, obj);
    let refs = obj.metadata.owner_references->0;
    let refs1 = relabel_obj(tc, r, obj).metadata.owner_references->0;
    assert(refs1 == refs.map_values(|x: OwnerReferenceView| relabel_owner_ref(tc, r, x)));
    assert forall |i: int| 0 <= i < refs1.len() implies ({
        let owner_key = owner_reference_to_object_reference(#[trigger] refs1[i], key.namespace);
        ||| !a.api_server.resources.contains_key(owner_key)
        ||| a.api_server.resources[owner_key].metadata.uid != Some(refs1[i].uid)
    }) by {
        let owner_key = owner_reference_to_object_reference(refs[i], key.namespace);
        assert(tc.side_of_kind(refs[i].kind) == side);
        assert(refs1[i] == relabel_owner_ref(tc, r, refs[i]));
        assert(owner_reference_to_object_reference(refs1[i], key.namespace) == owner_key);
        lemma_abs_store_index(tc, r, s, owner_key);
        if store.contains_key(owner_key) {
            let owner = store[owner_key];
            assert(tc.side_of_kind(owner.kind) == side);
            match owner.metadata.uid {
                Some(u) => { if (r.uid)(side, u) == (r.uid)(side, refs[i].uid) { assert(u == refs[i].uid); } },
                None => {},
            }
        }
    }
    let pre = PreconditionsView { uid: obj.metadata.uid, resource_version: None };
    let req = built_in_controller_req_msg(s.rpc_id_allocator.allocate().1, delete_req_msg_content(key, Some(pre)));
    let pre1 = PreconditionsView { uid: relabel_obj(tc, r, obj).metadata.uid, resource_version: None };
    let req1 = built_in_controller_req_msg(s.rpc_id_allocator.allocate().1, delete_req_msg_content(key, Some(pre1)));
    assert(req1 == relabel_msg(tc, r, req));
    lemma_relabel_msgs_insert(tc, r, s.network.in_flight, req);
    assert(tc.cluster.builtin_controllers_next().forward(input)(a, a_prime));
    assert forall |m: Message| #[trigger] s_prime.in_flight().contains(m) && m.content is APIRequest implies tc.request_ok(m.content->APIRequest_0) by {
        if m != req { assert(s.in_flight().contains(m)); }
    }
}

pub proof fn lemma_restart_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, input: int, uid_next: Uid, rv_next: ResourceVersion)
    requires
        inv(tc, s),
        tc.restart_controller().forward(input)(s, s_prime),
    ensures
        tc.cluster.restart_controller().forward(input)(abs(tc, r, s, uid_next, rv_next), abs(tc, r, s_prime, uid_next, rv_next)),
        inv(tc, s_prime),
        s_prime.primary == s.primary,
        s_prime.remote == s.remote,
{
    let id = input;
    let a = abs(tc, r, s, uid_next, rv_next);
    let a_prime = abs(tc, r, s_prime, uid_next, rv_next);
    lemma_abs_controller(tc, r, s, id, uid_next, rv_next);
    let cae = s.controller_and_externals[id];
    let f_cae = |x: ControllerAndExternalState| relabel_cae(tc, r, x);
    let cae_prime = ControllerAndExternalState {
        controller: ControllerState {
            scheduled_reconciles: Map::<ObjectRef, DynamicObjectView>::empty(),
            ongoing_reconciles: Map::<ObjectRef, OngoingReconcile>::empty(),
            reconcile_id_allocator: cae.controller.reconcile_id_allocator,
        },
        ..cae
    };
    lemma_map_values_empty::<ObjectRef, OngoingReconcile, OngoingReconcile>(|o: OngoingReconcile| relabel_ongoing(tc, r, o));
    lemma_map_values_empty::<ObjectRef, DynamicObjectView, DynamicObjectView>(|o: DynamicObjectView| relabel_obj(tc, r, o));
    lemma_map_values_insert(s.controller_and_externals, f_cae, id, cae_prime);
    assert(a_prime.controller_and_externals == a.controller_and_externals.insert(id, relabel_cae(tc, r, cae_prime)));
    assert(tc.cluster.restart_controller().forward(input)(a, a_prime));
}

pub proof fn lemma_disable_crash_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, input: int, uid_next: Uid, rv_next: ResourceVersion)
    requires
        inv(tc, s),
        tc.disable_crash().forward(input)(s, s_prime),
    ensures
        tc.cluster.disable_crash().forward(input)(abs(tc, r, s, uid_next, rv_next), abs(tc, r, s_prime, uid_next, rv_next)),
        inv(tc, s_prime),
        s_prime.primary == s.primary,
        s_prime.remote == s.remote,
{
    let id = input;
    let a = abs(tc, r, s, uid_next, rv_next);
    let a_prime = abs(tc, r, s_prime, uid_next, rv_next);
    lemma_abs_controller(tc, r, s, id, uid_next, rv_next);
    let cae = s.controller_and_externals[id];
    let f_cae = |x: ControllerAndExternalState| relabel_cae(tc, r, x);
    let cae_prime = ControllerAndExternalState { crash_enabled: false, ..cae };
    lemma_map_values_insert(s.controller_and_externals, f_cae, id, cae_prime);
    assert(a_prime.controller_and_externals == a.controller_and_externals.insert(id, relabel_cae(tc, r, cae_prime)));
    assert(tc.cluster.disable_crash().forward(input)(a, a_prime));
}

pub proof fn lemma_drop_req_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, input: (Message, APIError), uid_next: Uid, rv_next: ResourceVersion)
    requires
        inv(tc, s),
        tc.drop_req().forward(input)(s, s_prime),
    ensures
        tc.cluster.drop_req().forward((relabel_msg(tc, r, input.0), input.1))(abs(tc, r, s, uid_next, rv_next), abs(tc, r, s_prime, uid_next, rv_next)),
        inv(tc, s_prime),
        s_prime.primary == s.primary,
        s_prime.remote == s.remote,
{
    let msg = input.0;
    let err = input.1;
    let a = abs(tc, r, s, uid_next, rv_next);
    let a_prime = abs(tc, r, s_prime, uid_next, rv_next);
    let resp = form_matched_err_resp_msg(msg, err);
    lemma_err_resp_relabel(tc, r, msg, err);
    lemma_relabel_msgs_contains(tc, r, s.network.in_flight, msg);
    lemma_relabel_msgs_remove(tc, r, s.network.in_flight, msg);
    lemma_relabel_msgs_insert(tc, r, s.network.in_flight.remove(msg), resp);
    assert(tc.cluster.drop_req().forward((relabel_msg(tc, r, msg), err))(a, a_prime));
    assert forall |m: Message| #[trigger] s_prime.in_flight().contains(m) && m.content is APIRequest implies tc.request_ok(m.content->APIRequest_0) by {
        if m != resp { assert(s.in_flight().contains(m)); }
    }
}

pub proof fn lemma_disable_req_drop_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, uid_next: Uid, rv_next: ResourceVersion)
    requires
        inv(tc, s),
        tc.disable_req_drop().forward(())(s, s_prime),
    ensures
        tc.cluster.disable_req_drop().forward(())(abs(tc, r, s, uid_next, rv_next), abs(tc, r, s_prime, uid_next, rv_next)),
        inv(tc, s_prime),
        s_prime.primary == s.primary,
        s_prime.remote == s.remote,
{
}

pub proof fn lemma_disable_pod_monkey_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, uid_next: Uid, rv_next: ResourceVersion)
    requires
        inv(tc, s),
        tc.disable_pod_monkey().forward(())(s, s_prime),
    ensures
        tc.cluster.disable_pod_monkey().forward(())(abs(tc, r, s, uid_next, rv_next), abs(tc, r, s_prime, uid_next, rv_next)),
        inv(tc, s_prime),
        s_prime.primary == s.primary,
        s_prime.remote == s.remote,
{
}

pub proof fn lemma_stutter_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, uid_next: Uid, rv_next: ResourceVersion)
    requires
        inv(tc, s),
        tc.stutter().forward(())(s, s_prime),
    ensures
        tc.cluster.stutter().forward(())(abs(tc, r, s, uid_next, rv_next), abs(tc, r, s_prime, uid_next, rv_next)),
        inv(tc, s_prime),
        s_prime == s,
{
}

// A pod the monkey may write reads the same after relabeling.
pub proof fn lemma_pod_ok_fixed(tc: TwoCluster, r: Relabeling, pod: PodView)
    requires tc.pod_ok(pod),
    ensures relabel_obj(tc, r, pod.marshal()) == pod.marshal(),
{
}

pub proof fn lemma_pod_monkey_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, input: PodView, uid_next: Uid, rv_next: ResourceVersion)
    requires
        inv(tc, s),
        tc.pod_monkey_next().forward(input)(s, s_prime),
    ensures
        tc.cluster.pod_monkey_next().forward(input)(abs(tc, r, s, uid_next, rv_next), abs(tc, r, s_prime, uid_next, rv_next)),
        inv(tc, s_prime),
        s_prime.primary == s.primary,
        s_prime.remote == s.remote,
{
    let a = abs(tc, r, s, uid_next, rv_next);
    let a_prime = abs(tc, r, s_prime, uid_next, rv_next);
    let sm = tc.cluster.pod_monkey();
    let pin = PodMonkeyActionInput { pod: input, rpc_id_allocator: s.rpc_id_allocator };
    let st = choose |step: PodMonkeyStep| (#[trigger] (sm.step_to_action)(step).precondition)((sm.action_input)(step, pin), ());
    lemma_pod_ok_fixed(tc, r, input);
    let host = sm.next_result(pin, ());
    let sent = ((sm.step_to_action)(st).transition)(pin, ()).1.send;
    assert(host->Enabled_1.send == sent);
    let m = match st {
        PodMonkeyStep::CreatePod => pod_monkey_req_msg(s.rpc_id_allocator.allocate().1, create_req_msg_content(input.metadata.namespace->0, input.marshal())),
        PodMonkeyStep::UpdatePod => pod_monkey_req_msg(s.rpc_id_allocator.allocate().1, update_req_msg_content(input.metadata.namespace->0, input.metadata.name->0, input.marshal())),
        PodMonkeyStep::UpdatePodStatus => pod_monkey_req_msg(s.rpc_id_allocator.allocate().1, update_status_req_msg_content(input.metadata.namespace->0, input.metadata.name->0, input.marshal())),
        PodMonkeyStep::DeletePod => pod_monkey_req_msg(s.rpc_id_allocator.allocate().1, delete_req_msg_content(input.object_ref(), None)),
    };
    assert(sent == Multiset::singleton(m));
    assert(relabel_msg(tc, r, m) == m);
    assert(tc.request_ok(m.content->APIRequest_0));
    lemma_relabel_msgs_insert(tc, r, s.network.in_flight, m);
    assert(tc.cluster.pod_monkey_next().forward(input)(a, a_prime));
    assert forall |mm: Message| #[trigger] s_prime.in_flight().contains(mm) && mm.content is APIRequest implies tc.request_ok(mm.content->APIRequest_0) by {
        if mm != m { assert(s.in_flight().contains(mm)); }
    }
}

// ---------------------------------------------------------------------------
// Every step.
// ---------------------------------------------------------------------------

pub proof fn lemma_next_step(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, side: Side, step: Step, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        models_ok(tc),
        models_commute(tc, r),
        inv(tc, s),
        tc.next_step(s, s_prime, side, step),
        step_compatible(tc, r, s, s_prime, uid_next, rv_next),
    ensures
        tc.cluster.next_step(
            abs(tc, r, s, uid_next, rv_next),
            abs(tc, r, s_prime, uid_next_after(s, s_prime, uid_next), rv_next_after(s, s_prime, rv_next)),
            relabel_step(tc, r, step)
        ),
        inv(tc, s_prime),
        counters_step(s, s_prime),
{
    match step {
        Step::APIServerStep(input) => { lemma_api_server_step(tc, r, s, s_prime, side, input, uid_next, rv_next); },
        Step::BuiltinControllersStep(input) => { lemma_builtin_step(tc, r, s, s_prime, side, input, uid_next, rv_next); },
        Step::ControllerStep(input) => { lemma_controller_step(tc, r, s, s_prime, input, uid_next, rv_next); },
        Step::ScheduleControllerReconcileStep(input) => { lemma_schedule_step(tc, r, s, s_prime, side, input, uid_next, rv_next); },
        Step::RestartControllerStep(input) => { lemma_restart_step(tc, r, s, s_prime, input, uid_next, rv_next); },
        Step::DisableCrashStep(input) => { lemma_disable_crash_step(tc, r, s, s_prime, input, uid_next, rv_next); },
        Step::DropReqStep(input) => { lemma_drop_req_step(tc, r, s, s_prime, input, uid_next, rv_next); },
        Step::DisableReqDropStep => { lemma_disable_req_drop_step(tc, r, s, s_prime, uid_next, rv_next); },
        Step::PodMonkeyStep(input) => { lemma_pod_monkey_step(tc, r, s, s_prime, input, uid_next, rv_next); },
        Step::DisablePodMonkeyStep => { lemma_disable_pod_monkey_step(tc, r, s, s_prime, uid_next, rv_next); },
        Step::ExternalStep(input) => {
            // No controller has an external system, so this step is never enabled.
            assert(tc.cluster.controller_models.contains_key(input.0));
            assert(false);
        },
        Step::StutterStep => { lemma_stutter_step(tc, r, s, s_prime, uid_next, rv_next); },
    }
}

}
