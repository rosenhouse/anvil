// R3: the janitor eventually removes a mirror object whose parent is gone for good.
//
// For a mirror object (key `key`, parent uid `parent_uid`, uid `uid`):
//     always(parent_absent(k, key, parent_uid)) /\ mirror_object_is(inner_kind(k, b), key, parent_uid, uid)
//         ~> object_is_gone(key, uid)
//
// The proof is per object. It first turns the premise into a stable predicate
// (the object is there as that mirror, or it is gone: nothing else can happen to
// it under the rely; the step lemma is in api_actions.rs), then, under that and
// the eventual facts of section "phases", walks the janitor's state machine: idle ~> scheduled ~> Init ~> List
// sent ~> List answered ~> Delete sent ~> object removed or terminating; D3 turns
// terminating into removed.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
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
    model::{install::*, janitor_reconciler, sync_reconciler, janitor_reconciler::WidgetJanitorReconcileState},
    proof::{
        guarantee::*, helper_invariants::*, janitor_invariants::*,
        liveness::{api_actions::*, spec::*, terminate},
        predicate::*, sync_invariants::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The states of the walk.
// ---------------------------------------------------------------------------

// The janitor is at `step` on a reconcile of the mirror object.
pub open spec fn janitor_at_step_for(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid, step: WidgetJanitorStepView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& snapshot_of_mirror(k, b, s.ongoing_reconciles(controller_id)[key].triggering_cr, key, parent_uid, uid)
        &&& WidgetJanitorReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state)->Ok_0.reconcile_step == step
    }
}

pub open spec fn janitor_list_req_msg(k: SyncKind, controller_id: int, key: ObjectRef, msg: Message) -> bool {
    &&& msg.src == HostId::Controller(controller_id, key)
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& msg.content.is_list_request()
    &&& msg.content.get_list_request() == janitor_list_request(k, key)
}

pub open spec fn janitor_delete_req_msg(controller_id: int, key: ObjectRef, uid: Uid, msg: Message) -> bool {
    &&& msg.src == HostId::Controller(controller_id, key)
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& msg.content.is_delete_request()
    &&& msg.content.get_delete_request() == DeleteRequest {
        key: key,
        preconditions: Some(PreconditionsView { uid: Some(uid), resource_version: None }),
    }
}

// The states of the walk.
pub open spec fn st_idle(controller_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    Cluster::reconcile_idle(controller_id, key)
}

pub open spec fn st_scheduled(controller_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
    }
}

pub open spec fn st_init(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& janitor_at_step_for(k, b, controller_id, key, parent_uid, uid, WidgetJanitorStepView::Init)(s)
        &&& Cluster::no_pending_req_msg(controller_id, s, key)
    }
}

pub open spec fn st_list_req_in_flight(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& janitor_at_step_for(k, b, controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterListOuter)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& janitor_list_req_msg(k, controller_id, key, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_list_req_msg_in_flight(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& janitor_at_step_for(k, b, controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterListOuter)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg)
        &&& janitor_list_req_msg(k, controller_id, key, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn ok_list_resp_for(resp: Message, msg: Message) -> bool {
    &&& resp_msg_matches_req_msg(resp, msg)
    &&& resp.content.get_list_response().res is Ok
}

pub open spec fn st_list_resp_in_flight(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& janitor_at_step_for(k, b, controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterListOuter)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& janitor_list_req_msg(k, controller_id, key, msg)
        &&& exists |resp: Message| #[trigger] s.in_flight().contains(resp) && ok_list_resp_for(resp, msg)
    }
}

pub open spec fn st_list_resp_msg_in_flight(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid, resp: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& janitor_at_step_for(k, b, controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterListOuter)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& janitor_list_req_msg(k, controller_id, key, msg)
        &&& s.in_flight().contains(resp)
        &&& ok_list_resp_for(resp, msg)
    }
}

pub open spec fn st_delete_req_in_flight(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& janitor_at_step_for(k, b, controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterDeleteInner)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& janitor_delete_req_msg(controller_id, key, uid, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_delete_req_msg_in_flight(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& janitor_at_step_for(k, b, controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterDeleteInner)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg)
        &&& janitor_delete_req_msg(controller_id, key, uid, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_terminating(k: SyncKind, key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    inner_terminating_object(k, key, uid)
}

// ---------------------------------------------------------------------------
// Eventual facts (the phases).
// ---------------------------------------------------------------------------

// Phase II, per object: the scheduled snapshot for the key is the mirror object
// (or the object is gone); requests and responses of the janitor's reconcile on
// the key are consistent; every List response the janitor holds for the key was
// answered after the parent went absent, so it does not list the parent.
pub open spec fn scheduled_snapshot_ok(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.scheduled_reconciles(controller_id).contains_key(key)
            ==> snapshot_of_mirror(k, b, s.scheduled_reconciles(controller_id)[key], key, parent_uid, uid)
    }
}

pub open spec fn list_responses_are_fresh(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let reconcile = s.ongoing_reconciles(controller_id)[key];
        let step = WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
        s.ongoing_reconciles(controller_id).contains_key(key)
        && step is AfterListOuter
        && snapshot_is_mirror(inner_kind(k, b), reconcile.triggering_cr)
        && snapshot_parent(inner_kind(k, b), reconcile.triggering_cr) == int_to_string_view(parent_uid)
        && reconcile.pending_req_msg is Some
        ==> forall |resp: Message| {
            &&& #[trigger] s.in_flight().contains(resp)
            &&& ok_list_resp_for(resp, reconcile.pending_req_msg->0)
        } ==> !janitor_reconciler::parent_listed(k, b, resp.content.get_list_response().res->Ok_0, int_to_string_view(parent_uid))
    }
}

pub open spec fn scheduled_ok_or_gone(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| scheduled_snapshot_ok(k, b, controller_id, key, parent_uid, uid)(s) || gone(key, uid)(s)
}

pub open spec fn phase_ii(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid)(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& list_responses_are_fresh(k, b, controller_id, key, parent_uid)(s)
    }
}

// Once the mirror object is there it stays there as that mirror until it is
// removed, and it never comes back.
pub proof fn lemma_mirror_leads_to_always_present_or_gone(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    spec: TempPred<ClusterState>, cluster: Cluster, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))))),
        spec.entails(always(lift_state(every_mirror_is_bound(k, b)))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity(k)))),
    ensures spec.entails(lift_state(mirror_object_is(inner_kind(k, b), key, parent_uid, uid)).leads_to(always(lift_state(present_or_gone(k, b, key, parent_uid, uid))))),
{
    let post = present_or_gone(k, b, key, parent_uid, uid);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s_prime)
        &&& every_mirror_is_bound(k, b)(s)
        &&& every_in_flight_inner_update_preserves_identity(k)(s)
    };
    always_to_always_later(spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_to_always_later(spec, lift_state(cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        later(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        later(lift_state(cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b)))),
        lift_state(every_mirror_is_bound(k, b)),
        lift_state(every_in_flight_inner_update_preserves_identity(k))
    );
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        if mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s) {
            lemma_mirror_object_after_step(k, b, spec_ok, cluster, s, s_prime, key, parent_uid, uid);
        } else {
            lemma_next_only_grows_by_fresh_uids(cluster, s, s_prime);
            lemma_gone_is_stable(k, b, key, uid, s, s_prime);
        }
    }
    entails_implies_leads_to(spec, lift_state(mirror_object_is(inner_kind(k, b), key, parent_uid, uid)), lift_state(post));
    leads_to_stable(spec, lift_action(stronger_next), lift_state(mirror_object_is(inner_kind(k, b), key, parent_uid, uid)), lift_state(post));
}

// ---------------------------------------------------------------------------
// Phase II (a): the scheduled snapshot for the key is the mirror object.
// ---------------------------------------------------------------------------

// Scheduling copies the stored object; while the mirror is there, that is the
// mirror. The schedule action is always enabled while the object exists, so no
// termination argument is needed.
pub proof fn lemma_true_leads_to_always_scheduled_ok_or_gone(k: SyncKind, b: Binding, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(present_or_gone(k, b, key, parent_uid, uid)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid))))),
{
    let ok = scheduled_snapshot_ok(k, b, controller_id, key, parent_uid, uid);
    let q = present_or_gone(k, b, key, parent_uid, uid);
    let post = scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid);
    let pre = |s: ClusterState| mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s) && !ok(s);
    let q_and_post = |s: ClusterState| q(s) && post(s);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& q(s)
        &&& q(s_prime)
    };
    always_to_always_later(spec, lift_state(q));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(q),
        later(lift_state(q))
    );
    // What a schedule step of the key writes while the mirror is there.
    assert forall |s: ClusterState| mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s) && Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    implies #[trigger] snapshot_of_mirror(k, b, s.resources()[key], key, parent_uid, uid) by {
        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        assert(q(s_prime));
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.schedule_controller_reconcile().forward((controller_id, key))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
        assert(snapshot_of_mirror(k, b, s.resources()[key], key, parent_uid, uid));
        assert(ok(s_prime));
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.schedule_controller_reconcile().pre((controller_id, key))(s) by {
        assert(s.resources().contains_key(key));
        assert(cluster.controller_models.contains_key(controller_id));
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, key, stronger_next, pre, post);
    entails_implies_leads_to(spec, lift_state(q_and_post), lift_state(post));
    or_leads_to(spec, lift_state(pre), lift_state(q_and_post), lift_state(post));
    temp_pred_equality(true_pred().and(lift_state(q)), lift_state(pre).or(lift_state(q_and_post)));
    leads_to_by_borrowing_inv(spec, true_pred(), lift_state(post), lift_state(q));
    // Stability: a schedule step rewrites the snapshot from the store, running the
    // scheduled reconcile removes it, and nothing else touches it.
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        lemma_next_only_grows_by_fresh_uids(cluster, s, s_prime);
        if gone(key, uid)(s) {
            lemma_gone_is_stable(k, b, key, uid, s, s_prime);
        } else {
            assert(mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s));
            assert(ok(s));
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ScheduleControllerReconcileStep(input) => {
                    if input.0 == controller_id && input.1 == key {
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
                        assert(snapshot_of_mirror(k, b, s.resources()[key], key, parent_uid, uid));
                        assert(ok(s_prime));
                    } else {
                        if s_prime.scheduled_reconciles(controller_id).contains_key(key) {
                            assert(s.scheduled_reconciles(controller_id).contains_key(key));
                            assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                        }
                        assert(ok(s_prime));
                    }
                },
                _ => {
                    if s_prime.scheduled_reconciles(controller_id).contains_key(key) {
                        assert(s.scheduled_reconciles(controller_id).contains_key(key));
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                    }
                    assert(ok(s_prime));
                },
            }
        }
    }
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(post));
}

// ---------------------------------------------------------------------------
// Phase II (c): every List response the janitor holds for the key was answered
// after the parent went absent.
// ---------------------------------------------------------------------------

// A List answered while the parent is absent (and its uid string is bound to the
// outer key) does not list the parent.
pub proof fn lemma_list_answered_while_parent_absent(k: SyncKind, b: Binding, s: ClusterState, req: ListRequest, key: ObjectRef, parent_uid: Uid)
    requires
        k.bindings.contains(b),
        parent_absent(k, key, parent_uid)(s),
        parent_uid_string_is_bound_to_key(int_to_string_view(parent_uid), outer_key_of(k, key))(s),
    ensures !janitor_reconciler::parent_listed(k, b, handle_list_request(req, s.api_server).res->Ok_0, int_to_string_view(parent_uid)),
{
    let parent = int_to_string_view(parent_uid);
    let selected = s.resources().values().filter(|o: DynamicObjectView| {
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    });
    let objs = selected.to_seq();
    assert(handle_list_request(req, s.api_server).res->Ok_0 == objs);
    if janitor_reconciler::parent_listed(k, b, objs, parent) {
        let i = choose |i: int| 0 <= i < objs.len()
            && (#[trigger] objs[i]).kind == k.outer_kind
            && objs[i].metadata.uid is Some
            && int_to_string_view(objs[i].metadata.uid->0) == parent
            && cluster_of_dynamic(k.selector, objs[i]) == Some(b.name);
        let o = objs[i];
        assert(objs.contains(o));
        lemma_set_to_seq_contains_all_elements(selected);
        assert(selected.contains(o));
        assert(s.resources().values().contains(o));
        let okey = choose |okey: ObjectRef| #[trigger] s.resources().dom().contains(okey) && s.resources()[okey] == o;
        assert(s.resources().contains_key(okey));
        assert(okey == outer_key_of(k, key));
        int_to_string_view_injectivity();
        assert(o.metadata.uid->0 == parent_uid);
        assert(false);
    }
}

pub proof fn lemma_list_responses_are_fresh_preserved(k: SyncKind, b: Binding, 
    cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, s: ClusterState, s_prime: ClusterState
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        cluster.next()(s, s_prime),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        Cluster::crash_disabled(controller_id)(s),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)(s),
        janitor_triggering_crs_are_sound(k, b, controller_id)(s),
        janitor_decisions_are_sound(k, b, controller_id)(s),
        parent_absent(k, key, parent_uid)(s),
        list_responses_are_fresh(k, b, controller_id, key, parent_uid)(s),
    ensures list_responses_are_fresh(k, b, controller_id, key, parent_uid)(s_prime),
{
    let parent = int_to_string_view(parent_uid);
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    unmarshal_of_marshal();
    if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
        let reconcile_prime = s_prime.ongoing_reconciles(controller_id)[key];
        let step_prime = WidgetJanitorReconcileState::unmarshal(reconcile_prime.local_state)->Ok_0.reconcile_step;
        if step_prime is AfterListOuter
            && snapshot_is_mirror(inner_kind(k, b), reconcile_prime.triggering_cr)
            && snapshot_parent(inner_kind(k, b), reconcile_prime.triggering_cr) == parent
            && reconcile_prime.pending_req_msg is Some
        {
            let pending = reconcile_prime.pending_req_msg->0;
            assert forall |resp: Message| {
                &&& #[trigger] s_prime.in_flight().contains(resp)
                &&& ok_list_resp_for(resp, pending)
            } implies !janitor_reconciler::parent_listed(k, b, resp.content.get_list_response().res->Ok_0, parent) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        let msg = input->0;
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        let reconcile = s.ongoing_reconciles(controller_id)[key];
                        assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
                        assert(pending.content.is_list_request());
                        if !s.in_flight().contains(resp) {
                            assert(resp == transition_by_etcd(cluster.installed_types, msg, s.api_server).1);
                            assert(resp.content->APIResponse_0 is ListResponse);
                            match msg.content->APIRequest_0 {
                                APIRequest::ListRequest(req) => {
                                    assert(resp.content.get_list_response() == handle_list_request(req, s.api_server));
                                    assert(janitor_snapshot_is_sound(k, b, reconcile.triggering_cr, key)(s));
                                    assert(parent_uid_string_is_bound_to_key(parent, outer_key_of(k, key))(s));
                                    lemma_list_answered_while_parent_absent(k, b, s, req, key, parent_uid);
                                },
                                _ => {
                                    assert(false);
                                },
                            }
                        }
                    },
                    Step::ControllerStep(input) => {
                        if input.0 == controller_id && input.2 == Some(key) {
                            assert(s.ongoing_reconciles(controller_id).contains_key(key));
                            let reconcile = s.ongoing_reconciles(controller_id)[key];
                            let step_s = WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
                            if reconcile_prime == reconcile {
                                // Unchanged; the step added a request, not a response.
                                assert(s_prime.in_flight().contains(resp) && !s.in_flight().contains(resp) ==> false);
                            } else {
                                // The only transition into AfterListOuter is from Init and sends
                                // the List with a fresh rpc id, so no response matches it yet.
                                assert(step_s is Init);
                                assert(pending.rpc_id == s.rpc_id_allocator.rpc_id_counter);
                                assert(resp.rpc_id == pending.rpc_id);
                                if s.in_flight().contains(resp) {
                                    assert(resp.rpc_id < s.rpc_id_allocator.rpc_id_counter);
                                    assert(false);
                                } else {
                                    assert(resp == pending);
                                    assert(false);
                                }
                            }
                        } else {
                            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                            if !s.in_flight().contains(resp) {
                                assert(resp.content is APIRequest || resp.content is ExternalRequest);
                                assert(false);
                            }
                        }
                    },
                    Step::DropReqStep(input) => {
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
                        assert(pending.content.is_list_request());
                        if !s.in_flight().contains(resp) {
                            assert(resp == form_matched_err_resp_msg(input.0, input.1));
                            match input.0.content->APIRequest_0 {
                                APIRequest::ListRequest(_) => {
                                    assert(resp.content.get_list_response().res is Err);
                                },
                                _ => {
                                    assert(!(resp.content->APIResponse_0 is ListResponse));
                                },
                            }
                            assert(false);
                        }
                    },
                    Step::ExternalStep(input) => {
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        if !s.in_flight().contains(resp) {
                            assert(resp.content is ExternalResponse);
                            assert(false);
                        }
                    },
                    Step::RestartControllerStep(id) => {
                        assert(id != controller_id);
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        assert(s_prime.in_flight() == s.in_flight());
                    },
                    _ => {
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        if !s.in_flight().contains(resp) {
                            assert(resp.content is APIRequest);
                            assert(false);
                        }
                    },
                }
            }
        }
    }
}

pub proof fn lemma_true_leads_to_always_list_responses_are_fresh(k: SyncKind, b: Binding, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)))),
        spec.entails(always(lift_state(janitor_triggering_crs_are_sound(k, b, controller_id)))),
        spec.entails(always(lift_state(janitor_decisions_are_sound(k, b, controller_id)))),
        spec.entails(always(lift_state(parent_absent(k, key, parent_uid)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(list_responses_are_fresh(k, b, controller_id, key, parent_uid))))),
{
    let post = list_responses_are_fresh(k, b, controller_id, key, parent_uid);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)(s)
        &&& janitor_triggering_crs_are_sound(k, b, controller_id)(s)
        &&& janitor_decisions_are_sound(k, b, controller_id)(s)
        &&& parent_absent(k, key, parent_uid)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)),
        lift_state(janitor_triggering_crs_are_sound(k, b, controller_id)),
        lift_state(janitor_decisions_are_sound(k, b, controller_id)),
        lift_state(parent_absent(k, key, parent_uid))
    );
    entails_implies_leads_to(spec, lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    leads_to_trans(spec, true_pred(), lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        lemma_list_responses_are_fresh_preserved(k, b, cluster, controller_id, key, parent_uid, s, s_prime);
    }
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(post));
}

// ---------------------------------------------------------------------------
// The walk through the janitor's reconcile, one step per lemma. Each step is a
// WF1 application; "or gone" absorbs the removal of the object by anyone else.
// ---------------------------------------------------------------------------

// idle ~> scheduled \/ gone: the schedule action is enabled while the object exists.
pub proof fn lemma_idle_leads_to_scheduled_or_gone(k: SyncKind, b: Binding, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(present_or_gone(k, b, key, parent_uid, uid)))),
    ensures
        spec.entails(lift_state(st_idle(controller_id, key))
            .leads_to(lift_state(st_scheduled(controller_id, key)).or(lift_state(gone(key, uid))))),
{
    let q = present_or_gone(k, b, key, parent_uid, uid);
    let idle = st_idle(controller_id, key);
    let scheduled = st_scheduled(controller_id, key);
    let g = gone(key, uid);
    let pre = |s: ClusterState| idle(s) && !scheduled(s) && mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s);
    let post = |s: ClusterState| scheduled(s) || g(s);
    let idle_q_post = |s: ClusterState| idle(s) && q(s) && post(s);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& q(s_prime)
    };
    always_to_always_later(spec, lift_state(q));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        later(lift_state(q))
    );
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        if !g(s_prime) {
            assert(mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s_prime));
            if !scheduled(s_prime) {
                // No scheduled reconcile of the key means none can start.
                assert(!s_prime.ongoing_reconciles(controller_id).contains_key(key));
            }
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.schedule_controller_reconcile().forward((controller_id, key))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.scheduled_reconciles(controller_id).contains_key(key));
        assert(!s_prime.ongoing_reconciles(controller_id).contains_key(key));
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.schedule_controller_reconcile().pre((controller_id, key))(s) by {
        assert(s.resources().contains_key(key));
        assert(cluster.controller_models.contains_key(controller_id));
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, key, stronger_next, pre, post);
    entails_implies_leads_to(spec, lift_state(idle_q_post), lift_state(post));
    or_leads_to(spec, lift_state(pre), lift_state(idle_q_post), lift_state(post));
    temp_pred_equality(lift_state(idle).and(lift_state(q)), lift_state(pre).or(lift_state(idle_q_post)));
    leads_to_by_borrowing_inv(spec, lift_state(idle), lift_state(post), lift_state(q));
    temp_pred_equality(lift_state(post), lift_state(scheduled).or(lift_state(g)));
}

// scheduled ~> Init \/ gone: running the scheduled reconcile copies the snapshot.
pub proof fn lemma_scheduled_leads_to_init_or_gone(k: SyncKind, b: Binding, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid)))),
    ensures
        spec.entails(lift_state(st_scheduled(controller_id, key))
            .leads_to(lift_state(st_init(k, b, controller_id, key, parent_uid, uid)).or(lift_state(gone(key, uid))))),
{
    let pre = st_scheduled(controller_id, key);
    let init = st_init(k, b, controller_id, key, parent_uid, uid);
    let g = gone(key, uid);
    let post = |s: ClusterState| init(s) || g(s);
    let input = (None::<Message>, Some(key));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid))
    );
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        lemma_next_only_grows_by_fresh_uids(cluster, s, s_prime);
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
            // The scheduled reconcile of the key was run.
            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is None);
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == janitor_reconciler::reconcile_init_state().marshal());
            if g(s) {
                lemma_gone_is_stable(k, b, key, uid, s, s_prime);
            } else {
                assert(scheduled_snapshot_ok(k, b, controller_id, key, parent_uid, uid)(s));
                assert(init(s_prime));
            }
        } else {
            assert(pre(s_prime));
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        lemma_next_only_grows_by_fresh_uids(cluster, s, s_prime);
        assert(s_prime.ongoing_reconciles(controller_id).contains_key(key));
        assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is None);
        assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == janitor_reconciler::reconcile_init_state().marshal());
        if g(s) {
            lemma_gone_is_stable(k, b, key, uid, s, s_prime);
        } else {
            assert(scheduled_snapshot_ok(k, b, controller_id, key, parent_uid, uid)(s));
            assert(init(s_prime));
        }
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::RunScheduledReconcile, (controller_id, input.0, input.1))(s) by {
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, pre, post);
    temp_pred_equality(lift_state(post), lift_state(init).or(lift_state(g)));
}

// Init ~> the List is in flight.
pub proof fn lemma_init_leads_to_list_req_in_flight(k: SyncKind, b: Binding, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
    ensures
        spec.entails(lift_state(st_init(k, b, controller_id, key, parent_uid, uid))
            .leads_to(lift_state(st_list_req_in_flight(k, b, controller_id, key, parent_uid, uid)))),
{
    let pre = st_init(k, b, controller_id, key, parent_uid, uid);
    let post = st_list_req_in_flight(k, b, controller_id, key, parent_uid, uid);
    let input = (None::<Message>, Some(key));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id))
    );
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    unmarshal_of_marshal();
    // What the janitor sends from Init on a mirror snapshot.
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        let inner = unmarshal(inner_kind(k, b), cr)->Ok_0;
        assert(has_mirror_identity(inner));
        assert(inner.metadata.namespace->0 == key.namespace);
        let req = APIRequest::ListRequest(ListRequest { kind: k.outer_kind, namespace: inner.metadata.namespace->0 });
        let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
        assert(s_prime.in_flight().contains(msg));
        assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == janitor_reconciler::at_step(WidgetJanitorStepView::AfterListOuter).marshal());
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(i) => {
                if i.0 == controller_id && i.2 == Some(key) {
                    // Only the input (None, Some(key)) is enabled at Init without a pending request.
                    assert(i.1 is None);
                    assert(cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime));
                } else {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                }
            },
            _ => {
                assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            },
        }
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::ContinueReconcile, (controller_id, input.0, input.1))(s) by {
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post);
}

// The List in flight ~> an Ok List response in flight.
pub proof fn lemma_list_req_leads_to_list_resp(k: SyncKind, b: Binding, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)))),
    ensures
        spec.entails(lift_state(st_list_req_in_flight(k, b, controller_id, key, parent_uid, uid))
            .leads_to(lift_state(st_list_resp_in_flight(k, b, controller_id, key, parent_uid, uid)))),
{
    let post = st_list_resp_in_flight(k, b, controller_id, key, parent_uid, uid);
    let pre_of = |msg: Message| lift_state(st_list_req_msg_in_flight(k, b, controller_id, key, parent_uid, uid, msg));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key))
    );
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_list_req_msg_in_flight(k, b, controller_id, key, parent_uid, uid, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            let resp = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
            assert(s_prime.in_flight().contains(resp));
            assert(resp_msg_matches_req_msg(resp, msg));
            assert(resp.content.get_list_response().res is Ok);
            assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
            assert(ok_list_resp_for(resp, msg));
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(i) => {
                    if i->0 == msg {
                        assert(post(s_prime));
                    } else {
                        assert(s_prime.in_flight().contains(msg));
                        assert(pre(s_prime));
                    }
                },
                Step::ControllerStep(i) => {
                    if i.0 == controller_id && i.2 == Some(key) {
                        // The request is in flight, so no response to it is: the janitor cannot step.
                        assert(i.1 is Some);
                        assert(s.in_flight().contains(i.1->0) && resp_msg_matches_req_msg(i.1->0, msg));
                        assert(false);
                    } else {
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        assert(s_prime.in_flight().contains(msg));
                        assert(pre(s_prime));
                    }
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(pre(s_prime));
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    assert(s_prime.in_flight().contains(msg));
                    assert(pre(s_prime));
                },
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_list_req_in_flight(k, b, controller_id, key, parent_uid, uid)), {
        assert forall |ex| #[trigger] lift_state(st_list_req_in_flight(k, b, controller_id, key, parent_uid, uid)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let msg = ex.head().ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_list_req_in_flight(k, b, controller_id, key, parent_uid, uid)));
    });
}

// An Ok List response in flight ~> the Delete is in flight. The response was
// answered while the parent was absent (phase II), so the janitor deletes.
pub proof fn lemma_list_resp_leads_to_delete_req_in_flight(k: SyncKind, b: Binding, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(list_responses_are_fresh(k, b, controller_id, key, parent_uid)))),
    ensures
        spec.entails(lift_state(st_list_resp_in_flight(k, b, controller_id, key, parent_uid, uid))
            .leads_to(lift_state(st_delete_req_in_flight(k, b, controller_id, key, parent_uid, uid)))),
{
    let post = st_delete_req_in_flight(k, b, controller_id, key, parent_uid, uid);
    let pre_of = |resp: Message| lift_state(st_list_resp_msg_in_flight(k, b, controller_id, key, parent_uid, uid, resp));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& list_responses_are_fresh(k, b, controller_id, key, parent_uid)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(list_responses_are_fresh(k, b, controller_id, key, parent_uid))
    );
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    unmarshal_of_marshal();
    assert forall |resp: Message| spec.entails(#[trigger] pre_of(resp).leads_to(lift_state(post))) by {
        let pre = st_list_resp_msg_in_flight(k, b, controller_id, key, parent_uid, uid, resp);
        let input = (Some(resp), Some(key));
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
            let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
            let inner = unmarshal(inner_kind(k, b), cr)->Ok_0;
            let objs = resp.content.get_list_response().res->Ok_0;
            assert(has_mirror_identity(inner));
            assert(parent_uid_annotation(inner) == int_to_string_view(parent_uid));
            assert(!janitor_reconciler::parent_listed(k, b, objs, int_to_string_view(parent_uid)));
            assert(inner.object_ref() == key);
            assert(inner.metadata.uid == Some(uid));
            let req = APIRequest::DeleteRequest(DeleteRequest {
                key: inner.object_ref(),
                preconditions: Some(PreconditionsView::default().with_uid_from_object_meta(inner.metadata)),
            });
            let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
            assert(s_prime.in_flight().contains(msg));
            assert(janitor_delete_req_msg(controller_id, key, uid, msg));
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == janitor_reconciler::at_step(WidgetJanitorStepView::AfterDeleteInner).marshal());
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            let pending = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(i) => {
                    if i.0 == controller_id && i.2 == Some(key) {
                        // The janitor consumes a response to its List; by uniqueness of ids it is this one.
                        assert(i.1 is Some);
                        let other = i.1->0;
                        assert(s.in_flight().contains(other) && resp_msg_matches_req_msg(other, pending));
                        assert(other.rpc_id == resp.rpc_id);
                        assert(other == resp);
                        assert(cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime));
                    } else {
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        // Another reconcile can only consume a response addressed to it.
                        if !s_prime.in_flight().contains(resp) {
                            assert(i.1 == Some(resp));
                            assert(resp.dst == HostId::Controller(controller_id, key));
                            assert(resp.dst == HostId::Controller(i.0, i.2->0));
                            assert(false);
                        }
                        assert(pre(s_prime));
                    }
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(pre(s_prime));
                },
                Step::APIServerStep(i) => {
                    assert(i->0 != resp);
                    assert(s_prime.in_flight().contains(resp));
                    assert(pre(s_prime));
                },
                Step::DropReqStep(i) => {
                    assert(i.0 != resp);
                    assert(s_prime.in_flight().contains(resp));
                    assert(pre(s_prime));
                },
                Step::ExternalStep(i) => {
                    assert(i.1 != Some(resp));
                    assert(s_prime.in_flight().contains(resp));
                    assert(pre(s_prime));
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    assert(s_prime.in_flight().contains(resp));
                    assert(pre(s_prime));
                },
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::ContinueReconcile, (controller_id, input.0, input.1))(s) by {
            assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
            assert(resp.content is APIResponse);
        }
        cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_list_resp_in_flight(k, b, controller_id, key, parent_uid, uid)), {
        assert forall |ex| #[trigger] lift_state(st_list_resp_in_flight(k, b, controller_id, key, parent_uid, uid)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            let resp = choose |resp: Message| #[trigger] s.in_flight().contains(resp) && ok_list_resp_for(resp, msg);
            assert(pre_of(resp).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_list_resp_in_flight(k, b, controller_id, key, parent_uid, uid)));
    });
}

// The Delete in flight ~> the object is terminating or gone.
pub proof fn lemma_delete_req_leads_to_terminating_or_gone(k: SyncKind, b: Binding, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)))),
        spec.entails(always(lift_state(present_or_gone(k, b, key, parent_uid, uid)))),
    ensures
        spec.entails(lift_state(st_delete_req_in_flight(k, b, controller_id, key, parent_uid, uid))
            .leads_to(lift_state(st_terminating(k, key, uid)).or(lift_state(gone(key, uid))))),
{
    let g = gone(key, uid);
    let post = |s: ClusterState| st_terminating(k, key, uid)(s) || g(s);
    let pre_of = |msg: Message| lift_state(st_delete_req_msg_in_flight(k, b, controller_id, key, parent_uid, uid, msg));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& present_or_gone(k, b, key, parent_uid, uid)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)),
        lift_state(present_or_gone(k, b, key, parent_uid, uid))
    );
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_delete_req_msg_in_flight(k, b, controller_id, key, parent_uid, uid, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
            if g(s) {
                lemma_gone_is_stable(k, b, key, uid, s, s_prime);
            } else {
                assert(mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s));
                assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                let req = msg.content.get_delete_request();
                assert(req.key == key);
                assert(delete_request_admission_check(req, s.api_server) is None);
                let obj = s.resources()[key];
                if obj.metadata.finalizers is Some && obj.metadata.finalizers->0.len() > 0 {
                    assert(s_prime.resources().contains_key(key));
                    assert(s_prime.resources()[key].metadata.uid == Some(uid));
                    assert(s_prime.resources()[key].metadata.deletion_timestamp is Some);
                    assert(st_terminating(k, key, uid)(s_prime));
                } else {
                    assert(!s_prime.resources().contains_key(key));
                    assert(uid < s_prime.api_server.uid_counter);
                    assert(g(s_prime));
                }
            }
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(i) => {
                    if i->0 == msg {
                        assert(post(s_prime));
                    } else {
                        assert(s_prime.in_flight().contains(msg));
                        assert(pre(s_prime));
                    }
                },
                Step::ControllerStep(i) => {
                    if i.0 == controller_id && i.2 == Some(key) {
                        assert(i.1 is Some);
                        assert(s.in_flight().contains(i.1->0) && resp_msg_matches_req_msg(i.1->0, msg));
                        assert(false);
                    } else {
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        assert(s_prime.in_flight().contains(msg));
                        assert(pre(s_prime));
                    }
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(pre(s_prime));
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    assert(s_prime.in_flight().contains(msg));
                    assert(pre(s_prime));
                },
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_delete_req_in_flight(k, b, controller_id, key, parent_uid, uid)), {
        assert forall |ex| #[trigger] lift_state(st_delete_req_in_flight(k, b, controller_id, key, parent_uid, uid)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let msg = ex.head().ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_delete_req_in_flight(k, b, controller_id, key, parent_uid, uid)));
    });
    temp_pred_equality(lift_state(post), lift_state(st_terminating(k, key, uid)).or(lift_state(g)));
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

// The stable spec together with the premise of R3 for one object, made stable.
pub open spec fn janitor_spec_with_object(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> TempPred<ClusterState> {
    janitor_stable_spec(k, b, spec_ok, cluster, controller_id)
    .and(always(lift_state(parent_absent(k, key, parent_uid))).and(always(lift_state(present_or_gone(k, b, key, parent_uid, uid)))))
}

pub proof fn janitor_spec_with_object_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid)
    requires
        k.bindings.contains(b),
    ensures valid(stable(janitor_spec_with_object(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid))),
{
    janitor_stable_spec_is_stable(k, b, spec_ok, cluster, controller_id);
    always_p_is_stable(lift_state(parent_absent(k, key, parent_uid)));
    always_p_is_stable(lift_state(present_or_gone(k, b, key, parent_uid, uid)));
    stable_and_n!(always(lift_state(parent_absent(k, key, parent_uid))), always(lift_state(present_or_gone(k, b, key, parent_uid, uid))));
    stable_and_n!(
        janitor_stable_spec(k, b, spec_ok, cluster, controller_id),
        always(lift_state(parent_absent(k, key, parent_uid))).and(always(lift_state(present_or_gone(k, b, key, parent_uid, uid))))
    );
}

pub open spec fn janitor_spec_with_phase_i(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> TempPred<ClusterState> {
    janitor_spec_with_object(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid).and(always(lift_state(phase_i(controller_id))))
}

pub proof fn janitor_spec_with_phase_i_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid)
    requires
        k.bindings.contains(b),
    ensures valid(stable(janitor_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid))),
{
    janitor_spec_with_object_is_stable(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid);
    always_p_is_stable(lift_state(phase_i(controller_id)));
    stable_and_n!(janitor_spec_with_object(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid), always(lift_state(phase_i(controller_id))));
}

pub open spec fn janitor_spec_with_phases(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> TempPred<ClusterState> {
    janitor_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid).and(always(lift_state(phase_ii(k, b, controller_id, key, parent_uid, uid))))
}

// Under the stable spec, the premise and phase I: phase II eventually holds forever.
pub proof fn lemma_true_leads_to_always_phase_ii(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(janitor_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(phase_ii(k, b, controller_id, key, parent_uid, uid))))),
{
    let spec_o = janitor_spec_with_object(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid);
    entails_and_split(spec, spec_o, always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, janitor_stable_spec(k, b, spec_ok, cluster, controller_id), always(lift_state(parent_absent(k, key, parent_uid))).and(always(lift_state(present_or_gone(k, b, key, parent_uid, uid)))));
    entails_and_split(spec, always(lift_state(parent_absent(k, key, parent_uid))), always(lift_state(present_or_gone(k, b, key, parent_uid, uid))));
    lemma_janitor_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id);
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), key);

    // Termination of every reconcile of the janitor.
    terminate::janitor_reconcile_eventually_terminates(k, b, spec, cluster, controller_id);
    let idle_of = |key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)));
    spec_entails_tla_forall_apply(spec, idle_of, key);
    let idle_of_alt = |key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !(s.ongoing_reconciles(controller_id).contains_key(key))));
    assert forall |key: ObjectRef| #[trigger] idle_of(key) == idle_of_alt(key) by {
        temp_pred_equality(idle_of(key), idle_of_alt(key));
    }
    tla_forall_p_tla_forall_q_equality(idle_of, idle_of_alt);

    lemma_true_leads_to_always_scheduled_ok_or_gone(k, b, spec, cluster, controller_id, key, parent_uid, uid);
    cluster.lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(spec, controller_id, key);
    lemma_true_leads_to_always_list_responses_are_fresh(k, b, spec, cluster, controller_id, key, parent_uid);
    leads_to_always_and(
        spec, true_pred(),
        lift_state(scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid)),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key))
    );
    leads_to_always_and(
        spec, true_pred(),
        lift_state(scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid))
            .and(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key))),
        lift_state(list_responses_are_fresh(k, b, controller_id, key, parent_uid))
    );
    temp_pred_equality(
        lift_state(phase_ii(k, b, controller_id, key, parent_uid, uid)),
        lift_state(scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid))
            .and(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)))
            .and(lift_state(list_responses_are_fresh(k, b, controller_id, key, parent_uid)))
    );
}

// Under the stable spec, the premise and both phases: the object is eventually gone.
pub proof fn lemma_true_leads_to_gone_under_phases(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(janitor_spec_with_phases(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid)),
    ensures spec.entails(true_pred().leads_to(lift_state(object_is_gone(key, uid)))),
{
    let phase_ii_state = phase_ii(k, b, controller_id, key, parent_uid, uid);
    entails_and_split(spec, janitor_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid), always(lift_state(phase_ii_state)));
    entails_and_split(spec, janitor_spec_with_object(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, janitor_stable_spec(k, b, spec_ok, cluster, controller_id), always(lift_state(parent_absent(k, key, parent_uid))).and(always(lift_state(present_or_gone(k, b, key, parent_uid, uid)))));
    entails_and_split(spec, always(lift_state(parent_absent(k, key, parent_uid))), always(lift_state(present_or_gone(k, b, key, parent_uid, uid))));
    lemma_janitor_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id);
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_weaken(spec, lift_state(phase_ii_state), lift_state(scheduled_ok_or_gone(k, b, controller_id, key, parent_uid, uid)));
    always_weaken(spec, lift_state(phase_ii_state), lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)));
    always_weaken(spec, lift_state(phase_ii_state), lift_state(list_responses_are_fresh(k, b, controller_id, key, parent_uid)));

    // true ~> idle
    terminate::janitor_reconcile_eventually_terminates(k, b, spec, cluster, controller_id);
    spec_entails_tla_forall_apply(spec, |key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key))), key);

    let idle = lift_state(st_idle(controller_id, key));
    let scheduled = lift_state(st_scheduled(controller_id, key));
    let init = lift_state(st_init(k, b, controller_id, key, parent_uid, uid));
    let list_req = lift_state(st_list_req_in_flight(k, b, controller_id, key, parent_uid, uid));
    let list_resp = lift_state(st_list_resp_in_flight(k, b, controller_id, key, parent_uid, uid));
    let delete_req = lift_state(st_delete_req_in_flight(k, b, controller_id, key, parent_uid, uid));
    let terminating = lift_state(st_terminating(k, key, uid));
    let g = lift_state(gone(key, uid));
    let target = lift_state(object_is_gone(key, uid));

    lemma_idle_leads_to_scheduled_or_gone(k, b, spec, cluster, controller_id, key, parent_uid, uid);
    lemma_scheduled_leads_to_init_or_gone(k, b, spec, cluster, controller_id, key, parent_uid, uid);
    lemma_init_leads_to_list_req_in_flight(k, b, spec, cluster, controller_id, key, parent_uid, uid);
    lemma_list_req_leads_to_list_resp(k, b, spec, cluster, controller_id, key, parent_uid, uid);
    lemma_list_resp_leads_to_delete_req_in_flight(k, b, spec, cluster, controller_id, key, parent_uid, uid);
    lemma_delete_req_leads_to_terminating_or_gone(k, b, spec, cluster, controller_id, key, parent_uid, uid);
    // D3 for this object.
    spec_entails_tla_forall_apply(
        spec,
        |i: (ObjectRef, Uid)| lift_state(inner_terminating_object(k, i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1))),
        (key, uid)
    );

    // Frame the steps that do not need "or gone".
    entails_implies_leads_to(spec, list_req, list_req.or(g));
    leads_to_trans(spec, init, list_req, list_req.or(g));
    entails_implies_leads_to(spec, list_resp, list_resp.or(g));
    leads_to_trans(spec, list_req, list_resp, list_resp.or(g));
    entails_implies_leads_to(spec, delete_req, delete_req.or(g));
    leads_to_trans(spec, list_resp, delete_req, delete_req.or(g));

    leads_to_shortcut(spec, idle, scheduled, init, g);
    leads_to_shortcut(spec, idle, init, list_req, g);
    leads_to_shortcut(spec, idle, list_req, list_resp, g);
    leads_to_shortcut(spec, idle, list_resp, delete_req, g);
    leads_to_shortcut(spec, idle, delete_req, terminating, g);

    entails_implies_leads_to(spec, g, target);
    or_leads_to(spec, terminating, g, target);
    leads_to_trans_n!(spec, true_pred(), idle, terminating.or(g), target);
}

// Under the stable spec and the premise: the object is eventually gone.
pub proof fn lemma_object_leads_to_gone(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        key.kind == inner_kind(k, b),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(janitor_spec_with_object(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid)),
    ensures spec.entails(true_pred().leads_to(lift_state(object_is_gone(key, uid)))),
{
    let target = lift_state(object_is_gone(key, uid));
    let spec_o = janitor_spec_with_object(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid);
    let spec_i = janitor_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid);
    let spec_ii = janitor_spec_with_phases(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid);
    let phase_i_temp = always(lift_state(phase_i(controller_id)));
    let phase_ii_temp = always(lift_state(phase_ii(k, b, controller_id, key, parent_uid, uid)));

    // Under both phases.
    assert(spec_ii.entails(spec_ii));
    lemma_true_leads_to_gone_under_phases(k, b, spec_ok, spec_ii, cluster, controller_id, key, parent_uid, uid);
    // Move phase II from the spec to the premise.
    janitor_spec_with_phase_i_is_stable(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid);
    unpack_conditions_from_spec(spec_i, phase_ii_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_ii_temp), phase_ii_temp);
    assert(spec_i.entails(spec_i));
    lemma_true_leads_to_always_phase_ii(k, b, spec_ok, spec_i, cluster, controller_id, key, parent_uid, uid);
    leads_to_trans(spec_i, true_pred(), phase_ii_temp, target);
    // Move phase I from the spec to the premise.
    janitor_spec_with_object_is_stable(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid);
    unpack_conditions_from_spec(spec_o, phase_i_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_i_temp), phase_i_temp);
    assert(spec_o.entails(spec_o));
    lemma_janitor_stable_spec_facts(k, b, spec_ok, spec_o, cluster, controller_id);
    lemma_true_leads_to_always_phase_i(k, b, spec_o, cluster, controller_id);
    leads_to_trans(spec_o, true_pred(), phase_i_temp, target);
    entails_trans(spec, spec_o, true_pred().leads_to(target));
}

// R3 for one object under the stable spec.
pub proof fn lemma_mirror_eventually_collected_per_object(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        k.bindings.contains(b),
        spec.entails(janitor_stable_spec(k, b, spec_ok, cluster, controller_id)),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
    ensures spec.entails(widget_mirror_eventually_collected_per_object(k, b, key, parent_uid, uid)),
{
    let stable_spec = janitor_stable_spec(k, b, spec_ok, cluster, controller_id);
    let p = lift_state(parent_absent(k, key, parent_uid));
    let m = lift_state(mirror_object_is(inner_kind(k, b), key, parent_uid, uid));
    let q = lift_state(present_or_gone(k, b, key, parent_uid, uid));
    let target = lift_state(object_is_gone(key, uid));
    assert(stable_spec.entails(stable_spec));
    lemma_janitor_stable_spec_facts(k, b, spec_ok, stable_spec, cluster, controller_id);
    if key.kind != inner_kind(k, b) {
        // A mirror object never sits at a key of another kind.
        let wf = lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed());
        assert forall |ex: Execution<ClusterState>| !(#[trigger] always(p).and(m).and(wf).satisfied_by(ex)) by {
            if m.satisfied_by(ex) && wf.satisfied_by(ex) {
                let s = ex.head();
                assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                assert(s.resources()[key].kind == inner_kind(k, b));
                assert(s.resources()[key].object_ref() == key);
                assert(false);
            }
        }
        temp_pred_equality(always(p).and(m).and(wf), false_pred());
        vacuous_leads_to(stable_spec, always(p).and(m), target, wf);
    } else {
        lemma_mirror_leads_to_always_present_or_gone(k, b, spec_ok, stable_spec, cluster, key, parent_uid, uid);
        leads_to_with_always(stable_spec, m, always(q), p);
        let spec_o = janitor_spec_with_object(k, b, spec_ok, cluster, controller_id, key, parent_uid, uid);
        assert(spec_o.entails(spec_o));
        lemma_object_leads_to_gone(k, b, spec_ok, spec_o, cluster, controller_id, key, parent_uid, uid);
        janitor_stable_spec_is_stable(k, b, spec_ok, cluster, controller_id);
        unpack_conditions_from_spec(stable_spec, always(p).and(always(q)), true_pred(), target);
        temp_pred_equality(true_pred().and(always(p).and(always(q))), always(q).and(always(p)));
        leads_to_trans(stable_spec, m.and(always(p)), always(q).and(always(p)), target);
        temp_pred_equality(always(p).and(m), m.and(always(p)));
    }
    entails_trans(spec, stable_spec, always(p).and(m).leads_to(target));
}

// R3: the janitor eventually removes every mirror whose parent is gone for good.
pub proof fn janitor_eventually_collects_mirrors(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        k.bindings.contains(b),
        spec.entails(lift_state(cluster.init())),
        spec.entails(janitor_next_with_wf(cluster, controller_id)),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(always(lifted_janitor_rely_condition(k, cluster, controller_id))),
        spec.entails(inner_releases_terminating_objects(k)),
    ensures spec.entails(widget_mirrors_eventually_collected(k, b)),
{
    assert(janitor_next_with_wf(cluster, controller_id).entails(always(lift_action(cluster.next()))));
    entails_trans(spec, janitor_next_with_wf(cluster, controller_id), always(lift_action(cluster.next())));
    janitor_invariants_hold(k, b, spec_ok, spec, cluster, controller_id);
    entails_and_n!(
        spec,
        janitor_next_with_wf(cluster, controller_id),
        always(lifted_janitor_rely_condition(k, cluster, controller_id)),
        inner_releases_terminating_objects(k),
        janitor_invariants(k, b, spec_ok, cluster, controller_id)
    );
    let per_object = |i: (ObjectRef, Uid, Uid)| widget_mirror_eventually_collected_per_object(k, b, i.0, i.1, i.2);
    assert forall |i: (ObjectRef, Uid, Uid)| spec.entails(#[trigger] per_object(i)) by {
        lemma_mirror_eventually_collected_per_object(k, b, spec_ok, spec, cluster, controller_id, i.0, i.1, i.2);
    }
    spec_entails_tla_forall(spec, per_object);
}

// The janitor's ESR as a whole: R3 and sound deletes.
pub proof fn janitor_satisfies_its_spec(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        k.bindings.contains(b),
        spec.entails(lift_state(cluster.init())),
        spec.entails(janitor_next_with_wf(cluster, controller_id)),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(always(lifted_janitor_rely_condition(k, cluster, controller_id))),
        spec.entails(inner_releases_terminating_objects(k)),
    ensures spec.entails(widget_janitor_esr(k, b, controller_id)),
{
    janitor_eventually_collects_mirrors(k, b, spec_ok, spec, cluster, controller_id);
    assert(janitor_next_with_wf(cluster, controller_id).entails(always(lift_action(cluster.next()))));
    entails_trans(spec, janitor_next_with_wf(cluster, controller_id), always(lift_action(cluster.next())));
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    lemma_always_widget_janitor_guarantee(spec, cluster, k, b, spec_ok, controller_id);
    lemma_janitor_rely_implies_mirror_write_facts(k, b, spec, cluster, controller_id);
    lemma_always_every_mirror_is_bound(spec, cluster, k, b, spec_ok);
    lemma_always_janitor_deletes_are_sound(spec, cluster, k, b, spec_ok, controller_id);
    entails_and(spec, widget_mirrors_eventually_collected(k, b), always(lift_state(janitor_deletes_are_sound(k, b, controller_id))));
}

}
