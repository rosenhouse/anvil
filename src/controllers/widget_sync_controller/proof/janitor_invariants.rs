// Safety invariants about the janitor's reconciles, used by the janitor's own
// liveness proof (R3) and by the sync reconciler's proof (R1, to show that no
// janitor Delete ever lands on a mirror whose parent exists).
//
// The janitor decides from a snapshot of the mirror (its triggering object) and
// from one List of the outer copies. Two facts make that sound:
//   - the parent uid on the snapshot is bound to the outer key of the same name
//     (it names no uid the API server may still issue, and the only object it may
//     name is the outer copy at that key), and while the mirror object keeps its
//     uid it keeps that parent uid;
//   - once a List answered while no object carried the parent uid, no object ever
//     will (uids are never reused): the parent is absent for good.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::api_server::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{set_lib::*, string_view::*};
use crate::widget_sync_controller::{
    model::{install::*, janitor_reconciler, janitor_reconciler::WidgetJanitorReconcileState},
    proof::{guarantee::*, helper_invariants::*, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Snapshots of mirrors.
// ---------------------------------------------------------------------------

// Absence of the parent is stable over an API server step: a new object carries a
// fresh uid, and an object that stays keeps both its uid and the cluster its
// selector names (lemma_api_server_step_preserves_cluster_of).
pub proof fn lemma_parent_absent_forever_is_stable(
    cluster: Cluster, k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, parent: StringView,
    s: ClusterState, s_prime: ClusterState, msg: Message
)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime),
        parent_absent_forever(k, b, parent)(s),
    ensures parent_absent_forever(k, b, parent)(s_prime),
{
    lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
    assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && key.kind == k.outer_kind
        && s_prime.resources()[key].metadata.uid is Some
        && cluster_of_dynamic(k.selector, s_prime.resources()[key]) == Some(b.name)
    implies int_to_string_view(s_prime.resources()[key].metadata.uid->0) != parent by {
        if s.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == s.resources()[key].metadata.uid {
            Cluster::lemma_api_server_step_preserves_cluster_of(cluster, k.outer_kind, spec_ok, k.selector, s, s_prime, msg, key);
        } else {
            assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
            assert(int_to_string_view(s.api_server.uid_counter) != parent);
        }
    }
}

// A janitor snapshot `cr` of the mirror at `key` is sound: it unmarshals, it is a
// snapshot of that key with a uid the API server has issued, its parent uid (if it
// is a mirror) is bound to the outer key, and while the stored object keeps the
// snapshot's uid it keeps the snapshot's mirror identity.
pub open spec fn janitor_snapshot_is_sound(k: SyncKind, b: Binding, cr: DynamicObjectView, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& unmarshal(inner_kind(k, b), cr) is Ok
        &&& cr.object_ref() == key
        &&& cr.metadata.uid is Some
        &&& cr.metadata.uid->0 < s.api_server.uid_counter
        &&& snapshot_is_mirror(inner_kind(k, b), cr) ==> parent_uid_string_is_bound_to_key(snapshot_parent(inner_kind(k, b), cr), outer_key_of(k, key))(s)
        &&& (s.resources().contains_key(key) && s.resources()[key].metadata.uid == cr.metadata.uid)
            ==> preserves_mirror_identity(cr.metadata, s.resources()[key].metadata)
    }
}

pub open spec fn janitor_scheduled_crs_are_sound(k: SyncKind, b: Binding, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            ==> janitor_snapshot_is_sound(k, b, s.scheduled_reconciles(controller_id)[key], key)(s)
    }
}

pub open spec fn janitor_triggering_crs_are_sound(k: SyncKind, b: Binding, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> janitor_snapshot_is_sound(k, b, s.ongoing_reconciles(controller_id)[key].triggering_cr, key)(s)
    }
}

// Soundness of a snapshot carries over an API server step.
pub proof fn lemma_snapshot_soundness_preserved_by_api_server_step(
    cluster: Cluster, k: SyncKind, b: Binding, s: ClusterState, s_prime: ClusterState, msg: Message, cr: DynamicObjectView, key: ObjectRef
)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        key.kind == inner_kind(k, b),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        every_in_flight_inner_update_preserves_identity(k)(s),
        every_mirror_is_bound(k, b)(s),
        janitor_snapshot_is_sound(k, b, cr, key)(s),
    ensures janitor_snapshot_is_sound(k, b, cr, key)(s_prime),
{
    lemma_weakly_well_formed_implies_kinds_match(s);
    lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
    if snapshot_is_mirror(inner_kind(k, b), cr) {
        lemma_string_bound_preserved(snapshot_parent(inner_kind(k, b), cr), outer_key_of(k, key), s, s_prime);
    }
    if s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == cr.metadata.uid {
        // The stored object is the one the snapshot was taken from (uids are fresh).
        assert(s.resources().contains_key(key) && s.resources()[key].metadata.uid == cr.metadata.uid) by {
            if !(s.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == s.resources()[key].metadata.uid) {
                assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
                assert(false);
            }
        }
        let old_obj = s.resources()[key];
        let new_obj = s_prime.resources()[key];
        assert(preserves_mirror_identity(cr.metadata, old_obj.metadata));
        assert(mirror_is_bound(k, key)(s));
        assert(s_prime.api_server == transition_by_etcd(cluster.installed_types, msg, s.api_server).0);
        assert(s.in_flight().contains(msg));
        match msg.content->APIRequest_0 {
            APIRequest::CreateRequest(_) => {
                // A create never replaces an existing object.
                assert(new_obj == old_obj);
            },
            APIRequest::UpdateRequest(req) => {
                assert(mirror_update_req(k, req)(s));
                if new_obj != old_obj {
                    assert(req.key() == key);
                    assert(is_inner_kind(k, req.obj.kind));
                    assert(req.obj.metadata.resource_version == old_obj.metadata.resource_version);
                    assert(preserves_mirror_identity(old_obj.metadata, req.obj.metadata));
                    assert(new_obj.metadata.labels == req.obj.metadata.labels);
                    assert(new_obj.metadata.annotations == req.obj.metadata.annotations);
                }
            },
            APIRequest::GetThenUpdateRequest(_) => {
                lemma_get_then_update_keeps_unowned_objects(cluster.installed_types, msg, s.api_server, key);
            },
            _ => {
                lemma_other_requests_keep_identity(cluster.installed_types, msg, s.api_server);
            },
        }
        assert(new_obj.metadata.labels == old_obj.metadata.labels || preserves_mirror_identity(old_obj.metadata, new_obj.metadata));
        assert(preserves_mirror_identity(cr.metadata, new_obj.metadata));
    }
}

pub proof fn lemma_always_janitor_crs_are_sound(spec: TempPred<ClusterState>, cluster: Cluster, k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(always(lift_state(every_mirror_is_bound(k, b)))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity(k)))),
    ensures
        spec.entails(always(lift_state(janitor_scheduled_crs_are_sound(k, b, controller_id)))),
        spec.entails(always(lift_state(janitor_triggering_crs_are_sound(k, b, controller_id)))),
{
    let inv = |s: ClusterState| {
        &&& janitor_scheduled_crs_are_sound(k, b, controller_id)(s)
        &&& janitor_triggering_crs_are_sound(k, b, controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& every_mirror_is_bound(k, b)(s)
        &&& every_in_flight_inner_update_preserves_identity(k)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(every_mirror_is_bound(k, b)),
        lift_state(every_in_flight_inner_update_preserves_identity(k))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                implies janitor_snapshot_is_sound(k, b, s_prime.scheduled_reconciles(controller_id)[key], key)(s_prime) by {
                    assert(s.scheduled_reconciles(controller_id).contains_key(key));
                    assert(key.kind == inner_kind(k, b));
                    lemma_snapshot_soundness_preserved_by_api_server_step(cluster, k, b, s, s_prime, input->0, s.scheduled_reconciles(controller_id)[key], key);
                }
                assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
                implies janitor_snapshot_is_sound(k, b, s_prime.ongoing_reconciles(controller_id)[key].triggering_cr, key)(s_prime) by {
                    assert(s.ongoing_reconciles(controller_id).contains_key(key));
                    assert(key.kind == inner_kind(k, b));
                    lemma_snapshot_soundness_preserved_by_api_server_step(cluster, k, b, s, s_prime, input->0, s.ongoing_reconciles(controller_id)[key].triggering_cr, key);
                }
            },
            Step::ScheduleControllerReconcileStep(input) => {
                assert(s_prime.api_server == s.api_server);
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                implies janitor_snapshot_is_sound(k, b, s_prime.scheduled_reconciles(controller_id)[key], key)(s_prime) by {
                    if input.0 == controller_id && input.1 == key {
                        let obj = s.resources()[key];
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == obj);
                        assert(key.kind == inner_kind(k, b));
                        assert(mirror_is_bound(k, key)(s));
                        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                        assert(unmarshal(inner_kind(k, b), obj)->Ok_0.metadata == obj.metadata);
                    } else {
                        assert(s.scheduled_reconciles(controller_id).contains_key(key));
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                    }
                }
                assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
            },
            Step::ControllerStep(input) => {
                assert(s_prime.api_server == s.api_server);
                assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
                implies janitor_snapshot_is_sound(k, b, s_prime.ongoing_reconciles(controller_id)[key].triggering_cr, key)(s_prime) by {
                    if s.ongoing_reconciles(controller_id).contains_key(key) {
                        assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.ongoing_reconciles(controller_id)[key].triggering_cr);
                    } else {
                        assert(input.0 == controller_id && input.2 == Some(key));
                        assert(s.scheduled_reconciles(controller_id).contains_key(key));
                        assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
                    }
                }
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                implies janitor_snapshot_is_sound(k, b, s_prime.scheduled_reconciles(controller_id)[key], key)(s_prime) by {
                    assert(s.scheduled_reconciles(controller_id).contains_key(key));
                    assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                }
            },
            Step::RestartControllerStep(id) => {
                assert(s_prime.api_server == s.api_server);
                if id == controller_id {
                    assert(s_prime.ongoing_reconciles(controller_id) == Map::<ObjectRef, OngoingReconcile>::empty());
                    assert(s_prime.scheduled_reconciles(controller_id) == Map::<ObjectRef, DynamicObjectView>::empty());
                } else {
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                    assert(s_prime.scheduled_reconciles(controller_id) == s.scheduled_reconciles(controller_id));
                }
            },
            _ => {
                assert(s_prime.api_server == s.api_server);
                assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                assert(s_prime.scheduled_reconciles(controller_id) == s.scheduled_reconciles(controller_id));
            },
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
    always_weaken(spec, lift_state(inv), lift_state(janitor_scheduled_crs_are_sound(k, b, controller_id)));
    always_weaken(spec, lift_state(inv), lift_state(janitor_triggering_crs_are_sound(k, b, controller_id)));
}

// ---------------------------------------------------------------------------
// The janitor's decisions are sound.
// ---------------------------------------------------------------------------

// The List request the janitor sends for the mirror at `key`.
pub open spec fn janitor_list_request(k: SyncKind, key: ObjectRef) -> ListRequest {
    ListRequest { kind: k.outer_kind, namespace: key.namespace }
}

pub open spec fn janitor_reconcile_is_sound(k: SyncKind, b: Binding, controller_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let reconcile = s.ongoing_reconciles(controller_id)[key];
        let step = WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
        let parent = snapshot_parent(inner_kind(k, b), reconcile.triggering_cr);
        &&& (step is AfterListOuter || step is AfterDeleteInner) ==> snapshot_is_mirror(inner_kind(k, b), reconcile.triggering_cr)
        &&& step is AfterListOuter ==> {
            &&& reconcile.pending_req_msg is Some
            &&& reconcile.pending_req_msg->0.content is APIRequest
            &&& reconcile.pending_req_msg->0.content.is_list_request()
            &&& reconcile.pending_req_msg->0.content.get_list_request() == janitor_list_request(k, key)
            &&& forall |resp: Message| {
                &&& #[trigger] s.in_flight().contains(resp)
                &&& resp_msg_matches_req_msg(resp, reconcile.pending_req_msg->0)
                &&& resp.content.get_list_response().res is Ok
            } ==> janitor_reconciler::parent_listed(k, b, resp.content.get_list_response().res->Ok_0, parent) || parent_absent_forever(k, b, parent)(s)
        }
        &&& step is AfterDeleteInner ==> parent_absent_forever(k, b, parent)(s)
    }
}

pub open spec fn janitor_decisions_are_sound(k: SyncKind, b: Binding, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> janitor_reconcile_is_sound(k, b, controller_id, key)(s)
    }
}

// The List of the outer copies in the mirror's namespace either lists the parent or
// shows it absent for good.
proof fn lemma_list_response_decides_parent(k: SyncKind, b: Binding, s: ClusterState, cr: DynamicObjectView, key: ObjectRef)
    requires
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        janitor_snapshot_is_sound(k, b, cr, key)(s),
        snapshot_is_mirror(inner_kind(k, b), cr),
    ensures ({
        let objs = handle_list_request(janitor_list_request(k, key), s.api_server).res->Ok_0;
        janitor_reconciler::parent_listed(k, b, objs, snapshot_parent(inner_kind(k, b), cr))
            || parent_absent_forever(k, b, snapshot_parent(inner_kind(k, b), cr))(s)
    }),
{
    let parent = snapshot_parent(inner_kind(k, b), cr);
    let sel = |o: DynamicObjectView| {
        &&& o.object_ref().namespace == key.namespace
        &&& o.object_ref().kind == k.outer_kind
    };
    let selected = s.resources().values().filter(sel);
    let objs = selected.to_seq();
    assert(handle_list_request(janitor_list_request(k, key), s.api_server).res->Ok_0 == objs);
    if exists |k2: ObjectRef| #[trigger] s.resources().contains_key(k2) && k2.kind == k.outer_kind
        && s.resources()[k2].metadata.uid is Some
        && int_to_string_view(s.resources()[k2].metadata.uid->0) == parent
        && cluster_of_dynamic(k.selector, s.resources()[k2]) == Some(b.name) {
        let k2 = choose |k2: ObjectRef| #[trigger] s.resources().contains_key(k2) && k2.kind == k.outer_kind
            && s.resources()[k2].metadata.uid is Some
            && int_to_string_view(s.resources()[k2].metadata.uid->0) == parent
            && cluster_of_dynamic(k.selector, s.resources()[k2]) == Some(b.name);
        // The parent uid is bound to the outer key, so this is the outer copy, which the List returns.
        assert(k2 == outer_key_of(k, key));
        let o = s.resources()[k2];
        assert(Cluster::etcd_object_is_weakly_well_formed(k2)(s));
        assert(o.object_ref() == k2);
        assert(sel(o));
        assert(s.resources().values().contains(o)) by {
            assert(s.resources().dom().contains(k2));
        }
        assert(selected.contains(o));
        lemma_set_to_seq_contains_all_elements(selected);
        assert(objs.contains(o));
        let i = choose |i: int| 0 <= i < objs.len() && objs[i] == o;
        assert((#[trigger] objs[i]).kind == k.outer_kind);
        assert(objs[i].metadata.uid is Some && int_to_string_view(objs[i].metadata.uid->0) == parent);
        assert(cluster_of_dynamic(k.selector, objs[i]) == Some(b.name));
        assert(janitor_reconciler::parent_listed(k, b, objs, parent));
    } else {
        assert(parent_absent_forever(k, b, parent)(s));
    }
}

pub proof fn lemma_always_janitor_decisions_are_sound(spec: TempPred<ClusterState>, cluster: Cluster, k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(always(lift_state(every_mirror_is_bound(k, b)))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity(k)))),
    ensures spec.entails(always(lift_state(janitor_decisions_are_sound(k, b, controller_id)))),
{
    let inv = janitor_decisions_are_sound(k, b, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    always_to_always_later(spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_synced_states_are_unmarshallable::<WidgetJanitorReconcileState, VoidEReqView, VoidERespView>(
        spec, inner_kind(k, b),
        || janitor_reconciler::reconcile_init_state(),
        |obj: SyncedObjectView, resp_o, st| janitor_reconciler::reconcile_core(k, b, obj, resp_o, st),
        |st| janitor_reconciler::reconcile_done(st),
        |st| janitor_reconciler::reconcile_error(st),
        controller_id);
    cluster.lemma_always_objects_in_reconcile_have_kind(spec, inner_kind(k, b), controller_id);
    lemma_always_janitor_crs_are_sound(spec, cluster, k, b, spec_ok, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)(s)
        &&& Cluster::objects_in_reconcile_have_kind(inner_kind(k, b), controller_id)(s)
        &&& janitor_triggering_crs_are_sound(k, b, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        later(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)),
        lift_state(Cluster::objects_in_reconcile_have_kind(inner_kind(k, b), controller_id)),
        lift_state(janitor_triggering_crs_are_sound(k, b, controller_id))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        unmarshal_of_marshal();
        WidgetJanitorReconcileState::marshal_preserves_integrity();
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
        implies janitor_reconcile_is_sound(k, b, controller_id, key)(s_prime) by {
            match step {
                Step::APIServerStep(input) => {
                    lemma_janitor_decision_soundness_preserved_by_api_server_step(cluster, k, b, spec_ok, controller_id, s, s_prime, input->0, key);
                },
                Step::ControllerStep(input) => {
                    lemma_janitor_decision_soundness_preserved_by_controller_step(cluster, k, b, controller_id, s, s_prime, input, key);
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                    assert(s_prime.api_server == s.api_server);
                    assert(s_prime.in_flight() == s.in_flight());
                    assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
                },
                Step::DropReqStep(input) => {
                    // Dropping a request answers it with an error response, which the
                    // invariant does not constrain.
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                    assert(s_prime.api_server == s.api_server);
                    assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
                    let reconcile = s.ongoing_reconciles(controller_id)[key];
                    let step = WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
                    if step is AfterListOuter {
                        assert forall |resp: Message| {
                            &&& #[trigger] s_prime.in_flight().contains(resp)
                            &&& resp_msg_matches_req_msg(resp, reconcile.pending_req_msg->0)
                            &&& resp.content.get_list_response().res is Ok
                        } implies s.in_flight().contains(resp) by {
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
                            }
                        }
                    }
                },
                Step::ExternalStep(input) => {
                    // External systems answer external requests; ongoing reconciles and the
                    // store do not change.
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                    assert(s_prime.api_server == s.api_server);
                    assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
                    let reconcile = s.ongoing_reconciles(controller_id)[key];
                    let step = WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
                    if step is AfterListOuter {
                        assert forall |resp: Message| {
                            &&& #[trigger] s_prime.in_flight().contains(resp)
                            &&& resp_msg_matches_req_msg(resp, reconcile.pending_req_msg->0)
                        } implies s.in_flight().contains(resp) by {
                            if !s.in_flight().contains(resp) {
                                assert(reconcile.pending_req_msg->0.content is APIRequest);
                                assert(resp.content is ExternalResponse);
                            }
                        }
                    }
                },
                _ => {
                    // Built-in controllers and the pod monkey only add API requests; the
                    // remaining steps send nothing.
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                    assert(s_prime.api_server == s.api_server);
                    assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
                    let reconcile = s.ongoing_reconciles(controller_id)[key];
                    if reconcile.pending_req_msg is Some {
                        assert forall |resp: Message| {
                            &&& #[trigger] s_prime.in_flight().contains(resp)
                            &&& resp_msg_matches_req_msg(resp, reconcile.pending_req_msg->0)
                        } implies s.in_flight().contains(resp) by {
                            if !s.in_flight().contains(resp) {
                                assert(resp.content is APIRequest);
                            }
                        }
                    }
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

proof fn lemma_janitor_decision_soundness_preserved_by_api_server_step(
    cluster: Cluster, k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, controller_id: int, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef
)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime),
        Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s),
        janitor_triggering_crs_are_sound(k, b, controller_id)(s),
        janitor_decisions_are_sound(k, b, controller_id)(s),
        s_prime.ongoing_reconciles(controller_id).contains_key(key),
    ensures janitor_reconcile_is_sound(k, b, controller_id, key)(s_prime),
{
    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
    assert(s.ongoing_reconciles(controller_id).contains_key(key));
    assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
    assert(janitor_snapshot_is_sound(k, b, s.ongoing_reconciles(controller_id)[key].triggering_cr, key)(s));
    lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
    let reconcile = s.ongoing_reconciles(controller_id)[key];
    let step = WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
    let parent = snapshot_parent(inner_kind(k, b), reconcile.triggering_cr);
    if step is AfterDeleteInner {
        lemma_parent_absent_forever_is_stable(cluster, k, b, spec_ok, parent, s, s_prime, msg);
    }
    if step is AfterListOuter {
        let pending = reconcile.pending_req_msg->0;
        let new_resp = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
        assert forall |resp: Message| {
            &&& #[trigger] s_prime.in_flight().contains(resp)
            &&& resp_msg_matches_req_msg(resp, pending)
            &&& resp.content.get_list_response().res is Ok
        } implies janitor_reconciler::parent_listed(k, b, resp.content.get_list_response().res->Ok_0, parent) || parent_absent_forever(k, b, parent)(s_prime) by {
            if s.in_flight().contains(resp) {
                if parent_absent_forever(k, b, parent)(s) {
                    lemma_parent_absent_forever_is_stable(cluster, k, b, spec_ok, parent, s, s_prime, msg);
                }
            } else {
                // The response was just produced, and it answers the pending List.
                assert(resp == new_resp);
                assert(resp.rpc_id == msg.rpc_id);
                assert(s.in_flight().contains(msg));
                assert(msg == pending);
                assert(msg.content.get_list_request() == janitor_list_request(k, key));
                assert(s_prime.api_server == s.api_server);
                assert(resp.content.get_list_response() == handle_list_request(janitor_list_request(k, key), s.api_server));
                lemma_list_response_decides_parent(k, b, s, reconcile.triggering_cr, key);
            }
        }
    }
}

proof fn lemma_janitor_decision_soundness_preserved_by_controller_step(
    cluster: Cluster, k: SyncKind, b: Binding, controller_id: int, s: ClusterState, s_prime: ClusterState,
    input: (int, Option<Message>, Option<ObjectRef>), key: ObjectRef
)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        cluster.next_step(s, s_prime, Step::ControllerStep(input)),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)(s),
        Cluster::objects_in_reconcile_have_kind(inner_kind(k, b), controller_id)(s),
        janitor_triggering_crs_are_sound(k, b, controller_id)(s),
        janitor_decisions_are_sound(k, b, controller_id)(s),
        s_prime.ongoing_reconciles(controller_id).contains_key(key),
    ensures janitor_reconcile_is_sound(k, b, controller_id, key)(s_prime),
{
    unmarshal_of_marshal();
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    assert(s_prime.api_server == s.api_server);
    let (id, resp_msg_opt, cr_key_opt) = input;
    if id == controller_id && cr_key_opt == Some(key) && s.ongoing_reconciles(controller_id).contains_key(key)
        && s_prime.ongoing_reconciles(controller_id)[key] != s.ongoing_reconciles(controller_id)[key] {
        // ContinueReconcile on this key.
        let reconcile = s.ongoing_reconciles(controller_id)[key];
        let reconcile_prime = s_prime.ongoing_reconciles(controller_id)[key];
        assert(reconcile_prime.triggering_cr == reconcile.triggering_cr);
        assert(janitor_snapshot_is_sound(k, b, reconcile.triggering_cr, key)(s));
        assert(unmarshal(inner_kind(k, b), reconcile.triggering_cr) is Ok);
        let inner = unmarshal(inner_kind(k, b), reconcile.triggering_cr)->Ok_0;
        assert(inner.metadata == reconcile.triggering_cr.metadata);
        assert(inner.object_ref() == key);
        assert(WidgetJanitorReconcileState::unmarshal(reconcile.local_state) is Ok);
        let state = WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0;
        let resp_o = if resp_msg_opt is Some {
            if resp_msg_opt->0.content is APIResponse {
                Some(ResponseView::<VoidERespView>::KResponse(resp_msg_opt->0.content->APIResponse_0))
            } else {
                Some(ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(resp_msg_opt->0.content->ExternalResponse_0)->Ok_0))
            }
        } else {
            None
        };
        let (state_prime, req_o) = janitor_reconciler::reconcile_core(k, b, inner, resp_o, state);
        assert(reconcile_prime.local_state == state_prime.marshal());
        assert(WidgetJanitorReconcileState::unmarshal(reconcile_prime.local_state)->Ok_0 == state_prime);
        let parent = snapshot_parent(inner_kind(k, b), reconcile.triggering_cr);
        match state.reconcile_step {
            WidgetJanitorStepView::Init => {
                if has_mirror_identity(inner) {
                    assert(state_prime.reconcile_step is AfterListOuter);
                    assert(snapshot_is_mirror(inner_kind(k, b), reconcile.triggering_cr));
                    let pending = reconcile_prime.pending_req_msg->0;
                    assert(reconcile_prime.pending_req_msg is Some);
                    assert(pending.content.get_list_request() == janitor_list_request(k, key));
                    // The new request carries a fresh rpc id, so no response matches it yet.
                    assert(pending.rpc_id == s.rpc_id_allocator.rpc_id_counter);
                    assert forall |resp: Message| {
                        &&& #[trigger] s_prime.in_flight().contains(resp)
                        &&& resp_msg_matches_req_msg(resp, pending)
                    } implies false by {
                        if s.in_flight().contains(resp) {
                            assert(resp.rpc_id < s.rpc_id_allocator.rpc_id_counter);
                        } else {
                            assert(resp == pending);
                            assert(resp.content is APIRequest);
                        }
                    }
                } else {
                    assert(state_prime.reconcile_step is Done);
                }
            },
            WidgetJanitorStepView::AfterListOuter => {
                assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
                assert(snapshot_is_mirror(inner_kind(k, b), reconcile.triggering_cr));
                if state_prime.reconcile_step is AfterDeleteInner {
                    // The List answered without the parent, so the parent is absent for good.
                    let resp_msg = resp_msg_opt->0;
                    assert(s.in_flight().contains(resp_msg));
                    assert(resp_msg_matches_req_msg(resp_msg, reconcile.pending_req_msg->0));
                    assert(resp_msg.content.get_list_response().res is Ok);
                    let objs = resp_msg.content.get_list_response().res->Ok_0;
                    assert(!janitor_reconciler::parent_listed(k, b, objs, parent_uid_annotation(inner)));
                    assert(parent_uid_annotation(inner) == parent);
                    assert(parent_absent_forever(k, b, parent)(s));
                }
            },
            WidgetJanitorStepView::AfterDeleteInner => {
                assert(state_prime.reconcile_step is Done || state_prime.reconcile_step is Error);
            },
            _ => {
                assert(false);
            },
        }
    } else {
        // Another controller's step, a reconcile that just started (at Init), or a
        // step on another key: this key's reconcile is unchanged, the store is
        // unchanged, and only requests were added to the network.
        if s.ongoing_reconciles(controller_id).contains_key(key) {
            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
            let reconcile = s.ongoing_reconciles(controller_id)[key];
            if reconcile.pending_req_msg is Some {
                assert forall |resp: Message| {
                    &&& #[trigger] s_prime.in_flight().contains(resp)
                    &&& resp_msg_matches_req_msg(resp, reconcile.pending_req_msg->0)
                } implies s.in_flight().contains(resp) by {
                    if !s.in_flight().contains(resp) {
                        assert(resp.content is APIRequest || resp.content is ExternalRequest);
                    }
                }
            }
        } else {
            // A reconcile that just started is at Init.
            assert(id == controller_id && cr_key_opt == Some(key));
            let reconcile_prime = s_prime.ongoing_reconciles(controller_id)[key];
            assert(reconcile_prime.local_state == janitor_reconciler::reconcile_init_state().marshal());
            assert(WidgetJanitorReconcileState::unmarshal(reconcile_prime.local_state)->Ok_0.reconcile_step is Init);
        }
    }
}


// ---------------------------------------------------------------------------
// The janitor's Deletes in flight are sound (janitor_deletes_are_sound in
// trusted/liveness_theorem.rs, part of the janitor's ESR).
// ---------------------------------------------------------------------------

pub proof fn lemma_always_janitor_deletes_are_sound(spec: TempPred<ClusterState>, cluster: Cluster, k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        spec.entails(always(lift_state(every_mirror_is_bound(k, b)))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity(k)))),
        spec.entails(always(lift_state(widget_janitor_guarantee(k, b, controller_id)))),
    ensures spec.entails(always(lift_state(janitor_deletes_are_sound(k, b, controller_id)))),
{
    let inv = janitor_deletes_are_sound(k, b, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    always_to_always_later(spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    cluster.lemma_always_each_synced_object_in_etcd_is_well_formed(spec, inner_kind(k, b), spec_ok, k.selector);
    cluster.lemma_always_synced_states_are_unmarshallable::<WidgetJanitorReconcileState, VoidEReqView, VoidERespView>(
        spec, inner_kind(k, b),
        || janitor_reconciler::reconcile_init_state(),
        |obj: SyncedObjectView, resp_o, st| janitor_reconciler::reconcile_core(k, b, obj, resp_o, st),
        |st| janitor_reconciler::reconcile_done(st),
        |st| janitor_reconciler::reconcile_error(st),
        controller_id);
    cluster.lemma_always_objects_in_reconcile_have_kind(spec, inner_kind(k, b), controller_id);
    lemma_always_janitor_crs_are_sound(spec, cluster, k, b, spec_ok, controller_id);
    lemma_always_janitor_decisions_are_sound(spec, cluster, k, b, spec_ok, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s)
        &&& every_mirror_is_bound(k, b)(s)
        &&& every_in_flight_inner_update_preserves_identity(k)(s)
        &&& widget_janitor_guarantee(k, b, controller_id)(s)
        &&& Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)(s)
        &&& Cluster::objects_in_reconcile_have_kind(inner_kind(k, b), controller_id)(s)
        &&& janitor_triggering_crs_are_sound(k, b, controller_id)(s)
        &&& janitor_decisions_are_sound(k, b, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        later(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        lift_state(cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))),
        lift_state(every_mirror_is_bound(k, b)),
        lift_state(every_in_flight_inner_update_preserves_identity(k)),
        lift_state(widget_janitor_guarantee(k, b, controller_id)),
        lift_state(Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)),
        lift_state(Cluster::objects_in_reconcile_have_kind(inner_kind(k, b), controller_id)),
        lift_state(janitor_triggering_crs_are_sound(k, b, controller_id)),
        lift_state(janitor_decisions_are_sound(k, b, controller_id))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.content is APIRequest
            &&& msg.content.is_delete_request()
        } implies janitor_delete_is_sound(k, b, msg, s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    let handled = input->0;
                    // The API server only adds a response, so the Delete was already in flight.
                    assert(s.in_flight().contains(msg));
                    assert(janitor_delete_is_sound(k, b, msg, s));
                    lemma_janitor_delete_soundness_preserved_by_api_server_step(cluster, k, b, spec_ok, controller_id, s, s_prime, handled, msg);
                },
                Step::ControllerStep(input) => {
                    assert(s_prime.api_server == s.api_server);
                    if s.in_flight().contains(msg) {
                        assert(janitor_delete_is_sound(k, b, msg, s));
                    } else {
                        lemma_new_janitor_delete_is_sound(cluster, k, b, controller_id, s, s_prime, input, msg);
                    }
                },
                _ => {
                    // No other step sends a request on behalf of the janitor, and none changes the store.
                    assert(s_prime.api_server == s.api_server);
                    assert(s.in_flight().contains(msg));
                    assert(janitor_delete_is_sound(k, b, msg, s));
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

proof fn lemma_janitor_delete_soundness_preserved_by_api_server_step(
    cluster: Cluster, k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    controller_id: int, s: ClusterState, s_prime: ClusterState, handled: Message, msg: Message
)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(handled))),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime),
        cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s),
        every_mirror_is_bound(k, b)(s),
        every_in_flight_inner_update_preserves_identity(k)(s),
        widget_janitor_guarantee(k, b, controller_id)(s),
        s.in_flight().contains(msg),
        msg.src.is_controller_id(controller_id),
        msg.content is APIRequest,
        msg.content.is_delete_request(),
        janitor_delete_is_sound(k, b, msg, s),
    ensures janitor_delete_is_sound(k, b, msg, s_prime),
{
    lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, handled);
    let req = msg.content.get_delete_request();
    let m = req.preconditions->0.uid->0;
    assert(req.key.kind == inner_kind(k, b));
    if s_prime.resources().contains_key(req.key)
        && s_prime.resources()[req.key].metadata.uid == Some(m)
        && snapshot_is_mirror(inner_kind(k, b), s_prime.resources()[req.key])
    {
        // The object was there at s with the same uid: a fresh uid is above m.
        assert(s.resources().contains_key(req.key) && s.resources()[req.key].metadata.uid == Some(m)) by {
            if !(s.resources().contains_key(req.key) && s_prime.resources()[req.key].metadata.uid == s.resources()[req.key].metadata.uid) {
                assert(s_prime.resources()[req.key].metadata.uid == Some(s.api_server.uid_counter));
                assert(false);
            }
        }
        let cr = s.resources()[req.key];
        lemma_well_formed_inner_unmarshals(cluster, inner_kind(k, b), spec_ok, k.selector, s, req.key);
        assert(mirror_is_bound(k, req.key)(s));
        assert(snapshot_is_mirror(inner_kind(k, b), cr));
        assert(Cluster::etcd_object_is_weakly_well_formed(req.key)(s));
        assert(janitor_snapshot_is_sound(k, b, cr, req.key)(s));
        lemma_snapshot_soundness_preserved_by_api_server_step(cluster, k, b, s, s_prime, handled, cr, req.key);
        let new_obj = s_prime.resources()[req.key];
        assert(preserves_mirror_identity(cr.metadata, new_obj.metadata));
        assert(snapshot_parent(inner_kind(k, b), new_obj) == snapshot_parent(inner_kind(k, b), cr));
        assert(parent_absent_forever(k, b, snapshot_parent(inner_kind(k, b), cr))(s));
        lemma_parent_absent_forever_is_stable(cluster, k, b, spec_ok, snapshot_parent(inner_kind(k, b), cr), s, s_prime, handled);
    }
}

// A Delete the janitor just sent: it comes from AfterListOuter, after a List that
// answered without the parent.
proof fn lemma_new_janitor_delete_is_sound(
    cluster: Cluster, k: SyncKind, b: Binding, controller_id: int, s: ClusterState, s_prime: ClusterState,
    input: (int, Option<Message>, Option<ObjectRef>), msg: Message
)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(k, b)),
        cluster.next_step(s, s_prime, Step::ControllerStep(input)),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::synced_states_are_unmarshallable::<WidgetJanitorReconcileState>(inner_kind(k, b), controller_id)(s),
        Cluster::objects_in_reconcile_have_kind(inner_kind(k, b), controller_id)(s),
        janitor_triggering_crs_are_sound(k, b, controller_id)(s),
        janitor_decisions_are_sound(k, b, controller_id)(s),
        s_prime.in_flight().contains(msg),
        !s.in_flight().contains(msg),
        msg.src.is_controller_id(controller_id),
        msg.content is APIRequest,
        msg.content.is_delete_request(),
    ensures janitor_delete_is_sound(k, b, msg, s_prime),
{
    unmarshal_of_marshal();
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    assert(s_prime.api_server == s.api_server);
    let (id, resp_msg_opt, cr_key_opt) = input;
    // The new message is the request sent by the reconcile that stepped.
    assert(id == controller_id);
    assert(cr_key_opt is Some);
    let key = cr_key_opt->0;
    assert(msg.src == HostId::Controller(controller_id, key));
    assert(s.ongoing_reconciles(controller_id).contains_key(key));
    let reconcile = s.ongoing_reconciles(controller_id)[key];
    let reconcile_prime = s_prime.ongoing_reconciles(controller_id)[key];
    assert(reconcile_prime.pending_req_msg == Some(msg));
    assert(janitor_snapshot_is_sound(k, b, reconcile.triggering_cr, key)(s));
    let inner = unmarshal(inner_kind(k, b), reconcile.triggering_cr)->Ok_0;
    assert(inner.metadata == reconcile.triggering_cr.metadata);
    assert(inner.object_ref() == key);
    let state = WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0;
    let resp_o = if resp_msg_opt is Some {
        if resp_msg_opt->0.content is APIResponse {
            Some(ResponseView::<VoidERespView>::KResponse(resp_msg_opt->0.content->APIResponse_0))
        } else {
            Some(ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(resp_msg_opt->0.content->ExternalResponse_0)->Ok_0))
        }
    } else {
        None
    };
    let (state_prime, req_o) = janitor_reconciler::reconcile_core(k, b, inner, resp_o, state);
    assert(req_o is Some);
    let parent = snapshot_parent(inner_kind(k, b), reconcile.triggering_cr);
    match state.reconcile_step {
        WidgetJanitorStepView::Init => {
            // Sends a List, not a Delete.
            assert(false);
        },
        WidgetJanitorStepView::AfterListOuter => {
            assert(janitor_reconcile_is_sound(k, b, controller_id, key)(s));
            assert(snapshot_is_mirror(inner_kind(k, b), reconcile.triggering_cr));
            assert(state_prime.reconcile_step is AfterDeleteInner);
            let resp_msg = resp_msg_opt->0;
            assert(s.in_flight().contains(resp_msg));
            assert(resp_msg_matches_req_msg(resp_msg, reconcile.pending_req_msg->0));
            assert(resp_msg.content.get_list_response().res is Ok);
            let objs = resp_msg.content.get_list_response().res->Ok_0;
            assert(!janitor_reconciler::parent_listed(k, b, objs, parent_uid_annotation(inner)));
            assert(parent_uid_annotation(inner) == parent);
            assert(parent_absent_forever(k, b, parent)(s));
            let req = msg.content.get_delete_request();
            assert(req.key == key);
            assert(req.preconditions == Some(PreconditionsView::default().with_uid_from_object_meta(inner.metadata)));
            assert(req.preconditions->0.uid == inner.metadata.uid);
            assert(inner.metadata.uid is Some);
            assert(inner.metadata.uid->0 < s.api_server.uid_counter);
            if s.resources().contains_key(key) && s.resources()[key].metadata.uid == inner.metadata.uid && snapshot_is_mirror(inner_kind(k, b), s.resources()[key]) {
                assert(preserves_mirror_identity(reconcile.triggering_cr.metadata, s.resources()[key].metadata));
                assert(snapshot_parent(inner_kind(k, b), s.resources()[key]) == parent);
            }
        },
        _ => {
            assert(false);
        },
    }
}

}
