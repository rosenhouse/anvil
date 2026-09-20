// R4: once the outer copy is terminating and the writes that would keep it from
// being released have stopped, the sync finalizer is eventually off it for good.
//
// For an outer copy `outer` (key `key`, uid `u`, mirror key `ikey`):
//     always(outer_terminating_stable(k, b, outer)) ~> always(finalizer_released(outer))
//
// The proof has these parts, each a layer under the previous ones.
// 1. Phase I (failures are disabled), and phase II: the snapshots the sync
//    reconciler works from are terminating copies of `outer`, unless the copy is
//    released already; the only request of the sync reconciler for `key` in
//    flight is the pending one; requests and responses are consistent.
// 2. Quiet: no status write of the copy is in flight, since a teardown writes
//    none and the reconciler writes the status of live copies only; and every
//    snapshot carries the stored copy's version, since nothing writes the copy
//    but a release.
// 3. The walk. A reconcile of the copy lists the mirror key. Finding nothing
//    there, it releases the copy with the Update built from its snapshot. The
//    Update lands, or the copy was written since the snapshot, and by the
//    premise that write was a release.
//    Finding something, it reads it: not the mirror, and it releases; the mirror,
//    and it deletes it, after which the inner side releases the mirror (D3).
//    Nothing recreates the mirror (the premise), so the mirror key is empty from
//    then on, and the next reconcile finds it so and releases the copy.
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
    model::{install::*, sync_reconciler, sync_reconciler::WidgetSyncReconcileState},
    proof::{
        guarantee::*, helper_invariants::*, janitor_invariants::*,
        liveness::{api_actions::*, finalizer_proof::*, spec::*, sync_spec_proof::*, terminate},
        predicate::*, sync_invariants::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The object-level predicates of the proof.
// ---------------------------------------------------------------------------

// The object with uid `m` at the mirror key is a mirror of `outer`.
pub open spec fn mirror_of_outer_at(k: SyncKind, b: Binding, outer: SyncedObjectView, m: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let ikey = inner_key(k, outer);
        &&& s.resources().contains_key(ikey)
        &&& s.resources()[ikey].metadata.uid == Some(m)
        &&& unmarshal(inner_kind(k, b), s.resources()[ikey]) is Ok
        &&& is_mirror_of(unmarshal(inner_kind(k, b), s.resources()[ikey])->Ok_0, outer)
    }
}

pub open spec fn terminating_mirror_of_outer_at(k: SyncKind, b: Binding, outer: SyncedObjectView, m: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& mirror_of_outer_at(k, b, outer, m)(s)
        &&& s.resources()[inner_key(k, outer)].metadata.deletion_timestamp is Some
    }
}

pub open spec fn some_terminating_mirror_of_outer(k: SyncKind, b: Binding, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |m: Uid| #[trigger] terminating_mirror_of_outer_at(k, b, outer, m)(s)
}

// The mirror key holds nothing, or the mirror of `outer` with uid `m`: what a
// step keeps once the mirror is known to be there, since nothing creates at the
// key and updates keep identity.
pub open spec fn mirror_key_empty_or_holds(k: SyncKind, b: Binding, outer: SyncedObjectView, m: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| mirror_absent(k, outer)(s) || mirror_of_outer_at(k, b, outer, m)(s)
}

// A snapshot is a terminating copy of `outer`, unless the copy is released.
pub open spec fn snapshot_of_terminating_copy(k: SyncKind, outer: SyncedObjectView) -> spec_fn(DynamicObjectView, ClusterState) -> bool {
    |o: DynamicObjectView, s: ClusterState| {
        ||| finalizer_released(outer)(s)
        ||| {
            &&& o.metadata.uid == outer.metadata.uid
            &&& o.metadata.deletion_timestamp is Some
            &&& unmarshal(k.outer_kind, o) is Ok
            &&& unmarshal(k.outer_kind, o)->Ok_0.spec == outer.spec
        }
    }
}

// A snapshot carries the stored copy's version, unless the copy is released.
pub open spec fn snapshot_current_or_released(outer: SyncedObjectView) -> spec_fn(DynamicObjectView, ClusterState) -> bool {
    |o: DynamicObjectView, s: ClusterState| {
        ||| o.metadata.resource_version == s.resources()[outer.object_ref()].metadata.resource_version
        ||| finalizer_released(outer)(s)
    }
}

// ---------------------------------------------------------------------------
// The layers of the spec: premise, phase I, phase II, quiet.
// ---------------------------------------------------------------------------

pub open spec fn r4_spec_with_premise(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> TempPred<ClusterState> {
    sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id).and(always(lift_state(outer_terminating_stable(k, b, outer))))
}

pub proof fn r4_spec_with_premise_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires k.bindings.contains(b),
    ensures valid(stable(r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer))),
{
    sync_stable_spec_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id);
    always_p_is_stable(lift_state(outer_terminating_stable(k, b, outer)));
    stable_and_n!(sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_terminating_stable(k, b, outer))));
}

pub open spec fn r4_spec_with_phase_i(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> TempPred<ClusterState> {
    r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer).and(always(lift_state(phase_i(controller_id))))
}

pub proof fn r4_spec_with_phase_i_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires k.bindings.contains(b),
    ensures valid(stable(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer))),
{
    r4_spec_with_premise_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    always_p_is_stable(lift_state(phase_i(controller_id)));
    stable_and_n!(r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
}

// Phase II of R4: the snapshots are terminating copies of `outer` unless released,
// and the message facts of R1's phase II.
pub open spec fn r4_phase_ii(k: SyncKind, controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& snapshots_satisfy(controller_id, outer.object_ref(), snapshot_of_terminating_copy(k, outer))(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer.object_ref())(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())(s)
    }
}

pub open spec fn r4_spec_with_phase_ii(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> TempPred<ClusterState> {
    r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer).and(always(lift_state(r4_phase_ii(k, controller_id, outer))))
}

pub proof fn r4_spec_with_phase_ii_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires k.bindings.contains(b),
    ensures valid(stable(r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer))),
{
    r4_spec_with_phase_i_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    always_p_is_stable(lift_state(r4_phase_ii(k, controller_id, outer)));
    stable_and_n!(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(r4_phase_ii(k, controller_id, outer))));
}

// Quiet: no status write of the copy is in flight, and every snapshot carries the
// stored copy's version; each unless the copy is released.
pub open spec fn r4_quiet(controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& no_status_write_in_flight_for(controller_id, outer.object_ref())(s) || finalizer_released(outer)(s)
        &&& snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_released(outer))(s)
    }
}

pub open spec fn r4_spec_with_quiet(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> TempPred<ClusterState> {
    r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer).and(always(lift_state(r4_quiet(controller_id, outer))))
}

pub proof fn r4_spec_with_quiet_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires k.bindings.contains(b),
    ensures valid(stable(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer))),
{
    r4_spec_with_phase_ii_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    always_p_is_stable(lift_state(r4_quiet(controller_id, outer)));
    stable_and_n!(r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(r4_quiet(controller_id, outer))));
}

// Unfolding the layers.
pub proof fn lemma_unfold_r4_spec_with_phase_ii(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        spec.entails(r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id)),
        spec.entails(always(lift_state(outer_terminating_stable(k, b, outer)))),
        spec.entails(always(lift_state(phase_i(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(r4_phase_ii(k, controller_id, outer)))),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_of_terminating_copy(k, outer))))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer.object_ref())))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())))),
{
    entails_and_split(spec, r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(r4_phase_ii(k, controller_id, outer))));
    entails_and_split(spec, r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_terminating_stable(k, b, outer))));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_weaken(spec, lift_state(r4_phase_ii(k, controller_id, outer)), lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_of_terminating_copy(k, outer))));
    always_weaken(spec, lift_state(r4_phase_ii(k, controller_id, outer)), lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer.object_ref())));
    always_weaken(spec, lift_state(r4_phase_ii(k, controller_id, outer)), lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())));
}

pub proof fn lemma_unfold_r4_spec_with_quiet(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(r4_quiet(controller_id, outer)))),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_released(outer))))),
{
    entails_and_split(spec, r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(r4_quiet(controller_id, outer))));
    always_weaken(spec, lift_state(r4_quiet(controller_id, outer)), lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_released(outer))));
}

// ---------------------------------------------------------------------------
// One step of the cluster, under phase II.
// ---------------------------------------------------------------------------

// The facts about the current state the step lemmas use: the invariants R1's
// step lemmas use that do not rest on R1's premise, phase I, and R4's premise.
// In two halves, so that each is a conjunction the solver folds.
pub open spec fn r4_base_ctx_a1(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)(s)
        &&& every_mirror_is_bound(k, b)(s)
        &&& every_in_flight_inner_create_is_a_mirror_create(k)(s)
        &&& every_in_flight_inner_update_preserves_identity(k)(s)
        &&& sync_rely_with_janitor(k, b, cluster, controller_id, janitor_id)(s)
    }
}

pub open spec fn r4_base_ctx_a2(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& widget_sync_guarantee(k, controller_id)(s)
        &&& widget_janitor_guarantee(k, b, janitor_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& Cluster::every_in_flight_msg_from_controller_has_key_kind(k.outer_kind, controller_id)(s)
    }
}

pub open spec fn r4_base_ctx_a(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& r4_base_ctx_a1(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s)
        &&& r4_base_ctx_a2(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s)
    }
}

pub open spec fn r4_base_ctx_b(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& sync_pending_requests_match_snapshots(k, controller_id)(s)
        &&& snapshots_are_current(controller_id)(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer.object_ref(), at_sync_step_closure(WidgetSyncStepView::Init))(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer.object_ref(), cluster.reconcile_model(controller_id).done)(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer.object_ref(), cluster.reconcile_model(controller_id).error)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& outer_terminating_stable(k, b, outer)(s)
    }
}

pub open spec fn r4_base_ctx(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& r4_base_ctx_a(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s)
        &&& r4_base_ctx_b(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s)
    }
}

proof fn lemma_always_r4_base_ctx_a1(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_state(r4_base_ctx_a1(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    hide(Cluster::each_object_in_etcd_is_weakly_well_formed);
    hide(Cluster::each_synced_object_in_etcd_is_well_formed);
    hide(every_mirror_is_bound);
    hide(every_in_flight_inner_create_is_a_mirror_create);
    hide(every_in_flight_inner_update_preserves_identity);
    hide(sync_rely_with_janitor);
    entails_and_split(spec, r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_terminating_stable(k, b, outer))));
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_sync_rely_implies_mirror_write_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    entails_always_and_n!(
        spec,
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))),
        lift_state(cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)),
        lift_state(every_mirror_is_bound(k, b)),
        lift_state(every_in_flight_inner_create_is_a_mirror_create(k)),
        lift_state(every_in_flight_inner_update_preserves_identity(k)),
        lift_state(sync_rely_with_janitor(k, b, cluster, controller_id, janitor_id))
    );
    temp_pred_equality(
        lift_state(r4_base_ctx_a1(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
            .and(lift_state(cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))))
            .and(lift_state(cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)))
            .and(lift_state(every_mirror_is_bound(k, b)))
            .and(lift_state(every_in_flight_inner_create_is_a_mirror_create(k)))
            .and(lift_state(every_in_flight_inner_update_preserves_identity(k)))
            .and(lift_state(sync_rely_with_janitor(k, b, cluster, controller_id, janitor_id)))
    );
}

proof fn lemma_always_r4_base_ctx_a2(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_state(r4_base_ctx_a2(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    hide(widget_sync_guarantee);
    hide(widget_janitor_guarantee);
    hide(Cluster::every_in_flight_req_msg_from_controller_has_valid_controller_id);
    hide(Cluster::no_pending_request_to_api_server_from_api_server_or_external);
    hide(Cluster::all_requests_from_pod_monkey_are_api_pod_requests);
    hide(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests);
    hide(Cluster::every_in_flight_msg_from_controller_has_key_kind);
    entails_and_split(spec, r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_terminating_stable(k, b, outer))));
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    entails_always_and_n!(
        spec,
        lift_state(widget_sync_guarantee(k, controller_id)),
        lift_state(widget_janitor_guarantee(k, b, janitor_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_key_kind(k.outer_kind, controller_id))
    );
    temp_pred_equality(
        lift_state(r4_base_ctx_a2(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(widget_sync_guarantee(k, controller_id))
            .and(lift_state(widget_janitor_guarantee(k, b, janitor_id)))
            .and(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))
            .and(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()))
            .and(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()))
            .and(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))
            .and(lift_state(Cluster::every_in_flight_msg_from_controller_has_key_kind(k.outer_kind, controller_id)))
    );
}

proof fn lemma_always_r4_base_ctx_a(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_state(r4_base_ctx_a(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    lemma_always_r4_base_ctx_a1(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_always_r4_base_ctx_a2(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    combine_spec_entails_always_n!(
        spec, lift_state(r4_base_ctx_a(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(r4_base_ctx_a1(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(r4_base_ctx_a2(k, b, spec_ok, cluster, controller_id, janitor_id, outer))
    );
}

proof fn lemma_always_r4_base_ctx_b(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_state(r4_base_ctx_b(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    let key = outer.object_ref();
    entails_and_split(spec, r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_terminating_stable(k, b, outer))));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))), key);
    always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)), key);
    always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)), key);
    entails_always_and_n!(
        spec,
        lift_state(sync_pending_requests_match_snapshots(k, controller_id)),
        lift_state(snapshots_are_current(controller_id)),
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))),
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)),
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(outer_terminating_stable(k, b, outer))
    );
    temp_pred_equality(
        lift_state(r4_base_ctx_b(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(sync_pending_requests_match_snapshots(k, controller_id))
            .and(lift_state(snapshots_are_current(controller_id)))
            .and(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))))
            .and(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)))
            .and(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)))
            .and(lift_state(Cluster::there_is_the_controller_state(controller_id)))
            .and(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))
            .and(lift_state(cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)))
            .and(lift_state(Cluster::crash_disabled(controller_id)))
            .and(lift_state(Cluster::req_drop_disabled()))
            .and(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
            .and(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))
            .and(lift_state(outer_terminating_stable(k, b, outer)))
    );
}

pub proof fn lemma_always_r4_base_ctx(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_state(r4_base_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    lemma_always_r4_base_ctx_a(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_always_r4_base_ctx_b(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    combine_spec_entails_always_n!(
        spec, lift_state(r4_base_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(r4_base_ctx_a(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(r4_base_ctx_b(k, b, spec_ok, cluster, controller_id, janitor_id, outer))
    );
}

// The base facts, and phase II.
pub open spec fn r4_step_ctx(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& r4_base_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s)
        &&& r4_phase_ii(k, controller_id, outer)(s)
    }
}

// One step under the base facts, with the well-formedness of the store and the
// premise carried to the next state.
pub open spec fn r4_base_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& r4_base_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s_prime)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)(s_prime)
        &&& outer_terminating_stable(k, b, outer)(s_prime)
    }
}

pub open spec fn r4_step_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& r4_phase_ii(k, controller_id, outer)(s)
    }
}

pub proof fn lemma_always_r4_base_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_action(r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    entails_and_split(spec, r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_terminating_stable(k, b, outer))));
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_base_ctx(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    always_to_always_later(spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_to_always_later(spec, lift_state(cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))));
    always_to_always_later(spec, lift_state(cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)));
    always_to_always_later(spec, lift_state(outer_terminating_stable(k, b, outer)));
    combine_spec_entails_always_n!(
        spec, lift_action(r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_action(cluster.next()),
        lift_state(r4_base_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        later(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        later(lift_state(cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b)))),
        later(lift_state(cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind))),
        later(lift_state(outer_terminating_stable(k, b, outer)))
    );
}

pub proof fn lemma_always_r4_step_ctx(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_state(r4_step_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_always_r4_base_ctx(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    combine_spec_entails_always_n!(
        spec, lift_state(r4_step_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(r4_base_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(r4_phase_ii(k, controller_id, outer))
    );
}

pub proof fn lemma_always_r4_step_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_action(r4_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_always_r4_base_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    combine_spec_entails_always_n!(
        spec, lift_action(r4_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_action(r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(r4_phase_ii(k, controller_id, outer))
    );
}

// The snapshot of the current reconcile of the outer copy: a terminating copy of
// `outer` unless released, with the key's name and namespace, and the pending
// request the invariant says.
pub proof fn lemma_r4_current_reconcile(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_step_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s),
        s.ongoing_reconciles(controller_id).contains_key(outer.object_ref()),
    ensures
        ({
            let cr = s.ongoing_reconciles(controller_id)[outer.object_ref()].triggering_cr;
            let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
            &&& unmarshal(k.outer_kind, cr) is Ok
            &&& cr_outer.metadata == cr.metadata
            &&& cr.object_ref() == outer.object_ref()
            &&& cr.metadata.well_formed_for_namespaced()
            &&& cr_outer.kind == k.outer_kind
            &&& spec_ok(cr_outer.spec)
            &&& finalizer_released(outer)(s) || {
                &&& cr.metadata.uid == outer.metadata.uid
                &&& cr.metadata.deletion_timestamp is Some
                &&& cr_outer.spec == outer.spec
                &&& cluster_of(k.selector, cr_outer) == cluster_of(k.selector, outer)
                &&& binding_of(k, cr_outer) == binding_of(k, outer)
                &&& inner_key(k, cr_outer) == inner_key(k, outer)
                &&& parent_uid_of(cr_outer) == parent_uid_of(outer)
            }
        }),
{
    let key = outer.object_ref();
    let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
    assert(key.kind == k.outer_kind);
    assert(key.kind is CustomResourceKind);
    assert(unmarshal(k.outer_kind, cr) is Ok);
    let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
    assert(cr_outer.metadata == cr.metadata);
    assert(cr.object_ref() == key);
    assert(snapshot_of_terminating_copy(k, outer)(cr, s));
    if !finalizer_released(outer)(s) {
        assert(cr_outer.spec == outer.spec);
        assert(cr_outer.metadata.name == outer.metadata.name);
        assert(cr_outer.metadata.namespace == outer.metadata.namespace);
        assert(cluster_of(k.selector, cr_outer) == cluster_of(k.selector, outer));
        assert(binding_of(k, cr_outer) == binding_of(k, outer));
    }
}

// ---------------------------------------------------------------------------
// What one step keeps.
// ---------------------------------------------------------------------------

// One step under the premise alone.
pub open spec fn r4_premise_next(k: SyncKind, b: Binding, cluster: Cluster, outer: SyncedObjectView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& outer_terminating_stable(k, b, outer)(s)
        &&& outer_terminating_stable(k, b, outer)(s_prime)
    }
}

pub proof fn lemma_always_r4_premise_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        spec.entails(r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_action(r4_premise_next(k, b, cluster, outer)))),
{
    entails_and_split(spec, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_terminating_stable(k, b, outer))));
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    always_to_always_later(spec, lift_state(outer_terminating_stable(k, b, outer)));
    combine_spec_entails_always_n!(
        spec, lift_action(r4_premise_next(k, b, cluster, outer)),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(outer_terminating_stable(k, b, outer)),
        later(lift_state(outer_terminating_stable(k, b, outer)))
    );
}

// Released stays released: the finalizer cannot be added to a terminating
// object, and no object with the copy's uid can appear live (the premise).
pub proof fn lemma_released_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        r4_premise_next(k, b, cluster, outer)(s, s_prime),
        finalizer_released(outer)(s),
    ensures finalizer_released(outer)(s_prime),
{
    let key = outer.object_ref();
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            if s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == outer.metadata.uid
                && has_sync_finalizer(s_prime.resources()[key].metadata) {
                // The copy is terminating (the premise at s_prime).
                assert(s_prime.resources()[key].metadata.deletion_timestamp is Some);
                match msg.content->APIRequest_0 {
                    APIRequest::CreateRequest(req) => {
                        if s_prime.api_server != s.api_server {
                            // A created object is live, so it is not the copy.
                            if !s.resources().contains_key(key) || s_prime.resources()[key] != s.resources()[key] {
                                assert(s_prime.resources()[key].metadata.deletion_timestamp is None);
                                assert(false);
                            }
                        }
                    },
                    APIRequest::UpdateRequest(req) => {
                        if s_prime.api_server != s.api_server && s_prime.resources()[key] != s.resources()[key] {
                            // It landed on the terminating copy, so it added no finalizer.
                            let old = s.resources()[key];
                            assert(s.resources().contains_key(key));
                            assert(old.metadata.deletion_timestamp is Some);
                            let updated = updated_object(req, old);
                            let with_rv = updated.with_resource_version(s.api_server.resource_version_counter);
                            assert(metadata_transition_validity_check(with_rv, old) is None);
                            assert(with_rv.metadata.finalizers is Some);
                            assert(with_rv.metadata.finalizers_as_set().subset_of(old.metadata.finalizers_as_set()));
                            assert(with_rv.metadata.finalizers_as_set().contains(sync_finalizer()));
                            assert(old.metadata.finalizers_as_set().contains(sync_finalizer()));
                            assert(has_sync_finalizer(old.metadata));
                            assert(false);
                        }
                    },
                    APIRequest::GetThenUpdateRequest(req) => {
                        if s_prime.api_server != s.api_server && s_prime.resources()[key] != s.resources()[key] {
                            let old = s.resources()[key];
                            assert(s.resources().contains_key(key));
                            assert(old.metadata.deletion_timestamp is Some);
                            let updated = updated_object(UpdateRequest { namespace: req.namespace, name: req.name, obj: req.obj }, old);
                            let with_rv = updated.with_resource_version(s.api_server.resource_version_counter);
                            assert(metadata_transition_validity_check(with_rv, old) is None);
                            assert(with_rv.metadata.finalizers is Some);
                            assert(with_rv.metadata.finalizers_as_set().subset_of(old.metadata.finalizers_as_set()));
                            assert(with_rv.metadata.finalizers_as_set().contains(sync_finalizer()));
                            assert(old.metadata.finalizers_as_set().contains(sync_finalizer()));
                            assert(has_sync_finalizer(old.metadata));
                            assert(false);
                        }
                    },
                    _ => {
                        // Every other write keeps the finalizers, the uid, or removes the object.
                        if s.resources().contains_key(key) && s_prime.resources()[key] != s.resources()[key] {
                            assert(s_prime.resources()[key].metadata.finalizers == s.resources()[key].metadata.finalizers);
                            assert(false);
                        }
                    },
                }
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// The mirror key, once empty, stays empty: only a Create fills a key, and none
// in flight names the mirror key (the premise; every Create of a mirror kind is
// a named one).
pub proof fn lemma_mirror_absent_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        mirror_absent(k, outer)(s),
    ensures mirror_absent(k, outer)(s_prime),
{
    let ikey = inner_key(k, outer);
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            if s_prime.resources().contains_key(ikey) {
                match msg.content->APIRequest_0 {
                    APIRequest::CreateRequest(req) => {
                        // It created the object at the mirror key: it named it.
                        assert(s_prime.api_server != s.api_server);
                        let created = s_prime.resources()[ikey];
                        assert(req.obj.kind == ikey.kind);
                        assert(req.namespace == ikey.namespace);
                        assert(is_inner_kind(k, req.obj.kind)) by {
                            assert(ikey.kind == inner_kind(k, binding_of(k, outer)));
                        }
                        // A Create of a mirror kind is a mirror create, which names the mirror.
                        assert(req.obj.metadata.name is Some);
                        assert(req.obj.metadata.name == Some(ikey.name));
                        assert(false);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// The object at the mirror key keeps its uid while there, keeps a deletion
// timestamp once it has one, and keeps the identity of a mirror of `outer`:
// updates that land preserve identity (the rely), and nothing replaces it (no
// Create names the key).
pub proof fn lemma_mirror_key_object_after_step(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        s.resources().contains_key(inner_key(k, outer)),
        s_prime.resources().contains_key(inner_key(k, outer)),
    ensures
        s_prime.resources()[inner_key(k, outer)].metadata.uid == s.resources()[inner_key(k, outer)].metadata.uid,
        s.resources()[inner_key(k, outer)].metadata.deletion_timestamp is Some ==> s_prime.resources()[inner_key(k, outer)].metadata.deletion_timestamp is Some,
        ({
            let old = s.resources()[inner_key(k, outer)];
            let new = s_prime.resources()[inner_key(k, outer)];
            unmarshal(inner_kind(k, b), old) is Ok && is_mirror_of(unmarshal(inner_kind(k, b), old)->Ok_0, outer)
                ==> unmarshal(inner_kind(k, b), new) is Ok && is_mirror_of(unmarshal(inner_kind(k, b), new)->Ok_0, outer)
        }),
{
    let ikey = inner_key(k, outer);
    let old = s.resources()[ikey];
    let new = s_prime.resources()[ikey];
    marshal_preserves_metadata();
    assert(cluster.etcd_object_is_well_formed(ikey)(s_prime));
    assert(ikey.kind == inner_kind(k, binding_of(k, outer)));
    assert(is_inner_kind(k, ikey.kind));
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            if new != old {
                match msg.content->APIRequest_0 {
                    APIRequest::CreateRequest(req) => {
                        // The key is taken: the Create fails.
                        assert(false);
                    },
                    APIRequest::UpdateRequest(req) => {
                        assert(req.key() == ikey);
                        assert(mirror_update_req(k, req)(s));
                        assert(req.obj.metadata.resource_version == old.metadata.resource_version);
                        assert(preserves_mirror_identity(old.metadata, req.obj.metadata));
                        assert(new.metadata.labels == req.obj.metadata.labels);
                        assert(new.metadata.annotations == req.obj.metadata.annotations);
                    },
                    APIRequest::GetThenUpdateRequest(req) => {
                        assert(req.key() == ikey);
                        assert(mirror_get_then_update_req(k, req)(s));
                        assert(preserves_mirror_identity(old.metadata, req.obj.metadata));
                        assert(new.metadata.labels == req.obj.metadata.labels);
                        assert(new.metadata.annotations == req.obj.metadata.annotations);
                    },
                    APIRequest::DeleteRequest(req) => {
                        assert(new.metadata.labels == old.metadata.labels);
                        assert(new.metadata.annotations == old.metadata.annotations);
                    },
                    APIRequest::GetThenDeleteRequest(req) => {
                        assert(new.metadata.labels == old.metadata.labels);
                        assert(new.metadata.annotations == old.metadata.annotations);
                    },
                    _ => {
                        // Patches and status writes keep the metadata but the version.
                        assert(new.metadata.labels == old.metadata.labels);
                        assert(new.metadata.annotations == old.metadata.annotations);
                    },
                }
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// While the sync reconciler has no status write of the copy in flight, a step that
// changes the stored copy is a release: an Update that lands releases (the
// premise), a Patch that lands writes the spec the copy has, a Delete of a
// terminating copy with finalizers does nothing, and nobody else writes it.
pub proof fn lemma_outer_copy_unchanged_or_released_after_step(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        no_status_write_in_flight_for(controller_id, outer.object_ref())(s),
    ensures
        finalizer_released(outer)(s_prime)
            || (s.resources().contains_key(outer.object_ref()) && s_prime.resources().contains_key(outer.object_ref())
                && s_prime.resources()[outer.object_ref()] == s.resources()[outer.object_ref()]),
{
    let key = outer.object_ref();
    if finalizer_released(outer)(s) {
        lemma_released_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    } else {
        // The copy is stored, with the outer uid and the finalizer, terminating.
        assert(s.resources().contains_key(key));
        let old = s.resources()[key];
        assert(old.metadata.uid == outer.metadata.uid);
        assert(has_sync_finalizer(old.metadata));
        assert(old.metadata.deletion_timestamp is Some);
        assert(old.metadata.finalizers is Some && old.metadata.finalizers->0.len() > 0);
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let msg = input->0;
                assert(s.in_flight().contains(msg));
                assert(msg.content is APIRequest);
                match msg.content->APIRequest_0 {
                    APIRequest::UpdateRequest(req) => {
                        if req.key() == key && s_prime.api_server != s.api_server {
                            // It landed, so it carries the stored version and, by the
                            // premise, no sync finalizer.
                            assert(req.obj.metadata.resource_version == old.metadata.resource_version);
                            assert(!has_sync_finalizer(req.obj.metadata));
                            assert(s_prime.resources().contains_key(key) ==> s_prime.resources()[key].metadata.finalizers == req.obj.metadata.finalizers);
                        }
                    },
                    APIRequest::GetThenUpdateRequest(req) => {
                        if req.key() == key && s_prime.api_server != s.api_server {
                            assert(!has_sync_finalizer(req.obj.metadata));
                            assert(s_prime.resources().contains_key(key) ==> s_prime.resources()[key].metadata.finalizers == req.obj.metadata.finalizers);
                        }
                    },
                    APIRequest::PatchRequest(req) => {
                        if req.key() == key && s_prime.api_server != s.api_server {
                            // A patch that lands writes the outer spec, which the copy has.
                            assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                            assert(old.metadata.namespace == Some(req.namespace));
                            assert(unmarshal(k.outer_kind, old)->Ok_0.spec == outer.spec);
                            marshal_preserves_metadata();
                            assert(old.spec == outer.spec);
                            assert(s_prime.resources()[key].spec == req.spec);
                            assert(s_prime.resources()[key].spec == outer.spec);
                            assert(req.spec == old.spec);
                            assert(old.with_spec(req.spec) == old);
                            assert(false);
                        }
                    },
                    APIRequest::DeleteRequest(req) => {
                        if req.key() == key && s_prime.api_server != s.api_server {
                            // A terminating object with finalizers is left as it is.
                            assert(false);
                        }
                    },
                    APIRequest::GetThenDeleteRequest(req) => {
                        if req.key() == key && s_prime.api_server != s.api_server {
                            assert(false);
                        }
                    },
                    APIRequest::PatchStatusRequest(req) => {
                        if req.key() == key {
                            match msg.src {
                                HostId::Controller(id, okey) => {
                                    if id == controller_id {
                                        assert(widget_sync_guarantee(k, controller_id)(s));
                                        assert(sync_status_patch_req(k, req, okey));
                                        assert(okey.kind == k.outer_kind);
                                        assert(okey == key);
                                        assert(false);
                                    } else if id == janitor_id {
                                        assert(false);
                                    } else {
                                        assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                        assert(widget_sync_rely(k, id)(s));
                                        assert(req.kind != k.outer_kind);
                                        assert(false);
                                    }
                                },
                                _ => { assert(false); },
                            }
                        }
                    },
                    APIRequest::UpdateStatusRequest(req) => {
                        if req.key() == key {
                            match msg.src {
                                HostId::Controller(id, okey) => {
                                    if id == controller_id {
                                        assert(widget_sync_guarantee(k, controller_id)(s));
                                        assert(false);
                                    } else if id == janitor_id {
                                        assert(false);
                                    } else {
                                        assert(widget_sync_rely(k, id)(s));
                                        assert(req.obj.kind != k.outer_kind);
                                        assert(false);
                                    }
                                },
                                _ => { assert(false); },
                            }
                        }
                    },
                    APIRequest::GetThenUpdateStatusRequest(req) => {
                        if req.key() == key {
                            match msg.src {
                                HostId::Controller(id, okey) => {
                                    if id == controller_id {
                                        assert(widget_sync_guarantee(k, controller_id)(s));
                                        assert(false);
                                    } else if id == janitor_id {
                                        assert(false);
                                    } else {
                                        assert(widget_sync_rely(k, id)(s));
                                        assert(req.obj.kind != k.outer_kind);
                                        assert(false);
                                    }
                                },
                                _ => { assert(false); },
                            }
                        }
                    },
                    APIRequest::CreateRequest(_) => {
                        assert(s_prime.resources()[key] == old);
                    },
                    _ => {
                        assert(s_prime.api_server == s.api_server);
                    },
                }
            },
            _ => {
                assert(s_prime.api_server == s.api_server);
            },
        }
    }
}

// While the copy is not released, the sync reconciler has no status write of it
// in flight: a status is written by a reconcile of a live copy it owns, or of one
// it refuses, and the snapshots are terminating copies of `outer` (phase II).
pub proof fn lemma_no_status_write_in_flight_unless_released(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_step_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s),
        !finalizer_released(outer)(s),
    ensures no_status_write_in_flight_for(controller_id, outer.object_ref())(s),
{
    let key = outer.object_ref();
    assert forall |m: Message| #![trigger s.in_flight().contains(m)] {
        &&& s.in_flight().contains(m)
        &&& m.src == HostId::Controller(controller_id, key)
        &&& m.dst is APIServer
        &&& m.content is APIRequest
    } implies !(m.content->APIRequest_0 is PatchStatusRequest) by {
        assert(s.ongoing_reconciles(controller_id).contains_key(key));
        assert(Cluster::pending_req_msg_is(controller_id, s, key, m));
        let reconcile = s.ongoing_reconciles(controller_id)[key];
        assert(sync_pending_request_is(k, controller_id, key, reconcile));
        lemma_r4_current_reconcile(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
        let cr = reconcile.triggering_cr;
        let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
        let step = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
        if m.content->APIRequest_0 is PatchStatusRequest {
            assert(step is AfterPatchOuterStatus || step is AfterReportError) by {
                assert(!(step is Init));
                assert(!(step is Done) && !(step is Error));
            }
            // The snapshot is terminating, so its reconcile owns no live copy; and
            // it names the copy's cluster, which the reconciler serves.
            assert(cr_outer.metadata.deletion_timestamp is Some);
            assert(cluster_of(k.selector, cr_outer) is Some);
            assert(serves(k, cr_outer));
            assert(false);
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers: the finalizers after a release, and what a List of the mirror key
// answers.
// ---------------------------------------------------------------------------

// Removing the sync finalizer leaves a subset of the finalizers, without it.
pub proof fn lemma_without_sync_finalizer(meta: ObjectMetaView)
    ensures
        !has_sync_finalizer(without_sync_finalizer(meta)),
        without_sync_finalizer(meta).finalizers_as_set().subset_of(meta.finalizers_as_set()),
{
    broadcast use Seq::lemma_filter_pred;
    broadcast use Seq::lemma_filter_contains_rev;
    let all = finalizers_or_empty(meta);
    let pred = not_sync_finalizer();
    let rest = all.filter(pred);
    if rest.len() > 0 {
        assert(!rest.contains(sync_finalizer())) by {
            if rest.contains(sync_finalizer()) {
                let i = choose |i: int| 0 <= i < rest.len() && rest[i] == sync_finalizer();
                assert(pred(rest[i]));
            }
        }
        assert forall |f: StringView| #[trigger] rest.to_set().contains(f) implies meta.finalizers_as_set().contains(f) by {
            assert(rest.contains(f));
            assert(all.contains(f));
            assert(meta.finalizers is Some);
        }
    }
}

// A List of the mirror key of `cr_outer` answers with an object at that key iff
// the store holds one: every object listed is a stored one, at the key its
// metadata names, and the stored one, if any, is listed.
pub proof fn lemma_mirror_list_answer(k: SyncKind, s: ClusterState, cr_outer: SyncedObjectView)
    requires Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    ensures
        sync_reconciler::listed_at(handle_list_request(sync_reconciler::mirror_list(k, cr_outer), s.api_server).res->Ok_0, inner_key(k, cr_outer))
            == s.resources().contains_key(inner_key(k, cr_outer)),
{
    let req = sync_reconciler::mirror_list(k, cr_outer);
    let ikey = inner_key(k, cr_outer);
    let selected = s.resources().values().filter(|o: DynamicObjectView| {
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
        &&& o.object_ref().name == req.name->0
    });
    let objs = selected.to_seq();
    assert(req.name is Some);
    assert(handle_list_request(req, s.api_server).res->Ok_0 == objs);
    lemma_set_to_seq_contains_all_elements(selected);
    if sync_reconciler::listed_at(objs, ikey) {
        let i = choose |i: int| 0 <= i < objs.len() && sync_reconciler::is_at(#[trigger] objs[i], ikey);
        let o = objs[i];
        assert(objs.contains(o));
        assert(selected.contains(o));
        assert(s.resources().values().contains(o));
        let okey = choose |okey: ObjectRef| #[trigger] s.resources().dom().contains(okey) && s.resources()[okey] == o;
        assert(s.resources().contains_key(okey));
        assert(Cluster::etcd_object_is_weakly_well_formed(okey)(s));
        assert(o.object_ref() == okey);
        assert(okey == ikey);
    }
    if s.resources().contains_key(ikey) {
        let o = s.resources()[ikey];
        assert(Cluster::etcd_object_is_weakly_well_formed(ikey)(s));
        assert(o.object_ref() == ikey);
        assert(s.resources().dom().contains(ikey) && s.resources()[ikey] == o);
        assert(s.resources().values().contains(o));
        assert(selected.contains(o));
        assert(objs.contains(o));
        let i = choose |i: int| 0 <= i < objs.len() && objs[i] == o;
        assert(sync_reconciler::is_at(objs[i], ikey));
    }
}

// Under the quiet layer, a reconcile of a copy that is not released works from the
// stored copy itself: terminating, carrying the sync finalizer, naming a cluster
// the reconciler serves.
pub proof fn lemma_r4_current_snapshot_is_stored(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_step_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s),
        r4_quiet(controller_id, outer)(s),
        s.ongoing_reconciles(controller_id).contains_key(outer.object_ref()),
        !finalizer_released(outer)(s),
    ensures
        ({
            let key = outer.object_ref();
            let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
            let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
            &&& unmarshal(k.outer_kind, cr) is Ok
            &&& cr_outer.metadata == cr.metadata
            &&& cr.object_ref() == key
            &&& cr.metadata.well_formed_for_namespaced()
            &&& cr_outer.kind == k.outer_kind
            &&& spec_ok(cr_outer.spec)
            &&& s.resources().contains_key(key)
            &&& s.resources()[key] == cr
            &&& cr.metadata.uid == outer.metadata.uid
            &&& cr.metadata.deletion_timestamp is Some
            &&& has_sync_finalizer(cr.metadata)
            &&& cr_outer.spec == outer.spec
            &&& cluster_of(k.selector, cr_outer) is Some
            &&& binding_of(k, cr_outer) == b
            &&& serves(k, cr_outer)
            &&& inner_key(k, cr_outer) == inner_key(k, outer)
            &&& parent_uid_of(cr_outer) == parent_uid_of(outer)
        }),
{
    let key = outer.object_ref();
    lemma_r4_current_reconcile(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
    let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
    let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
    assert(snapshot_current_or_released(outer)(cr, s));
    assert(s.resources().contains_key(key));
    assert(snapshot_is_current_at(key, cr, s));
    assert(s.resources()[key] == cr);
    if !has_sync_finalizer(cr.metadata) {
        assert(finalizer_released(outer)(s));
    }
    assert(binding_of(k, cr_outer) == b);
}

// ---------------------------------------------------------------------------
// The states of the walk.
// ---------------------------------------------------------------------------

// The List of the mirror key, built from the snapshot `cr`.
pub open spec fn list_req_msg_for(k: SyncKind, controller_id: int, outer: SyncedObjectView, msg: Message, cr: DynamicObjectView) -> bool {
    &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& msg.content->APIRequest_0 == APIRequest::ListRequest(sync_reconciler::mirror_list(k, unmarshal(k.outer_kind, cr)->Ok_0))
}

pub open spec fn st_list_req_msg_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        &&& at_sync_step(controller_id, key, WidgetSyncStepView::AfterListMirror)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg)
        &&& list_req_msg_for(k, controller_id, outer, msg, cr)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_list_req_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |msg: Message| #[trigger] st_list_req_msg_in_flight(k, controller_id, outer, msg)(s)
}

// The answer to the List is in flight. It is always a successful one.
pub open spec fn st_list_resp_msg_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView, resp: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        &&& at_sync_step(controller_id, key, WidgetSyncStepView::AfterListMirror)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& list_req_msg_for(k, controller_id, outer, msg, cr)
        &&& s.in_flight().contains(resp)
        &&& resp_msg_matches_req_msg(resp, msg)
        &&& resp.content.get_list_response().res is Ok
    }
}

pub open spec fn st_list_resp_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |resp: Message| #[trigger] st_list_resp_msg_in_flight(k, controller_id, outer, resp)(s)
}

// The answer lists nothing at the mirror key the snapshot names.
pub open spec fn st_list_resp_unlisted_msg_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView, resp: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let cr = s.ongoing_reconciles(controller_id)[outer.object_ref()].triggering_cr;
        &&& st_list_resp_msg_in_flight(k, controller_id, outer, resp)(s)
        &&& !sync_reconciler::listed_at(resp.content.get_list_response().res->Ok_0, inner_key(k, unmarshal(k.outer_kind, cr)->Ok_0))
    }
}

pub open spec fn st_list_resp_unlisted_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |resp: Message| #[trigger] st_list_resp_unlisted_msg_in_flight(k, controller_id, outer, resp)(s)
}

// The Update that removes the finalizer, built from the snapshot `cr`.
pub open spec fn remove_req_msg_for(k: SyncKind, controller_id: int, outer: SyncedObjectView, msg: Message, cr: DynamicObjectView) -> bool {
    &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& msg.content->APIRequest_0 == APIRequest::UpdateRequest(sync_reconciler::outer_finalizer_update(unmarshal(k.outer_kind, cr)->Ok_0, false))
}

pub open spec fn st_remove_req_msg_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        &&& at_sync_step(controller_id, key, WidgetSyncStepView::AfterRemoveFinalizer)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg)
        &&& remove_req_msg_for(k, controller_id, outer, msg, cr)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_remove_req_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |msg: Message| #[trigger] st_remove_req_msg_in_flight(k, controller_id, outer, msg)(s)
}

// The Get of the mirror key, sent by the teardown.
pub open spec fn st_get_mirror_req_msg_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        &&& at_sync_step(controller_id, key, WidgetSyncStepView::AfterGetMirror)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg)
        &&& get_req_msg_for(k, controller_id, outer, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_get_mirror_req_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |msg: Message| #[trigger] st_get_mirror_req_msg_in_flight(k, controller_id, outer, msg)(s)
}

// What the answer to the Get says about the store now: the mirror key was empty
// and still is; or it held the object read, which is still there with that uid
// (nothing replaces it), terminating if it was, a mirror of `outer` if it was,
// unless the key is empty by now.
pub open spec fn get_mirror_resp_reflects_store(k: SyncKind, b: Binding, resp: Message, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let ikey = inner_key(k, outer);
        let res = resp.content.get_get_response().res;
        let obj = res->Ok_0;
        &&& res is Err ==> res->Err_0 is ObjectNotFound && mirror_absent(k, outer)(s)
        &&& res is Ok ==> {
            &&& obj.metadata.uid is Some
            &&& unmarshal(inner_kind(k, b), obj) is Ok
            &&& mirror_absent(k, outer)(s) || {
                &&& s.resources().contains_key(ikey)
                &&& s.resources()[ikey].metadata.uid == obj.metadata.uid
                &&& obj.metadata.deletion_timestamp is Some ==> s.resources()[ikey].metadata.deletion_timestamp is Some
                &&& is_mirror_of(unmarshal(inner_kind(k, b), obj)->Ok_0, outer) ==> mirror_of_outer_at(k, b, outer, obj.metadata.uid->0)(s)
            }
        }
    }
}

pub open spec fn st_get_mirror_resp_msg_in_flight(k: SyncKind, b: Binding, controller_id: int, outer: SyncedObjectView, resp: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& at_sync_step(controller_id, key, WidgetSyncStepView::AfterGetMirror)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& get_req_msg_for(k, controller_id, outer, msg)
        &&& s.in_flight().contains(resp)
        &&& resp_msg_matches_req_msg(resp, msg)
        &&& get_mirror_resp_reflects_store(k, b, resp, outer)(s)
    }
}

pub open spec fn st_get_mirror_resp_in_flight(k: SyncKind, b: Binding, controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |resp: Message| #[trigger] st_get_mirror_resp_msg_in_flight(k, b, controller_id, outer, resp)(s)
}

// The Delete of the mirror with uid `m`, pinned to that uid.
pub open spec fn delete_req_msg_for(k: SyncKind, controller_id: int, outer: SyncedObjectView, msg: Message, m: Uid) -> bool {
    let req = msg.content->APIRequest_0->DeleteRequest_0;
    &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& msg.content->APIRequest_0 is DeleteRequest
    &&& req.key == inner_key(k, outer)
    &&& req.preconditions is Some
    &&& req.preconditions->0.uid == Some(m)
    &&& req.preconditions->0.resource_version is None
}

// The Delete is in flight, and the mirror key is empty or holds the mirror it names.
pub open spec fn st_delete_req_msg_in_flight(k: SyncKind, b: Binding, controller_id: int, outer: SyncedObjectView, msg: Message, m: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        &&& at_sync_step(controller_id, key, WidgetSyncStepView::AfterDeleteMirror)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg)
        &&& delete_req_msg_for(k, controller_id, outer, msg, m)
        &&& s.in_flight().contains(msg)
        &&& mirror_key_empty_or_holds(k, b, outer, m)(s)
    }
}

pub open spec fn st_delete_req_in_flight(k: SyncKind, b: Binding, controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |i: (Message, Uid)| #[trigger] st_delete_req_msg_in_flight(k, b, controller_id, outer, i.0, i.1)(s)
}

// The mirror key is empty, or holds the terminating mirror with uid `m`.
pub open spec fn mirror_key_empty_or_terminating(k: SyncKind, b: Binding, outer: SyncedObjectView, m: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| mirror_absent(k, outer)(s) || terminating_mirror_of_outer_at(k, b, outer, m)(s)
}

// The action the walk's step lemmas assume: one step under phase II, from a
// quiet state.
pub open spec fn r4_walk_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& r4_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& r4_quiet(controller_id, outer)(s)
    }
}

pub proof fn lemma_always_r4_walk_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_action(r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_always_r4_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    combine_spec_entails_always_n!(
        spec, lift_action(r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_action(r4_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(r4_quiet(controller_id, outer))
    );
}

// ---------------------------------------------------------------------------
// What one step keeps of the walk's states.
// ---------------------------------------------------------------------------

// A pending request of the reconcile of the outer copy stays pending and in
// flight through any step but the one that answers it: the reconcile cannot
// move on without the answer, and nothing else touches the message.
pub proof fn lemma_r4_pending_req_stays(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, msg: Message
)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        s.ongoing_reconciles(controller_id).contains_key(outer.object_ref()),
        s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg == Some(msg),
        msg.src == HostId::Controller(controller_id, outer.object_ref()),
        msg.dst is APIServer,
        msg.content is APIRequest,
        s.in_flight().contains(msg),
        !cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures
        s_prime.ongoing_reconciles(controller_id).contains_key(outer.object_ref()),
        s_prime.ongoing_reconciles(controller_id)[outer.object_ref()] == s.ongoing_reconciles(controller_id)[outer.object_ref()],
        s_prime.in_flight().contains(msg),
{
    let key = outer.object_ref();
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(i) => {
            assert(i->0 != msg);
            assert(s_prime.in_flight().contains(msg));
            assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
        },
        Step::ControllerStep(i) => {
            if i.0 == controller_id && i.2 == Some(key) {
                assert(i.1 is Some);
                assert(s.in_flight().contains(i.1->0) && resp_msg_matches_req_msg(i.1->0, msg));
                assert(false);
            } else {
                assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                assert(s_prime.in_flight().contains(msg));
            }
        },
        Step::RestartControllerStep(id) => {
            assert(id != controller_id);
        },
        _ => {
            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            assert(s_prime.in_flight().contains(msg));
        },
    }
}

// The answer to a pending request stays in flight, and the reconcile where it
// is, through any step but the one that consumes it.
pub proof fn lemma_r4_pending_resp_stays(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, resp: Message
)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        s.ongoing_reconciles(controller_id).contains_key(outer.object_ref()),
        s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg is Some,
        ({
            let msg = s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg->0;
            &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
            &&& resp_msg_matches_req_msg(resp, msg)
        }),
        s.in_flight().contains(resp),
        !cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp), Some(outer.object_ref())))),
    ensures
        s_prime.ongoing_reconciles(controller_id).contains_key(outer.object_ref()),
        s_prime.ongoing_reconciles(controller_id)[outer.object_ref()] == s.ongoing_reconciles(controller_id)[outer.object_ref()],
        s_prime.in_flight().contains(resp),
{
    let key = outer.object_ref();
    let pending = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::ControllerStep(i) => {
            if i.0 == controller_id && i.2 == Some(key) {
                assert(i.1 is Some);
                let other = i.1->0;
                assert(s.in_flight().contains(other) && resp_msg_matches_req_msg(other, pending));
                assert(other.rpc_id == resp.rpc_id);
                assert(other == resp);
                assert(false);
            } else {
                assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                if !s_prime.in_flight().contains(resp) {
                    assert(i.1 == Some(resp));
                    assert(resp.dst == HostId::Controller(controller_id, key));
                    assert(resp.dst == HostId::Controller(i.0, i.2->0));
                    assert(false);
                }
            }
        },
        Step::RestartControllerStep(id) => {
            assert(id != controller_id);
        },
        Step::APIServerStep(i) => {
            assert(i->0 != resp);
            assert(s_prime.in_flight().contains(resp));
            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
        },
        Step::DropReqStep(i) => {
            assert(i.0 != resp);
            assert(s_prime.in_flight().contains(resp));
        },
        Step::ExternalStep(i) => {
            assert(i.1 != Some(resp));
            assert(s_prime.in_flight().contains(resp));
        },
        _ => {
            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            assert(s_prime.in_flight().contains(resp));
        },
    }
}

// The answer to the Get keeps reflecting the store: an empty key stays empty, an
// object at the key keeps its uid, stays terminating, and stays a mirror.
pub proof fn lemma_get_mirror_resp_keeps_reflecting_store(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, resp: Message
)
    requires
        k.bindings.contains(b),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        get_mirror_resp_reflects_store(k, b, resp, outer)(s),
    ensures get_mirror_resp_reflects_store(k, b, resp, outer)(s_prime),
{
    let ikey = inner_key(k, outer);
    let res = resp.content.get_get_response().res;
    if mirror_absent(k, outer)(s) {
        lemma_mirror_absent_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    } else if res is Ok && !mirror_absent(k, outer)(s_prime) {
        lemma_mirror_key_object_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    }
}

// ---------------------------------------------------------------------------
// The walk: idle ~> scheduled ~> Init ~> List ~> ...
// ---------------------------------------------------------------------------

// idle ~> scheduled, unless the copy is released: a reconcile of the copy is
// scheduled while it is stored, and a copy that is not stored is released.
pub proof fn lemma_r4_idle_leads_to_scheduled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(Cluster::reconcile_idle(controller_id, outer.object_ref()))
            .leads_to(lift_state(|s: ClusterState| {
                &&& !s.ongoing_reconciles(controller_id).contains_key(outer.object_ref())
                &&& s.scheduled_reconciles(controller_id).contains_key(outer.object_ref())
            }).or(lift_state(finalizer_released(outer))))),
{
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    let sched = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
    };
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& !s.scheduled_reconciles(controller_id).contains_key(key)
        &&& s.resources().contains_key(key)
    };
    let post = |s: ClusterState| sched(s) || !s.resources().contains_key(key);
    let next = cluster.next();
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
        && cluster.schedule_controller_reconcile().forward((controller_id, key))(s, s_prime) implies post(s_prime) by {}
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.schedule_controller_reconcile().pre((controller_id, key))(s) by {
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, key, next, pre, post);
    let rest = |s: ClusterState| Cluster::reconcile_idle(controller_id, key)(s) && !pre(s);
    entails_implies_leads_to(spec, lift_state(rest), lift_state(post));
    or_leads_to(spec, lift_state(pre), lift_state(rest), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(rest)), lift_state(Cluster::reconcile_idle(controller_id, key)));
    entails_implies_leads_to(spec, lift_state(post), lift_state(sched).or(lift_state(finalizer_released(outer))));
    leads_to_trans(spec, lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post), lift_state(sched).or(lift_state(finalizer_released(outer))));
}

// scheduled ~> Init with no pending request.
pub proof fn lemma_r4_scheduled_leads_to_init(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
                &&& !s.ongoing_reconciles(controller_id).contains_key(outer.object_ref())
                &&& s.scheduled_reconciles(controller_id).contains_key(outer.object_ref())
            }).leads_to(lift_state(st_sync_init(controller_id, outer.object_ref())))),
{
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_r4_scheduled_leads_to_init_core(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
}

// The step itself, with only the facts it uses in context.
proof fn lemma_r4_scheduled_leads_to_init_core(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
                &&& !s.ongoing_reconciles(controller_id).contains_key(outer.object_ref())
                &&& s.scheduled_reconciles(controller_id).contains_key(outer.object_ref())
            }).leads_to(lift_state(st_sync_init(controller_id, outer.object_ref())))),
{
    let key = outer.object_ref();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
    };
    let post = st_sync_init(controller_id, key);
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
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == sync_reconciler::reconcile_init_state().marshal());
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is None);
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == sync_reconciler::reconcile_init_state().marshal());
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::RunScheduledReconcile, (controller_id, input.0, input.1))(s) by {
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, pre, post);
}

// Init ~> the List of the mirror key is in flight, unless the copy is released.
pub proof fn lemma_r4_init_leads_to_list_req(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_sync_init(controller_id, outer.object_ref()))
            .leads_to(lift_state(st_list_req_in_flight(k, controller_id, outer)).or(lift_state(finalizer_released(outer))))),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let pre = st_sync_init(controller_id, key);
    let post = |s: ClusterState| st_list_req_in_flight(k, controller_id, outer)(s) || finalizer_released(outer)(s);
    let input = (None::<Message>, Some(key));
    let next = r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.api_server == s.api_server);
        if finalizer_released(outer)(s) {
            assert(finalizer_released(outer)(s_prime));
        } else {
            lemma_r4_current_snapshot_is_stored(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
            let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
            let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
            let req = APIRequest::ListRequest(sync_reconciler::mirror_list(k, cr_outer));
            let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == cr);
            assert(s_prime.in_flight().contains(msg));
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == sync_reconciler::at_step(WidgetSyncStepView::AfterListMirror).marshal());
            assert(list_req_msg_for(k, controller_id, outer, msg, cr));
            assert(st_list_req_msg_in_flight(k, controller_id, outer, msg)(s_prime));
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(i) => {
                if i.0 == controller_id && i.2 == Some(key) {
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
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, next, ControllerStep::ContinueReconcile, pre, post);
    temp_pred_equality(lift_state(post), lift_state(st_list_req_in_flight(k, controller_id, outer)).or(lift_state(finalizer_released(outer))));
}

// The API server answers the List: with the objects at the mirror key, none of
// them when the key is empty.
proof fn lemma_r4_list_req_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, msg: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        st_list_req_msg_in_flight(k, controller_id, outer, msg)(s),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures
        st_list_resp_in_flight(k, controller_id, outer)(s_prime),
        mirror_absent(k, outer)(s) ==> finalizer_released(outer)(s_prime) || st_list_resp_unlisted_in_flight(k, controller_id, outer)(s_prime),
{
    hide(sync_reconciler::reconcile_core);
    let key = outer.object_ref();
    let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
    let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
    let req = sync_reconciler::mirror_list(k, cr_outer);
    let resp = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
    assert(s_prime.in_flight().contains(resp));
    assert(resp_msg_matches_req_msg(resp, msg));
    assert(s_prime.api_server == s.api_server);
    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
    assert(resp.content.get_list_response() == handle_list_request(req, s.api_server));
    assert(resp.content.get_list_response().res is Ok);
    assert(st_list_resp_msg_in_flight(k, controller_id, outer, resp)(s_prime));
    if mirror_absent(k, outer)(s) && !finalizer_released(outer)(s) {
        lemma_r4_current_snapshot_is_stored(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
        lemma_mirror_list_answer(k, s, cr_outer);
        assert(!sync_reconciler::listed_at(resp.content.get_list_response().res->Ok_0, inner_key(k, cr_outer)));
        assert(st_list_resp_unlisted_msg_in_flight(k, controller_id, outer, resp)(s_prime));
    }
}

// The List in flight ~> its answer is in flight.
pub proof fn lemma_r4_list_req_leads_to_list_resp(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_list_req_in_flight(k, controller_id, outer))
            .leads_to(lift_state(st_list_resp_in_flight(k, controller_id, outer)))),
{
    hide(sync_reconciler::reconcile_core);
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    let next = r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let post = st_list_resp_in_flight(k, controller_id, outer);
    let pre_of = |msg: Message| lift_state(st_list_req_msg_in_flight(k, controller_id, outer, msg));
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_list_req_msg_in_flight(k, controller_id, outer, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_r4_list_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            if cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))) {
                lemma_r4_list_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
            } else {
                lemma_r4_pending_req_stays(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_list_req_in_flight(k, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_list_req_in_flight(k, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = choose |msg: Message| #[trigger] st_list_req_msg_in_flight(k, controller_id, outer, msg)(s);
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_list_req_in_flight(k, controller_id, outer)));
    });
}

// While the mirror key is empty for good: the List in flight ~> an answer that
// lists nothing at the key, unless the copy is released.
pub proof fn lemma_r4_list_req_leads_to_unlisted_resp(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(mirror_absent(k, outer)))),
    ensures
        spec.entails(lift_state(st_list_req_in_flight(k, controller_id, outer))
            .leads_to(lift_state(st_list_resp_unlisted_in_flight(k, controller_id, outer)).or(lift_state(finalizer_released(outer))))),
{
    hide(sync_reconciler::reconcile_core);
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    let next = |s, s_prime: ClusterState| {
        &&& r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& mirror_absent(k, outer)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_state(mirror_absent(k, outer))
    );
    let post = |s: ClusterState| st_list_resp_unlisted_in_flight(k, controller_id, outer)(s) || finalizer_released(outer)(s);
    let pre_of = |msg: Message| lift_state(st_list_req_msg_in_flight(k, controller_id, outer, msg));
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_list_req_msg_in_flight(k, controller_id, outer, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_r4_list_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            if cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))) {
                lemma_r4_list_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
            } else {
                lemma_r4_pending_req_stays(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_list_req_in_flight(k, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_list_req_in_flight(k, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = choose |msg: Message| #[trigger] st_list_req_msg_in_flight(k, controller_id, outer, msg)(s);
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_list_req_in_flight(k, controller_id, outer)));
    });
    temp_pred_equality(lift_state(post), lift_state(st_list_resp_unlisted_in_flight(k, controller_id, outer)).or(lift_state(finalizer_released(outer))));
}

// The sync reconciler consumes the answer to the List: nothing at the key, and it
// sends the Update that releases; something there, and it sends the Get.
proof fn lemma_r4_list_resp_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, resp: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        st_list_resp_msg_in_flight(k, controller_id, outer, resp)(s),
        cluster.controller_next().forward((controller_id, Some(resp), Some(outer.object_ref())))(s, s_prime),
    ensures
        st_remove_req_in_flight(k, controller_id, outer)(s_prime) || st_get_mirror_req_in_flight(k, controller_id, outer)(s_prime) || finalizer_released(outer)(s_prime),
        st_list_resp_unlisted_msg_in_flight(k, controller_id, outer, resp)(s) ==> st_remove_req_in_flight(k, controller_id, outer)(s_prime),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
    let key = outer.object_ref();
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    lemma_r4_current_reconcile(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
    let reconcile = s.ongoing_reconciles(controller_id)[key];
    let cr = reconcile.triggering_cr;
    let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
    let res = resp.content.get_list_response().res;
    let resp_o = Some(ResponseView::<VoidERespView>::KResponse(resp.content->APIResponse_0));
    assert(is_some_k_list_resp_view(resp_o));
    assert(extract_some_k_list_resp_view(resp_o) == res);
    let (state_prime, req_o) = sync_reconciler::reconcile_core(k, cr_outer, resp_o, sync_reconciler::at_step(WidgetSyncStepView::AfterListMirror));
    assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == state_prime.marshal());
    assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == cr);
    assert(s_prime.api_server == s.api_server);
    let ikey_cr = inner_key(k, cr_outer);
    if !sync_reconciler::listed_at(res->Ok_0, ikey_cr) {
        let req = APIRequest::UpdateRequest(sync_reconciler::outer_finalizer_update(cr_outer, false));
        let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
        assert(s_prime.in_flight().contains(msg));
        assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == sync_reconciler::at_step(WidgetSyncStepView::AfterRemoveFinalizer).marshal());
        assert(remove_req_msg_for(k, controller_id, outer, msg, cr));
        assert(st_remove_req_msg_in_flight(k, controller_id, outer, msg)(s_prime));
    } else if finalizer_released(outer)(s) {
        assert(finalizer_released(outer)(s_prime));
    } else {
        lemma_r4_current_snapshot_is_stored(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
        let req = APIRequest::GetRequest(GetRequest { key: ikey_cr });
        let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
        assert(s_prime.in_flight().contains(msg));
        assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == sync_reconciler::at_step(WidgetSyncStepView::AfterGetMirror).marshal());
        assert(get_req_msg_for(k, controller_id, outer, msg));
        assert(st_get_mirror_req_msg_in_flight(k, controller_id, outer, msg)(s_prime));
    }
}

// The answer to the List in flight ~> the Update that releases or the Get of the
// mirror key is in flight, unless the copy is released.
pub proof fn lemma_r4_list_resp_leads_to_decision(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_list_resp_in_flight(k, controller_id, outer))
            .leads_to(lift_state(st_remove_req_in_flight(k, controller_id, outer))
                .or(lift_state(st_get_mirror_req_in_flight(k, controller_id, outer)))
                .or(lift_state(finalizer_released(outer))))),
{
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    let next = r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let post = |s: ClusterState| {
        ||| st_remove_req_in_flight(k, controller_id, outer)(s)
        ||| st_get_mirror_req_in_flight(k, controller_id, outer)(s)
        ||| finalizer_released(outer)(s)
    };
    let pre_of = |resp: Message| lift_state(st_list_resp_msg_in_flight(k, controller_id, outer, resp));
    assert forall |resp: Message| spec.entails(#[trigger] pre_of(resp).leads_to(lift_state(post))) by {
        let pre = st_list_resp_msg_in_flight(k, controller_id, outer, resp);
        let input = (Some(resp), Some(key));
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
            && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
            lemma_r4_list_resp_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            if cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp), Some(key)))) {
                lemma_r4_list_resp_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
            } else {
                lemma_r4_pending_resp_stays(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::ContinueReconcile, (controller_id, input.0, input.1))(s) by {
            assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
            assert(resp.content is APIResponse);
        }
        cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, next, ControllerStep::ContinueReconcile, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_list_resp_in_flight(k, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_list_resp_in_flight(k, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let resp = choose |resp: Message| #[trigger] st_list_resp_msg_in_flight(k, controller_id, outer, resp)(s);
            assert(pre_of(resp).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_list_resp_in_flight(k, controller_id, outer)));
    });
    temp_pred_equality(
        lift_state(post),
        lift_state(st_remove_req_in_flight(k, controller_id, outer)).or(lift_state(st_get_mirror_req_in_flight(k, controller_id, outer))).or(lift_state(finalizer_released(outer)))
    );
}

// An answer that lists nothing at the key ~> the Update that releases is in flight.
pub proof fn lemma_r4_unlisted_resp_leads_to_remove_req(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_list_resp_unlisted_in_flight(k, controller_id, outer))
            .leads_to(lift_state(st_remove_req_in_flight(k, controller_id, outer)))),
{
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    let next = r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let post = st_remove_req_in_flight(k, controller_id, outer);
    let pre_of = |resp: Message| lift_state(st_list_resp_unlisted_msg_in_flight(k, controller_id, outer, resp));
    assert forall |resp: Message| spec.entails(#[trigger] pre_of(resp).leads_to(lift_state(post))) by {
        let pre = st_list_resp_unlisted_msg_in_flight(k, controller_id, outer, resp);
        let input = (Some(resp), Some(key));
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
            && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
            lemma_r4_list_resp_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            if cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp), Some(key)))) {
                lemma_r4_list_resp_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
            } else {
                lemma_r4_pending_resp_stays(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::ContinueReconcile, (controller_id, input.0, input.1))(s) by {
            assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
            assert(resp.content is APIResponse);
        }
        cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, next, ControllerStep::ContinueReconcile, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_list_resp_unlisted_in_flight(k, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_list_resp_unlisted_in_flight(k, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let resp = choose |resp: Message| #[trigger] st_list_resp_unlisted_msg_in_flight(k, controller_id, outer, resp)(s);
            assert(pre_of(resp).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_list_resp_unlisted_in_flight(k, controller_id, outer)));
    });
}

// The API server handles the Update that releases: it lands, since under the
// quiet layer the snapshot it was built from is the stored copy, and what it
// leaves at the key, if anything, lacks the sync finalizer.
proof fn lemma_r4_remove_req_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, msg: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        st_remove_req_msg_in_flight(k, controller_id, outer, msg)(s),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures finalizer_released(outer)(s_prime),
{
    hide(sync_reconciler::reconcile_core);
    let key = outer.object_ref();
    marshal_status_preserves_integrity();
    marshal_preserves_metadata();
    marshal_preserves_kind();
    unmarshal_is_representable();
    if finalizer_released(outer)(s) {
        lemma_released_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    } else {
        lemma_r4_current_snapshot_is_stored(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
        let old = s.resources()[key];
        assert(old == cr);
        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
        assert(cluster.etcd_object_is_well_formed(key)(s));
        assert(Cluster::etcd_object_has_at_most_one_controller_owner(key)(s));
        let req = msg.content->APIRequest_0->UpdateRequest_0;
        let updated_meta = without_sync_finalizer(cr_outer.metadata);
        lemma_without_sync_finalizer(cr_outer.metadata);
        assert(req == sync_reconciler::outer_finalizer_update(cr_outer, false));
        assert(req.obj == marshal(cr_outer.with_metadata(updated_meta)));
        assert(req.obj.kind == k.outer_kind);
        assert(req.obj.metadata == updated_meta);
        assert(req.obj.spec == old.spec);
        assert(req.obj.status == marshal_status(cr_outer.status));
        // Admission: the object names itself, unmarshals, exists, and carries the
        // stored version and uid.
        assert(req.key() == key);
        assert(key.kind is CustomResourceKind);
        assert(cluster.installed_types[key.kind->CustomResourceKind_0] == Cluster::synced_installed_type(spec_ok, k.selector));
        assert(unmarshallable_object(req.obj, cluster.installed_types)) by {
            assert(unmarshal_status(marshal_status(cr_outer.status)) is Ok);
        }
        assert(update_request_admission_check(cluster.installed_types, req, s.api_server) is None);
        let updated = updated_object(req, old);
        assert(updated.metadata.finalizers == updated_meta.finalizers);
        assert(updated != old) by {
            assert(has_sync_finalizer(old.metadata));
            assert(!has_sync_finalizer(updated.metadata));
        }
        let with_rv = updated.with_resource_version(s.api_server.resource_version_counter);
        // Validity: the metadata is the stored one but for the finalizers, which
        // shrink, and the spec is the stored one.
        assert(old.metadata.deletion_timestamp is Some);
        assert(with_rv.metadata.owner_references == old.metadata.owner_references);
        assert(metadata_validity_check(with_rv) is None);
        assert(with_rv.metadata.finalizers_as_set() == updated_meta.finalizers_as_set());
        assert(metadata_transition_validity_check(with_rv, old) is None);
        assert(valid_object(old, cluster.installed_types));
        assert(valid_object(with_rv, cluster.installed_types));
        assert(valid_transition(with_rv, old, cluster.installed_types)) by {
            assert(with_rv.spec == old.spec);
        }
        assert(updated_object_validity_check(with_rv, old, cluster.installed_types) is None);
        assert(!has_sync_finalizer(with_rv.metadata));
        if with_rv.metadata.finalizers is Some && with_rv.metadata.finalizers->0.len() > 0 {
            assert(s_prime.resources()[key] == with_rv);
        } else {
            assert(with_rv.object_ref() == key);
            assert(!s_prime.resources().contains_key(key));
        }
    }
}

// The Update that releases in flight ~> released.
pub proof fn lemma_r4_remove_req_leads_to_released(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_remove_req_in_flight(k, controller_id, outer)).leads_to(lift_state(finalizer_released(outer)))),
{
    hide(sync_reconciler::reconcile_core);
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    let next = r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let post = finalizer_released(outer);
    let pre_of = |msg: Message| lift_state(st_remove_req_msg_in_flight(k, controller_id, outer, msg));
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_remove_req_msg_in_flight(k, controller_id, outer, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_r4_remove_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            if cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))) {
                lemma_r4_remove_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
            } else {
                lemma_r4_pending_req_stays(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_remove_req_in_flight(k, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_remove_req_in_flight(k, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = choose |msg: Message| #[trigger] st_remove_req_msg_in_flight(k, controller_id, outer, msg)(s);
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_remove_req_in_flight(k, controller_id, outer)));
    });
}

// The API server answers the Get of the mirror key with what is there.
proof fn lemma_r4_get_mirror_req_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, msg: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        st_get_mirror_req_msg_in_flight(k, controller_id, outer, msg)(s),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures st_get_mirror_resp_in_flight(k, b, controller_id, outer)(s_prime),
{
    hide(sync_reconciler::reconcile_core);
    let key = outer.object_ref();
    let ikey = inner_key(k, outer);
    let resp = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
    assert(s_prime.in_flight().contains(resp));
    assert(resp_msg_matches_req_msg(resp, msg));
    assert(s_prime.api_server == s.api_server);
    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
    assert(resp.content.get_get_response() == handle_get_request(GetRequest { key: ikey }, s.api_server));
    if s.resources().contains_key(ikey) {
        let obj = s.resources()[ikey];
        assert(resp.content.get_get_response().res == Ok::<DynamicObjectView, APIError>(obj));
        assert(ikey.kind == inner_kind(k, b));
        assert(cluster.etcd_object_is_well_formed(ikey)(s));
        assert(obj.metadata.uid is Some);
        assert(unmarshal(inner_kind(k, b), obj) is Ok);
        if is_mirror_of(unmarshal(inner_kind(k, b), obj)->Ok_0, outer) {
            assert(mirror_of_outer_at(k, b, outer, obj.metadata.uid->0)(s_prime));
        }
    } else {
        assert(resp.content.get_get_response().res == Err::<DynamicObjectView, APIError>(APIError::ObjectNotFound));
    }
    assert(get_mirror_resp_reflects_store(k, b, resp, outer)(s_prime));
    assert(st_get_mirror_resp_msg_in_flight(k, b, controller_id, outer, resp)(s_prime));
}

// The Get of the mirror key in flight ~> its answer is in flight.
pub proof fn lemma_r4_get_mirror_req_leads_to_resp(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_get_mirror_req_in_flight(k, controller_id, outer))
            .leads_to(lift_state(st_get_mirror_resp_in_flight(k, b, controller_id, outer)))),
{
    hide(sync_reconciler::reconcile_core);
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    let next = r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let post = st_get_mirror_resp_in_flight(k, b, controller_id, outer);
    let pre_of = |msg: Message| lift_state(st_get_mirror_req_msg_in_flight(k, controller_id, outer, msg));
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_get_mirror_req_msg_in_flight(k, controller_id, outer, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_r4_get_mirror_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            if cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))) {
                lemma_r4_get_mirror_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
            } else {
                lemma_r4_pending_req_stays(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_get_mirror_req_in_flight(k, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_get_mirror_req_in_flight(k, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = choose |msg: Message| #[trigger] st_get_mirror_req_msg_in_flight(k, controller_id, outer, msg)(s);
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_get_mirror_req_in_flight(k, controller_id, outer)));
    });
}

// The sync reconciler consumes the answer to the Get: nothing there, and it is
// done with the key empty; not the mirror, and it releases; the mirror, being
// released by the inner side, and it is done with a terminating mirror at the
// key; the mirror, live, and it sends the Delete.
proof fn lemma_r4_get_mirror_resp_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, resp: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        st_get_mirror_resp_msg_in_flight(k, b, controller_id, outer, resp)(s),
        cluster.controller_next().forward((controller_id, Some(resp), Some(outer.object_ref())))(s, s_prime),
    ensures
        ({
            ||| mirror_absent(k, outer)(s_prime)
            ||| st_remove_req_in_flight(k, controller_id, outer)(s_prime)
            ||| some_terminating_mirror_of_outer(k, b, outer)(s_prime)
            ||| st_delete_req_in_flight(k, b, controller_id, outer)(s_prime)
            ||| finalizer_released(outer)(s_prime)
        }),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
    let key = outer.object_ref();
    let ikey = inner_key(k, outer);
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    lemma_r4_current_reconcile(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
    let reconcile = s.ongoing_reconciles(controller_id)[key];
    let cr = reconcile.triggering_cr;
    let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
    let res = resp.content.get_get_response().res;
    let resp_o = Some(ResponseView::<VoidERespView>::KResponse(resp.content->APIResponse_0));
    assert(is_some_k_get_resp_view(resp_o));
    assert(extract_some_k_get_resp_view(resp_o) == res);
    let (state_prime, req_o) = sync_reconciler::reconcile_core(k, cr_outer, resp_o, sync_reconciler::at_step(WidgetSyncStepView::AfterGetMirror));
    assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == state_prime.marshal());
    assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == cr);
    assert(s_prime.api_server == s.api_server);
    if finalizer_released(outer)(s) {
        assert(finalizer_released(outer)(s_prime));
    } else if res is Err {
        assert(mirror_absent(k, outer)(s_prime));
    } else {
        lemma_r4_current_snapshot_is_stored(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
        assert(inner_key(k, cr_outer) == ikey);
        assert(ikey.kind == inner_kind(k, b));
        let obj = res->Ok_0;
        let inner = unmarshal(inner_kind(k, b), obj)->Ok_0;
        assert(unmarshal(inner_key(k, cr_outer).kind, obj) is Ok);
        assert(inner.metadata == obj.metadata);
        assert(is_mirror_of(inner, cr_outer) == is_mirror_of(inner, outer));
        if !is_mirror_of(inner, cr_outer) {
            let req = APIRequest::UpdateRequest(sync_reconciler::outer_finalizer_update(cr_outer, false));
            let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
            assert(s_prime.in_flight().contains(msg));
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == sync_reconciler::at_step(WidgetSyncStepView::AfterRemoveFinalizer).marshal());
            assert(remove_req_msg_for(k, controller_id, outer, msg, cr));
            assert(st_remove_req_msg_in_flight(k, controller_id, outer, msg)(s_prime));
        } else if inner.metadata.deletion_timestamp is Some {
            if mirror_absent(k, outer)(s) {
                assert(mirror_absent(k, outer)(s_prime));
            } else {
                let m = obj.metadata.uid->0;
                assert(mirror_of_outer_at(k, b, outer, m)(s));
                assert(s.resources()[ikey].metadata.deletion_timestamp is Some);
                assert(terminating_mirror_of_outer_at(k, b, outer, m)(s_prime));
                assert(some_terminating_mirror_of_outer(k, b, outer)(s_prime));
            }
        } else {
            assert(inner.metadata.uid is Some);
            let m = inner.metadata.uid->0;
            let req = APIRequest::DeleteRequest(sync_reconciler::mirror_delete(k, cr_outer, inner));
            let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
            assert(s_prime.in_flight().contains(msg));
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == sync_reconciler::at_step(WidgetSyncStepView::AfterDeleteMirror).marshal());
            assert(delete_req_msg_for(k, controller_id, outer, msg, m));
            assert(mirror_key_empty_or_holds(k, b, outer, m)(s_prime));
            assert(st_delete_req_msg_in_flight(k, b, controller_id, outer, msg, m)(s_prime));
            assert(st_delete_req_in_flight(k, b, controller_id, outer)(s_prime)) by {
                let i = (msg, m);
                assert(st_delete_req_msg_in_flight(k, b, controller_id, outer, i.0, i.1)(s_prime));
            }
        }
    }
}

// The answer to the Get in flight ~> the reconcile decided.
pub proof fn lemma_r4_get_mirror_resp_leads_to_decision(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_get_mirror_resp_in_flight(k, b, controller_id, outer))
            .leads_to(lift_state(mirror_absent(k, outer))
                .or(lift_state(st_remove_req_in_flight(k, controller_id, outer)))
                .or(lift_state(some_terminating_mirror_of_outer(k, b, outer)))
                .or(lift_state(st_delete_req_in_flight(k, b, controller_id, outer)))
                .or(lift_state(finalizer_released(outer))))),
{
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    let next = r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let post = |s: ClusterState| {
        ||| mirror_absent(k, outer)(s)
        ||| st_remove_req_in_flight(k, controller_id, outer)(s)
        ||| some_terminating_mirror_of_outer(k, b, outer)(s)
        ||| st_delete_req_in_flight(k, b, controller_id, outer)(s)
        ||| finalizer_released(outer)(s)
    };
    let pre_of = |resp: Message| lift_state(st_get_mirror_resp_msg_in_flight(k, b, controller_id, outer, resp));
    assert forall |resp: Message| spec.entails(#[trigger] pre_of(resp).leads_to(lift_state(post))) by {
        let pre = st_get_mirror_resp_msg_in_flight(k, b, controller_id, outer, resp);
        let input = (Some(resp), Some(key));
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
            && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
            lemma_r4_get_mirror_resp_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            if cluster.next_step(s, s_prime, Step::ControllerStep((controller_id, Some(resp), Some(key)))) {
                lemma_r4_get_mirror_resp_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
            } else {
                lemma_r4_pending_resp_stays(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
                lemma_get_mirror_resp_keeps_reflecting_store(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::ContinueReconcile, (controller_id, input.0, input.1))(s) by {
            assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
            assert(resp.content is APIResponse);
        }
        cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, next, ControllerStep::ContinueReconcile, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_get_mirror_resp_in_flight(k, b, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_get_mirror_resp_in_flight(k, b, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let resp = choose |resp: Message| #[trigger] st_get_mirror_resp_msg_in_flight(k, b, controller_id, outer, resp)(s);
            assert(pre_of(resp).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_get_mirror_resp_in_flight(k, b, controller_id, outer)));
    });
    temp_pred_equality(
        lift_state(post),
        lift_state(mirror_absent(k, outer))
            .or(lift_state(st_remove_req_in_flight(k, controller_id, outer)))
            .or(lift_state(some_terminating_mirror_of_outer(k, b, outer)))
            .or(lift_state(st_delete_req_in_flight(k, b, controller_id, outer)))
            .or(lift_state(finalizer_released(outer)))
    );
}

// The API server handles the Delete: the key is empty, and stays so; or it holds
// the mirror named, which is removed, or stamped terminating if it has
// finalizers of its own.
proof fn lemma_r4_delete_req_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, msg: Message, m: Uid
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        st_delete_req_msg_in_flight(k, b, controller_id, outer, msg, m)(s),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures mirror_absent(k, outer)(s_prime) || terminating_mirror_of_outer_at(k, b, outer, m)(s_prime),
{
    hide(sync_reconciler::reconcile_core);
    let ikey = inner_key(k, outer);
    let req = msg.content->APIRequest_0->DeleteRequest_0;
    assert(req.key == ikey);
    if mirror_absent(k, outer)(s) {
        assert(delete_request_admission_check(req, s.api_server) is Some);
        assert(s_prime.api_server == s.api_server);
        assert(mirror_absent(k, outer)(s_prime));
    } else {
        let old = s.resources()[ikey];
        assert(old.metadata.uid == Some(m));
        assert(delete_request_admission_check(req, s.api_server) is None);
        if old.metadata.finalizers is Some && old.metadata.finalizers->0.len() > 0 {
            assert(s_prime.resources().contains_key(ikey));
            assert(s_prime.resources()[ikey].metadata.deletion_timestamp is Some);
            lemma_mirror_key_object_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            assert(terminating_mirror_of_outer_at(k, b, outer, m)(s_prime));
        } else {
            assert(!s_prime.resources().contains_key(ikey));
        }
    }
}

// The Delete in flight ~> the mirror key is empty, or holds a terminating mirror.
pub proof fn lemma_r4_delete_req_leads_to_absent_or_terminating(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_delete_req_in_flight(k, b, controller_id, outer))
            .leads_to(lift_state(mirror_absent(k, outer)).or(lift_state(some_terminating_mirror_of_outer(k, b, outer))))),
{
    hide(sync_reconciler::reconcile_core);
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    let next = r4_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let post = |s: ClusterState| mirror_absent(k, outer)(s) || some_terminating_mirror_of_outer(k, b, outer)(s);
    let pre_of = |i: (Message, Uid)| lift_state(st_delete_req_msg_in_flight(k, b, controller_id, outer, i.0, i.1));
    assert forall |i: (Message, Uid)| spec.entails(#[trigger] pre_of(i).leads_to(lift_state(post))) by {
        let msg = i.0;
        let m = i.1;
        let pre = st_delete_req_msg_in_flight(k, b, controller_id, outer, msg, m);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_r4_delete_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg, m);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            if cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))) {
                lemma_r4_delete_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg, m);
            } else {
                lemma_r4_pending_req_stays(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
                if mirror_absent(k, outer)(s) {
                    lemma_mirror_absent_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
                } else if !mirror_absent(k, outer)(s_prime) {
                    lemma_mirror_key_object_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
                }
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_delete_req_in_flight(k, b, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_delete_req_in_flight(k, b, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let i = choose |i: (Message, Uid)| #[trigger] st_delete_req_msg_in_flight(k, b, controller_id, outer, i.0, i.1)(s);
            assert(pre_of(i).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_delete_req_in_flight(k, b, controller_id, outer)));
    });
    temp_pred_equality(lift_state(post), lift_state(mirror_absent(k, outer)).or(lift_state(some_terminating_mirror_of_outer(k, b, outer))));
}

// ---------------------------------------------------------------------------
// After the walk: a terminating mirror goes (D3), and an empty mirror key lets
// the next reconcile release.
// ---------------------------------------------------------------------------

// A terminating mirror at the key ~> the key is empty: the inner side releases the
// mirror (D3), nothing replaces it (no Create names the key), so what goes is
// the object at the key.
pub proof fn lemma_r4_terminating_mirror_leads_to_absent(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(some_terminating_mirror_of_outer(k, b, outer)).leads_to(lift_state(mirror_absent(k, outer)))),
{
    let ikey = inner_key(k, outer);
    assert(ikey.kind == inner_kind(k, b));
    let spec_q = r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    r4_spec_with_quiet_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert(spec_q.entails(spec_q));
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec_q, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec_q, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec_q, cluster, controller_id, janitor_id);
    lemma_always_r4_base_next(k, b, spec_ok, spec_q, cluster, controller_id, janitor_id, outer);
    let next = r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let absent = lift_state(mirror_absent(k, outer));
    let t_of = |m: Uid| lift_state(terminating_mirror_of_outer_at(k, b, outer, m));
    assert forall |m: Uid| spec_q.entails(#[trigger] t_of(m).leads_to(absent)) by {
        let e = mirror_key_empty_or_terminating(k, b, outer, m);
        let ito = lift_state(inner_terminating_object(k, b, ikey, m));
        let gone = lift_state(object_is_gone(ikey, m));
        // T(m) ~> []E(m): E holds where T does, and a step keeps it.
        assert forall |s, s_prime: ClusterState| e(s) && #[trigger] next(s, s_prime) implies e(s_prime) by {
            if mirror_absent(k, outer)(s) {
                lemma_mirror_absent_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            } else if !mirror_absent(k, outer)(s_prime) {
                lemma_mirror_key_object_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            }
        }
        entails_implies_leads_to(spec_q, t_of(m), lift_state(e));
        leads_to_stable(spec_q, lift_action(next), t_of(m), lift_state(e));
        // Under spec_q /\ []E(m): true ~> absent, by D3.
        let spec_e = spec_q.and(always(lift_state(e)));
        assert(spec_e.entails(spec_e));
        entails_and_split(spec_e, spec_q, always(lift_state(e)));
        entails_trans(spec_e, spec_q, inner_releases_terminating_objects(k, b));
        spec_entails_tla_forall_apply(spec_e, |i: (ObjectRef, Uid)| lift_state(inner_terminating_object(k, b, i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1))), (ikey, m));
        assert(spec_e.entails(ito.leads_to(gone)));
        assert forall |s: ClusterState| #[trigger] e(s) implies mirror_absent(k, outer)(s) || inner_terminating_object(k, b, ikey, m)(s) by {}
        assert forall |s: ClusterState| #[trigger] e(s) && object_is_gone(ikey, m)(s) implies mirror_absent(k, outer)(s) by {}
        always_weaken(spec_e, lift_state(e), true_pred().implies(absent.or(ito)));
        always_implies_to_leads_to(spec_e, true_pred(), absent.or(ito));
        always_weaken(spec_e, lift_state(e), gone.implies(absent));
        always_weaken(spec_e, lift_state(e), ito.implies(ito));
        leads_to_weaken(spec_e, ito, gone, ito, absent);
        entails_implies_leads_to(spec_e, absent, absent);
        or_leads_to(spec_e, absent, ito, absent);
        leads_to_trans(spec_e, true_pred(), absent.or(ito), absent);
        // Fold back.
        unpack_conditions_from_spec(spec_q, always(lift_state(e)), true_pred(), absent);
        temp_pred_equality(true_pred().and(always(lift_state(e))), always(lift_state(e)));
        leads_to_trans(spec_q, t_of(m), always(lift_state(e)), absent);
    }
    leads_to_exists_intro(spec_q, t_of, absent);
    assert_by(tla_exists(t_of) == lift_state(some_terminating_mirror_of_outer(k, b, outer)), {
        assert forall |ex| #[trigger] lift_state(some_terminating_mirror_of_outer(k, b, outer)).satisfied_by(ex)
        implies tla_exists(t_of).satisfied_by(ex) by {
            let s = ex.head();
            let m = choose |m: Uid| #[trigger] terminating_mirror_of_outer_at(k, b, outer, m)(s);
            assert(t_of(m).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(t_of), lift_state(some_terminating_mirror_of_outer(k, b, outer)));
    });
    entails_trans(spec, spec_q, lift_state(some_terminating_mirror_of_outer(k, b, outer)).leads_to(absent));
}

// The mirror key empty ~> released: it stays empty, so the next reconcile of the
// copy lists nothing there and releases.
pub proof fn lemma_r4_absent_leads_to_released(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(mirror_absent(k, outer)).leads_to(lift_state(finalizer_released(outer)))),
{
    let key = outer.object_ref();
    let spec_q = r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    r4_spec_with_quiet_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert(spec_q.entails(spec_q));
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec_q, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec_q, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec_q, cluster, controller_id, janitor_id);
    lemma_always_r4_base_next(k, b, spec_ok, spec_q, cluster, controller_id, janitor_id, outer);
    let next = r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let absent = lift_state(mirror_absent(k, outer));
    let rel = lift_state(finalizer_released(outer));
    // absent ~> []absent.
    assert forall |s, s_prime: ClusterState| mirror_absent(k, outer)(s) && #[trigger] next(s, s_prime) implies mirror_absent(k, outer)(s_prime) by {
        lemma_mirror_absent_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    }
    entails_implies_leads_to(spec_q, absent, absent);
    leads_to_stable(spec_q, lift_action(next), absent, absent);
    // Under spec_q /\ []absent: true ~> released.
    let spec_a = spec_q.and(always(absent));
    always_p_is_stable(absent);
    stable_and_n!(spec_q, always(absent));
    assert(spec_a.entails(spec_a));
    entails_and_split(spec_a, spec_q, always(absent));
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id);
    lemma_sync_terminates(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id, key);
    let idle = lift_state(Cluster::reconcile_idle(controller_id, key));
    let sched = lift_state(|s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
    });
    let init = lift_state(st_sync_init(controller_id, key));
    let list_req = lift_state(st_list_req_in_flight(k, controller_id, outer));
    let unlisted = lift_state(st_list_resp_unlisted_in_flight(k, controller_id, outer));
    let remove_req = lift_state(st_remove_req_in_flight(k, controller_id, outer));
    lemma_r4_idle_leads_to_scheduled(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id, outer);
    lemma_r4_scheduled_leads_to_init(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id, outer);
    lemma_r4_init_leads_to_list_req(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id, outer);
    lemma_r4_list_req_leads_to_unlisted_resp(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id, outer);
    lemma_r4_unlisted_resp_leads_to_remove_req(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id, outer);
    lemma_r4_remove_req_leads_to_released(k, b, spec_ok, spec_a, cluster, controller_id, janitor_id, outer);
    entails_implies_leads_to(spec_a, rel, rel);
    leads_to_trans(spec_a, unlisted, remove_req, rel);
    or_leads_to(spec_a, unlisted, rel, rel);
    leads_to_trans(spec_a, list_req, unlisted.or(rel), rel);
    or_leads_to(spec_a, list_req, rel, rel);
    leads_to_trans(spec_a, init, list_req.or(rel), rel);
    leads_to_trans(spec_a, sched, init, rel);
    or_leads_to(spec_a, sched, rel, rel);
    leads_to_trans(spec_a, idle, sched.or(rel), rel);
    leads_to_trans(spec_a, true_pred(), idle, rel);
    // Fold back.
    unpack_conditions_from_spec(spec_q, always(absent), true_pred(), rel);
    temp_pred_equality(true_pred().and(always(absent)), always(absent));
    leads_to_trans(spec_q, absent, always(absent), rel);
    entails_trans(spec, spec_q, absent.leads_to(rel));
}

// ---------------------------------------------------------------------------
// Under all layers: the copy is eventually and forever released.
// ---------------------------------------------------------------------------

pub proof fn lemma_r4_true_leads_to_always_released(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(finalizer_released(outer))))),
{
    let key = outer.object_ref();
    lemma_unfold_r4_spec_with_quiet(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r4_base_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    let rel = lift_state(finalizer_released(outer));
    let absent = lift_state(mirror_absent(k, outer));
    let t_any = lift_state(some_terminating_mirror_of_outer(k, b, outer));
    let idle = lift_state(Cluster::reconcile_idle(controller_id, key));
    let sched = lift_state(|s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
    });
    let init = lift_state(st_sync_init(controller_id, key));
    let list_req = lift_state(st_list_req_in_flight(k, controller_id, outer));
    let list_resp = lift_state(st_list_resp_in_flight(k, controller_id, outer));
    let remove_req = lift_state(st_remove_req_in_flight(k, controller_id, outer));
    let get_req = lift_state(st_get_mirror_req_in_flight(k, controller_id, outer));
    let get_resp = lift_state(st_get_mirror_resp_in_flight(k, b, controller_id, outer));
    let delete_req = lift_state(st_delete_req_in_flight(k, b, controller_id, outer));
    lemma_r4_idle_leads_to_scheduled(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_scheduled_leads_to_init(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_init_leads_to_list_req(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_list_req_leads_to_list_resp(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_list_resp_leads_to_decision(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_remove_req_leads_to_released(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_get_mirror_req_leads_to_resp(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_get_mirror_resp_leads_to_decision(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_delete_req_leads_to_absent_or_terminating(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_terminating_mirror_leads_to_absent(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r4_absent_leads_to_released(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    entails_implies_leads_to(spec, rel, rel);
    leads_to_trans(spec, t_any, absent, rel);
    or_leads_to(spec, absent, t_any, rel);
    leads_to_trans(spec, delete_req, absent.or(t_any), rel);
    or_leads_to(spec, absent, remove_req, rel);
    or_leads_to(spec, absent.or(remove_req), t_any, rel);
    or_leads_to(spec, absent.or(remove_req).or(t_any), delete_req, rel);
    or_leads_to(spec, absent.or(remove_req).or(t_any).or(delete_req), rel, rel);
    leads_to_trans(spec, get_resp, absent.or(remove_req).or(t_any).or(delete_req).or(rel), rel);
    leads_to_trans(spec, get_req, get_resp, rel);
    or_leads_to(spec, remove_req, get_req, rel);
    or_leads_to(spec, remove_req.or(get_req), rel, rel);
    leads_to_trans(spec, list_resp, remove_req.or(get_req).or(rel), rel);
    leads_to_trans(spec, list_req, list_resp, rel);
    or_leads_to(spec, list_req, rel, rel);
    leads_to_trans(spec, init, list_req.or(rel), rel);
    leads_to_trans(spec, sched, init, rel);
    or_leads_to(spec, sched, rel, rel);
    leads_to_trans(spec, idle, sched.or(rel), rel);
    leads_to_trans(spec, true_pred(), idle, rel);
    // Stability.
    let next = r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert forall |s, s_prime: ClusterState| finalizer_released(outer)(s) && #[trigger] next(s, s_prime) implies finalizer_released(outer)(s_prime) by {
        lemma_released_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    }
    leads_to_stable(spec, lift_action(next), true_pred(), rel);
}

// ---------------------------------------------------------------------------
// The layers hold eventually forever.
// ---------------------------------------------------------------------------

// An invariant is reached at once.
proof fn lemma_always_implies_true_leads_to_always(spec: TempPred<ClusterState>, p: TempPred<ClusterState>)
    requires spec.entails(always(p)),
    ensures spec.entails(true_pred().leads_to(always(p))),
{
    always_double_equality(p);
    always_weaken(spec, always(p), true_pred().implies(always(p)));
    always_implies_to_leads_to(spec, true_pred(), always(p));
}

// Quiet, under phase II: no status write of the copy is in flight unless it is
// released, an invariant; and every snapshot carries the stored version unless
// the copy is released, since a step that changes the stored copy releases it.
pub proof fn lemma_true_leads_to_always_r4_quiet(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(r4_quiet(controller_id, outer))))),
{
    let key = outer.object_ref();
    let spec_ii = r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    r4_spec_with_phase_ii_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert(spec_ii.entails(spec_ii));
    lemma_unfold_r4_spec_with_phase_ii(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id);
    lemma_always_r4_step_ctx(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id, outer);
    lemma_always_r4_step_next(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id, outer);
    lemma_sync_terminates(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id, key);
    let ctx = r4_step_ctx(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    // No status write in flight unless released: an invariant.
    let q1_pred = |s: ClusterState| no_status_write_in_flight_for(controller_id, key)(s) || finalizer_released(outer)(s);
    let q1 = lift_state(q1_pred);
    assert forall |s: ClusterState| #[trigger] ctx(s) implies q1_pred(s) by {
        if !finalizer_released(outer)(s) {
            lemma_no_status_write_in_flight_unless_released(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
        }
    }
    always_weaken(spec_ii, lift_state(ctx), q1);
    lemma_always_implies_true_leads_to_always(spec_ii, q1);
    // The snapshots carry the stored version, unless released.
    let pred = snapshot_current_or_released(outer);
    let q2 = lift_state(snapshots_satisfy(controller_id, key, pred));
    let next = r4_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert forall |s, s_prime: ClusterState| #[trigger] next(s, s_prime) implies preserves(pred)(s, s_prime) by {
        assert forall |o: DynamicObjectView| #[trigger] pred(o, s) implies pred(o, s_prime) by {
            if finalizer_released(outer)(s) {
                lemma_released_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            } else {
                lemma_no_status_write_in_flight_unless_released(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
                lemma_outer_copy_unchanged_or_released_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            }
        }
    }
    always_weaken(spec_ii, lift_action(next), lift_action(preserves(pred)));
    assert forall |s: ClusterState| #[trigger] ctx(s) implies stored_satisfies(key, pred)(s) by {}
    always_weaken(spec_ii, lift_state(ctx), lift_state(stored_satisfies(key, pred)));
    lemma_snapshots_eventually_satisfy(spec_ii, cluster, controller_id, key, pred);
    // Combine.
    leads_to_always_and(spec_ii, true_pred(), q1, q2);
    temp_pred_equality(lift_state(r4_quiet(controller_id, outer)), q1.and(q2));
    entails_trans(spec, spec_ii, true_pred().leads_to(always(lift_state(r4_quiet(controller_id, outer)))));
}

// Phase II, under phase I: the snapshots are terminating copies of `outer` unless
// released, since the stored copy is one (the premise) and a copy once released
// stays released; and the message facts, as for R1.
pub proof fn lemma_true_leads_to_always_r4_phase_ii(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(r4_phase_ii(k, controller_id, outer))))),
{
    let key = outer.object_ref();
    let spec_i = r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    r4_spec_with_phase_i_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert(spec_i.entails(spec_i));
    entails_and_split(spec_i, r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec_i, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_terminating_stable(k, b, outer))));
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec_i, cluster, controller_id, janitor_id);
    always_weaken(spec_i, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec_i, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec_i, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_tla_forall_apply(spec_i, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), key);
    always_tla_forall_apply(spec_i, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)), key);
    always_tla_forall_apply(spec_i, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)), key);
    lemma_sync_terminates(k, b, spec_ok, spec_i, cluster, controller_id, janitor_id, key);
    lemma_always_r4_base_next(k, b, spec_ok, spec_i, cluster, controller_id, janitor_id, outer);

    // The snapshots.
    let pred = snapshot_of_terminating_copy(k, outer);
    let snap = lift_state(snapshots_satisfy(controller_id, key, pred));
    let next = r4_base_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert forall |s, s_prime: ClusterState| #[trigger] next(s, s_prime) implies preserves(pred)(s, s_prime) by {
        assert forall |o: DynamicObjectView| #[trigger] pred(o, s) implies pred(o, s_prime) by {
            if finalizer_released(outer)(s) {
                lemma_released_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            }
        }
    }
    always_weaken(spec_i, lift_action(next), lift_action(preserves(pred)));
    assert forall |s: ClusterState| #[trigger] outer_terminating_stable(k, b, outer)(s) implies stored_satisfies(key, pred)(s) by {
        if s.resources().contains_key(key) && s.resources()[key].metadata.uid != outer.metadata.uid {
            assert(finalizer_released(outer)(s));
        }
    }
    always_weaken(spec_i, lift_state(outer_terminating_stable(k, b, outer)), lift_state(stored_satisfies(key, pred)));
    lemma_snapshots_eventually_satisfy(spec_i, cluster, controller_id, key, pred);

    // The message facts: the xor, then the message fact under it.
    let xor = lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key));
    let msg_fact = lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, key));
    cluster.lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(spec_i, controller_id, key);
    let spec_x = spec_i.and(always(xor));
    always_p_is_stable(xor);
    stable_and_n!(spec_i, always(xor));
    assert(spec_x.entails(spec_x));
    entails_and_split(spec_x, spec_i, always(xor));
    entails_and_split(spec_x, r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec_x, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_terminating_stable(k, b, outer))));
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec_x, cluster, controller_id, janitor_id);
    always_weaken(spec_x, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec_x, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec_x, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_tla_forall_apply(spec_x, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), key);
    always_tla_forall_apply(spec_x, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)), key);
    always_tla_forall_apply(spec_x, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)), key);
    cluster.lemma_true_leads_to_always_every_msg_from_key_is_pending_req_msg_of(spec_x, controller_id, key);
    unpack_conditions_from_spec(spec_i, always(xor), true_pred(), always(msg_fact));
    temp_pred_equality(true_pred().and(always(xor)), always(xor));
    leads_to_trans(spec_i, true_pred(), always(xor), always(msg_fact));
    leads_to_always_and(spec_i, true_pred(), snap, msg_fact);
    leads_to_always_and(spec_i, true_pred(), snap.and(msg_fact), xor);
    temp_pred_equality(lift_state(r4_phase_ii(k, controller_id, outer)), snap.and(msg_fact).and(xor));
    entails_trans(spec, spec_i, true_pred().leads_to(always(lift_state(r4_phase_ii(k, controller_id, outer)))));
}

// ---------------------------------------------------------------------------
// Assembly: R4 for one outer copy, then for all.
// ---------------------------------------------------------------------------

pub proof fn lemma_outer_terminating_stable_leads_to_always_released(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id)),
    ensures spec.entails(always(lift_state(outer_terminating_stable(k, b, outer))).leads_to(always(lift_state(finalizer_released(outer))))),
{
    let target = always(lift_state(finalizer_released(outer)));
    let stable_spec = sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id);
    let spec_p = r4_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let spec_i = r4_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let spec_ii = r4_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let spec_q = r4_spec_with_quiet(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let quiet_temp = always(lift_state(r4_quiet(controller_id, outer)));
    let phase_ii_temp = always(lift_state(r4_phase_ii(k, controller_id, outer)));
    let phase_i_temp = always(lift_state(phase_i(controller_id)));
    let premise_temp = always(lift_state(outer_terminating_stable(k, b, outer)));

    // Under all layers.
    assert(spec_q.entails(spec_q));
    lemma_r4_true_leads_to_always_released(k, b, spec_ok, spec_q, cluster, controller_id, janitor_id, outer);
    // Remove the quiet layer.
    r4_spec_with_phase_ii_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    unpack_conditions_from_spec(spec_ii, quiet_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(quiet_temp), quiet_temp);
    assert(spec_ii.entails(spec_ii));
    lemma_true_leads_to_always_r4_quiet(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id, outer);
    leads_to_trans(spec_ii, true_pred(), quiet_temp, target);
    // Remove phase II.
    r4_spec_with_phase_i_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    unpack_conditions_from_spec(spec_i, phase_ii_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_ii_temp), phase_ii_temp);
    assert(spec_i.entails(spec_i));
    lemma_true_leads_to_always_r4_phase_ii(k, b, spec_ok, spec_i, cluster, controller_id, janitor_id, outer);
    leads_to_trans(spec_i, true_pred(), phase_ii_temp, target);
    // Remove phase I.
    r4_spec_with_premise_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    unpack_conditions_from_spec(spec_p, phase_i_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_i_temp), phase_i_temp);
    assert(spec_p.entails(spec_p));
    entails_and_split(spec_p, stable_spec, premise_temp);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec_p, cluster, controller_id, janitor_id);
    lemma_true_leads_to_always_phase_i(k, b, spec_p, cluster, controller_id);
    leads_to_trans(spec_p, true_pred(), phase_i_temp, target);
    // Remove the premise.
    sync_stable_spec_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id);
    unpack_conditions_from_spec(stable_spec, premise_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(premise_temp), premise_temp);
    entails_trans(spec, stable_spec, premise_temp.leads_to(target));
}

// R4: once the outer copy is terminating and nothing keeps it from being
// released, the sync finalizer is eventually and forever off it.
pub proof fn sync_eventually_releases(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int)
    requires
        k.bindings.contains(b),
        spec.entails(lift_state(cluster.init())),
        spec.entails(sync_next_with_wf(cluster, controller_id)),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(always(lift_state(sync_rely_with_janitor(k, b, cluster, controller_id, janitor_id)))),
        spec.entails(inner_releases_terminating_objects(k, b)),
        spec.entails(widget_janitor_esr(k, b, janitor_id)),
    ensures spec.entails(widget_finalizer_eventually_released(k, b)),
{
    entails_and_split(spec, widget_mirrors_eventually_collected(k, b), always(lift_state(janitor_deletes_are_sound(k, b, janitor_id))));
    assert(sync_next_with_wf(cluster, controller_id).entails(always(lift_action(cluster.next()))));
    entails_trans(spec, sync_next_with_wf(cluster, controller_id), always(lift_action(cluster.next())));
    sync_invariants_hold(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    entails_and_n!(
        spec,
        sync_next_with_wf(cluster, controller_id),
        always(lift_state(sync_rely_with_janitor(k, b, cluster, controller_id, janitor_id))),
        inner_releases_terminating_objects(k, b),
        widget_mirrors_eventually_collected(k, b),
        sync_invariants(k, b, spec_ok, cluster, controller_id, janitor_id)
    );
    let per_cr = |outer: SyncedObjectView| widget_finalizer_eventually_released_per_cr(k, b, outer);
    assert forall |outer: SyncedObjectView| spec.entails(#[trigger] per_cr(outer)) by {
        if outer.kind == k.outer_kind && cluster_of(k.selector, outer) is Some && b == binding_of(k, outer) {
            lemma_outer_terminating_stable_leads_to_always_released(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
        } else {
            lemma_vacuous_always_leads_to(spec, outer_terminating_stable(k, b, outer), always(lift_state(finalizer_released(outer))));
        }
    }
    spec_entails_tla_forall(spec, per_cr);
}

}
