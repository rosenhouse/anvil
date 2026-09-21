// Safety invariants about the sync reconciler's own requests and about the
// built-in garbage collector, used by the sync reconciler's liveness proofs.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::api_server::*;
use crate::kubernetes_cluster::spec::install_helpers::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    builtin_controllers::types::*,
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::{
    model::{install::*, sync_reconciler, sync_reconciler::WidgetSyncReconcileState},
    proof::{guarantee::*, helper_invariants::*, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The garbage collector never deletes a mirror: it only deletes objects that
// carry owner references, and a mirror never does.
// ---------------------------------------------------------------------------

pub open spec fn builtin_delete_never_targets_a_mirror(k: SyncKind, b: Binding, msg: Message, s: ClusterState) -> bool {
    let req = msg.content.get_delete_request();
    &&& req.preconditions is Some
    &&& req.preconditions->0.uid is Some
    &&& req.preconditions->0.uid->0 < s.api_server.uid_counter
    &&& forall |key: ObjectRef| #[trigger] s.resources().contains_key(key) && key.kind == inner_kind(k, b)
        ==> s.resources()[key].metadata.uid != req.preconditions->0.uid
}

pub open spec fn builtin_deletes_never_target_mirrors(k: SyncKind, b: Binding) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src is BuiltinController
            &&& msg.content is APIRequest
            &&& msg.content.is_delete_request()
        } ==> builtin_delete_never_targets_a_mirror(k, b, msg, s)
    }
}

pub proof fn lemma_always_builtin_deletes_never_target_mirrors(spec: TempPred<ClusterState>, cluster: Cluster, k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        spec.entails(always(lift_state(every_mirror_is_bound(k, b)))),
    ensures spec.entails(always(lift_state(builtin_deletes_never_target_mirrors(k, b)))),
{
    let inv = builtin_deletes_never_target_mirrors(k, b);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_etcd_objects_have_unique_uids(spec);
    cluster.lemma_always_each_synced_object_in_etcd_is_well_formed(spec, inner_kind(k, b), spec_ok, k.selector);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::etcd_objects_have_unique_uids()(s)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s)
        &&& every_mirror_is_bound(k, b)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::etcd_objects_have_unique_uids()),
        lift_state(cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))),
        lift_state(every_mirror_is_bound(k, b))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.src is BuiltinController
            &&& msg.content is APIRequest
            &&& msg.content.is_delete_request()
        } implies builtin_delete_never_targets_a_mirror(k, b, msg, s_prime) by {
            let req = msg.content.get_delete_request();
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    assert(builtin_delete_never_targets_a_mirror(k, b, msg, s));
                    lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, input->0);
                    let m = req.preconditions->0.uid;
                    assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && key.kind == inner_kind(k, b)
                    implies s_prime.resources()[key].metadata.uid != m by {
                        if s.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == s.resources()[key].metadata.uid {
                        } else {
                            assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
                        }
                    }
                },
                Step::BuiltinControllersStep(input) => {
                    assert(s_prime.api_server == s.api_server);
                    if s.in_flight().contains(msg) {
                        assert(builtin_delete_never_targets_a_mirror(k, b, msg, s));
                    } else {
                        // The garbage collector's Delete of the object at input.1, which has owner references.
                        let key = input.1;
                        assert(s.resources().contains_key(key));
                        assert(s.resources()[key].metadata.owner_references is Some);
                        assert(req.preconditions == Some(PreconditionsView { uid: s.resources()[key].metadata.uid, resource_version: None }));
                        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                        assert(s.resources()[key].metadata.uid is Some);
                        assert(key.kind != inner_kind(k, b)) by {
                            if key.kind == inner_kind(k, b) {
                                assert(mirror_is_bound(k, key)(s));
                                assert(false);
                            }
                        }
                        assert forall |k2: ObjectRef| #[trigger] s.resources().contains_key(k2) && k2.kind == inner_kind(k, b)
                        implies s.resources()[k2].metadata.uid != req.preconditions->0.uid by {
                            assert(k2 != key);
                            assert(Cluster::etcd_object_is_weakly_well_formed(k2)(s));
                            assert(s.resources()[k2].metadata.uid->0 != s.resources()[key].metadata.uid->0);
                        }
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                    assert(s.in_flight().contains(msg));
                    assert(builtin_delete_never_targets_a_mirror(k, b, msg, s));
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// ---------------------------------------------------------------------------
// The sync reconciler's pending request is the one its model sends from its
// triggering snapshot at its current step.
// ---------------------------------------------------------------------------

// The status in the sync reconciler's pending status patch is outer_status_for of
// a source status and an outcome. It does not say the source is a status the
// mirror held.
pub open spec fn pending_status_patch_is_merged(k: SyncKind, msg: Message, outer: SyncedObjectView) -> bool {
    exists |source: SyncedStatusView, outcome: SyncOutcomeView|
        msg.content->APIRequest_0 == APIRequest::PatchStatusRequest(
            #[trigger] sync_reconciler::outer_status_patch(k, outer, outer_status_for(outer.metadata.generation, source, outcome)))
}

// The steps that sync the mirror: the reconcile that reaches them started from a
// live snapshot that carries the sync finalizer.
pub open spec fn sync_step_syncing_mirror(step: WidgetSyncStepView) -> bool {
    ||| step is AfterGetInner
    ||| step is AfterCreateInner
    ||| step is AfterPatchInner
}

// The steps that work on a live outer copy: the reconcile that reaches them
// started from a snapshot without a deletion timestamp.
pub open spec fn sync_step_on_live_copy(step: WidgetSyncStepView) -> bool {
    ||| sync_step_syncing_mirror(step)
    ||| step is AfterAddFinalizer
}

// The steps of a teardown: the reconcile that reaches them started from a
// terminating snapshot that carries the sync finalizer.
pub open spec fn sync_step_of_teardown(step: WidgetSyncStepView) -> bool {
    ||| step is AfterListMirror
    ||| step is AfterGetMirror
    ||| step is AfterDeleteMirror
    ||| step is AfterRemoveFinalizer
}

pub open spec fn sync_pending_request_is(k: SyncKind, controller_id: int, key: ObjectRef, reconcile: OngoingReconcile) -> bool {
    let msg = reconcile.pending_req_msg->0;
    let outer = unmarshal(k.outer_kind, reconcile.triggering_cr)->Ok_0;
    let step = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
    &&& msg.src == HostId::Controller(controller_id, key)
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& step is AfterGetInner ==> msg.content->APIRequest_0 == APIRequest::GetRequest(GetRequest { key: inner_key(k, outer) })
    &&& step is AfterCreateInner ==> msg.content->APIRequest_0 == APIRequest::CreateRequest(CreateRequest {
        namespace: outer.metadata.namespace->0,
        obj: marshal(make_inner(k, outer)),
    })
    &&& step is AfterPatchInner ==> exists |inner: SyncedObjectView| msg.content->APIRequest_0 == APIRequest::PatchRequest(#[trigger] sync_reconciler::inner_spec_patch(k, inner, outer))
    &&& step is AfterAddFinalizer ==> msg.content->APIRequest_0 == APIRequest::UpdateRequest(sync_reconciler::outer_finalizer_update(outer, true))
    &&& step is AfterRemoveFinalizer ==> msg.content->APIRequest_0 == APIRequest::UpdateRequest(sync_reconciler::outer_finalizer_update(outer, false))
    &&& step is AfterListMirror ==> msg.content->APIRequest_0 == APIRequest::ListRequest(sync_reconciler::mirror_list(k, outer))
    &&& step is AfterGetMirror ==> msg.content->APIRequest_0 == APIRequest::GetRequest(GetRequest { key: inner_key(k, outer) })
    &&& step is AfterDeleteMirror ==> exists |inner: SyncedObjectView| msg.content->APIRequest_0 == APIRequest::DeleteRequest(#[trigger] sync_reconciler::mirror_delete(k, outer, inner))
        && inner.metadata.uid is Some
    &&& step is AfterPatchOuterStatus ==> pending_status_patch_is_merged(k, msg, outer)
    &&& step is AfterReportError ==> pending_status_patch_is_merged(k, msg, outer)
    // The steps on a live copy start from a live snapshot: the ones that sync the
    // mirror from one that carries the finalizer, the one that takes it from one
    // that lacks it.
    &&& sync_step_on_live_copy(step) ==> outer.metadata.deletion_timestamp is None
    &&& sync_step_syncing_mirror(step) ==> has_sync_finalizer(outer.metadata)
    &&& step is AfterAddFinalizer ==> !has_sync_finalizer(outer.metadata)
    &&& sync_step_of_teardown(step) ==> outer.metadata.deletion_timestamp is Some && has_sync_finalizer(outer.metadata)
    // A status is written by a reconcile of a live copy it owns, or of one it
    // refuses; a teardown writes none.
    &&& (step is AfterPatchOuterStatus || step is AfterReportError) ==> {
        ||| outer.metadata.deletion_timestamp is None && has_sync_finalizer(outer.metadata)
        ||| cluster_of(k.selector, outer) is None
        ||| !serves(k, outer)
    }
}

// ---------------------------------------------------------------------------
// A snapshot that carries the stored object's resource version is that object.
// ---------------------------------------------------------------------------

// The snapshot `o` of the object at `key` is current when the versions agree:
// scheduling copies the store, and every write of the store stamps a version no
// snapshot has yet.
pub open spec fn snapshot_is_current_at(key: ObjectRef, o: DynamicObjectView, s: ClusterState) -> bool {
    &&& o.metadata.resource_version is Some
    &&& o.metadata.resource_version->0 < s.api_server.resource_version_counter
    &&& (s.resources().contains_key(key) && s.resources()[key].metadata.resource_version == o.metadata.resource_version)
        ==> s.resources()[key] == o
}

pub open spec fn snapshots_are_current(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |key: ObjectRef| #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            ==> snapshot_is_current_at(key, s.scheduled_reconciles(controller_id)[key], s)
        &&& forall |key: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> snapshot_is_current_at(key, s.ongoing_reconciles(controller_id)[key].triggering_cr, s)
    }
}

proof fn lemma_snapshot_stays_current_across_api_server_step(cluster: Cluster, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef, o: DynamicObjectView)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        snapshot_is_current_at(key, o, s),
    ensures snapshot_is_current_at(key, o, s_prime),
{
    lemma_api_server_step_stamps_resource_version(cluster, s, s_prime, msg, key);
    if s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.resource_version == o.metadata.resource_version {
        if s.resources().contains_key(key) && s_prime.resources()[key] == s.resources()[key] {
        } else {
            assert(s_prime.resources()[key].metadata.resource_version == Some(s.api_server.resource_version_counter));
            assert(false);
        }
    }
}

pub proof fn lemma_always_snapshots_are_current(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(snapshots_are_current(controller_id)))),
{
    let inv = snapshots_are_current(controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                assert(s_prime.scheduled_reconciles(controller_id) == s.scheduled_reconciles(controller_id));
                assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                    implies snapshot_is_current_at(key, s_prime.scheduled_reconciles(controller_id)[key], s_prime) by {
                    lemma_snapshot_stays_current_across_api_server_step(cluster, s, s_prime, input->0, key, s.scheduled_reconciles(controller_id)[key]);
                }
                assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
                    implies snapshot_is_current_at(key, s_prime.ongoing_reconciles(controller_id)[key].triggering_cr, s_prime) by {
                    lemma_snapshot_stays_current_across_api_server_step(cluster, s, s_prime, input->0, key, s.ongoing_reconciles(controller_id)[key].triggering_cr);
                }
            },
            Step::ScheduleControllerReconcileStep(input) => {
                assert(s_prime.api_server == s.api_server);
                assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                    implies snapshot_is_current_at(key, s_prime.scheduled_reconciles(controller_id)[key], s_prime) by {
                    if input.0 == controller_id && input.1 == key {
                        // The new snapshot is the stored object.
                        assert(s.resources().contains_key(key));
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
                        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                    } else {
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                    }
                }
            },
            Step::ControllerStep(input) => {
                assert(s_prime.api_server == s.api_server);
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                    implies snapshot_is_current_at(key, s_prime.scheduled_reconciles(controller_id)[key], s_prime) by {
                    assert(s.scheduled_reconciles(controller_id).contains_key(key));
                    assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                }
                assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
                    implies snapshot_is_current_at(key, s_prime.ongoing_reconciles(controller_id)[key].triggering_cr, s_prime) by {
                    if input.0 == controller_id && input.2 == Some(key) {
                        if s.ongoing_reconciles(controller_id).contains_key(key) {
                            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.ongoing_reconciles(controller_id)[key].triggering_cr);
                        } else {
                            // Started from the scheduled snapshot.
                            assert(s.scheduled_reconciles(controller_id).contains_key(key));
                            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
                        }
                    } else {
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    }
                }
            },
            Step::RestartControllerStep(id) => {
                assert(s_prime.api_server == s.api_server);
                if id == controller_id {
                    assert(s_prime.scheduled_reconciles(controller_id) =~= Map::empty());
                    assert(s_prime.ongoing_reconciles(controller_id) =~= Map::empty());
                } else {
                    assert(s_prime.scheduled_reconciles(controller_id) == s.scheduled_reconciles(controller_id));
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                }
            },
            _ => {
                assert(s_prime.api_server == s.api_server);
                assert(s_prime.scheduled_reconciles(controller_id) == s.scheduled_reconciles(controller_id));
                assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
            },
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// The model sends nothing when it ends, never starts over, and sends no external
// request: Init, Done and Error come with no pending request.
pub proof fn lemma_sync_core_ends_without_a_request(k: SyncKind, outer: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetSyncReconcileState)
    ensures ({
        let (state_prime, req_o) = sync_reconciler::reconcile_core(k, outer, resp_o, state);
        &&& !(state_prime.reconcile_step is Init)
        &&& (state_prime.reconcile_step is Done || state_prime.reconcile_step is Error) ==> req_o is None
        &&& req_o is Some ==> req_o->0 is KRequest
    }),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
}

// The same, as the preconditions of the framework's lemmas about those states.
pub proof fn lemma_sync_steps_without_a_pending_request(k: SyncKind, cluster: Cluster, controller_id: int)
    requires cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model(k)),
    ensures
        forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
            #[trigger] at_sync_step_closure(WidgetSyncStepView::Init)((cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0)
            ==> (cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1 is None,
        forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
            #[trigger] (cluster.reconcile_model(controller_id).done)((cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0)
            ==> (cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1 is None,
        forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
            #[trigger] (cluster.reconcile_model(controller_id).error)((cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0)
            ==> (cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1 is None,
        Cluster::reconcile_model_sends_no_external_request(cluster.reconcile_model(controller_id)),
{
    hide(sync_reconciler::reconcile_core);
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let model = cluster.controller_models[controller_id].reconcile_model;
    assert forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
        #[trigger] at_sync_step_closure(WidgetSyncStepView::Init)((model.transition)(cr, resp_o, pre_state).0)
        implies (model.transition)(cr, resp_o, pre_state).1 is None by {
        let outer = unmarshal(k.outer_kind, cr)->Ok_0;
        let resp_um = unmarshal_response_content::<VoidERespView>(resp_o);
        let st0 = WidgetSyncReconcileState::unmarshal(pre_state)->Ok_0;
        let (state_prime, req_o) = sync_reconciler::reconcile_core(k, outer, resp_um, st0);
        assert((model.transition)(cr, resp_o, pre_state) == (state_prime.marshal(), marshal_request_view::<VoidEReqView>(req_o)));
        assert(WidgetSyncReconcileState::unmarshal(state_prime.marshal()) == Ok::<WidgetSyncReconcileState, UnmarshalError>(state_prime));
        lemma_sync_core_ends_without_a_request(k, outer, resp_um, st0);
    }
    assert forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
        #[trigger] (cluster.reconcile_model(controller_id).done)((model.transition)(cr, resp_o, pre_state).0)
        implies (model.transition)(cr, resp_o, pre_state).1 is None by {
        let outer = unmarshal(k.outer_kind, cr)->Ok_0;
        let resp_um = unmarshal_response_content::<VoidERespView>(resp_o);
        let st0 = WidgetSyncReconcileState::unmarshal(pre_state)->Ok_0;
        let (state_prime, req_o) = sync_reconciler::reconcile_core(k, outer, resp_um, st0);
        assert((model.transition)(cr, resp_o, pre_state) == (state_prime.marshal(), marshal_request_view::<VoidEReqView>(req_o)));
        assert(WidgetSyncReconcileState::unmarshal(state_prime.marshal()) == Ok::<WidgetSyncReconcileState, UnmarshalError>(state_prime));
        lemma_sync_core_ends_without_a_request(k, outer, resp_um, st0);
    }
    assert forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
        #[trigger] (cluster.reconcile_model(controller_id).error)((model.transition)(cr, resp_o, pre_state).0)
        implies (model.transition)(cr, resp_o, pre_state).1 is None by {
        let outer = unmarshal(k.outer_kind, cr)->Ok_0;
        let resp_um = unmarshal_response_content::<VoidERespView>(resp_o);
        let st0 = WidgetSyncReconcileState::unmarshal(pre_state)->Ok_0;
        let (state_prime, req_o) = sync_reconciler::reconcile_core(k, outer, resp_um, st0);
        assert((model.transition)(cr, resp_o, pre_state) == (state_prime.marshal(), marshal_request_view::<VoidEReqView>(req_o)));
        assert(WidgetSyncReconcileState::unmarshal(state_prime.marshal()) == Ok::<WidgetSyncReconcileState, UnmarshalError>(state_prime));
        lemma_sync_core_ends_without_a_request(k, outer, resp_um, st0);
    }
    assert forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, local: ReconcileLocalState|
        #[trigger] (model.transition)(cr, resp_o, local).1 is Some
        implies (model.transition)(cr, resp_o, local).1->0 is KubernetesRequest by {
        let outer = unmarshal(k.outer_kind, cr)->Ok_0;
        let resp_um = unmarshal_response_content::<VoidERespView>(resp_o);
        let st0 = WidgetSyncReconcileState::unmarshal(local)->Ok_0;
        let (state_prime, req_o) = sync_reconciler::reconcile_core(k, outer, resp_um, st0);
        assert((model.transition)(cr, resp_o, local) == (state_prime.marshal(), marshal_request_view::<VoidEReqView>(req_o)));
        lemma_sync_core_ends_without_a_request(k, outer, resp_um, st0);
    }
}

// The model sends a request whenever it moves to a step other than Init, Done
// and Error.
pub proof fn lemma_sync_core_sends_a_request_into_every_middle_step(k: SyncKind, outer: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetSyncReconcileState)
    ensures ({
        let (state_prime, req_o) = sync_reconciler::reconcile_core(k, outer, resp_o, state);
        !(state_prime.reconcile_step is Init) && !(state_prime.reconcile_step is Done) && !(state_prime.reconcile_step is Error) ==> req_o is Some
    }),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
}

// So the sync reconciler has a request pending at every such step: the
// precondition of the framework's lemma about those steps, discharged once here
// rather than by unfolding the model at every use.
pub proof fn lemma_sync_step_comes_with_a_pending_request(k: SyncKind, cluster: Cluster, controller_id: int, step: WidgetSyncStepView)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model(k)),
        !(step is Init),
        !(step is Done),
        !(step is Error),
    ensures cluster.state_comes_with_a_pending_request(controller_id, at_sync_step_closure(step)),
{
    hide(sync_reconciler::reconcile_core);
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let model = cluster.controller_models[controller_id].reconcile_model;
    let at = at_sync_step_closure(step);
    assert forall |s: ReconcileLocalState| #[trigger] at(s) implies s != (model.init)() by {
        assert((model.init)() == sync_reconciler::reconcile_init_state().marshal());
        assert(WidgetSyncReconcileState::unmarshal(sync_reconciler::reconcile_init_state().marshal()) == Ok::<WidgetSyncReconcileState, UnmarshalError>(sync_reconciler::reconcile_init_state()));
    }
    assert forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState| #[trigger] at((model.transition)(cr, resp_o, pre_state).0)
        implies (model.transition)(cr, resp_o, pre_state).1 is Some by {
        let outer = unmarshal(k.outer_kind, cr)->Ok_0;
        let resp_um = unmarshal_response_content::<VoidERespView>(resp_o);
        let st = WidgetSyncReconcileState::unmarshal(pre_state)->Ok_0;
        let (state_prime, req_o) = sync_reconciler::reconcile_core(k, outer, resp_um, st);
        assert((model.transition)(cr, resp_o, pre_state) == (state_prime.marshal(), marshal_request_view::<VoidEReqView>(req_o)));
        assert(WidgetSyncReconcileState::unmarshal(state_prime.marshal()) == Ok::<WidgetSyncReconcileState, UnmarshalError>(state_prime));
        assert(state_prime.reconcile_step == step);
        lemma_sync_core_sends_a_request_into_every_middle_step(k, outer, resp_um, st);
        assert(req_o is Some);
    }
}

pub open spec fn sync_pending_requests_match_snapshots(k: SyncKind, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            && s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
            ==> sync_pending_request_is(k, controller_id, key, s.ongoing_reconciles(controller_id)[key])
    }
}

pub proof fn lemma_always_sync_pending_requests_match_snapshots(spec: TempPred<ClusterState>, cluster: Cluster, k: SyncKind, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model(k)),
    ensures spec.entails(always(lift_state(sync_pending_requests_match_snapshots(k, controller_id)))),
{
    let inv = sync_pending_requests_match_snapshots(k, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_synced_states_are_unmarshallable::<WidgetSyncReconcileState, VoidEReqView, VoidERespView>(
        spec, k.outer_kind,
        || sync_reconciler::reconcile_init_state(),
        |obj: SyncedObjectView, resp_o, st| sync_reconciler::reconcile_core(k, obj, resp_o, st),
        |st| sync_reconciler::reconcile_done(st),
        |st| sync_reconciler::reconcile_error(st),
        controller_id);
    cluster.lemma_always_objects_in_reconcile_have_kind(spec, k.outer_kind, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::synced_states_are_unmarshallable::<WidgetSyncReconcileState>(k.outer_kind, controller_id)(s)
        &&& Cluster::objects_in_reconcile_have_kind(k.outer_kind, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::synced_states_are_unmarshallable::<WidgetSyncReconcileState>(k.outer_kind, controller_id)),
        lift_state(Cluster::objects_in_reconcile_have_kind(k.outer_kind, controller_id))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        unmarshal_of_marshal();
        WidgetSyncReconcileState::marshal_preserves_integrity();
        assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
            && s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        implies sync_pending_request_is(k, controller_id, key, s_prime.ongoing_reconciles(controller_id)[key]) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    let (id, resp_msg_opt, cr_key_opt) = input;
                    if id == controller_id && cr_key_opt == Some(key) && s.ongoing_reconciles(controller_id).contains_key(key)
                        && s_prime.ongoing_reconciles(controller_id)[key] != s.ongoing_reconciles(controller_id)[key] {
                        let reconcile = s.ongoing_reconciles(controller_id)[key];
                        let reconcile_prime = s_prime.ongoing_reconciles(controller_id)[key];
                        assert(reconcile_prime.triggering_cr == reconcile.triggering_cr);
                        let outer = unmarshal(k.outer_kind, reconcile.triggering_cr)->Ok_0;
                        let state = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0;
                        let resp_o = if resp_msg_opt is Some {
                            if resp_msg_opt->0.content is APIResponse {
                                Some(ResponseView::<VoidERespView>::KResponse(resp_msg_opt->0.content->APIResponse_0))
                            } else {
                                Some(ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(resp_msg_opt->0.content->ExternalResponse_0)->Ok_0))
                            }
                        } else {
                            None
                        };
                        let (state_prime, req_o) = sync_reconciler::reconcile_core(k, outer, resp_o, state);
                        assert(reconcile_prime.local_state == state_prime.marshal());
                        assert(WidgetSyncReconcileState::unmarshal(reconcile_prime.local_state)->Ok_0 == state_prime);
                        assert(req_o is Some);
                        let msg = reconcile_prime.pending_req_msg->0;
                        assert(msg == controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req_o->0->KRequest_0));
                        // A response consumed means the request it answers was pending, so
                        // the invariant already held of this reconcile.
                        assert(resp_msg_opt is Some ==> reconcile.pending_req_msg is Some);
                        assert(reconcile.pending_req_msg is Some ==> sync_pending_request_is(k, controller_id, key, reconcile));
                        match state.reconcile_step {
                            WidgetSyncStepView::Init => {
                                if state_prime.reconcile_step is AfterGetInner || state_prime.reconcile_step is AfterAddFinalizer
                                    || state_prime.reconcile_step is AfterListMirror
                                    || state_prime.reconcile_step is AfterRemoveFinalizer {
                                } else {
                                    // A live object that names no inner cluster (the
                                    // rejection is reported) or a binding this reconciler
                                    // does not serve (the inner cluster is reported
                                    // unreachable); a terminating one is released above.
                                    assert(state_prime.reconcile_step is AfterPatchOuterStatus || state_prime.reconcile_step is AfterReportError);
                                    assert(pending_status_patch_is_merged(k, msg, outer));
                                    assert(cluster_of(k.selector, outer) is None || !serves(k, outer));
                                }
                            },
                            WidgetSyncStepView::AfterGetInner => {
                                assert(resp_msg_opt is Some);
                                assert(has_sync_finalizer(outer.metadata));
                                if state_prime.reconcile_step is AfterCreateInner {
                                } else if state_prime.reconcile_step is AfterPatchInner {
                                    let res = extract_some_k_get_resp_view(resp_o);
                                    let inner = unmarshal(inner_key(k, outer).kind, res->Ok_0)->Ok_0;
                                    assert(msg.content->APIRequest_0 == APIRequest::PatchRequest(sync_reconciler::inner_spec_patch(k, inner, outer)));
                                } else {
                                    assert(state_prime.reconcile_step is AfterPatchOuterStatus || state_prime.reconcile_step is AfterReportError);
                                    assert(pending_status_patch_is_merged(k, msg, outer));
                                }
                            },
                            WidgetSyncStepView::AfterListMirror => {
                                assert(resp_msg_opt is Some);
                                assert(state_prime.reconcile_step is AfterRemoveFinalizer || state_prime.reconcile_step is AfterGetMirror);
                            },
                            WidgetSyncStepView::AfterGetMirror => {
                                assert(resp_msg_opt is Some);
                                if state_prime.reconcile_step is AfterRemoveFinalizer {
                                } else {
                                    assert(state_prime.reconcile_step is AfterDeleteMirror);
                                    let res = extract_some_k_get_resp_view(resp_o);
                                    let inner = unmarshal(inner_key(k, outer).kind, res->Ok_0)->Ok_0;
                                    assert(msg.content->APIRequest_0 == APIRequest::DeleteRequest(sync_reconciler::mirror_delete(k, outer, inner)));
                                    assert(inner.metadata.uid is Some);
                                }
                            },
                            // After a failed Create of the mirror, the failure is being
                            // reported. After a Patch, the same -- unless the inner
                            // cluster stored another spec, and SpecRewritten is.
                            WidgetSyncStepView::AfterCreateInner => {
                                assert(resp_msg_opt is Some);
                                assert(state_prime.reconcile_step is AfterReportError);
                                assert(pending_status_patch_is_merged(k, msg, outer));
                            },
                            WidgetSyncStepView::AfterPatchInner => {
                                assert(resp_msg_opt is Some);
                                assert(state_prime.reconcile_step is AfterPatchOuterStatus || state_prime.reconcile_step is AfterReportError);
                                assert(pending_status_patch_is_merged(k, msg, outer));
                            },
                            // The Delete of the mirror and the Update of the finalizers
                            // are followed by no request.
                            _ => {
                                assert(false);
                            },
                        }
                        let step_prime = state_prime.reconcile_step;
                        assert(sync_step_on_live_copy(step_prime) ==> outer.metadata.deletion_timestamp is None);
                        assert(sync_step_syncing_mirror(step_prime) ==> has_sync_finalizer(outer.metadata));
                        assert(step_prime is AfterAddFinalizer ==> !has_sync_finalizer(outer.metadata));
                        assert(sync_step_of_teardown(step_prime) ==> outer.metadata.deletion_timestamp is Some && has_sync_finalizer(outer.metadata));
                        assert((step_prime is AfterPatchOuterStatus || step_prime is AfterReportError)
                            ==> (outer.metadata.deletion_timestamp is None && has_sync_finalizer(outer.metadata))
                                || cluster_of(k.selector, outer) is None || !serves(k, outer));
                    } else {
                        if s.ongoing_reconciles(controller_id).contains_key(key) {
                            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        } else {
                            // Just started: no pending request.
                            assert(false);
                        }
                    }
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

}
