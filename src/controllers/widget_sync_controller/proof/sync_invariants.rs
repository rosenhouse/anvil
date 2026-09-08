// Safety invariants about the sync reconciler's own requests and about the
// built-in garbage collector, used by the sync reconciler's liveness proofs.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::api_server::*;
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
    &&& step is AfterPatchOuterStatus ==> exists |status: SyncedStatusView| msg.content->APIRequest_0 == APIRequest::PatchStatusRequest(#[trigger] sync_reconciler::outer_status_patch(k, outer, status))
    &&& step is AfterReportError ==> exists |status: SyncedStatusView| msg.content->APIRequest_0 == APIRequest::PatchStatusRequest(#[trigger] sync_reconciler::outer_status_patch(k, outer, status))
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
                        match state.reconcile_step {
                            WidgetSyncStepView::Init => {
                                if state_prime.reconcile_step is AfterGetInner {
                                } else {
                                    // The object names no inner cluster: the rejection is reported.
                                    assert(state_prime.reconcile_step is AfterPatchOuterStatus);
                                    assert(exists |status: SyncedStatusView| msg.content->APIRequest_0 == APIRequest::PatchStatusRequest(#[trigger] sync_reconciler::outer_status_patch(k, outer, status)));
                                }
                            },
                            WidgetSyncStepView::AfterGetInner => {
                                if state_prime.reconcile_step is AfterCreateInner {
                                } else if state_prime.reconcile_step is AfterPatchInner {
                                    let res = extract_some_k_get_resp_view(resp_o);
                                    let inner = unmarshal(inner_key(k, outer).kind, res->Ok_0)->Ok_0;
                                    assert(msg.content->APIRequest_0 == APIRequest::PatchRequest(sync_reconciler::inner_spec_patch(k, inner, outer)));
                                } else {
                                    assert(state_prime.reconcile_step is AfterPatchOuterStatus || state_prime.reconcile_step is AfterReportError);
                                    assert(exists |status: SyncedStatusView| msg.content->APIRequest_0 == APIRequest::PatchStatusRequest(#[trigger] sync_reconciler::outer_status_patch(k, outer, status)));
                                }
                            },
                            WidgetSyncStepView::AfterCreateInner => {
                                // The Create failed and the failure is being reported.
                                assert(state_prime.reconcile_step is AfterReportError);
                                assert(exists |status: SyncedStatusView| msg.content->APIRequest_0 == APIRequest::PatchStatusRequest(#[trigger] sync_reconciler::outer_status_patch(k, outer, status)));
                            },
                            WidgetSyncStepView::AfterPatchInner => {
                                // The Patch failed and the failure is being reported.
                                assert(state_prime.reconcile_step is AfterReportError);
                                assert(exists |status: SyncedStatusView| msg.content->APIRequest_0 == APIRequest::PatchStatusRequest(#[trigger] sync_reconciler::outer_status_patch(k, outer, status)));
                            },
                            _ => {
                                assert(false);
                            },
                        }
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
