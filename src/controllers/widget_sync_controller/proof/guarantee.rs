// The guarantee conditions of the sync reconciler and of the janitor, proved as
// invariants from the cluster model alone (no rely needed): they describe the
// requests the two reconcilers send.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::api_server::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::{
    model::{install::*, janitor_reconciler, sync_reconciler::*},
    proof::{helper_invariants::*, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The sync reconciler: every scheduled and ongoing reconcile is triggered by a
// snapshot of a well-formed outer copy whose uid is bound to its key.
// ---------------------------------------------------------------------------

pub open spec fn outer_snapshot_is_bound(cr: DynamicObjectView, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& OuterWidgetView::unmarshal(cr) is Ok
        &&& cr.object_ref() == key
        &&& cr.metadata.uid is Some
        &&& cr.metadata.generation is Some
        &&& parent_uid_is_bound_to_key(cr.metadata.uid->0, key)(s)
    }
}

pub open spec fn sync_scheduled_crs_are_bound(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            ==> outer_snapshot_is_bound(s.scheduled_reconciles(controller_id)[key], key)(s)
    }
}

pub open spec fn sync_triggering_crs_are_bound(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> outer_snapshot_is_bound(s.ongoing_reconciles(controller_id)[key].triggering_cr, key)(s)
    }
}

pub proof fn lemma_always_sync_crs_are_bound(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<OuterWidgetView>(),
        cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model()),
    ensures
        spec.entails(always(lift_state(sync_scheduled_crs_are_bound(controller_id)))),
        spec.entails(always(lift_state(sync_triggering_crs_are_bound(controller_id)))),
{
    let inv = |s: ClusterState| {
        &&& sync_scheduled_crs_are_bound(controller_id)(s)
        &&& sync_triggering_crs_are_bound(controller_id)(s)
    };
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>(spec);
    cluster.lemma_always_etcd_objects_have_unique_uids(spec);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>()(s)
        &&& Cluster::etcd_objects_have_unique_uids()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>()),
        lift_state(Cluster::etcd_objects_have_unique_uids())
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, input->0);
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                implies outer_snapshot_is_bound(s_prime.scheduled_reconciles(controller_id)[key], key)(s_prime) by {
                    assert(s.scheduled_reconciles(controller_id).contains_key(key));
                    let cr = s.scheduled_reconciles(controller_id)[key];
                    lemma_uid_stays_bound_to_key(cr.metadata.uid->0, key, s, s_prime);
                }
                assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
                implies outer_snapshot_is_bound(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr, key)(s_prime) by {
                    assert(s.ongoing_reconciles(controller_id).contains_key(key));
                    let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
                    lemma_uid_stays_bound_to_key(cr.metadata.uid->0, key, s, s_prime);
                }
            },
            Step::ScheduleControllerReconcileStep(input) => {
                assert(s_prime.api_server == s.api_server);
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                implies outer_snapshot_is_bound(s_prime.scheduled_reconciles(controller_id)[key], key)(s_prime) by {
                    if input.0 == controller_id && input.1 == key {
                        // The snapshot is the stored outer copy.
                        let obj = s.resources()[key];
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == obj);
                        assert(key.kind == OuterWidgetView::kind());
                        assert(cluster.etcd_object_is_well_formed(key)(s));
                        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                        assert(OuterWidgetView::unmarshal(obj) is Ok);
                        assert forall |k: ObjectRef| #[trigger] s.resources().contains_key(k) && s.resources()[k].metadata.uid == obj.metadata.uid
                        implies k == key by {
                            if k != key {
                                assert(s.resources()[k].metadata.uid->0 != s.resources()[key].metadata.uid->0);
                            }
                        }
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
                implies outer_snapshot_is_bound(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr, key)(s_prime) by {
                    if s.ongoing_reconciles(controller_id).contains_key(key) {
                        assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.ongoing_reconciles(controller_id)[key].triggering_cr);
                    } else {
                        // A scheduled reconcile just started running.
                        assert(input.0 == controller_id && input.2 == Some(key));
                        assert(s.scheduled_reconciles(controller_id).contains_key(key));
                        assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
                    }
                }
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                implies outer_snapshot_is_bound(s_prime.scheduled_reconciles(controller_id)[key], key)(s_prime) by {
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
    always_weaken(spec, lift_state(inv), lift_state(sync_scheduled_crs_are_bound(controller_id)));
    always_weaken(spec, lift_state(inv), lift_state(sync_triggering_crs_are_bound(controller_id)));
}

// ---------------------------------------------------------------------------
// The status the sync reconciler writes has exactly one condition, Synced.
// ---------------------------------------------------------------------------

pub proof fn lemma_synced_condition_of_written_status(status: WidgetStatusView)
    requires
        status.conditions is Some,
        status.conditions->0.len() == 1,
        status.conditions->0[0].type_ == synced_condition_type(),
    ensures status.synced_condition() == Some(status.conditions->0[0]),
{
    let conditions = status.conditions->0;
    assert(0 <= 0 < conditions.len() && (#[trigger] conditions[0]).type_ == synced_condition_type());
    let i = choose |i: int| 0 <= i < conditions.len() && (#[trigger] conditions[i]).type_ == synced_condition_type();
    assert(i == 0);
}

// ---------------------------------------------------------------------------
// The sync guarantee.
// ---------------------------------------------------------------------------

pub proof fn lemma_always_widget_sync_guarantee(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<OuterWidgetView>(),
        cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model()),
    ensures spec.entails(always(lift_state(widget_sync_guarantee(controller_id)))),
{
    let inv = widget_sync_guarantee(controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    lemma_always_sync_crs_are_bound(spec, cluster, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& sync_triggering_crs_are_bound(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(sync_triggering_crs_are_bound(controller_id))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        OuterWidgetView::marshal_preserves_integrity();
        InnerWidgetView::marshal_preserves_integrity();
        OuterWidgetView::marshal_status_preserves_integrity();
        WidgetSyncReconcileState::marshal_preserves_integrity();
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } implies sync_request_is_guaranteed(msg, s_prime) by {
            match step {
                Step::APIServerStep(input) => {
                    // No new request from this controller; the store may have changed.
                    assert(s.in_flight().contains(msg));
                    assert(sync_request_is_guaranteed(msg, s));
                    lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, input->0);
                    lemma_sync_request_guarantee_is_preserved(msg, s, s_prime);
                },
                Step::ControllerStep(input) => {
                    assert(s_prime.api_server == s.api_server);
                    if s.in_flight().contains(msg) {
                        assert(sync_request_is_guaranteed(msg, s));
                        lemma_sync_request_guarantee_is_preserved(msg, s, s_prime);
                    } else {
                        // A request this controller just sent.
                        let (id, resp_msg_opt, cr_key_opt) = input;
                        assert(id == controller_id);
                        let cr_key = cr_key_opt->0;
                        assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
                        assert(msg == s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0);
                        assert(msg.src == HostId::Controller(controller_id, cr_key));
                        lemma_sync_new_request_is_guaranteed(cluster, controller_id, s, s_prime, input, msg);
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                    assert(s.in_flight().contains(msg));
                    assert(sync_request_is_guaranteed(msg, s));
                    lemma_sync_request_guarantee_is_preserved(msg, s, s_prime);
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// The body of widget_sync_guarantee for one message.
pub open spec fn sync_request_is_guaranteed(msg: Message, s: ClusterState) -> bool {
    let outer_key = msg.src->Controller_1;
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(req) => req.key == inner_key_of(outer_key),
        APIRequest::CreateRequest(req) => mirror_create_req(req, outer_key)(s),
        APIRequest::PatchRequest(req) => {
            &&& req.kind == InnerWidgetView::kind()
            &&& req.namespace == outer_key.namespace
            &&& req.name == outer_key.name
        },
        APIRequest::PatchStatusRequest(req) => sync_status_patch_req(req, outer_key),
        _ => false,
    }
}

proof fn lemma_sync_request_guarantee_is_preserved(msg: Message, s: ClusterState, s_prime: ClusterState)
    requires
        sync_request_is_guaranteed(msg, s),
        store_only_grows_by_fresh_uids(s, s_prime) || s_prime.api_server == s.api_server,
    ensures sync_request_is_guaranteed(msg, s_prime),
{
    let outer_key = msg.src->Controller_1;
    match msg.content->APIRequest_0 {
        APIRequest::CreateRequest(req) => {
            let outer = choose |outer: OuterWidgetView| {
                &&& outer.object_ref() == outer_key
                &&& outer.metadata.uid is Some
                &&& req.namespace == outer_key.namespace
                &&& req.obj == #[trigger] make_inner(outer).marshal()
                &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s)
            };
            if s_prime.api_server == s.api_server {
                assert(parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s_prime));
            } else {
                lemma_uid_stays_bound_to_key(outer.metadata.uid->0, outer_key, s, s_prime);
            }
            assert(mirror_create_req(req, outer_key)(s_prime));
        },
        _ => {},
    }
}

proof fn lemma_sync_new_request_is_guaranteed(
    cluster: Cluster, controller_id: int, s: ClusterState, s_prime: ClusterState,
    input: (int, Option<Message>, Option<ObjectRef>), msg: Message
)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model()),
        cluster.next_step(s, s_prime, Step::ControllerStep(input)),
        Cluster::there_is_the_controller_state(controller_id)(s),
        sync_triggering_crs_are_bound(controller_id)(s),
        input.0 == controller_id,
        input.2 is Some,
        s.ongoing_reconciles(controller_id).contains_key(input.2->0),
        s_prime.ongoing_reconciles(controller_id).contains_key(input.2->0),
        s_prime.ongoing_reconciles(controller_id)[input.2->0].pending_req_msg == Some(msg),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        msg.content is APIRequest,
    ensures sync_request_is_guaranteed(msg, s_prime),
{
    OuterWidgetView::marshal_preserves_integrity();
    InnerWidgetView::marshal_preserves_integrity();
    OuterWidgetView::marshal_status_preserves_integrity();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let cr_key = input.2->0;
    let reconcile = s.ongoing_reconciles(controller_id)[cr_key];
    let outer = OuterWidgetView::unmarshal(reconcile.triggering_cr)->Ok_0;
    assert(outer_snapshot_is_bound(reconcile.triggering_cr, cr_key)(s));
    assert(outer.object_ref() == cr_key);
    assert(outer.metadata == reconcile.triggering_cr.metadata);
    assert(s_prime.api_server == s.api_server);
    let state = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0;
    let resp_o = if input.1 is Some {
        if input.1->0.content is APIResponse {
            Some(ResponseView::<VoidERespView>::KResponse(input.1->0.content->APIResponse_0))
        } else {
            Some(ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(input.1->0.content->ExternalResponse_0)->Ok_0))
        }
    } else {
        None
    };
    let (state_prime, req_o) = reconcile_core(outer, resp_o, state);
    assert(req_o is Some);
    assert(req_o->0 is KRequest);
    let req = req_o->0->KRequest_0;
    assert(msg.content->APIRequest_0 == req);
    assert(msg.src == HostId::Controller(controller_id, cr_key));
    match state.reconcile_step {
        WidgetSyncStepView::Init => {
            assert(req == APIRequest::GetRequest(GetRequest { key: inner_key(outer) }));
            assert(inner_key(outer) == inner_key_of(cr_key));
        },
        WidgetSyncStepView::AfterGetInner => {
            match req {
                APIRequest::CreateRequest(create_req) => {
                    assert(create_req.obj == make_inner(outer).marshal());
                    assert(create_req.namespace == cr_key.namespace);
                    assert(mirror_create_req(create_req, cr_key)(s_prime));
                },
                APIRequest::PatchRequest(patch_req) => {
                    assert(patch_req.kind == InnerWidgetView::kind());
                    assert(patch_req.namespace == cr_key.namespace);
                    assert(patch_req.name == cr_key.name);
                },
                APIRequest::PatchStatusRequest(patch_req) => {
                    lemma_outer_status_patch_is_guaranteed(outer, patch_req, cr_key);
                },
                _ => { assert(false); },
            }
        },
        // After a failed Create or Patch of the mirror the reconciler reports the
        // failure with a status patch of the outer copy.
        WidgetSyncStepView::AfterCreateInner => {
            match req {
                APIRequest::PatchStatusRequest(patch_req) => {
                    lemma_outer_status_patch_is_guaranteed(outer, patch_req, cr_key);
                },
                _ => { assert(false); },
            }
        },
        WidgetSyncStepView::AfterPatchInner => {
            match req {
                APIRequest::PatchStatusRequest(patch_req) => {
                    lemma_outer_status_patch_is_guaranteed(outer, patch_req, cr_key);
                },
                _ => { assert(false); },
            }
        },
        _ => { assert(false); },
    }
}

// Every status patch the sync reconciler forms from a bound outer snapshot
// satisfies sync_status_patch_req.
proof fn lemma_outer_status_patch_is_guaranteed(outer: OuterWidgetView, req: PatchStatusRequest, outer_key: ObjectRef)
    requires
        outer.object_ref() == outer_key,
        outer.metadata.uid is Some,
        outer.metadata.generation is Some,
        exists |status: WidgetStatusView| req == outer_status_patch(outer, status) && written_status_shape(status, outer.metadata.generation),
    ensures sync_status_patch_req(req, outer_key),
{
    OuterWidgetView::marshal_status_preserves_integrity();
    let status = choose |status: WidgetStatusView| req == outer_status_patch(outer, status) && written_status_shape(status, outer.metadata.generation);
    assert(req.status == OuterWidgetView::marshal_status(Some(status)));
    assert(OuterWidgetView::unmarshal_status(req.status) == Ok::<Option<WidgetStatusView>, UnmarshalError>(Some(status)));
    lemma_synced_condition_of_written_status(status);
}

// The shape of every status the sync reconciler writes for a snapshot at `generation`.
pub open spec fn written_status_shape(status: WidgetStatusView, generation: Option<int>) -> bool {
    &&& status.observed_generation == generation
    &&& status.conditions is Some
    &&& status.conditions->0.len() == 1
    &&& status.conditions->0[0].type_ == synced_condition_type()
    &&& status.conditions->0[0].observed_generation == generation
}

pub proof fn lemma_outer_status_for_has_written_shape(generation: Option<int>, inner_status: WidgetStatusView, synced: bool, reason: StringView)
    ensures written_status_shape(outer_status_for(generation, inner_status, synced, reason), generation),
{
}

pub proof fn lemma_outer_status_without_inner_has_written_shape(generation: Option<int>, previous: Option<WidgetStatusView>, reason: StringView)
    ensures written_status_shape(outer_status_without_inner(generation, previous, reason), generation),
{
}

// ---------------------------------------------------------------------------
// The janitor guarantee.
// ---------------------------------------------------------------------------

// The body of widget_janitor_guarantee for one message.
pub open spec fn janitor_request_is_guaranteed(msg: Message) -> bool {
    let inner_key = msg.src->Controller_1;
    match msg.content->APIRequest_0 {
        APIRequest::ListRequest(req) => {
            &&& req.kind == OuterWidgetView::kind()
            &&& req.namespace == inner_key.namespace
        },
        APIRequest::DeleteRequest(req) => {
            &&& req.key == inner_key
            &&& mirror_delete_req(req)
        },
        _ => false,
    }
}

pub proof fn lemma_always_widget_janitor_guarantee(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<InnerWidgetView>(),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
    ensures spec.entails(always(lift_state(widget_janitor_guarantee(controller_id)))),
{
    let inv = widget_janitor_guarantee(controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<InnerWidgetView>(spec, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<InnerWidgetView>(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<InnerWidgetView>(controller_id))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        InnerWidgetView::marshal_preserves_integrity();
        janitor_reconciler::WidgetJanitorReconcileState::marshal_preserves_integrity();
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } implies janitor_request_is_guaranteed(msg) by {
            if s.in_flight().contains(msg) {
                assert(janitor_request_is_guaranteed(msg));
            } else {
                match step {
                    Step::ControllerStep(input) => {
                        let (id, resp_msg_opt, cr_key_opt) = input;
                        assert(id == controller_id);
                        let cr_key = cr_key_opt->0;
                        assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
                        assert(msg == s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0);
                        assert(msg.src == HostId::Controller(controller_id, cr_key));
                        lemma_janitor_new_request_is_guaranteed(cluster, controller_id, s, s_prime, input, msg);
                    },
                    _ => { assert(false); },
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

proof fn lemma_janitor_new_request_is_guaranteed(
    cluster: Cluster, controller_id: int, s: ClusterState, s_prime: ClusterState,
    input: (int, Option<Message>, Option<ObjectRef>), msg: Message
)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        cluster.next_step(s, s_prime, Step::ControllerStep(input)),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<InnerWidgetView>(controller_id)(s),
        input.0 == controller_id,
        input.2 is Some,
        s.ongoing_reconciles(controller_id).contains_key(input.2->0),
        s_prime.ongoing_reconciles(controller_id).contains_key(input.2->0),
        s_prime.ongoing_reconciles(controller_id)[input.2->0].pending_req_msg == Some(msg),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        msg.content is APIRequest,
    ensures janitor_request_is_guaranteed(msg),
{
    InnerWidgetView::marshal_preserves_integrity();
    janitor_reconciler::WidgetJanitorReconcileState::marshal_preserves_integrity();
    let cr_key = input.2->0;
    let reconcile = s.ongoing_reconciles(controller_id)[cr_key];
    assert(cr_key.kind == InnerWidgetView::kind());
    assert(InnerWidgetView::unmarshal(reconcile.triggering_cr) is Ok);
    let inner = InnerWidgetView::unmarshal(reconcile.triggering_cr)->Ok_0;
    assert(inner.metadata == reconcile.triggering_cr.metadata);
    assert(reconcile.triggering_cr.object_ref() == cr_key);
    assert(inner.object_ref() == cr_key);
    assert(inner.metadata.uid is Some);
    let state = janitor_reconciler::WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0;
    let resp_o = if input.1 is Some {
        if input.1->0.content is APIResponse {
            Some(ResponseView::<VoidERespView>::KResponse(input.1->0.content->APIResponse_0))
        } else {
            Some(ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(input.1->0.content->ExternalResponse_0)->Ok_0))
        }
    } else {
        None
    };
    let (state_prime, req_o) = janitor_reconciler::reconcile_core(inner, resp_o, state);
    assert(req_o is Some);
    assert(req_o->0 is KRequest);
    let req = req_o->0->KRequest_0;
    assert(msg.content->APIRequest_0 == req);
    assert(msg.src == HostId::Controller(controller_id, cr_key));
    match state.reconcile_step {
        WidgetJanitorStepView::Init => {
            assert(req == APIRequest::ListRequest(ListRequest {
                kind: OuterWidgetView::kind(),
                namespace: inner.metadata.namespace->0,
            }));
            assert(inner.metadata.namespace->0 == cr_key.namespace);
        },
        WidgetJanitorStepView::AfterListOuter => {
            match req {
                APIRequest::DeleteRequest(delete_req) => {
                    assert(delete_req.key == inner.object_ref());
                    assert(delete_req.preconditions == Some(PreconditionsView::default().with_uid_from_object_meta(inner.metadata)));
                    assert(delete_req.preconditions->0.uid == inner.metadata.uid);
                },
                _ => { assert(false); },
            }
        },
        _ => { assert(false); },
    }
}

}
