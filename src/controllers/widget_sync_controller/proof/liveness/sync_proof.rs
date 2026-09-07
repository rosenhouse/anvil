// R1: once the outer copy is stable, the mirror eventually exists, is ours and
// carries the outer spec, and stays so.
//
// For an outer copy `outer` (key `key`, mirror key `ikey`):
//     always(outer_stable(outer)) ~> always(spec_synced(outer))
//
// The proof has three parts.
// 1. Phases I and II: failures are disabled; the snapshots the sync reconciler
//    works from carry the outer spec and uid; the only request of the sync
//    reconciler for `key` in flight is the pending one; requests and responses
//    are consistent.
// 2. The mirror key eventually and stably holds nothing or our mirror: a stale
//    mirror is collected by the janitor (R3, the liveness dependency), a
//    terminating one is released by the inner side (D3), and our mirror is kept
//    by everyone.
// 3. One reconcile of the outer copy creates the mirror or patches its spec, after
//    which nothing changes it.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
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
    model::{install::*, sync_reconciler::*},
    proof::{
        guarantee::*, helper_invariants::*, janitor_invariants::*,
        liveness::{janitor_proof::*, terminate},
        predicate::*, sync_invariants::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Fairness, rely and invariants.
// ---------------------------------------------------------------------------

pub open spec fn sync_next_with_wf(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_action(cluster.next()))
    .and(tla_forall(|input| cluster.api_server_next().weak_fairness(input)))
    .and(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))))
    .and(tla_forall(|input| cluster.disable_crash().weak_fairness(input)))
    .and(tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))))
    .and(cluster.disable_req_drop().weak_fairness(()))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
}

pub proof fn sync_next_with_wf_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(sync_next_with_wf(cluster, controller_id))),
{
    always_p_is_stable(lift_action(cluster.next()));
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.api_server_next());
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.builtin_controllers_next());
    cluster.tla_forall_controller_next_weak_fairness_is_stable(controller_id);
    cluster.tla_forall_schedule_controller_reconcile_weak_fairness_is_stable(controller_id);
    cluster.tla_forall_external_next_weak_fairness_is_stable(controller_id);
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.disable_crash());
    Cluster::action_weak_fairness_is_stable(cluster.disable_req_drop());
    Cluster::action_weak_fairness_is_stable(cluster.disable_pod_monkey());
    stable_and_n!(
        always(lift_action(cluster.next())),
        tla_forall(|input| cluster.api_server_next().weak_fairness(input)),
        tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)),
        tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))),
        tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))),
        tla_forall(|input| cluster.disable_crash().weak_fairness(input)),
        tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))),
        cluster.disable_req_drop().weak_fairness(()),
        cluster.disable_pod_monkey().weak_fairness(())
    );
}

// What the sync reconciler assumes about every other controller: the janitor
// (identified by `janitor_id`) satisfies its own guarantee, anyone else satisfies
// widget_sync_rely.
pub open spec fn sync_rely_with_janitor(cluster: Cluster, controller_id: int, janitor_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |other_id| #[trigger] cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> if other_id == janitor_id { widget_janitor_guarantee(janitor_id)(s) } else { widget_sync_rely(other_id)(s) }
    }
}

// The sync reconciler's cluster: it runs at `controller_id`, the janitor at
// `janitor_id`, and both Widget types are installed.
pub open spec fn sync_membership(cluster: Cluster, controller_id: int, janitor_id: int) -> bool {
    &&& cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model())
    &&& cluster.controller_models.contains_key(janitor_id)
    &&& controller_id != janitor_id
    &&& cluster.type_is_installed_in_cluster::<InnerWidgetView>()
    &&& cluster.type_is_installed_in_cluster::<OuterWidgetView>()
}

// What the rely, together with the sync reconciler's own guarantee and the
// cluster's structural invariants, says about writes of mirrors by anyone.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_sync_rely_implies_mirror_write_facts(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))),
        spec.entails(always(lift_state(widget_sync_guarantee(controller_id)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
    ensures
        spec.entails(always(lift_state(every_in_flight_inner_create_is_a_mirror_create()))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity()))),
        spec.entails(always(lift_state(widget_janitor_guarantee(janitor_id)))),
{
    let rely = sync_rely_with_janitor(cluster, controller_id, janitor_id);
    let all = |s: ClusterState| {
        &&& rely(s)
        &&& widget_sync_guarantee(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
    };
    entails_always_and_n!(
        spec,
        lift_state(rely),
        lift_state(widget_sync_guarantee(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())
    );
    temp_pred_equality(
        lift_state(all),
        lift_state(rely)
            .and(lift_state(widget_sync_guarantee(controller_id)))
            .and(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))
            .and(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()))
            .and(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()))
            .and(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))
    );
    assert forall |s: ClusterState| #[trigger] all(s) implies {
        &&& every_in_flight_inner_create_is_a_mirror_create()(s)
        &&& every_in_flight_inner_update_preserves_identity()(s)
        &&& widget_janitor_guarantee(janitor_id)(s)
    } by {
        assert(cluster.controller_models.remove(controller_id).contains_key(janitor_id));
        assert(widget_janitor_guarantee(janitor_id)(s));
        assert forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        } implies {
            &&& (msg.content.is_create_request() && msg.content.get_create_request().obj.kind == InnerWidgetView::kind()) ==> {
                let req = msg.content.get_create_request();
                &&& req.obj.metadata.name is Some
                &&& mirror_create_req(req, ObjectRef {
                    kind: OuterWidgetView::kind(),
                    namespace: req.namespace,
                    name: req.obj.metadata.name->0,
                })(s)
            }
            &&& msg.content.is_update_request() ==> mirror_update_req(msg.content.get_update_request())(s)
            &&& msg.content.is_get_then_update_request() ==> mirror_get_then_update_req(msg.content.get_get_then_update_request())(s)
        } by {
            match msg.src {
                HostId::Controller(id, k) => {
                    assert(cluster.controller_models.contains_key(id));
                    if id == controller_id {
                        assert(sync_request_is_guaranteed(msg, s));
                        if msg.content.is_create_request() {
                            let req = msg.content.get_create_request();
                            assert(mirror_create_req(req, k)(s));
                            let outer = choose |outer: OuterWidgetView| {
                                &&& outer.object_ref() == k
                                &&& outer.metadata.uid is Some
                                &&& req.namespace == k.namespace
                                &&& req.obj == #[trigger] make_inner(outer).marshal()
                                &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, k)(s)
                            };
                            assert(req.obj.metadata.name == Some(k.name));
                            assert(ObjectRef { kind: OuterWidgetView::kind(), namespace: req.namespace, name: req.obj.metadata.name->0 } == k);
                        }
                    } else {
                        assert(cluster.controller_models.remove(controller_id).contains_key(id));
                        if id == janitor_id {
                            assert(janitor_request_is_guaranteed(msg));
                        } else {
                            assert(widget_sync_rely(id)(s));
                        }
                    }
                },
                HostId::BuiltinController => {},
                HostId::PodMonkey => {},
                _ => {},
            }
        }
    }
    always_weaken(spec, lift_state(all), lift_state(every_in_flight_inner_create_is_a_mirror_create()));
    always_weaken(spec, lift_state(all), lift_state(every_in_flight_inner_update_preserves_identity()));
    always_weaken(spec, lift_state(all), lift_state(widget_janitor_guarantee(janitor_id)));
}

// Invariants that hold from the initial state on.
pub open spec fn sync_invariants(cluster: Cluster, controller_id: int, janitor_id: int) -> TempPred<ClusterState> {
    always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>())))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(controller_id))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))))
    .and(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    .and(always(lift_state(Cluster::there_is_the_controller_state(janitor_id))))
    .and(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))))
    .and(always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner))))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner))))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner))))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus))))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)))))
    .and(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id))))
    .and(always(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external())))
    .and(always(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests())))
    .and(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())))
    .and(always(lift_state(widget_sync_guarantee(controller_id))))
    .and(always(lift_state(widget_janitor_guarantee(janitor_id))))
    .and(always(lift_state(every_in_flight_inner_create_is_a_mirror_create())))
    .and(always(lift_state(every_in_flight_inner_update_preserves_identity())))
    .and(always(lift_state(every_mirror_is_bound())))
    .and(always(lift_state(sync_scheduled_crs_are_bound(controller_id))))
    .and(always(lift_state(sync_triggering_crs_are_bound(controller_id))))
    .and(always(lift_state(janitor_deletes_are_sound(janitor_id))))
    .and(always(lift_state(builtin_deletes_never_target_mirrors())))
    .and(always(lift_state(sync_pending_requests_match_snapshots(controller_id))))
}

pub proof fn sync_invariants_is_stable(cluster: Cluster, controller_id: int, janitor_id: int)
    ensures valid(stable(sync_invariants(cluster, controller_id, janitor_id))),
{
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_unique_id()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_p_is_stable(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()));
    always_p_is_stable(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()));
    always_p_is_stable(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()));
    always_p_is_stable(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>()));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)));
    always_p_is_stable(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()));
    always_p_is_stable(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(controller_id)));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))));
    always_p_is_stable(lift_state(Cluster::there_is_the_controller_state(controller_id)));
    always_p_is_stable(lift_state(Cluster::there_is_the_controller_state(janitor_id)));
    always_p_is_stable(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)));
    always_p_is_stable(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id)));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init)))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner)))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner)))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner)))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus)))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error))));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id)));
    always_p_is_stable(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()));
    always_p_is_stable(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()));
    always_p_is_stable(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    always_p_is_stable(lift_state(widget_sync_guarantee(controller_id)));
    always_p_is_stable(lift_state(widget_janitor_guarantee(janitor_id)));
    always_p_is_stable(lift_state(every_in_flight_inner_create_is_a_mirror_create()));
    always_p_is_stable(lift_state(every_in_flight_inner_update_preserves_identity()));
    always_p_is_stable(lift_state(every_mirror_is_bound()));
    always_p_is_stable(lift_state(sync_scheduled_crs_are_bound(controller_id)));
    always_p_is_stable(lift_state(sync_triggering_crs_are_bound(controller_id)));
    always_p_is_stable(lift_state(janitor_deletes_are_sound(janitor_id)));
    always_p_is_stable(lift_state(builtin_deletes_never_target_mirrors()));
    always_p_is_stable(lift_state(sync_pending_requests_match_snapshots(controller_id)));
    stable_and_n!(
        always(lift_state(Cluster::every_in_flight_msg_has_unique_id())),
        always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())),
        always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))),
        always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())),
        always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())),
        always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>())),
        always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>())),
        always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id))),
        always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())),
        always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())),
        always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))),
        always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(controller_id))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))),
        always(lift_state(Cluster::there_is_the_controller_state(controller_id))),
        always(lift_state(Cluster::there_is_the_controller_state(janitor_id))),
        always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))),
        always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner))))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner))))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner))))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus))))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)))),
        always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id))),
        always(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external())),
        always(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests())),
        always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        always(lift_state(widget_sync_guarantee(controller_id))),
        always(lift_state(widget_janitor_guarantee(janitor_id))),
        always(lift_state(every_in_flight_inner_create_is_a_mirror_create())),
        always(lift_state(every_in_flight_inner_update_preserves_identity())),
        always(lift_state(every_mirror_is_bound())),
        always(lift_state(sync_scheduled_crs_are_bound(controller_id))),
        always(lift_state(sync_triggering_crs_are_bound(controller_id))),
        always(lift_state(janitor_deletes_are_sound(janitor_id))),
        always(lift_state(builtin_deletes_never_target_mirrors())),
        always(lift_state(sync_pending_requests_match_snapshots(controller_id)))
    );
}

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn sync_invariants_hold(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))),
        spec.entails(always(lift_state(janitor_deletes_are_sound(janitor_id)))),
    ensures spec.entails(sync_invariants(cluster, controller_id, janitor_id)),
{
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>(spec);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id(spec);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_ongoing_reconcile_has_lower_id_than_allocator(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(spec, controller_id);
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))) by {
        cluster.lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, controller_id, key);
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)));
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, janitor_id);
    cluster.lemma_always_there_is_no_request_msg_to_external_from_controller(spec, controller_id);
    cluster.lemma_always_cr_states_are_unmarshallable::<WidgetSyncReconciler, WidgetSyncReconcileState, OuterWidgetView, VoidEReqView, VoidERespView>(spec, controller_id);
    WidgetSyncReconcileState::marshal_preserves_integrity();
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, cluster.reconcile_model(controller_id).done);
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, cluster.reconcile_model(controller_id).error);
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)));
    cluster.lemma_always_every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(spec, controller_id);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    lemma_always_widget_sync_guarantee(spec, cluster, controller_id);
    lemma_sync_rely_implies_mirror_write_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_every_mirror_is_bound(spec, cluster);
    lemma_always_sync_crs_are_bound(spec, cluster, controller_id);
    lemma_always_builtin_deletes_never_target_mirrors(spec, cluster);
    lemma_always_sync_pending_requests_match_snapshots(spec, cluster, controller_id);
    entails_always_and_n!(
        spec,
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(controller_id)),
        tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::there_is_the_controller_state(janitor_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id)),
        tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init)))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner)))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner)))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner)))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus)))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error))),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id)),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(widget_sync_guarantee(controller_id)),
        lift_state(widget_janitor_guarantee(janitor_id)),
        lift_state(every_in_flight_inner_create_is_a_mirror_create()),
        lift_state(every_in_flight_inner_update_preserves_identity()),
        lift_state(every_mirror_is_bound()),
        lift_state(sync_scheduled_crs_are_bound(controller_id)),
        lift_state(sync_triggering_crs_are_bound(controller_id)),
        lift_state(janitor_deletes_are_sound(janitor_id)),
        lift_state(builtin_deletes_never_target_mirrors()),
        lift_state(sync_pending_requests_match_snapshots(controller_id))
    );
}

// The stable part of the sync reconciler's spec: fairness, rely, D3, R3 (the
// janitor's property, a liveness dependency) and the invariants.
pub open spec fn sync_stable_spec(cluster: Cluster, controller_id: int, janitor_id: int) -> TempPred<ClusterState> {
    sync_next_with_wf(cluster, controller_id)
    .and(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id))))
    .and(inner_releases_terminating_objects())
    .and(widget_mirrors_eventually_collected())
    .and(sync_invariants(cluster, controller_id, janitor_id))
}

pub proof fn sync_stable_spec_is_stable(cluster: Cluster, controller_id: int, janitor_id: int)
    ensures valid(stable(sync_stable_spec(cluster, controller_id, janitor_id))),
{
    sync_next_with_wf_is_stable(cluster, controller_id);
    always_p_is_stable(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)));
    assert(valid(stable(inner_releases_terminating_objects()))) by {
        let p = |i: (ObjectRef, Uid)| lift_state(inner_terminating_object(i.0, i.1));
        let q = |i: (ObjectRef, Uid)| lift_state(object_is_gone(i.0, i.1));
        tla_forall_a_p_a_leads_to_q_a_is_stable(p, q);
        tla_forall_p_tla_forall_q_equality(
            |i: (ObjectRef, Uid)| lift_state(inner_terminating_object(i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1))),
            |i: (ObjectRef, Uid)| p(i).leads_to(q(i))
        );
        temp_pred_equality(inner_releases_terminating_objects(), tla_forall(|i: (ObjectRef, Uid)| p(i).leads_to(q(i))));
    }
    assert(valid(stable(widget_mirrors_eventually_collected()))) by {
        let p = |i: (ObjectRef, Uid, Uid)| always(lift_state(parent_absent(i.0, i.1))).and(lift_state(mirror_object_is(i.0, i.1, i.2)));
        let q = |i: (ObjectRef, Uid, Uid)| lift_state(object_is_gone(i.0, i.2));
        tla_forall_a_p_a_leads_to_q_a_is_stable(p, q);
        tla_forall_p_tla_forall_q_equality(
            |i: (ObjectRef, Uid, Uid)| widget_mirror_eventually_collected_per_object(i.0, i.1, i.2),
            |i: (ObjectRef, Uid, Uid)| p(i).leads_to(q(i))
        );
        temp_pred_equality(widget_mirrors_eventually_collected(), tla_forall(|i: (ObjectRef, Uid, Uid)| p(i).leads_to(q(i))));
    }
    sync_invariants_is_stable(cluster, controller_id, janitor_id);
    stable_and_n!(
        sync_next_with_wf(cluster, controller_id),
        always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id))),
        inner_releases_terminating_objects(),
        widget_mirrors_eventually_collected(),
        sync_invariants(cluster, controller_id, janitor_id)
    );
}

// ---------------------------------------------------------------------------
// The object-level predicates of the proof.
// ---------------------------------------------------------------------------

pub open spec fn mirror_absent(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| !s.resources().contains_key(inner_key(outer))
}

// The mirror of `outer` is there, is ours, and is not terminating.
pub open spec fn mirror_is_ours(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[inner_key(outer)];
        &&& s.resources().contains_key(inner_key(outer))
        &&& InnerWidgetView::unmarshal(obj) is Ok
        &&& is_mirror_of(InnerWidgetView::unmarshal(obj)->Ok_0, outer)
        &&& obj.metadata.deletion_timestamp is None
    }
}

pub open spec fn mirror_settled(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| mirror_absent(outer)(s) || mirror_is_ours(outer)(s)
}

// The uid of the outer copy, as fixed by desired_state_is.
pub open spec fn outer_uid(outer: OuterWidgetView) -> Uid {
    outer.metadata.uid->0
}

// ---------------------------------------------------------------------------
// Nobody touches our mirror: neither its identity nor its lifecycle.
// ---------------------------------------------------------------------------

// The store facts a step of the API server keeps for our mirror.
#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_ours_after_api_server_step(
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, msg: Message, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s_prime),
        every_mirror_is_bound()(s),
        every_in_flight_inner_update_preserves_identity()(s),
        janitor_deletes_are_sound(janitor_id)(s),
        builtin_deletes_never_target_mirrors()(s),
        sync_rely_with_janitor(cluster, controller_id, janitor_id)(s),
        widget_sync_guarantee(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s),
        Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s),
        Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s),
        Cluster::desired_state_is(outer)(s),
        mirror_is_ours(outer)(s),
    ensures
        mirror_is_ours(outer)(s_prime),
        s_prime.resources()[inner_key(outer)].metadata.uid == s.resources()[inner_key(outer)].metadata.uid,
        s_prime.resources()[inner_key(outer)].metadata.generation == s.resources()[inner_key(outer)].metadata.generation
            || s_prime.resources()[inner_key(outer)].spec != s.resources()[inner_key(outer)].spec,
{
    let ikey = inner_key(outer);
    let key = outer.object_ref();
    let cr = s.resources()[ikey];
    let inner = InnerWidgetView::unmarshal(cr)->Ok_0;
    lemma_weakly_well_formed_implies_kinds_match(s);
    assert(Cluster::etcd_object_is_weakly_well_formed(ikey)(s));
    assert(cr.kind == InnerWidgetView::kind());
    assert(cr.object_ref() == ikey);
    assert(mirror_is_bound(ikey)(s));
    assert(cr.metadata.owner_references is None);
    assert(s.in_flight().contains(msg));
    assert(msg.content is APIRequest);
    lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
    // The parent uid on our mirror is the outer copy's, which exists.
    assert(parent_uid_annotation(inner) == parent_uid_of(outer));
    assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    assert(s.resources()[key].metadata.uid is Some);
    assert(outer.metadata.uid is Some);
    // Step 1: the object is still there, with its uid, and no deletion timestamp appeared.
    let kept = |s_prime: ClusterState| {
        &&& s_prime.resources().contains_key(ikey)
        &&& s_prime.resources()[ikey].metadata.uid == cr.metadata.uid
        &&& s_prime.resources()[ikey].metadata.deletion_timestamp is None
    };
    assert(kept(s_prime)) by {
        match msg.content->APIRequest_0 {
            APIRequest::DeleteRequest(req) => {
                if req.key == ikey {
                    match msg.src {
                        HostId::Controller(id, k) => {
                            assert(cluster.controller_models.contains_key(id));
                            if id == janitor_id {
                                assert(janitor_delete_is_sound(msg, s));
                                if req.preconditions->0.uid == cr.metadata.uid {
                                    assert(snapshot_is_mirror(cr));
                                    assert(parent_absent_forever(snapshot_parent(cr))(s));
                                    assert(snapshot_parent(cr) == int_to_string_view(outer_uid(outer)));
                                    assert(s.resources().contains_key(key) && s.resources()[key].metadata.uid is Some);
                                    assert(int_to_string_view(s.resources()[key].metadata.uid->0) != snapshot_parent(cr));
                                    assert(false);
                                }
                                assert(delete_request_admission_check(req, s.api_server) is Some);
                                assert(s_prime.api_server == s.api_server);
                            } else if id == controller_id {
                                assert(sync_request_is_guaranteed(msg, s));
                                assert(false);
                            } else {
                                assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                assert(widget_sync_rely(id)(s));
                                assert(req.key.kind != InnerWidgetView::kind());
                                assert(false);
                            }
                        },
                        HostId::BuiltinController => {
                            assert(builtin_delete_never_targets_a_mirror(msg, s));
                            assert(s.resources()[ikey].metadata.uid != req.preconditions->0.uid);
                            assert(delete_request_admission_check(req, s.api_server) is Some);
                            assert(s_prime.api_server == s.api_server);
                        },
                        HostId::PodMonkey => {
                            assert(req.key().kind == Kind::PodKind);
                            assert(false);
                        },
                        _ => {
                            assert(false);
                        },
                    }
                } else {
                    assert(s_prime.resources()[ikey] == cr);
                }
            },
            APIRequest::GetThenDeleteRequest(req) => {
                // A mirror has no owner references, so the transactional delete does nothing.
                assert(s_prime.resources()[ikey] == cr);
            },
            APIRequest::UpdateRequest(req) => {
                if req.key() == ikey {
                    if s_prime.api_server != s.api_server {
                        assert(s_prime.resources()[ikey].metadata.uid == cr.metadata.uid);
                        assert(s_prime.resources()[ikey].metadata.deletion_timestamp == cr.metadata.deletion_timestamp);
                    }
                } else {
                    assert(s_prime.resources()[ikey] == cr);
                }
            },
            APIRequest::GetThenUpdateRequest(_) => {
                lemma_get_then_update_keeps_unowned_objects(cluster.installed_types, msg, s.api_server, ikey);
            },
            APIRequest::GetThenUpdateStatusRequest(req) => {
                assert(s_prime.resources()[ikey] == cr);
            },
            APIRequest::PatchRequest(req) => {
                lemma_patch_request_keeps_identity_and_lifecycle(cluster.installed_types, req, s.api_server);
                if req.key() == ikey {
                    assert(keeps_identity_and_lifecycle(s.api_server, s_prime.api_server));
                } else {
                    assert(s_prime.resources()[ikey] == cr);
                }
            },
            APIRequest::PatchStatusRequest(req) => {
                lemma_patch_status_request_keeps_identity(cluster.installed_types, req, s.api_server);
                if req.key() != ikey {
                    assert(s_prime.resources()[ikey] == cr);
                }
            },
            APIRequest::UpdateStatusRequest(req) => {
                lemma_update_status_keeps_identity(cluster.installed_types, req, s.api_server);
                if req.key() != ikey {
                    assert(s_prime.resources()[ikey] == cr);
                }
            },
            APIRequest::CreateRequest(req) => {
                assert(s_prime.resources()[ikey] == cr);
            },
            _ => {
                assert(s_prime.api_server == s.api_server);
            },
        }
    }
    // Step 2: identity is kept.
    assert(snapshot_is_mirror(cr));
    assert(janitor_snapshot_is_sound(cr, ikey)(s));
    lemma_snapshot_soundness_preserved_by_api_server_step(cluster, s, s_prime, msg, cr, ikey);
    lemma_well_formed_inner_unmarshals(cluster, s_prime, ikey);
    let new_obj = s_prime.resources()[ikey];
    let new_inner = InnerWidgetView::unmarshal(new_obj)->Ok_0;
    assert(preserves_mirror_identity(cr.metadata, new_obj.metadata));
    assert(new_inner.metadata == new_obj.metadata);
    assert(is_mirror_of(new_inner, outer));
    // Step 3: the generation changes only with the spec (no deletion stamp landed).
    assert(new_obj.metadata.generation == cr.metadata.generation || new_obj.spec != cr.spec) by {
        match msg.content->APIRequest_0 {
            APIRequest::UpdateRequest(req) => {
                if req.key() == ikey && s_prime.api_server != s.api_server {
                    assert(new_obj.metadata.generation == next_generation(cr, req.obj.spec));
                }
            },
            APIRequest::PatchRequest(req) => {
                if req.key() == ikey && s_prime.api_server != s.api_server {
                    assert(new_obj.metadata.generation == next_generation(cr, req.spec));
                }
            },
            _ => {},
        }
    }
}

// Any step of the cluster keeps our mirror.
pub proof fn lemma_ours_after_step(
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        cluster.next()(s, s_prime),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s_prime),
        every_mirror_is_bound()(s),
        every_in_flight_inner_update_preserves_identity()(s),
        janitor_deletes_are_sound(janitor_id)(s),
        builtin_deletes_never_target_mirrors()(s),
        sync_rely_with_janitor(cluster, controller_id, janitor_id)(s),
        widget_sync_guarantee(controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s),
        Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s),
        Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s),
        Cluster::desired_state_is(outer)(s),
        mirror_is_ours(outer)(s),
    ensures
        mirror_is_ours(outer)(s_prime),
        s_prime.resources()[inner_key(outer)].metadata.uid == s.resources()[inner_key(outer)].metadata.uid,
        s_prime.resources()[inner_key(outer)].metadata.generation == s.resources()[inner_key(outer)].metadata.generation
            || s_prime.resources()[inner_key(outer)].spec != s.resources()[inner_key(outer)].spec,
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            lemma_ours_after_api_server_step(cluster, controller_id, janitor_id, s, s_prime, input->0, outer);
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}


// ---------------------------------------------------------------------------
// The facts of the stable spec, spelled out.
// ---------------------------------------------------------------------------

#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_sync_stable_spec_facts(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int)
    requires spec.entails(sync_stable_spec(cluster, controller_id, janitor_id)),
    ensures
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|input| cluster.disable_crash().weak_fairness(input))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(cluster.disable_req_drop().weak_fairness(())),
        spec.entails(cluster.disable_pod_monkey().weak_fairness(())),
        spec.entails(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))),
        spec.entails(inner_releases_terminating_objects()),
        spec.entails(widget_mirrors_eventually_collected()),
        spec.entails(sync_invariants(cluster, controller_id, janitor_id)),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id)))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error))))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
        spec.entails(always(lift_state(widget_sync_guarantee(controller_id)))),
        spec.entails(always(lift_state(widget_janitor_guarantee(janitor_id)))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity()))),
        spec.entails(always(lift_state(every_mirror_is_bound()))),
        spec.entails(always(lift_state(sync_triggering_crs_are_bound(controller_id)))),
        spec.entails(always(lift_state(janitor_deletes_are_sound(janitor_id)))),
        spec.entails(always(lift_state(builtin_deletes_never_target_mirrors()))),
        spec.entails(always(lift_state(sync_pending_requests_match_snapshots(controller_id)))),
{
    let stable_spec = sync_stable_spec(cluster, controller_id, janitor_id);
    let wf = sync_next_with_wf(cluster, controller_id);
    let inv = sync_invariants(cluster, controller_id, janitor_id);
    entails_and_split(spec, wf.and(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))).and(inner_releases_terminating_objects()).and(widget_mirrors_eventually_collected()), inv);
    entails_and_split(spec, wf.and(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))).and(inner_releases_terminating_objects()), widget_mirrors_eventually_collected());
    entails_and_split(spec, wf.and(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))), inner_releases_terminating_objects());
    entails_and_split(spec, wf, always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id))));
    assert(wf.entails(always(lift_action(cluster.next()))));
    entails_trans(spec, wf, always(lift_action(cluster.next())));
    assert(wf.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))));
    entails_trans(spec, wf, tla_forall(|i| cluster.api_server_next().weak_fairness(i)));
    assert(wf.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))));
    entails_trans(spec, wf, tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))));
    assert(wf.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))));
    entails_trans(spec, wf, tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i))));
    assert(wf.entails(tla_forall(|input| cluster.disable_crash().weak_fairness(input))));
    entails_trans(spec, wf, tla_forall(|input| cluster.disable_crash().weak_fairness(input)));
    assert(wf.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))));
    entails_trans(spec, wf, tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i))));
    assert(wf.entails(cluster.disable_req_drop().weak_fairness(())));
    entails_trans(spec, wf, cluster.disable_req_drop().weak_fairness(()));
    assert(wf.entails(cluster.disable_pod_monkey().weak_fairness(())));
    entails_trans(spec, wf, cluster.disable_pod_monkey().weak_fairness(()));
    assert(inv.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))));
    entails_trans(spec, inv, always(lift_state(Cluster::every_in_flight_msg_has_unique_id())));
    assert(inv.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))));
    entails_trans(spec, inv, always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())));
    assert(inv.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))));
    entails_trans(spec, inv, always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())));
    assert(inv.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()))));
    entails_trans(spec, inv, always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>())));
    assert(inv.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>()))));
    entails_trans(spec, inv, always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>())));
    assert(inv.entails(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))));
    entails_trans(spec, inv, always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())));
    assert(inv.entails(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id))));
    assert(inv.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))));
    entails_trans(spec, inv, always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())));
    assert(inv.entails(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()))));
    entails_trans(spec, inv, always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())));
    assert(inv.entails(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))));
    assert(inv.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))));
    assert(inv.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(controller_id))));
    assert(inv.entails(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<OuterWidgetView>(controller_id))));
    assert(inv.entails(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))));
    assert(inv.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::there_is_the_controller_state(controller_id))));
    assert(inv.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))));
    assert(inv.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetSyncReconcileState, OuterWidgetView>(controller_id))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init)))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner)))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner))))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner)))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner))))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner)))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner))))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus)))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus))))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)))));
    assert(inv.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()))));
    entails_trans(spec, inv, always(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external())));
    assert(inv.entails(always(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()))));
    entails_trans(spec, inv, always(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests())));
    assert(inv.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))));
    entails_trans(spec, inv, always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())));
    assert(inv.entails(always(lift_state(widget_sync_guarantee(controller_id)))));
    entails_trans(spec, inv, always(lift_state(widget_sync_guarantee(controller_id))));
    assert(inv.entails(always(lift_state(widget_janitor_guarantee(janitor_id)))));
    entails_trans(spec, inv, always(lift_state(widget_janitor_guarantee(janitor_id))));
    assert(inv.entails(always(lift_state(every_in_flight_inner_update_preserves_identity()))));
    entails_trans(spec, inv, always(lift_state(every_in_flight_inner_update_preserves_identity())));
    assert(inv.entails(always(lift_state(every_mirror_is_bound()))));
    entails_trans(spec, inv, always(lift_state(every_mirror_is_bound())));
    assert(inv.entails(always(lift_state(sync_triggering_crs_are_bound(controller_id)))));
    entails_trans(spec, inv, always(lift_state(sync_triggering_crs_are_bound(controller_id))));
    assert(inv.entails(always(lift_state(janitor_deletes_are_sound(janitor_id)))));
    entails_trans(spec, inv, always(lift_state(janitor_deletes_are_sound(janitor_id))));
    assert(inv.entails(always(lift_state(builtin_deletes_never_target_mirrors()))));
    entails_trans(spec, inv, always(lift_state(builtin_deletes_never_target_mirrors())));
    assert(inv.entails(always(lift_state(sync_pending_requests_match_snapshots(controller_id)))));
    entails_trans(spec, inv, always(lift_state(sync_pending_requests_match_snapshots(controller_id))));
}

// ---------------------------------------------------------------------------
// The layers of the spec: premise, phase I, phase II, settled mirror.
// ---------------------------------------------------------------------------

pub open spec fn sync_spec_with_desired(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView) -> TempPred<ClusterState> {
    sync_stable_spec(cluster, controller_id, janitor_id).and(always(lift_state(outer_stable(outer))))
}

pub proof fn sync_spec_with_desired_is_stable(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView)
    ensures valid(stable(sync_spec_with_desired(cluster, controller_id, janitor_id, outer))),
{
    sync_stable_spec_is_stable(cluster, controller_id, janitor_id);
    always_p_is_stable(lift_state(outer_stable(outer)));
    stable_and_n!(sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_stable(outer))));
}

pub open spec fn sync_spec_with_phase_i(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView) -> TempPred<ClusterState> {
    sync_spec_with_desired(cluster, controller_id, janitor_id, outer).and(always(lift_state(phase_i(controller_id))))
}

pub proof fn sync_spec_with_phase_i_is_stable(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView)
    ensures valid(stable(sync_spec_with_phase_i(cluster, controller_id, janitor_id, outer))),
{
    sync_spec_with_desired_is_stable(cluster, controller_id, janitor_id, outer);
    always_p_is_stable(lift_state(phase_i(controller_id)));
    stable_and_n!(sync_spec_with_desired(cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
}

// Phase II, per outer copy: the snapshots the sync reconciler works from carry the
// outer copy's spec and uid; the only request of the sync reconciler for the key
// in flight is the pending one; requests and responses are consistent.
pub open spec fn sync_phase_ii(controller_id: int, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::the_object_in_schedule_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer.object_ref())(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())(s)
    }
}

pub open spec fn sync_spec_with_phase_ii(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView) -> TempPred<ClusterState> {
    sync_spec_with_phase_i(cluster, controller_id, janitor_id, outer).and(always(lift_state(sync_phase_ii(controller_id, outer))))
}

pub proof fn sync_spec_with_phase_ii_is_stable(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView)
    ensures valid(stable(sync_spec_with_phase_ii(cluster, controller_id, janitor_id, outer))),
{
    sync_spec_with_phase_i_is_stable(cluster, controller_id, janitor_id, outer);
    always_p_is_stable(lift_state(sync_phase_ii(controller_id, outer)));
    stable_and_n!(sync_spec_with_phase_i(cluster, controller_id, janitor_id, outer), always(lift_state(sync_phase_ii(controller_id, outer))));
}

pub open spec fn sync_spec_with_settled(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView) -> TempPred<ClusterState> {
    sync_spec_with_phase_ii(cluster, controller_id, janitor_id, outer).and(always(lift_state(mirror_settled(outer))))
}

// Unfolding the layers.
pub proof fn lemma_unfold_sync_spec_with_phase_ii(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView)
    requires spec.entails(sync_spec_with_phase_ii(cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(sync_stable_spec(cluster, controller_id, janitor_id)),
        spec.entails(always(lift_state(outer_stable(outer)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(outer)))),
        spec.entails(always(lift_state(mirror_spec_undisturbed(outer)))),
        spec.entails(always(lift_state(phase_i(controller_id)))),
        spec.entails(always(lift_state(sync_phase_ii(controller_id, outer)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)))),
        spec.entails(always(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)))),
        spec.entails(always(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer.object_ref())))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())))),
{
    entails_and_split(spec, sync_spec_with_phase_i(cluster, controller_id, janitor_id, outer), always(lift_state(sync_phase_ii(controller_id, outer))));
    entails_and_split(spec, sync_spec_with_desired(cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_stable(outer))));
    always_weaken(spec, lift_state(outer_stable(outer)), lift_state(Cluster::desired_state_is(outer)));
    always_weaken(spec, lift_state(outer_stable(outer)), lift_state(mirror_spec_undisturbed(outer)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_weaken(spec, lift_state(sync_phase_ii(controller_id, outer)), lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)));
    always_weaken(spec, lift_state(sync_phase_ii(controller_id, outer)), lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)));
    always_weaken(spec, lift_state(sync_phase_ii(controller_id, outer)), lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer.object_ref())));
    always_weaken(spec, lift_state(sync_phase_ii(controller_id, outer)), lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())));
}

// ---------------------------------------------------------------------------
// Phase II holds eventually forever.
// ---------------------------------------------------------------------------

// The rest of phase II once the scheduled snapshot is known to carry the outer
// copy's spec and uid.
pub open spec fn sync_phase_ii_rest(controller_id: int, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer.object_ref())(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())(s)
    }
}

// Termination of the sync reconciler's reconciles under phase I.
pub proof fn lemma_sync_terminates(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, key: ObjectRef)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_stable_spec(cluster, controller_id, janitor_id)),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
    ensures
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key))))),
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !(s.ongoing_reconciles(controller_id).contains_key(key)))))),
        spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)))),
{
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    terminate::sync_reconcile_eventually_terminates(spec, cluster, controller_id);
    let idle_of = |key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)));
    spec_entails_tla_forall_apply(spec, idle_of, key);
    let idle_of_alt = |key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !(s.ongoing_reconciles(controller_id).contains_key(key))));
    assert forall |key: ObjectRef| #[trigger] idle_of(key) == idle_of_alt(key) by {
        temp_pred_equality(idle_of(key), idle_of_alt(key));
    }
    tla_forall_p_tla_forall_q_equality(idle_of, idle_of_alt);
}

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_true_leads_to_always_sync_phase_ii(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_i(cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(sync_phase_ii(controller_id, outer))))),
{
    let key = outer.object_ref();
    let spec_i = sync_spec_with_phase_i(cluster, controller_id, janitor_id, outer);
    let e1a = lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer));
    let xor = lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key));
    let rest = lift_state(sync_phase_ii_rest(controller_id, outer));
    OuterWidgetView::object_ref_is_well_formed();

    // Under spec_i: the scheduled snapshot eventually always carries the outer spec and uid.
    assert(spec_i.entails(spec_i));
    entails_and_split(spec_i, sync_spec_with_desired(cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec_i, sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_stable(outer))));
    always_weaken(spec_i, lift_state(outer_stable(outer)), lift_state(Cluster::desired_state_is(outer)));
    lemma_sync_stable_spec_facts(spec_i, cluster, controller_id, janitor_id);
    always_weaken(spec_i, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec_i, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec_i, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    cluster.lemma_true_leads_to_always_the_object_in_schedule_has_spec_and_uid_as::<OuterWidgetView>(spec_i, controller_id, outer);

    // Under spec_a = spec_i /\ []e1a: the rest, in two more layers (xor, then the message fact).
    let spec_a = spec_i.and(always(e1a));
    assert(spec_a.entails(spec_a));
    entails_and_split(spec_a, spec_i, always(e1a));
    entails_and_split(spec_a, sync_spec_with_desired(cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec_a, sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_stable(outer))));
    always_weaken(spec_a, lift_state(outer_stable(outer)), lift_state(Cluster::desired_state_is(outer)));
    lemma_sync_stable_spec_facts(spec_a, cluster, controller_id, janitor_id);
    always_weaken(spec_a, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec_a, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec_a, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_tla_forall_apply(spec_a, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), key);
    always_tla_forall_apply(spec_a, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)), key);
    always_tla_forall_apply(spec_a, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)), key);
    lemma_sync_terminates(spec_a, cluster, controller_id, janitor_id, key);
    cluster.lemma_true_leads_to_always_the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(spec_a, controller_id, outer);
    cluster.lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(spec_a, controller_id, key);

    // Under spec_b = spec_a /\ []xor: the message fact.
    let spec_b = spec_a.and(always(xor));
    assert(spec_b.entails(spec_b));
    entails_and_split(spec_b, spec_a, always(xor));
    entails_and_split(spec_b, spec_i, always(e1a));
    entails_and_split(spec_b, sync_spec_with_desired(cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec_b, sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_stable(outer))));
    always_weaken(spec_b, lift_state(outer_stable(outer)), lift_state(Cluster::desired_state_is(outer)));
    lemma_sync_stable_spec_facts(spec_b, cluster, controller_id, janitor_id);
    always_weaken(spec_b, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec_b, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec_b, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_tla_forall_apply(spec_b, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), key);
    always_tla_forall_apply(spec_b, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)), key);
    always_tla_forall_apply(spec_b, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)), key);
    cluster.lemma_true_leads_to_always_every_msg_from_key_is_pending_req_msg_of(spec_b, controller_id, key);
    let msg_fact = lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, key));
    // Back to spec_a.
    sync_spec_with_phase_i_is_stable(cluster, controller_id, janitor_id, outer);
    always_p_is_stable(e1a);
    stable_and_n!(spec_i, always(e1a));
    unpack_conditions_from_spec(spec_a, always(xor), true_pred(), always(msg_fact));
    temp_pred_equality(true_pred().and(always(xor)), always(xor));
    leads_to_trans(spec_a, true_pred(), always(xor), always(msg_fact));
    let e1b = lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer));
    leads_to_always_and(spec_a, true_pred(), e1b, msg_fact);
    leads_to_always_and(spec_a, true_pred(), e1b.and(msg_fact), xor);
    temp_pred_equality(rest, e1b.and(msg_fact).and(xor));
    // Back to spec_i.
    unpack_conditions_from_spec(spec_i, always(e1a), true_pred(), always(rest));
    temp_pred_equality(true_pred().and(always(e1a)), always(e1a));
    leads_to_trans(spec_i, true_pred(), always(e1a), always(rest));
    leads_to_always_and(spec_i, true_pred(), e1a, rest);
    temp_pred_equality(lift_state(sync_phase_ii(controller_id, outer)), e1a.and(rest));
    entails_trans(spec, spec_i, true_pred().leads_to(always(lift_state(sync_phase_ii(controller_id, outer)))));
}

// ---------------------------------------------------------------------------
// One step of the cluster at the mirror key, under phase II.
// ---------------------------------------------------------------------------

// The facts about the current state the step lemmas use.
pub open spec fn sync_step_ctx(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s)
        &&& every_mirror_is_bound()(s)
        &&& every_in_flight_inner_update_preserves_identity()(s)
        &&& janitor_deletes_are_sound(janitor_id)(s)
        &&& builtin_deletes_never_target_mirrors()(s)
        &&& sync_rely_with_janitor(cluster, controller_id, janitor_id)(s)
        &&& widget_sync_guarantee(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
        &&& Cluster::desired_state_is(outer)(s)
        &&& mirror_spec_undisturbed(outer)(s)
        &&& Cluster::the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)(s)
        &&& Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer.object_ref())(s)
        &&& sync_pending_requests_match_snapshots(controller_id)(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer.object_ref(), at_sync_step_closure(WidgetSyncStepView::Init))(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer.object_ref(), cluster.reconcile_model(controller_id).done)(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(controller_id, outer.object_ref(), cluster.reconcile_model(controller_id).error)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    }
}

// The action the step lemmas assume.
pub open spec fn sync_step_next(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& sync_step_ctx(cluster, controller_id, janitor_id, outer)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s_prime)
    }
}

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_always_sync_step_next(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_action(sync_step_next(cluster, controller_id, janitor_id, outer)))),
{
    let key = outer.object_ref();
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))), key);
    always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)), key);
    always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)), key);
    entails_always_and_n!(
        spec,
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()),
        lift_state(every_mirror_is_bound()),
        lift_state(every_in_flight_inner_update_preserves_identity()),
        lift_state(janitor_deletes_are_sound(janitor_id)),
        lift_state(builtin_deletes_never_target_mirrors()),
        lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)),
        lift_state(widget_sync_guarantee(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(Cluster::desired_state_is(outer)),
        lift_state(mirror_spec_undisturbed(outer)),
        lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)),
        lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, key)),
        lift_state(sync_pending_requests_match_snapshots(controller_id)),
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))),
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)),
        lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    temp_pred_equality(
        lift_state(sync_step_ctx(cluster, controller_id, janitor_id, outer)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
            .and(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()))
            .and(lift_state(every_mirror_is_bound()))
            .and(lift_state(every_in_flight_inner_update_preserves_identity()))
            .and(lift_state(janitor_deletes_are_sound(janitor_id)))
            .and(lift_state(builtin_deletes_never_target_mirrors()))
            .and(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))
            .and(lift_state(widget_sync_guarantee(controller_id)))
            .and(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))
            .and(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()))
            .and(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()))
            .and(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))
            .and(lift_state(Cluster::desired_state_is(outer)))
            .and(lift_state(mirror_spec_undisturbed(outer)))
            .and(lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)))
            .and(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, key)))
            .and(lift_state(sync_pending_requests_match_snapshots(controller_id)))
            .and(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))))
            .and(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)))
            .and(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)))
            .and(lift_state(Cluster::there_is_the_controller_state(controller_id)))
    );
    always_to_always_later(spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_to_always_later(spec, lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()));
    combine_spec_entails_always_n!(
        spec, lift_action(sync_step_next(cluster, controller_id, janitor_id, outer)),
        lift_action(cluster.next()),
        lift_state(sync_step_ctx(cluster, controller_id, janitor_id, outer)),
        later(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        later(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()))
    );
}

// The mirror key after one step: our mirror stays ours; an absent mirror stays
// absent or becomes ours (only the sync reconciler's current reconcile creates
// one); an existing object is never replaced by another.
#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_mirror_key_after_step(
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        sync_step_next(cluster, controller_id, janitor_id, outer)(s, s_prime),
    ensures
        mirror_is_ours(outer)(s) ==> mirror_is_ours(outer)(s_prime),
        mirror_absent(outer)(s) ==> mirror_absent(outer)(s_prime) || mirror_is_ours(outer)(s_prime),
        s.resources().contains_key(inner_key(outer)) && s_prime.resources().contains_key(inner_key(outer))
            ==> s_prime.resources()[inner_key(outer)].metadata.uid == s.resources()[inner_key(outer)].metadata.uid,
{
    let ikey = inner_key(outer);
    let key = outer.object_ref();
    OuterWidgetView::marshal_preserves_integrity();
    InnerWidgetView::marshal_preserves_integrity();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    if mirror_is_ours(outer)(s) {
        lemma_ours_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
    }
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            assert(msg.content is APIRequest);
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => {
                    if s.resources().contains_key(ikey) {
                        // A create never replaces an existing object.
                        assert(s_prime.resources()[ikey] == s.resources()[ikey]);
                    } else if s_prime.resources().contains_key(ikey) {
                        // The mirror was just created: by the sync reconciler's reconcile of the outer copy.
                        let created = s_prime.resources()[ikey];
                        assert(create_request_admission_check(cluster.installed_types, req, s.api_server) is None);
                        assert(created.kind == req.obj.kind);
                        assert(req.obj.kind == InnerWidgetView::kind());
                        assert(req.obj.metadata.name is Some);
                        assert(created.metadata.name == req.obj.metadata.name);
                        assert(created.metadata.namespace == Some(req.namespace));
                        assert(created.metadata.labels == req.obj.metadata.labels);
                        assert(created.metadata.annotations == req.obj.metadata.annotations);
                        assert(created.metadata.deletion_timestamp is None);
                        assert(req.namespace == key.namespace);
                        assert(req.obj.metadata.name->0 == key.name);
                        match msg.src {
                            HostId::Controller(id, k) => {
                                assert(cluster.controller_models.contains_key(id));
                                if id == controller_id {
                                    assert(sync_request_is_guaranteed(msg, s));
                                    assert(mirror_create_req(req, k)(s));
                                    let outer_k = choose |outer_k: OuterWidgetView| {
                                        &&& outer_k.object_ref() == k
                                        &&& outer_k.metadata.uid is Some
                                        &&& req.namespace == k.namespace
                                        &&& req.obj == #[trigger] make_inner(outer_k).marshal()
                                        &&& parent_uid_is_bound_to_key(outer_k.metadata.uid->0, k)(s)
                                    };
                                    assert(k.kind == OuterWidgetView::kind());
                                    assert(k.namespace == key.namespace);
                                    assert(k.name == key.name);
                                    assert(k == key);
                                    // It is the pending request of the current reconcile of the outer copy.
                                    assert(s.ongoing_reconciles(controller_id).contains_key(key));
                                    let reconcile = s.ongoing_reconciles(controller_id)[key];
                                    assert(reconcile.pending_req_msg == Some(msg));
                                    assert(sync_pending_request_is(controller_id, key, reconcile));
                                    let cr_outer = OuterWidgetView::unmarshal(reconcile.triggering_cr)->Ok_0;
                                    let step = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
                                    assert(!(step is Init));
                                    assert(!(step is Done));
                                    assert(!(step is Error));
                                    assert(step is AfterCreateInner);
                                    assert(req == CreateRequest { namespace: cr_outer.metadata.namespace->0, obj: make_inner(cr_outer).marshal() });
                                    // The snapshot has the outer copy's uid.
                                    assert(reconcile.triggering_cr.metadata.uid == outer.metadata.uid);
                                    assert(cr_outer.metadata == reconcile.triggering_cr.metadata);
                                    assert(parent_uid_of(cr_outer) == parent_uid_of(outer));
                                    assert(req.obj.metadata == make_inner(cr_outer).metadata);
                                    lemma_well_formed_inner_unmarshals(cluster, s_prime, ikey);
                                    let created_inner = InnerWidgetView::unmarshal(created)->Ok_0;
                                    assert(created_inner.metadata == created.metadata);
                                    assert(created.metadata.labels == make_inner(cr_outer).metadata.labels);
                                    assert(created.metadata.annotations == make_inner(cr_outer).metadata.annotations);
                                    assert(is_mirror_of(created_inner, outer));
                                    assert(mirror_is_ours(outer)(s_prime));
                                } else if id == janitor_id {
                                    assert(janitor_request_is_guaranteed(msg));
                                    assert(false);
                                } else {
                                    assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                    assert(widget_sync_rely(id)(s));
                                    assert(req.obj.kind != InnerWidgetView::kind());
                                    assert(false);
                                }
                            },
                            HostId::BuiltinController => { assert(false); },
                            HostId::PodMonkey => {
                                assert(req.key().kind == Kind::PodKind);
                                assert(false);
                            },
                            _ => { assert(false); },
                        }
                    }
                },
                _ => {
                    // No other request creates an object at a key.
                    if !s.resources().contains_key(ikey) {
                        assert(!s_prime.resources().contains_key(ikey));
                    }
                    if s.resources().contains_key(ikey) && s_prime.resources().contains_key(ikey) {
                        lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
                        assert(s_prime.resources()[ikey].metadata.uid == s.resources()[ikey].metadata.uid);
                    }
                },
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// ---------------------------------------------------------------------------
// The mirror key is eventually and forever settled: absent or ours.
// ---------------------------------------------------------------------------

pub open spec fn mirror_has_uid(outer: OuterWidgetView, m: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resources().contains_key(inner_key(outer))
        &&& s.resources()[inner_key(outer)].metadata.uid == Some(m)
    }
}

// The object with uid `m` at the mirror key, if it is not ours, is eventually gone,
// and nothing but our mirror can take its place.
#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_mirror_with_uid_leads_to_settled(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView, m: Uid
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(lift_state(mirror_has_uid(outer, m)).leads_to(lift_state(mirror_settled(outer)))),
{
    let ikey = inner_key(outer);
    let key = outer.object_ref();
    let u = outer_uid(outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(spec, cluster, controller_id, janitor_id, outer);
    let next = sync_step_next(cluster, controller_id, janitor_id, outer);
    let has_m = mirror_has_uid(outer, m);
    let ours = mirror_is_ours(outer);
    let settled = mirror_settled(outer);
    let inv = |s: ClusterState| {
        &&& every_mirror_is_bound()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::desired_state_is(outer)(s)
    };
    entails_always_and_n!(
        spec,
        lift_state(every_mirror_is_bound()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::desired_state_is(outer))
    );
    temp_pred_equality(
        lift_state(inv),
        lift_state(every_mirror_is_bound()).and(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())).and(lift_state(Cluster::desired_state_is(outer)))
    );
    let z = |s: ClusterState| has_m(s) && !ours(s);
    let has_m_ours = |s: ClusterState| has_m(s) && ours(s);
    let terminating = |s: ClusterState| z(s) && s.resources()[ikey].metadata.deletion_timestamp is Some;
    let stale = |s: ClusterState| z(s) && s.resources()[ikey].metadata.deletion_timestamp is None;
    let gone_m = lift_state(object_is_gone(ikey, m));

    // A terminating object is released by the inner side (D3).
    entails_implies_leads_to(spec, lift_state(terminating), lift_state(inner_terminating_object(ikey, m)));
    spec_entails_tla_forall_apply(
        spec,
        |i: (ObjectRef, Uid)| lift_state(inner_terminating_object(i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1))),
        (ikey, m)
    );
    leads_to_trans(spec, lift_state(terminating), lift_state(inner_terminating_object(ikey, m)), gone_m);

    // A stale mirror (another parent) is collected by the janitor (R3).
    let stale_p = |p: Uid| lift_state(|s: ClusterState| {
        &&& stale(s)
        &&& parent_uid_annotation(InnerWidgetView::unmarshal(s.resources()[ikey])->Ok_0) == int_to_string_view(p)
    });
    assert forall |p: Uid| spec.entails(#[trigger] stale_p(p).leads_to(gone_m)) by {
        if p == u {
            // Then it would be ours.
            assert forall |ex: Execution<ClusterState>| !(#[trigger] stale_p(p).and(lift_state(inv)).satisfied_by(ex)) by {
                if stale_p(p).satisfied_by(ex) && lift_state(inv).satisfied_by(ex) {
                    let s = ex.head();
                    assert(mirror_is_bound(ikey)(s));
                    let inner = InnerWidgetView::unmarshal(s.resources()[ikey])->Ok_0;
                    assert(has_mirror_identity(inner));
                    assert(is_mirror_of(inner, outer));
                    assert(ours(s));
                    assert(false);
                }
            }
            temp_pred_equality(stale_p(p).and(lift_state(inv)), false_pred());
            vacuous_leads_to(spec, stale_p(p), gone_m, lift_state(inv));
        } else {
            let p_absent = lift_state(parent_absent(ikey, p));
            let m_pm = lift_state(mirror_object_is(ikey, p, m));
            // The parent p is absent for good: the outer copy has uid u.
            assert(outer_key_of(ikey) == key);
            always_weaken(spec, lift_state(Cluster::desired_state_is(outer)), p_absent);
            spec_entails_tla_forall_apply(
                spec,
                |i: (ObjectRef, Uid, Uid)| widget_mirror_eventually_collected_per_object(i.0, i.1, i.2),
                (ikey, p, m)
            );
            always_double_equality(p_absent);
            temp_pred_equality(always(p_absent).and(m_pm), m_pm.and(always(p_absent)));
            leads_to_by_borrowing_inv(spec, m_pm, gone_m, always(p_absent));
            // stale_p(p) /\ inv ==> mirror_object_is(ikey, p, m)
            let stale_p_inv = |s: ClusterState| {
                &&& stale(s)
                &&& parent_uid_annotation(InnerWidgetView::unmarshal(s.resources()[ikey])->Ok_0) == int_to_string_view(p)
                &&& inv(s)
            };
            assert forall |s: ClusterState| #[trigger] stale_p_inv(s) implies mirror_object_is(ikey, p, m)(s) by {
                assert(mirror_is_bound(ikey)(s));
            }
            entails_implies_leads_to(spec, lift_state(stale_p_inv), m_pm);
            leads_to_trans(spec, lift_state(stale_p_inv), m_pm, gone_m);
            temp_pred_equality(stale_p(p).and(lift_state(inv)), lift_state(stale_p_inv));
            leads_to_by_borrowing_inv(spec, stale_p(p), gone_m, lift_state(inv));
        }
    }
    leads_to_exists_intro(spec, stale_p, gone_m);
    let stale_inv = |s: ClusterState| stale(s) && inv(s);
    assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(stale_inv).satisfied_by(ex) implies tla_exists(stale_p).satisfied_by(ex) by {
        let s = ex.head();
        assert(mirror_is_bound(ikey)(s));
        let inner = InnerWidgetView::unmarshal(s.resources()[ikey])->Ok_0;
        let p = choose |p: Uid| parent_uid_annotation(inner) == #[trigger] int_to_string_view(p);
        assert(stale_p(p).satisfied_by(ex));
    }
    entails_implies_leads_to(spec, lift_state(stale_inv), tla_exists(stale_p));
    leads_to_trans(spec, lift_state(stale_inv), tla_exists(stale_p), gone_m);
    temp_pred_equality(lift_state(stale).and(lift_state(inv)), lift_state(stale_inv));
    leads_to_by_borrowing_inv(spec, lift_state(stale), gone_m, lift_state(inv));

    // z ~> gone
    or_leads_to(spec, lift_state(terminating), lift_state(stale), gone_m);
    temp_pred_equality(lift_state(z), lift_state(terminating).or(lift_state(stale)));

    // While the object with uid m is being removed, nothing but our mirror takes its
    // place: j holds from now on.
    let j = |s: ClusterState| mirror_absent(outer)(s) || has_m(s) || ours(s);
    assert forall |s, s_prime: ClusterState| #[trigger] next(s, s_prime) && j(s) implies j(s_prime) by {
        lemma_mirror_key_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
    }
    next_to_stable(next, j);
    entails_preserved_by_always(always(lift_action(next)), stable(lift_state(j)));
    always_double_equality(lift_action(next));
    entails_trans(spec, always(lift_action(next)), always(stable(lift_state(j))));
    let zj = lift_state(z).and(always(lift_state(j)));
    assert(stable(lift_state(j)).entails(lift_state(z).implies(zj)));
    entails_preserved_by_always(stable(lift_state(j)), lift_state(z).implies(zj));
    entails_trans(spec, always(stable(lift_state(j))), always(lift_state(z).implies(zj)));
    always_implies_to_leads_to(spec, lift_state(z), zj);
    leads_to_with_always(spec, lift_state(z), gone_m, lift_state(j));
    always_entails_current(lift_state(j));
    assert forall |ex: Execution<ClusterState>| #[trigger] gone_m.and(always(lift_state(j))).satisfied_by(ex)
    implies lift_state(settled).satisfied_by(ex) by {
        assert(always(lift_state(j)).satisfied_by(ex));
        assert(always(lift_state(j)).implies(lift_state(j)).satisfied_by(ex));
        assert(lift_state(j).satisfied_by(ex));
    }
    entails_implies_leads_to(spec, gone_m.and(always(lift_state(j))), lift_state(settled));
    leads_to_trans_n!(spec, lift_state(z), zj, gone_m.and(always(lift_state(j))), lift_state(settled));

    // has_m ~> settled
    entails_implies_leads_to(spec, lift_state(has_m_ours), lift_state(settled));
    or_leads_to(spec, lift_state(z), lift_state(has_m_ours), lift_state(settled));
    temp_pred_equality(lift_state(has_m), lift_state(z).or(lift_state(has_m_ours)));
}

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_true_leads_to_always_mirror_settled(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(mirror_settled(outer))))),
{
    let ikey = inner_key(outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(spec, cluster, controller_id, janitor_id, outer);
    let next = sync_step_next(cluster, controller_id, janitor_id, outer);
    let settled = lift_state(mirror_settled(outer));
    let absent = lift_state(mirror_absent(outer));
    let has = |m: Uid| lift_state(mirror_has_uid(outer, m));
    assert forall |m: Uid| spec.entails(#[trigger] has(m).leads_to(settled)) by {
        lemma_mirror_with_uid_leads_to_settled(spec, cluster, controller_id, janitor_id, outer, m);
    }
    leads_to_exists_intro(spec, has, settled);
    entails_implies_leads_to(spec, absent, settled);
    or_leads_to(spec, absent, tla_exists(has), settled);
    // Every state is absent or has some uid at the mirror key (uids are set).
    let wf = lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed());
    assert forall |ex: Execution<ClusterState>| #[trigger] wf.satisfied_by(ex) implies absent.or(tla_exists(has)).satisfied_by(ex) by {
        let s = ex.head();
        if s.resources().contains_key(ikey) {
            assert(Cluster::etcd_object_is_weakly_well_formed(ikey)(s));
            let m = s.resources()[ikey].metadata.uid->0;
            assert(has(m).satisfied_by(ex));
        }
    }
    entails_implies_leads_to(spec, wf, absent.or(tla_exists(has)));
    leads_to_trans(spec, wf, absent.or(tla_exists(has)), settled);
    temp_pred_equality(true_pred().and(wf), wf);
    leads_to_by_borrowing_inv(spec, true_pred(), settled, wf);
    // Stability.
    assert forall |s, s_prime: ClusterState| mirror_settled(outer)(s) && #[trigger] next(s, s_prime) implies mirror_settled(outer)(s_prime) by {
        lemma_mirror_key_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
    }
    leads_to_stable(spec, lift_action(next), true_pred(), settled);
}


// ---------------------------------------------------------------------------
// Unfolding the last layer.
// ---------------------------------------------------------------------------

pub proof fn lemma_unfold_sync_spec_with_settled(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView)
    requires spec.entails(sync_spec_with_settled(cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(sync_spec_with_phase_ii(cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(mirror_settled(outer)))),
{
    entails_and_split(spec, sync_spec_with_phase_ii(cluster, controller_id, janitor_id, outer), always(lift_state(mirror_settled(outer))));
}

// ---------------------------------------------------------------------------
// spec_synced is stable once reached.
// ---------------------------------------------------------------------------

pub proof fn lemma_spec_synced_after_step(
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        sync_step_next(cluster, controller_id, janitor_id, outer)(s, s_prime),
        spec_synced(outer)(s),
    ensures spec_synced(outer)(s_prime),
{
    let ikey = inner_key(outer);
    InnerWidgetView::marshal_spec_preserves_integrity();
    assert(mirror_is_ours(outer)(s));
    lemma_ours_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            let old_obj = s.resources()[ikey];
            let new_obj = s_prime.resources()[ikey];
            lemma_weakly_well_formed_implies_kinds_match(s);
            match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => {
                    if req.key() == ikey && s_prime.api_server != s.api_server {
                        assert(new_obj.spec == req.obj.spec);
                        assert(writes_outer_spec(req.obj.spec, outer));
                    } else {
                        assert(new_obj.spec == old_obj.spec);
                    }
                },
                APIRequest::PatchRequest(req) => {
                    if req.key() == ikey && s_prime.api_server != s.api_server {
                        assert(new_obj.spec == req.spec);
                        assert(writes_outer_spec(req.spec, outer));
                    } else {
                        assert(new_obj.spec == old_obj.spec);
                    }
                },
                APIRequest::GetThenUpdateRequest(_) => {
                    lemma_get_then_update_keeps_unowned_objects(cluster.installed_types, msg, s.api_server, ikey);
                    assert(new_obj.spec == old_obj.spec);
                },
                APIRequest::UpdateStatusRequest(req) => {
                    lemma_update_status_keeps_identity(cluster.installed_types, req, s.api_server);
                    assert(new_obj.spec == old_obj.spec);
                },
                APIRequest::PatchStatusRequest(req) => {
                    lemma_patch_status_request_keeps_identity(cluster.installed_types, req, s.api_server);
                    assert(new_obj.spec == old_obj.spec);
                },
                _ => {
                    assert(new_obj.spec == old_obj.spec);
                },
            }
            let new_inner = InnerWidgetView::unmarshal(new_obj)->Ok_0;
            assert(new_inner.spec == InnerWidgetView::unmarshal_spec(new_obj.spec)->Ok_0);
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// ---------------------------------------------------------------------------
// The states of the reconcile walk.
// ---------------------------------------------------------------------------

pub open spec fn get_req_msg_for(controller_id: int, outer: OuterWidgetView, msg: Message) -> bool {
    &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& msg.content->APIRequest_0 == APIRequest::GetRequest(GetRequest { key: inner_key(outer) })
}

pub open spec fn st_sync_init(controller_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_sync_step(controller_id, key, WidgetSyncStepView::Init)(s)
        &&& Cluster::no_pending_req_msg(controller_id, s, key)
    }
}

pub open spec fn st_get_req_msg_in_flight(controller_id: int, outer: OuterWidgetView, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_sync_step(controller_id, outer.object_ref(), WidgetSyncStepView::AfterGetInner)(s)
        &&& s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg == Some(msg)
        &&& get_req_msg_for(controller_id, outer, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_get_req_in_flight(controller_id: int, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg->0;
        &&& at_sync_step(controller_id, outer.object_ref(), WidgetSyncStepView::AfterGetInner)(s)
        &&& s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg is Some
        &&& get_req_msg_for(controller_id, outer, msg)
        &&& s.in_flight().contains(msg)
    }
}

// What a Get response says about the store now: the mirror was absent when the
// Get was answered and still is, or it was ours and still is, with the uid,
// generation and spec the response shows, unless a write of the outer spec landed
// since (in which case the spec is synced already).
pub open spec fn get_resp_reflects_store(resp: Message, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let ikey = inner_key(outer);
        let res = resp.content.get_get_response().res;
        let obj = res->Ok_0;
        &&& res is Err ==> res->Err_0 is ObjectNotFound && mirror_absent(outer)(s)
        &&& res is Ok ==> {
            &&& mirror_is_ours(outer)(s)
            &&& InnerWidgetView::unmarshal(obj) is Ok
            &&& is_mirror_of(InnerWidgetView::unmarshal(obj)->Ok_0, outer)
            &&& obj.metadata.deletion_timestamp is None
            &&& s.resources()[ikey].metadata.uid == obj.metadata.uid
            &&& (s.resources()[ikey].metadata.generation == obj.metadata.generation && s.resources()[ikey].spec == obj.spec)
                || spec_synced(outer)(s)
        }
    }
}

pub open spec fn st_get_resp_msg_in_flight(controller_id: int, outer: OuterWidgetView, resp: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg->0;
        &&& at_sync_step(controller_id, outer.object_ref(), WidgetSyncStepView::AfterGetInner)(s)
        &&& s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg is Some
        &&& get_req_msg_for(controller_id, outer, msg)
        &&& s.in_flight().contains(resp)
        &&& resp_msg_matches_req_msg(resp, msg)
        &&& get_resp_reflects_store(resp, outer)(s)
    }
}

pub open spec fn st_get_resp_in_flight(controller_id: int, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg->0;
        &&& at_sync_step(controller_id, outer.object_ref(), WidgetSyncStepView::AfterGetInner)(s)
        &&& s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg is Some
        &&& get_req_msg_for(controller_id, outer, msg)
        &&& exists |resp: Message| {
            &&& #[trigger] s.in_flight().contains(resp)
            &&& resp_msg_matches_req_msg(resp, msg)
            &&& get_resp_reflects_store(resp, outer)(s)
        }
    }
}

pub open spec fn st_create_req_msg_in_flight(controller_id: int, outer: OuterWidgetView, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_sync_step(controller_id, outer.object_ref(), WidgetSyncStepView::AfterCreateInner)(s)
        &&& s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg == Some(msg)
        &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
        &&& msg.content.is_create_request()
        &&& s.in_flight().contains(msg)
        &&& mirror_absent(outer)(s)
    }
}

pub open spec fn st_create_req_in_flight(controller_id: int, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |msg: Message| #[trigger] st_create_req_msg_in_flight(controller_id, outer, msg)(s)
}

// The mirror is as the pending Patch read it: same uid and generation.
pub open spec fn patch_target_intact(msg: Message, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let ikey = inner_key(outer);
        let req = msg.content.get_patch_request();
        &&& mirror_is_ours(outer)(s)
        &&& req.tests.uid is Some
        &&& req.tests.generation is Some
        &&& s.resources()[ikey].metadata.uid == req.tests.uid
        &&& s.resources()[ikey].metadata.generation == req.tests.generation
    }
}

pub open spec fn st_patch_req_msg_in_flight(controller_id: int, outer: OuterWidgetView, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_sync_step(controller_id, outer.object_ref(), WidgetSyncStepView::AfterPatchInner)(s)
        &&& s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg == Some(msg)
        &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
        &&& msg.content.is_patch_request()
        &&& s.in_flight().contains(msg)
        &&& patch_target_intact(msg, outer)(s) || spec_synced(outer)(s)
    }
}

pub open spec fn st_patch_req_in_flight(controller_id: int, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |msg: Message| #[trigger] st_patch_req_msg_in_flight(controller_id, outer, msg)(s)
}

// ---------------------------------------------------------------------------
// What the sync reconciler's pending request looks like, given the invariants.
// ---------------------------------------------------------------------------

// The snapshot of the current reconcile of the outer copy, and what its pending
// request is, at each step.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_current_reconcile_of_outer(cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, outer: OuterWidgetView)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        sync_step_ctx(cluster, controller_id, janitor_id, outer)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)(s),
        s.ongoing_reconciles(controller_id).contains_key(outer.object_ref()),
    ensures
        ({
            let cr = s.ongoing_reconciles(controller_id)[outer.object_ref()].triggering_cr;
            let cr_outer = OuterWidgetView::unmarshal(cr)->Ok_0;
            &&& OuterWidgetView::unmarshal(cr) is Ok
            &&& cr_outer.metadata == cr.metadata
            &&& cr.object_ref() == outer.object_ref()
            &&& cr.metadata.well_formed_for_namespaced()
            &&& cr.metadata.uid == outer.metadata.uid
            &&& cr_outer.spec == outer.spec
            &&& cr_outer.state_validation()
            &&& inner_key(cr_outer) == inner_key(outer)
            &&& parent_uid_of(cr_outer) == parent_uid_of(outer)
        }),
{
    let key = outer.object_ref();
    let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
    OuterWidgetView::object_ref_is_well_formed();
    assert(key.kind == OuterWidgetView::kind());
    assert(key.kind is CustomResourceKind);
    assert(OuterWidgetView::unmarshal(cr) is Ok);
    let cr_outer = OuterWidgetView::unmarshal(cr)->Ok_0;
    assert(cr_outer.metadata == cr.metadata);
    assert(cr.object_ref() == key);
    assert(cr.metadata.uid == outer.metadata().uid);
    assert(cr_outer.spec() == outer.spec());
}

// ---------------------------------------------------------------------------
// The walk.
// ---------------------------------------------------------------------------

// idle ~> scheduled: the outer copy exists, so scheduling is enabled.
pub proof fn lemma_sync_idle_leads_to_scheduled(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_settled(cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(Cluster::reconcile_idle(controller_id, outer.object_ref()))
            .leads_to(lift_state(|s: ClusterState| {
                &&& !s.ongoing_reconciles(controller_id).contains_key(outer.object_ref())
                &&& s.scheduled_reconciles(controller_id).contains_key(outer.object_ref())
            }))),
{
    let key = outer.object_ref();
    lemma_unfold_sync_spec_with_settled(spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    OuterWidgetView::object_ref_is_well_formed();
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& !s.scheduled_reconciles(controller_id).contains_key(key)
    };
    let post = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
    };
    let d = Cluster::desired_state_is(outer);
    let stronger_pre = |s: ClusterState| pre(s) && d(s);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& d(s_prime)
    };
    always_to_always_later(spec, lift_state(d));
    combine_spec_entails_always_n!(spec, lift_action(stronger_next), lift_action(cluster.next()), later(lift_state(d)));
    assert forall |s: ClusterState| #[trigger] stronger_pre(s) implies cluster.schedule_controller_reconcile().pre((controller_id, key))(s) by {
        assert(s.resources().contains_key(key));
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, key, stronger_next, stronger_pre, post);
    temp_pred_equality(lift_state(pre).and(lift_state(d)), lift_state(stronger_pre));
    leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(d));
    entails_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), lift_state(Cluster::reconcile_idle(controller_id, key)));
}

// scheduled ~> Init with no pending request.
pub proof fn lemma_sync_scheduled_leads_to_init(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_settled(cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
                &&& !s.ongoing_reconciles(controller_id).contains_key(outer.object_ref())
                &&& s.scheduled_reconciles(controller_id).contains_key(outer.object_ref())
            }).leads_to(lift_state(st_sync_init(controller_id, outer.object_ref())))),
{
    let key = outer.object_ref();
    lemma_unfold_sync_spec_with_settled(spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    OuterWidgetView::object_ref_is_well_formed();
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
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == reconcile_init_state().marshal());
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is None);
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == reconcile_init_state().marshal());
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::RunScheduledReconcile, (controller_id, input.0, input.1))(s) by {
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, pre, post);
}

// Init ~> the Get of the mirror is in flight.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_sync_init_leads_to_get_req_in_flight(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_settled(cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_sync_init(controller_id, outer.object_ref()))
            .leads_to(lift_state(st_get_req_in_flight(controller_id, outer)))),
{
    let key = outer.object_ref();
    lemma_unfold_sync_spec_with_settled(spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(spec, cluster, controller_id, janitor_id, outer);
    OuterWidgetView::object_ref_is_well_formed();
    OuterWidgetView::marshal_preserves_integrity();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let pre = st_sync_init(controller_id, key);
    let post = st_get_req_in_flight(controller_id, outer);
    let input = (None::<Message>, Some(key));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& sync_step_next(cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(sync_step_next(cluster, controller_id, janitor_id, outer)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id))
    );
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        lemma_current_reconcile_of_outer(cluster, controller_id, janitor_id, s, outer);
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        let cr_outer = OuterWidgetView::unmarshal(cr)->Ok_0;
        let req = APIRequest::GetRequest(GetRequest { key: inner_key(cr_outer) });
        let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
        assert(s_prime.in_flight().contains(msg));
        assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == at_step(WidgetSyncStepView::AfterGetInner).marshal());
        assert(get_req_msg_for(controller_id, outer, msg));
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
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
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post);
}

// The Get in flight ~> its response is in flight, and reflects the store.
#[verifier(rlimit(300))]
#[verifier(spinoff_prover)]
pub proof fn lemma_sync_get_req_leads_to_get_resp(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_settled(cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_get_req_in_flight(controller_id, outer))
            .leads_to(lift_state(st_get_resp_in_flight(controller_id, outer)))),
{
    let key = outer.object_ref();
    let ikey = inner_key(outer);
    lemma_unfold_sync_spec_with_settled(spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(spec, cluster, controller_id, janitor_id, outer);
    OuterWidgetView::object_ref_is_well_formed();
    let post = st_get_resp_in_flight(controller_id, outer);
    let pre_of = |msg: Message| lift_state(st_get_req_msg_in_flight(controller_id, outer, msg));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& sync_step_next(cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& mirror_settled(outer)(s)
        &&& mirror_settled(outer)(s_prime)
    };
    always_to_always_later(spec, lift_state(mirror_settled(outer)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(sync_step_next(cluster, controller_id, janitor_id, outer)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)),
        lift_state(mirror_settled(outer)),
        later(lift_state(mirror_settled(outer)))
    );
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_get_req_msg_in_flight(controller_id, outer, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            let resp = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
            assert(s_prime.in_flight().contains(resp));
            assert(resp_msg_matches_req_msg(resp, msg));
            assert(s_prime.api_server == s.api_server);
            assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
            assert(resp.content.get_get_response() == handle_get_request(GetRequest { key: ikey }, s.api_server));
            if s.resources().contains_key(ikey) {
                assert(mirror_is_ours(outer)(s));
                assert(resp.content.get_get_response().res == Ok::<DynamicObjectView, APIError>(s.resources()[ikey]));
            } else {
                assert(resp.content.get_get_response().res == Err::<DynamicObjectView, APIError>(APIError::ObjectNotFound));
            }
            assert(get_resp_reflects_store(resp, outer)(s_prime));
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
    assert_by(tla_exists(pre_of) == lift_state(st_get_req_in_flight(controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_get_req_in_flight(controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let msg = ex.head().ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_get_req_in_flight(controller_id, outer)));
    });
}

// A Get response in flight keeps reflecting the store until it is consumed.
#[verifier(rlimit(300))]
#[verifier(spinoff_prover)]
pub proof fn lemma_get_resp_keeps_reflecting_store(
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: OuterWidgetView, resp: Message
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        sync_step_next(cluster, controller_id, janitor_id, outer)(s, s_prime),
        mirror_settled(outer)(s),
        st_get_resp_msg_in_flight(controller_id, outer, resp)(s),
        s_prime.ongoing_reconciles(controller_id)[outer.object_ref()] == s.ongoing_reconciles(controller_id)[outer.object_ref()],
        s_prime.ongoing_reconciles(controller_id).contains_key(outer.object_ref()),
    ensures get_resp_reflects_store(resp, outer)(s_prime),
{
    let key = outer.object_ref();
    let ikey = inner_key(outer);
    let res = resp.content.get_get_response().res;
    lemma_mirror_key_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
    if res is Err {
        // Absent stays absent: only the pending Get is in flight from the reconcile, so no create of ours lands.
        if !mirror_absent(outer)(s_prime) {
            assert(mirror_is_ours(outer)(s_prime));
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    let msg = input->0;
                    assert(s.in_flight().contains(msg));
                    // The object was created by a message from the reconcile of the outer copy: the pending Get. Contradiction.
                    match msg.content->APIRequest_0 {
                        APIRequest::CreateRequest(req) => {
                            match msg.src {
                                HostId::Controller(id, k) => {
                                    if id == controller_id {
                                        assert(sync_request_is_guaranteed(msg, s));
                                        let outer_k = choose |outer_k: OuterWidgetView| {
                                            &&& outer_k.object_ref() == k
                                            &&& outer_k.metadata.uid is Some
                                            &&& req.namespace == k.namespace
                                            &&& req.obj == #[trigger] make_inner(outer_k).marshal()
                                            &&& parent_uid_is_bound_to_key(outer_k.metadata.uid->0, k)(s)
                                        };
                                        assert(k == key);
                                        assert(s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
                                        assert(false);
                                    } else {
                                        assert(false);
                                    }
                                },
                                _ => { assert(false); },
                            }
                        },
                        _ => { assert(false); },
                    }
                },
                _ => { assert(false); },
            }
        }
    } else {
        let obj = res->Ok_0;
        assert(mirror_is_ours(outer)(s));
        lemma_ours_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
        if spec_synced(outer)(s) {
            lemma_spec_synced_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
        } else {
            assert(s.resources()[ikey].metadata.generation == obj.metadata.generation && s.resources()[ikey].spec == obj.spec);
            if s_prime.resources()[ikey].spec != s.resources()[ikey].spec {
                lemma_spec_change_means_synced(cluster, controller_id, janitor_id, s, s_prime, outer);
            }
        }
    }
}

// While our mirror is there, its spec changes only by a write of the outer spec.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_spec_change_means_synced(
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        sync_step_next(cluster, controller_id, janitor_id, outer)(s, s_prime),
        mirror_is_ours(outer)(s),
        s_prime.resources()[inner_key(outer)].spec != s.resources()[inner_key(outer)].spec,
    ensures spec_synced(outer)(s_prime),
{
    let ikey = inner_key(outer);
    lemma_ours_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            InnerWidgetView::marshal_spec_preserves_integrity();
            lemma_weakly_well_formed_implies_kinds_match(s);
            match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => {
                    assert(req.key() == ikey);
                    assert(s_prime.resources()[ikey].spec == req.obj.spec);
                    assert(writes_outer_spec(req.obj.spec, outer));
                },
                APIRequest::PatchRequest(req) => {
                    assert(req.key() == ikey);
                    assert(s_prime.resources()[ikey].spec == req.spec);
                    assert(writes_outer_spec(req.spec, outer));
                },
                APIRequest::GetThenUpdateRequest(_) => {
                    lemma_get_then_update_keeps_unowned_objects(cluster.installed_types, msg, s.api_server, ikey);
                    assert(false);
                },
                APIRequest::UpdateStatusRequest(req) => {
                    lemma_update_status_keeps_identity(cluster.installed_types, req, s.api_server);
                    assert(false);
                },
                APIRequest::PatchStatusRequest(req) => {
                    lemma_patch_status_request_keeps_identity(cluster.installed_types, req, s.api_server);
                    assert(false);
                },
                _ => { assert(false); },
            }
            let new_inner = InnerWidgetView::unmarshal(s_prime.resources()[ikey])->Ok_0;
            assert(new_inner.spec == outer.spec);
        },
        _ => { assert(false); },
    }
}

// The Get response in flight ~> the reconcile decided: the mirror is synced, or a
// Create or a Patch of the mirror is in flight.
#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_sync_get_resp_leads_to_decision(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_settled(cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_get_resp_in_flight(controller_id, outer))
            .leads_to(lift_state(st_create_req_in_flight(controller_id, outer))
                .or(lift_state(st_patch_req_in_flight(controller_id, outer)))
                .or(lift_state(spec_synced(outer))))),
{
    let key = outer.object_ref();
    let ikey = inner_key(outer);
    lemma_unfold_sync_spec_with_settled(spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(spec, cluster, controller_id, janitor_id, outer);
    OuterWidgetView::object_ref_is_well_formed();
    OuterWidgetView::marshal_preserves_integrity();
    InnerWidgetView::marshal_preserves_integrity();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let post = |s: ClusterState| {
        ||| st_create_req_in_flight(controller_id, outer)(s)
        ||| st_patch_req_in_flight(controller_id, outer)(s)
        ||| spec_synced(outer)(s)
    };
    let pre_of = |resp: Message| lift_state(st_get_resp_msg_in_flight(controller_id, outer, resp));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& sync_step_next(cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)(s)
        &&& mirror_settled(outer)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(sync_step_next(cluster, controller_id, janitor_id, outer)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)),
        lift_state(mirror_settled(outer))
    );
    assert forall |resp: Message| spec.entails(#[trigger] pre_of(resp).leads_to(lift_state(post))) by {
        let pre = st_get_resp_msg_in_flight(controller_id, outer, resp);
        let input = (Some(resp), Some(key));
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
            lemma_current_reconcile_of_outer(cluster, controller_id, janitor_id, s, outer);
            let reconcile = s.ongoing_reconciles(controller_id)[key];
            let cr = reconcile.triggering_cr;
            let cr_outer = OuterWidgetView::unmarshal(cr)->Ok_0;
            let res = resp.content.get_get_response().res;
            let resp_o = Some(ResponseView::<VoidERespView>::KResponse(resp.content->APIResponse_0));
            assert(is_some_k_get_resp_view(resp_o));
            assert(extract_some_k_get_resp_view(resp_o) == res);
            let (state_prime, req_o) = reconcile_core(cr_outer, resp_o, at_step(WidgetSyncStepView::AfterGetInner));
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == state_prime.marshal());
            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == cr);
            assert(s_prime.api_server == s.api_server);
            if res is Err {
                assert(res->Err_0 is ObjectNotFound);
                assert(state_prime.reconcile_step is AfterCreateInner);
                let req = APIRequest::CreateRequest(CreateRequest { namespace: cr_outer.metadata.namespace->0, obj: make_inner(cr_outer).marshal() });
                let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
                assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
                assert(s_prime.in_flight().contains(msg));
                assert(mirror_absent(outer)(s_prime));
                assert(st_create_req_msg_in_flight(controller_id, outer, msg)(s_prime));
            } else {
                let obj = res->Ok_0;
                let inner = InnerWidgetView::unmarshal(obj)->Ok_0;
                assert(InnerWidgetView::unmarshal(obj) is Ok);
                assert(inner.metadata.deletion_timestamp is None);
                assert(is_mirror_of(inner, cr_outer));
                if spec_synced(outer)(s) {
                    assert(spec_synced(outer)(s_prime));
                } else if inner.spec != cr_outer.spec {
                    assert(state_prime.reconcile_step is AfterPatchInner);
                    let req = APIRequest::PatchRequest(inner_spec_patch(inner, cr_outer));
                    let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
                    assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
                    assert(s_prime.in_flight().contains(msg));
                    assert(msg.content.get_patch_request().tests.uid == obj.metadata.uid);
                    assert(msg.content.get_patch_request().tests.generation == obj.metadata.generation);
                    assert(obj.metadata.uid is Some);
                    assert(obj.metadata.generation is Some);
                    assert(patch_target_intact(msg, outer)(s_prime));
                    assert(st_patch_req_msg_in_flight(controller_id, outer, msg)(s_prime));
                } else {
                    // The stored spec is the one read, which is the outer spec.
                    assert(s.resources()[ikey].spec == obj.spec);
                    let stored_inner = InnerWidgetView::unmarshal(s.resources()[ikey])->Ok_0;
                    assert(stored_inner.spec == inner.spec);
                    assert(spec_synced(outer)(s_prime));
                }
            }
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
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
                        assert(cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime));
                    } else {
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        if !s_prime.in_flight().contains(resp) {
                            assert(i.1 == Some(resp));
                            assert(resp.dst == HostId::Controller(controller_id, key));
                            assert(resp.dst == HostId::Controller(i.0, i.2->0));
                            assert(false);
                        }
                        lemma_get_resp_keeps_reflecting_store(cluster, controller_id, janitor_id, s, s_prime, outer, resp);
                        assert(pre(s_prime));
                    }
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(s_prime.api_server == s.api_server);
                    assert(pre(s_prime));
                },
                Step::APIServerStep(i) => {
                    assert(i->0 != resp);
                    assert(s_prime.in_flight().contains(resp));
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    lemma_get_resp_keeps_reflecting_store(cluster, controller_id, janitor_id, s, s_prime, outer, resp);
                    assert(pre(s_prime));
                },
                Step::DropReqStep(i) => {
                    assert(i.0 != resp);
                    assert(s_prime.in_flight().contains(resp));
                    assert(s_prime.api_server == s.api_server);
                    assert(pre(s_prime));
                },
                Step::ExternalStep(i) => {
                    assert(i.1 != Some(resp));
                    assert(s_prime.in_flight().contains(resp));
                    assert(s_prime.api_server == s.api_server);
                    assert(pre(s_prime));
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    assert(s_prime.in_flight().contains(resp));
                    assert(s_prime.api_server == s.api_server);
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
    assert_by(tla_exists(pre_of) == lift_state(st_get_resp_in_flight(controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_get_resp_in_flight(controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            let resp = choose |resp: Message| {
                &&& #[trigger] s.in_flight().contains(resp)
                &&& resp_msg_matches_req_msg(resp, msg)
                &&& get_resp_reflects_store(resp, outer)(s)
            };
            assert(pre_of(resp).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_get_resp_in_flight(controller_id, outer)));
    });
    temp_pred_equality(
        lift_state(post),
        lift_state(st_create_req_in_flight(controller_id, outer)).or(lift_state(st_patch_req_in_flight(controller_id, outer))).or(lift_state(spec_synced(outer)))
    );
}


// The Create in flight ~> the mirror is synced.
#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_sync_create_req_leads_to_synced(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_settled(cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_create_req_in_flight(controller_id, outer)).leads_to(lift_state(spec_synced(outer)))),
{
    let key = outer.object_ref();
    let ikey = inner_key(outer);
    lemma_unfold_sync_spec_with_settled(spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(spec, cluster, controller_id, janitor_id, outer);
    OuterWidgetView::object_ref_is_well_formed();
    OuterWidgetView::marshal_preserves_integrity();
    InnerWidgetView::marshal_preserves_integrity();
    InnerWidgetView::marshal_spec_preserves_integrity();
    InnerWidgetView::marshal_status_preserves_integrity();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let post = spec_synced(outer);
    let pre_of = |msg: Message| lift_state(st_create_req_msg_in_flight(controller_id, outer, msg));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& sync_step_next(cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(sync_step_next(cluster, controller_id, janitor_id, outer)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id))
    );
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_create_req_msg_in_flight(controller_id, outer, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_current_reconcile_of_outer(cluster, controller_id, janitor_id, s, outer);
            let reconcile = s.ongoing_reconciles(controller_id)[key];
            let cr = reconcile.triggering_cr;
            let cr_outer = OuterWidgetView::unmarshal(cr)->Ok_0;
            assert(sync_pending_request_is(controller_id, key, reconcile));
            let req = msg.content.get_create_request();
            assert(req == CreateRequest { namespace: cr_outer.metadata.namespace->0, obj: make_inner(cr_outer).marshal() });
            let inner_new = make_inner(cr_outer);
            assert(req.obj.metadata == inner_new.metadata);
            assert(req.obj.kind == InnerWidgetView::kind());
            assert(req.obj.spec == InnerWidgetView::marshal_spec(cr_outer.spec));
            assert(req.obj.metadata.name == Some(key.name));
            assert(req.obj.metadata.namespace == Some(key.namespace));
            assert(req.namespace == key.namespace);
            // Admission passes.
            assert(unmarshallable_object(req.obj, cluster.installed_types));
            assert(req.obj.with_namespace(req.namespace).object_ref() == ikey);
            assert(create_request_admission_check(cluster.installed_types, req, s.api_server) is None);
            let created = DynamicObjectView {
                kind: req.obj.kind,
                metadata: ObjectMetaView {
                    name: req.obj.metadata.name,
                    namespace: Some(req.namespace),
                    resource_version: Some(s.api_server.resource_version_counter),
                    uid: Some(s.api_server.uid_counter),
                    generation: initial_generation(req.obj.kind),
                    deletion_timestamp: None,
                    ..req.obj.metadata
                },
                spec: req.obj.spec,
                status: marshalled_default_status(req.obj.kind, cluster.installed_types),
            };
            assert(created.object_ref() == ikey);
            assert(!s.resources().contains_key(created.object_ref()));
            // The created object is valid: no owner references, an ascii name, a valid spec.
            assert(metadata_validity_check(created) is None);
            assert(created.status == InnerWidgetView::marshal_status(InnerWidgetView::default().status()));
            assert(InnerWidgetView::unmarshal(created) is Ok);
            let created_inner = InnerWidgetView::unmarshal(created)->Ok_0;
            assert(created_inner.spec == cr_outer.spec);
            assert(created_inner.state_validation());
            assert(valid_object(created, cluster.installed_types));
            assert(created_object_validity_check(created, cluster.installed_types) is None);
            assert(s_prime.resources() == s.resources().insert(ikey, created));
            assert(s_prime.resources()[ikey] == created);
            assert(created_inner.metadata == created.metadata);
            assert(is_mirror_of(created_inner, outer));
            assert(mirror_is_ours(outer)(s_prime));
            assert(created_inner.spec == outer.spec);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(i) => {
                    if i->0 == msg {
                        assert(post(s_prime));
                    } else {
                        assert(s_prime.in_flight().contains(msg));
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        // Nothing but the pending Create, which is msg, creates the mirror.
                        lemma_mirror_key_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
                        if !mirror_absent(outer)(s_prime) {
                            let handled = i->0;
                            assert(s.in_flight().contains(handled));
                            match handled.content->APIRequest_0 {
                                APIRequest::CreateRequest(req) => {
                                    match handled.src {
                                        HostId::Controller(id, k) => {
                                            if id == controller_id {
                                                assert(sync_request_is_guaranteed(handled, s));
                                                let outer_k = choose |outer_k: OuterWidgetView| {
                                                    &&& outer_k.object_ref() == k
                                                    &&& outer_k.metadata.uid is Some
                                                    &&& req.namespace == k.namespace
                                                    &&& req.obj == #[trigger] make_inner(outer_k).marshal()
                                                    &&& parent_uid_is_bound_to_key(outer_k.metadata.uid->0, k)(s)
                                                };
                                                assert(k == key);
                                                assert(s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(handled));
                                                assert(false);
                                            } else {
                                                assert(false);
                                            }
                                        },
                                        _ => { assert(false); },
                                    }
                                },
                                _ => { assert(false); },
                            }
                        }
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
                        assert(s_prime.api_server == s.api_server);
                        assert(pre(s_prime));
                    }
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(s_prime.api_server == s.api_server);
                    assert(pre(s_prime));
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    assert(s_prime.in_flight().contains(msg));
                    assert(s_prime.api_server == s.api_server);
                    assert(pre(s_prime));
                },
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_create_req_in_flight(controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_create_req_in_flight(controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = choose |msg: Message| #[trigger] st_create_req_msg_in_flight(controller_id, outer, msg)(s);
            assert(pre_of(msg).satisfied_by(ex));
        }
        assert forall |ex| #[trigger] tla_exists(pre_of).satisfied_by(ex)
        implies lift_state(st_create_req_in_flight(controller_id, outer)).satisfied_by(ex) by {
            let msg = choose |msg: Message| #[trigger] pre_of(msg).satisfied_by(ex);
            assert(st_create_req_msg_in_flight(controller_id, outer, msg)(ex.head()));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_create_req_in_flight(controller_id, outer)));
    });
}

// The Patch in flight ~> the mirror is synced.
#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_sync_patch_req_leads_to_synced(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_settled(cluster, controller_id, janitor_id, outer)),
    ensures
        spec.entails(lift_state(st_patch_req_in_flight(controller_id, outer)).leads_to(lift_state(spec_synced(outer)))),
{
    let key = outer.object_ref();
    let ikey = inner_key(outer);
    lemma_unfold_sync_spec_with_settled(spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(spec, cluster, controller_id, janitor_id, outer);
    OuterWidgetView::object_ref_is_well_formed();
    OuterWidgetView::marshal_preserves_integrity();
    InnerWidgetView::marshal_preserves_integrity();
    InnerWidgetView::marshal_spec_preserves_integrity();
    InnerWidgetView::marshal_status_preserves_integrity();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let post = spec_synced(outer);
    let pre_of = |msg: Message| lift_state(st_patch_req_msg_in_flight(controller_id, outer, msg));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& sync_step_next(cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(sync_step_next(cluster, controller_id, janitor_id, outer)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<OuterWidgetView>(controller_id))
    );
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_patch_req_msg_in_flight(controller_id, outer, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            if spec_synced(outer)(s) {
                lemma_spec_synced_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
            } else {
                assert(patch_target_intact(msg, outer)(s));
                lemma_current_reconcile_of_outer(cluster, controller_id, janitor_id, s, outer);
                lemma_weakly_well_formed_implies_kinds_match(s);
                let reconcile = s.ongoing_reconciles(controller_id)[key];
                let cr = reconcile.triggering_cr;
                let cr_outer = OuterWidgetView::unmarshal(cr)->Ok_0;
                assert(sync_pending_request_is(controller_id, key, reconcile));
                let req = msg.content.get_patch_request();
                let inner_read = choose |inner: InnerWidgetView| msg.content->APIRequest_0 == APIRequest::PatchRequest(#[trigger] inner_spec_patch(inner, cr_outer));
                assert(req == inner_spec_patch(inner_read, cr_outer));
                assert(req.key() == ikey);
                assert(req.spec == InnerWidgetView::marshal_spec(cr_outer.spec));
                let old_obj = s.resources()[ikey];
                assert(Cluster::etcd_object_is_weakly_well_formed(ikey)(s));
                assert(cluster.etcd_object_is_well_formed(ikey)(s));
                assert(old_obj.object_ref() == ikey);
                assert(req.tests.pass(old_obj));
                let update_req = UpdateRequest { namespace: req.namespace, name: req.name, obj: old_obj.with_spec(req.spec) };
                assert(update_req.key() == ikey);
                assert(unmarshallable_object(update_req.obj, cluster.installed_types));
                assert(update_request_admission_check(cluster.installed_types, update_req, s.api_server) is None);
                let updated = updated_object(update_req, old_obj);
                // The spec changes (it was not synced), so the object changes.
                let old_inner = InnerWidgetView::unmarshal(old_obj)->Ok_0;
                assert(old_inner.spec != outer.spec);
                assert(old_obj.spec != req.spec);
                assert(updated != old_obj);
                let updated_rv = updated.with_resource_version(s.api_server.resource_version_counter);
                assert(updated_rv.metadata.deletion_timestamp is None);
                assert(metadata_validity_check(updated_rv) is None);
                assert(metadata_transition_validity_check(updated_rv, old_obj) is None);
                assert(InnerWidgetView::unmarshal(updated_rv) is Ok);
                let updated_inner = InnerWidgetView::unmarshal(updated_rv)->Ok_0;
                assert(updated_inner.spec == cr_outer.spec);
                assert(updated_inner.state_validation());
                assert(valid_object(updated_rv, cluster.installed_types));
                assert(valid_transition(updated_rv, old_obj, cluster.installed_types));
                assert(updated_object_validity_check(updated_rv, old_obj, cluster.installed_types) is None);
                assert(s_prime.resources()[ikey] == updated_rv);
                assert(updated_inner.metadata == updated_rv.metadata);
                assert(updated_rv.metadata.labels == old_obj.metadata.labels);
                assert(updated_rv.metadata.annotations == old_obj.metadata.annotations);
                assert(is_mirror_of(updated_inner, outer));
                assert(mirror_is_ours(outer)(s_prime));
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
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                        if spec_synced(outer)(s) {
                            lemma_spec_synced_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
                        } else {
                            lemma_ours_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
                            if s_prime.resources()[ikey].spec != s.resources()[ikey].spec {
                                lemma_spec_change_means_synced(cluster, controller_id, janitor_id, s, s_prime, outer);
                            } else {
                                assert(patch_target_intact(msg, outer)(s_prime));
                            }
                        }
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
                        assert(s_prime.api_server == s.api_server);
                        assert(pre(s_prime));
                    }
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(s_prime.api_server == s.api_server);
                    assert(pre(s_prime));
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    assert(s_prime.in_flight().contains(msg));
                    assert(s_prime.api_server == s.api_server);
                    assert(pre(s_prime));
                },
            }
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_patch_req_in_flight(controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_patch_req_in_flight(controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = choose |msg: Message| #[trigger] st_patch_req_msg_in_flight(controller_id, outer, msg)(s);
            assert(pre_of(msg).satisfied_by(ex));
        }
        assert forall |ex| #[trigger] tla_exists(pre_of).satisfied_by(ex)
        implies lift_state(st_patch_req_in_flight(controller_id, outer)).satisfied_by(ex) by {
            let msg = choose |msg: Message| #[trigger] pre_of(msg).satisfied_by(ex);
            assert(st_patch_req_msg_in_flight(controller_id, outer, msg)(ex.head()));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_patch_req_in_flight(controller_id, outer)));
    });
}

// ---------------------------------------------------------------------------
// Under all layers: the mirror is eventually and forever synced.
// ---------------------------------------------------------------------------

#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_true_leads_to_always_spec_synced(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_settled(cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(spec_synced(outer))))),
{
    let key = outer.object_ref();
    lemma_unfold_sync_spec_with_settled(spec, cluster, controller_id, janitor_id, outer);
    lemma_unfold_sync_spec_with_phase_ii(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_terminates(spec, cluster, controller_id, janitor_id, key);
    let idle = lift_state(Cluster::reconcile_idle(controller_id, key));
    let scheduled = lift_state(|s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
    });
    let init = lift_state(st_sync_init(controller_id, key));
    let get_req = lift_state(st_get_req_in_flight(controller_id, outer));
    let get_resp = lift_state(st_get_resp_in_flight(controller_id, outer));
    let create_req = lift_state(st_create_req_in_flight(controller_id, outer));
    let patch_req = lift_state(st_patch_req_in_flight(controller_id, outer));
    let synced = lift_state(spec_synced(outer));
    lemma_sync_idle_leads_to_scheduled(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_scheduled_leads_to_init(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_init_leads_to_get_req_in_flight(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_get_req_leads_to_get_resp(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_get_resp_leads_to_decision(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_create_req_leads_to_synced(spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_patch_req_leads_to_synced(spec, cluster, controller_id, janitor_id, outer);
    entails_implies_leads_to(spec, synced, synced);
    or_leads_to(spec, create_req, patch_req, synced);
    or_leads_to(spec, create_req.or(patch_req), synced, synced);
    leads_to_trans_n!(spec, true_pred(), idle, scheduled, init, get_req, get_resp, create_req.or(patch_req).or(synced), synced);
    // Stability.
    let next = sync_step_next(cluster, controller_id, janitor_id, outer);
    assert forall |s, s_prime: ClusterState| spec_synced(outer)(s) && #[trigger] next(s, s_prime) implies spec_synced(outer)(s_prime) by {
        lemma_spec_synced_after_step(cluster, controller_id, janitor_id, s, s_prime, outer);
    }
    leads_to_stable(spec, lift_action(next), true_pred(), synced);
}

// ---------------------------------------------------------------------------
// Assembly: R1 for one outer copy, then for all.
// ---------------------------------------------------------------------------

pub proof fn lemma_outer_stable_leads_to_always_spec_synced(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView
)
    requires
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(sync_stable_spec(cluster, controller_id, janitor_id)),
    ensures spec.entails(always(lift_state(outer_stable(outer))).leads_to(always(lift_state(spec_synced(outer))))),
{
    let target = always(lift_state(spec_synced(outer)));
    let stable_spec = sync_stable_spec(cluster, controller_id, janitor_id);
    let spec_d = sync_spec_with_desired(cluster, controller_id, janitor_id, outer);
    let spec_i = sync_spec_with_phase_i(cluster, controller_id, janitor_id, outer);
    let spec_ii = sync_spec_with_phase_ii(cluster, controller_id, janitor_id, outer);
    let spec_iii = sync_spec_with_settled(cluster, controller_id, janitor_id, outer);
    let settled_temp = always(lift_state(mirror_settled(outer)));
    let phase_ii_temp = always(lift_state(sync_phase_ii(controller_id, outer)));
    let phase_i_temp = always(lift_state(phase_i(controller_id)));
    let premise_temp = always(lift_state(outer_stable(outer)));

    // Under all layers.
    assert(spec_iii.entails(spec_iii));
    lemma_true_leads_to_always_spec_synced(spec_iii, cluster, controller_id, janitor_id, outer);
    // Remove the settled layer.
    sync_spec_with_phase_ii_is_stable(cluster, controller_id, janitor_id, outer);
    unpack_conditions_from_spec(spec_ii, settled_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(settled_temp), settled_temp);
    assert(spec_ii.entails(spec_ii));
    lemma_true_leads_to_always_mirror_settled(spec_ii, cluster, controller_id, janitor_id, outer);
    leads_to_trans(spec_ii, true_pred(), settled_temp, target);
    // Remove phase II.
    sync_spec_with_phase_i_is_stable(cluster, controller_id, janitor_id, outer);
    unpack_conditions_from_spec(spec_i, phase_ii_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_ii_temp), phase_ii_temp);
    assert(spec_i.entails(spec_i));
    lemma_true_leads_to_always_sync_phase_ii(spec_i, cluster, controller_id, janitor_id, outer);
    leads_to_trans(spec_i, true_pred(), phase_ii_temp, target);
    // Remove phase I.
    sync_spec_with_desired_is_stable(cluster, controller_id, janitor_id, outer);
    unpack_conditions_from_spec(spec_d, phase_i_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_i_temp), phase_i_temp);
    assert(spec_d.entails(spec_d));
    entails_and_split(spec_d, stable_spec, premise_temp);
    lemma_sync_stable_spec_facts(spec_d, cluster, controller_id, janitor_id);
    lemma_true_leads_to_always_phase_i(spec_d, cluster, controller_id);
    leads_to_trans(spec_d, true_pred(), phase_i_temp, target);
    // Remove the premise.
    sync_stable_spec_is_stable(cluster, controller_id, janitor_id);
    unpack_conditions_from_spec(stable_spec, premise_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(premise_temp), premise_temp);
    entails_trans(spec, stable_spec, premise_temp.leads_to(target));
}

// R1: once the outer copy is stable and nobody writes anything but its spec to the
// mirror, the mirror is eventually and forever ours, with that spec.
pub proof fn sync_eventually_synced(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(sync_next_with_wf(cluster, controller_id)),
        sync_membership(cluster, controller_id, janitor_id),
        spec.entails(always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id)))),
        spec.entails(inner_releases_terminating_objects()),
        spec.entails(widget_janitor_esr(janitor_id)),
    ensures spec.entails(widget_spec_eventually_synced()),
{
    entails_and_split(spec, widget_mirrors_eventually_collected(), always(lift_state(janitor_deletes_are_sound(janitor_id))));
    assert(sync_next_with_wf(cluster, controller_id).entails(always(lift_action(cluster.next()))));
    entails_trans(spec, sync_next_with_wf(cluster, controller_id), always(lift_action(cluster.next())));
    sync_invariants_hold(spec, cluster, controller_id, janitor_id);
    entails_and_n!(
        spec,
        sync_next_with_wf(cluster, controller_id),
        always(lift_state(sync_rely_with_janitor(cluster, controller_id, janitor_id))),
        inner_releases_terminating_objects(),
        widget_mirrors_eventually_collected(),
        sync_invariants(cluster, controller_id, janitor_id)
    );
    let per_cr = |outer: OuterWidgetView| widget_spec_eventually_synced_per_cr(outer);
    assert forall |outer: OuterWidgetView| spec.entails(#[trigger] per_cr(outer)) by {
        lemma_outer_stable_leads_to_always_spec_synced(spec, cluster, controller_id, janitor_id, outer);
    }
    spec_entails_tla_forall(spec, per_cr);
}

}
