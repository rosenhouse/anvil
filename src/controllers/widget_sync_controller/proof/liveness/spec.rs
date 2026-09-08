// What the property proofs share.
//
// For each reconciler: the assumptions it runs under (fairness, rely,
// membership), the invariants that hold from the initial state on, the stable
// spec built from them and its facts spelled out. Then the object-level
// predicates of the proofs, phase I (failures are eventually disabled), the
// layered specs of the sync reconciler, which R1 (sync_spec_proof.rs), R2
// (sync_status_proof.rs) and R3s (cleanup_proof.rs) all walk under, and the step
// context of the sync reconciler that the step lemmas of api_actions.rs assume.
//
// Layers and phases that only one property uses live with that property:
// janitor_proof.rs (R3), sync_status_proof.rs (R2), cleanup_proof.rs (R3s).
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
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
    model::{install::*, janitor_reconciler::*, sync_reconciler::*},
    proof::{
        guarantee::*, helper_invariants::*, janitor_invariants::*,
        liveness::{terminate},
        predicate::*, sync_invariants::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Fairness, rely and membership of the sync reconciler.
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
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError))))))
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
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError)))));
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
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError))))),
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
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError))));
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
        tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError)))),
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
// The facts of the stable spec, spelled out.
// ---------------------------------------------------------------------------

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
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError)))))),
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
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError)))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError))))));
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
// Fairness, rely and invariants of the janitor.
// ---------------------------------------------------------------------------

pub open spec fn janitor_next_with_wf(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
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

pub proof fn janitor_next_with_wf_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(janitor_next_with_wf(cluster, controller_id))),
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

// What the janitor's rely, together with the janitor's own guarantee and the
// cluster's structural invariants, says about writes of mirrors by anyone.
pub proof fn lemma_janitor_rely_implies_mirror_write_facts(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(always(lifted_janitor_rely_condition(cluster, controller_id))),
        spec.entails(always(lift_state(widget_janitor_guarantee(controller_id)))),
        spec.entails(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))),
        spec.entails(always(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()))),
        spec.entails(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))),
    ensures
        spec.entails(always(lift_state(every_in_flight_inner_create_is_a_mirror_create()))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity()))),
{
    let rely = |s: ClusterState| {
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] widget_janitor_rely(other_id)(s)
    };
    let all = |s: ClusterState| {
        &&& rely(s)
        &&& widget_janitor_guarantee(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
    };
    entails_always_and_n!(
        spec,
        lift_state(rely),
        lift_state(widget_janitor_guarantee(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())
    );
    temp_pred_equality(
        lift_state(all),
        lift_state(rely)
            .and(lift_state(widget_janitor_guarantee(controller_id)))
            .and(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))
            .and(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()))
            .and(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()))
            .and(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))
    );
    assert forall |s: ClusterState| #[trigger] all(s) implies every_in_flight_inner_create_is_a_mirror_create()(s) && every_in_flight_inner_update_preserves_identity()(s) by {
        assert forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        } implies request_is_a_sound_mirror_write(msg, s) by {
            match msg.src {
                HostId::Controller(id, key) => {
                    assert(cluster.controller_models.contains_key(id));
                    if id == controller_id {
                        assert(janitor_request_is_guaranteed(msg));
                    } else {
                        assert(cluster.controller_models.remove(controller_id).contains_key(id));
                        assert(widget_janitor_rely(id)(s));
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
}

// The per-message body of the two write facts.
pub open spec fn request_is_a_sound_mirror_write(msg: Message, s: ClusterState) -> bool {
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
}

// Invariants that hold from the initial state on.
pub open spec fn janitor_invariants(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>())))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<InnerWidgetView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(controller_id))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))))
    .and(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    .and(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))))
    .and(always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init))))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter))))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner))))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)))))
    .and(always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<InnerWidgetView>(controller_id))))
    .and(always(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external())))
    .and(always(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests())))
    .and(always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())))
    .and(always(lift_state(widget_janitor_guarantee(controller_id))))
    .and(always(lift_state(every_in_flight_inner_create_is_a_mirror_create())))
    .and(always(lift_state(every_in_flight_inner_update_preserves_identity())))
    .and(always(lift_state(every_mirror_is_bound())))
    .and(always(lift_state(janitor_scheduled_crs_are_sound(controller_id))))
    .and(always(lift_state(janitor_triggering_crs_are_sound(controller_id))))
    .and(always(lift_state(janitor_decisions_are_sound(controller_id))))
}

pub proof fn janitor_invariants_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(janitor_invariants(cluster, controller_id))),
{
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_unique_id()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_p_is_stable(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()));
    always_p_is_stable(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()));
    always_p_is_stable(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>()));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<InnerWidgetView>(controller_id)));
    always_p_is_stable(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()));
    always_p_is_stable(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)));
    always_p_is_stable(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)));
    always_p_is_stable(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(controller_id)));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))));
    always_p_is_stable(lift_state(Cluster::there_is_the_controller_state(controller_id)));
    always_p_is_stable(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)));
    always_p_is_stable(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id)));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init)))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter)))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner)))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done))));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error))));
    always_p_is_stable(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<InnerWidgetView>(controller_id)));
    always_p_is_stable(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()));
    always_p_is_stable(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()));
    always_p_is_stable(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()));
    always_p_is_stable(lift_state(widget_janitor_guarantee(controller_id)));
    always_p_is_stable(lift_state(every_in_flight_inner_create_is_a_mirror_create()));
    always_p_is_stable(lift_state(every_in_flight_inner_update_preserves_identity()));
    always_p_is_stable(lift_state(every_mirror_is_bound()));
    always_p_is_stable(lift_state(janitor_scheduled_crs_are_sound(controller_id)));
    always_p_is_stable(lift_state(janitor_triggering_crs_are_sound(controller_id)));
    always_p_is_stable(lift_state(janitor_decisions_are_sound(controller_id)));
    stable_and_n!(
        always(lift_state(Cluster::every_in_flight_msg_has_unique_id())),
        always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())),
        always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))),
        always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())),
        always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>())),
        always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>())),
        always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<InnerWidgetView>(controller_id))),
        always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())),
        always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())),
        always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))),
        always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))),
        always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(controller_id))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))),
        always(lift_state(Cluster::there_is_the_controller_state(controller_id))),
        always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))),
        always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init))))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter))))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner))))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)))),
        always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)))),
        always(lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<InnerWidgetView>(controller_id))),
        always(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external())),
        always(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests())),
        always(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())),
        always(lift_state(widget_janitor_guarantee(controller_id))),
        always(lift_state(every_in_flight_inner_create_is_a_mirror_create())),
        always(lift_state(every_in_flight_inner_update_preserves_identity())),
        always(lift_state(every_mirror_is_bound())),
        always(lift_state(janitor_scheduled_crs_are_sound(controller_id))),
        always(lift_state(janitor_triggering_crs_are_sound(controller_id))),
        always(lift_state(janitor_decisions_are_sound(controller_id)))
    );
}

pub proof fn janitor_invariants_hold(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<InnerWidgetView>(),
        cluster.type_is_installed_in_cluster::<OuterWidgetView>(),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(always(lifted_janitor_rely_condition(cluster, controller_id))),
    ensures spec.entails(janitor_invariants(cluster, controller_id)),
{
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>(spec);
    cluster.lemma_always_each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>(spec);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<InnerWidgetView>(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id(spec);
    cluster.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_every_ongoing_reconcile_has_lower_id_than_allocator(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(spec, controller_id);
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))) by {
        cluster.lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, controller_id, key);
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)));
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_there_is_no_request_msg_to_external_from_controller(spec, controller_id);
    cluster.lemma_always_cr_states_are_unmarshallable::<WidgetJanitorReconciler, WidgetJanitorReconcileState, InnerWidgetView, VoidEReqView, VoidERespView>(spec, controller_id);
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init))))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, cluster.reconcile_model(controller_id).done);
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, cluster.reconcile_model(controller_id).error);
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error)));
    cluster.lemma_always_every_in_flight_msg_from_controller_has_kind_as::<InnerWidgetView>(spec, controller_id);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    lemma_always_widget_janitor_guarantee(spec, cluster, controller_id);
    lemma_janitor_rely_implies_mirror_write_facts(spec, cluster, controller_id);
    lemma_always_every_mirror_is_bound(spec, cluster);
    lemma_always_janitor_crs_are_sound(spec, cluster, controller_id);
    lemma_always_janitor_decisions_are_sound(spec, cluster, controller_id);
    entails_always_and_n!(
        spec,
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_builtin_object_in_etcd_is_well_formed()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()),
        lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<OuterWidgetView>()),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<InnerWidgetView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()),
        lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(controller_id)),
        tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id)),
        tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init)))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter)))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner)))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done))),
        tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).error))),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_kind_as::<InnerWidgetView>(controller_id)),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()),
        lift_state(widget_janitor_guarantee(controller_id)),
        lift_state(every_in_flight_inner_create_is_a_mirror_create()),
        lift_state(every_in_flight_inner_update_preserves_identity()),
        lift_state(every_mirror_is_bound()),
        lift_state(janitor_scheduled_crs_are_sound(controller_id)),
        lift_state(janitor_triggering_crs_are_sound(controller_id)),
        lift_state(janitor_decisions_are_sound(controller_id))
    );
}

// The stable part of the janitor's spec: fairness, rely, D3 and the invariants.
pub open spec fn janitor_stable_spec(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    janitor_next_with_wf(cluster, controller_id)
    .and(always(lifted_janitor_rely_condition(cluster, controller_id)))
    .and(inner_releases_terminating_objects())
    .and(janitor_invariants(cluster, controller_id))
}

pub proof fn janitor_stable_spec_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(janitor_stable_spec(cluster, controller_id))),
{
    janitor_next_with_wf_is_stable(cluster, controller_id);
    always_p_is_stable(lifted_janitor_rely_condition(cluster, controller_id));
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
    janitor_invariants_is_stable(cluster, controller_id);
    stable_and_n!(
        janitor_next_with_wf(cluster, controller_id),
        always(lifted_janitor_rely_condition(cluster, controller_id)),
        inner_releases_terminating_objects(),
        janitor_invariants(cluster, controller_id)
    );
}

// The facts of the stable spec that the step lemmas use, spelled out.
pub proof fn lemma_janitor_stable_spec_facts(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires spec.entails(janitor_stable_spec(cluster, controller_id)),
    ensures
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(tla_forall(|input| cluster.disable_crash().weak_fairness(input))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(cluster.disable_req_drop().weak_fairness(())),
        spec.entails(cluster.disable_pod_monkey().weak_fairness(())),
        spec.entails(always(lifted_janitor_rely_condition(cluster, controller_id))),
        spec.entails(inner_releases_terminating_objects()),
        spec.entails(janitor_invariants(cluster, controller_id)),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(controller_id)))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id)))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner)))))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity()))),
        spec.entails(always(lift_state(every_mirror_is_bound()))),
        spec.entails(always(lift_state(janitor_triggering_crs_are_sound(controller_id)))),
        spec.entails(always(lift_state(janitor_decisions_are_sound(controller_id)))),
{
    let stable_spec = janitor_stable_spec(cluster, controller_id);
    let wf = janitor_next_with_wf(cluster, controller_id);
    let inv = janitor_invariants(cluster, controller_id);
    assert(stable_spec.entails(wf));
    assert(stable_spec.entails(always(lifted_janitor_rely_condition(cluster, controller_id))));
    assert(stable_spec.entails(inner_releases_terminating_objects()));
    assert(stable_spec.entails(inv));
    entails_trans(spec, stable_spec, wf);
    entails_trans(spec, stable_spec, always(lifted_janitor_rely_condition(cluster, controller_id)));
    entails_trans(spec, stable_spec, inner_releases_terminating_objects());
    entails_trans(spec, stable_spec, inv);
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
    assert(inv.entails(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()))));
    entails_trans(spec, inv, always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())));
    assert(inv.entails(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))));
    assert(inv.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(controller_id))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))));
    assert(inv.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::there_is_the_controller_state(controller_id))));
    assert(inv.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))));
    assert(inv.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id)))));
    entails_trans(spec, inv, always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init)))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init))))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter)))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter))))));
    assert(inv.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner)))))));
    entails_trans(spec, inv, always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner))))));
    assert(inv.entails(always(lift_state(every_in_flight_inner_update_preserves_identity()))));
    entails_trans(spec, inv, always(lift_state(every_in_flight_inner_update_preserves_identity())));
    assert(inv.entails(always(lift_state(every_mirror_is_bound()))));
    entails_trans(spec, inv, always(lift_state(every_mirror_is_bound())));
    assert(inv.entails(always(lift_state(janitor_triggering_crs_are_sound(controller_id)))));
    entails_trans(spec, inv, always(lift_state(janitor_triggering_crs_are_sound(controller_id))));
    assert(inv.entails(always(lift_state(janitor_decisions_are_sound(controller_id)))));
    entails_trans(spec, inv, always(lift_state(janitor_decisions_are_sound(controller_id))));
}

// ---------------------------------------------------------------------------
// The object-level predicates of the proofs.
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

// The object with uid `uid` is not at `key` any more, and never will be again.
pub open spec fn gone(key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& object_is_gone(key, uid)(s)
        &&& uid < s.api_server.uid_counter
    }
}

// The mirror is there, or it is gone: nothing else happens to it.
pub open spec fn present_or_gone(key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| mirror_object_is(key, parent_uid, uid)(s) || gone(key, uid)(s)
}

// A snapshot of the mirror object.
pub open spec fn snapshot_of_mirror(cr: DynamicObjectView, key: ObjectRef, parent_uid: Uid, uid: Uid) -> bool {
    &&& snapshot_is_mirror(cr)
    &&& cr.object_ref() == key
    &&& cr.metadata.uid == Some(uid)
    &&& snapshot_parent(cr) == int_to_string_view(parent_uid)
}

// ---------------------------------------------------------------------------
// Phase I: failures are eventually disabled for good.
// ---------------------------------------------------------------------------

// Phase I: failures are eventually disabled.
pub open spec fn phase_i(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
    }
}

pub proof fn lemma_true_leads_to_always_phase_i(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(tla_forall(|input| cluster.disable_crash().weak_fairness(input))),
        spec.entails(cluster.disable_req_drop().weak_fairness(())),
        spec.entails(cluster.disable_pod_monkey().weak_fairness(())),
        cluster.controller_models.contains_key(controller_id),
    ensures spec.entails(true_pred().leads_to(always(lift_state(phase_i(controller_id))))),
{
    spec_entails_tla_forall_apply::<ClusterState, int>(spec, |input| cluster.disable_crash().weak_fairness(input), controller_id);
    cluster.lemma_true_leads_to_crash_always_disabled(spec, controller_id);
    cluster.lemma_true_leads_to_req_drop_always_disabled(spec);
    cluster.lemma_true_leads_to_pod_monkey_always_disabled(spec);
    leads_to_always_and(spec, true_pred(), lift_state(Cluster::crash_disabled(controller_id)), lift_state(Cluster::req_drop_disabled()));
    leads_to_always_and(
        spec, true_pred(),
        lift_state(Cluster::crash_disabled(controller_id)).and(lift_state(Cluster::req_drop_disabled())),
        lift_state(Cluster::pod_monkey_disabled())
    );
    temp_pred_equality(
        lift_state(phase_i(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)).and(lift_state(Cluster::req_drop_disabled())).and(lift_state(Cluster::pod_monkey_disabled()))
    );
}

// ---------------------------------------------------------------------------
// The layers of the spec: premise, phase I, phase II, settled mirror.
// ---------------------------------------------------------------------------

pub open spec fn sync_spec_with_desired(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView) -> TempPred<ClusterState> {
    sync_stable_spec(cluster, controller_id, janitor_id).and(always(lift_state(outer_spec_stable(outer))))
}

pub proof fn sync_spec_with_desired_is_stable(cluster: Cluster, controller_id: int, janitor_id: int, outer: OuterWidgetView)
    ensures valid(stable(sync_spec_with_desired(cluster, controller_id, janitor_id, outer))),
{
    sync_stable_spec_is_stable(cluster, controller_id, janitor_id);
    always_p_is_stable(lift_state(outer_spec_stable(outer)));
    stable_and_n!(sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_spec_stable(outer))));
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
        spec.entails(always(lift_state(outer_spec_stable(outer)))),
        spec.entails(always(lift_state(Cluster::desired_state_is(outer)))),
        spec.entails(always(lift_state(mirror_spec_undisturbed(outer)))),
        spec.entails(always(lift_state(mirror_undeleted(outer)))),
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
    entails_and_split(spec, sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_spec_stable(outer))));
    always_weaken(spec, lift_state(outer_spec_stable(outer)), lift_state(Cluster::desired_state_is(outer)));
    always_weaken(spec, lift_state(outer_spec_stable(outer)), lift_state(mirror_spec_undisturbed(outer)));
    always_weaken(spec, lift_state(outer_spec_stable(outer)), lift_state(mirror_undeleted(outer)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_weaken(spec, lift_state(sync_phase_ii(controller_id, outer)), lift_state(Cluster::the_object_in_schedule_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)));
    always_weaken(spec, lift_state(sync_phase_ii(controller_id, outer)), lift_state(Cluster::the_object_in_reconcile_has_spec_and_uid_as::<OuterWidgetView>(controller_id, outer)));
    always_weaken(spec, lift_state(sync_phase_ii(controller_id, outer)), lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, outer.object_ref())));
    always_weaken(spec, lift_state(sync_phase_ii(controller_id, outer)), lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())));
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
    entails_and_split(spec_i, sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_spec_stable(outer))));
    always_weaken(spec_i, lift_state(outer_spec_stable(outer)), lift_state(Cluster::desired_state_is(outer)));
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
    entails_and_split(spec_a, sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_spec_stable(outer))));
    always_weaken(spec_a, lift_state(outer_spec_stable(outer)), lift_state(Cluster::desired_state_is(outer)));
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
    entails_and_split(spec_b, sync_stable_spec(cluster, controller_id, janitor_id), always(lift_state(outer_spec_stable(outer))));
    always_weaken(spec_b, lift_state(outer_spec_stable(outer)), lift_state(Cluster::desired_state_is(outer)));
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
        &&& mirror_undeleted(outer)(s)
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
        lift_state(mirror_undeleted(outer)),
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
            .and(lift_state(mirror_undeleted(outer)))
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

// ---------------------------------------------------------------------------
// What the sync reconciler's pending request looks like, given the invariants.
// ---------------------------------------------------------------------------

// The snapshot of the current reconcile of the outer copy, and what its pending
// request is, at each step.
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

}
