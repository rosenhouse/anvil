// R3: the janitor eventually removes a mirror object whose parent is gone for good.
//
// For a mirror object (key `key`, parent uid `parent_uid`, uid `uid`):
//     always(parent_absent(key, parent_uid)) /\ mirror_object_is(key, parent_uid, uid)
//         ~> object_is_gone(key, uid)
//
// The proof is per object. It first turns the premise into a stable predicate
// (the object is there as that mirror, or it is gone: nothing else can happen to
// it under the rely), then, under that and the eventual facts of section
// "phases", walks the janitor's state machine: idle ~> scheduled ~> Init ~> List
// sent ~> List answered ~> Delete sent ~> object removed or terminating; D3 turns
// terminating into removed.
#![allow(unused_imports)]
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
    model::{install::*, janitor_reconciler::*, sync_reconciler},
    proof::{guarantee::*, helper_invariants::*, janitor_invariants::*, liveness::terminate, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Fairness and invariants.
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

#[verifier(rlimit(100))]
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
    assert forall |key: ObjectRef| spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, #[trigger] key)))) by {
        cluster.lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, controller_id, key);
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)));
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_there_is_no_request_msg_to_external_from_controller(spec, controller_id);
    cluster.lemma_always_cr_states_are_unmarshallable::<WidgetJanitorReconciler, WidgetJanitorReconcileState, InnerWidgetView, VoidEReqView, VoidERespView>(spec, controller_id);
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    assert forall |key: ObjectRef| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] key, at_janitor_step_closure(WidgetJanitorStepView::Init))))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, #[trigger] key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner))))) by {
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner));
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner))));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] key, cluster.reconcile_model(controller_id).done)))) by {
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, controller_id, key, cluster.reconcile_model(controller_id).done);
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, cluster.reconcile_model(controller_id).done)));
    assert forall |key: ObjectRef| spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, #[trigger] key, cluster.reconcile_model(controller_id).error)))) by {
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
    tla_forall_a_p_a_leads_to_q_a_is_stable(
        |i: (ObjectRef, Uid)| lift_state(inner_terminating_object(i.0, i.1)),
        |i: (ObjectRef, Uid)| lift_state(object_is_gone(i.0, i.1))
    );
    janitor_invariants_is_stable(cluster, controller_id);
    stable_and_n!(
        janitor_next_with_wf(cluster, controller_id),
        always(lifted_janitor_rely_condition(cluster, controller_id)),
        inner_releases_terminating_objects(),
        janitor_invariants(cluster, controller_id)
    );
}

// ---------------------------------------------------------------------------
// The object-level predicates of the proof.
// ---------------------------------------------------------------------------

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

// The janitor is at `step` on a reconcile of the mirror object.
pub open spec fn janitor_at_step_for(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid, step: WidgetJanitorStepView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& snapshot_of_mirror(s.ongoing_reconciles(controller_id)[key].triggering_cr, key, parent_uid, uid)
        &&& WidgetJanitorReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state)->Ok_0.reconcile_step == step
    }
}

pub open spec fn janitor_list_req_msg(controller_id: int, key: ObjectRef, msg: Message) -> bool {
    &&& msg.src == HostId::Controller(controller_id, key)
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& msg.content.is_list_request()
    &&& msg.content.get_list_request() == janitor_list_request(key)
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

pub open spec fn st_init(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& janitor_at_step_for(controller_id, key, parent_uid, uid, WidgetJanitorStepView::Init)(s)
        &&& Cluster::no_pending_req_msg(controller_id, s, key)
    }
}

pub open spec fn st_list_req_in_flight(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& janitor_at_step_for(controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterListOuter)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& janitor_list_req_msg(controller_id, key, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_list_req_msg_in_flight(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& janitor_at_step_for(controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterListOuter)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg)
        &&& janitor_list_req_msg(controller_id, key, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn ok_list_resp_for(resp: Message, msg: Message) -> bool {
    &&& resp_msg_matches_req_msg(resp, msg)
    &&& resp.content.get_list_response().res is Ok
}

pub open spec fn st_list_resp_in_flight(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& janitor_at_step_for(controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterListOuter)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& janitor_list_req_msg(controller_id, key, msg)
        &&& exists |resp: Message| #[trigger] s.in_flight().contains(resp) && ok_list_resp_for(resp, msg)
    }
}

pub open spec fn st_list_resp_msg_in_flight(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid, resp: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& janitor_at_step_for(controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterListOuter)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& janitor_list_req_msg(controller_id, key, msg)
        &&& s.in_flight().contains(resp)
        &&& ok_list_resp_for(resp, msg)
    }
}

pub open spec fn st_delete_req_in_flight(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
        &&& janitor_at_step_for(controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterDeleteInner)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        &&& janitor_delete_req_msg(controller_id, key, uid, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_delete_req_msg_in_flight(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& janitor_at_step_for(controller_id, key, parent_uid, uid, WidgetJanitorStepView::AfterDeleteInner)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg)
        &&& janitor_delete_req_msg(controller_id, key, uid, msg)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_terminating(key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    inner_terminating_object(key, uid)
}

// ---------------------------------------------------------------------------
// Eventual facts (the phases).
// ---------------------------------------------------------------------------

// Phase I: failures are eventually disabled.
pub open spec fn phase_i(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::pod_monkey_disabled()(s)
    }
}

// Phase II, per object: the scheduled snapshot for the key is the mirror object
// (or the object is gone); requests and responses of the janitor's reconcile on
// the key are consistent; every List response the janitor holds for the key was
// answered after the parent went absent, so it does not list the parent.
pub open spec fn scheduled_snapshot_ok(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.scheduled_reconciles(controller_id).contains_key(key)
            ==> snapshot_of_mirror(s.scheduled_reconciles(controller_id)[key], key, parent_uid, uid)
    }
}

pub open spec fn list_responses_are_fresh(controller_id: int, key: ObjectRef, parent_uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let reconcile = s.ongoing_reconciles(controller_id)[key];
        let step = WidgetJanitorReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
        s.ongoing_reconciles(controller_id).contains_key(key)
        && step is AfterListOuter
        && snapshot_is_mirror(reconcile.triggering_cr)
        && snapshot_parent(reconcile.triggering_cr) == int_to_string_view(parent_uid)
        && reconcile.pending_req_msg is Some
        ==> forall |resp: Message| {
            &&& #[trigger] s.in_flight().contains(resp)
            &&& ok_list_resp_for(resp, reconcile.pending_req_msg->0)
        } ==> !parent_listed(resp.content.get_list_response().res->Ok_0, int_to_string_view(parent_uid))
    }
}

pub open spec fn phase_ii(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& scheduled_snapshot_ok(controller_id, key, parent_uid, uid)(s) || gone(key, uid)(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& list_responses_are_fresh(controller_id, key, parent_uid)(s)
    }
}

}
