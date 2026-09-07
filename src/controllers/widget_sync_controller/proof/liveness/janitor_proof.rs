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

pub open spec fn scheduled_ok_or_gone(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| scheduled_snapshot_ok(controller_id, key, parent_uid, uid)(s) || gone(key, uid)(s)
}

pub open spec fn phase_ii(controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& scheduled_ok_or_gone(controller_id, key, parent_uid, uid)(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& list_responses_are_fresh(controller_id, key, parent_uid)(s)
    }
}

// ---------------------------------------------------------------------------
// Stability of the object-level facts.
// ---------------------------------------------------------------------------

pub proof fn lemma_next_only_grows_by_fresh_uids(cluster: Cluster, s: ClusterState, s_prime: ClusterState)
    requires cluster.next()(s, s_prime),
    ensures store_only_grows_by_fresh_uids(s, s_prime),
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, input->0);
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

pub proof fn lemma_gone_is_stable(key: ObjectRef, uid: Uid, s: ClusterState, s_prime: ClusterState)
    requires
        gone(key, uid)(s),
        store_only_grows_by_fresh_uids(s, s_prime),
    ensures gone(key, uid)(s_prime),
{
    if s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == Some(uid) {
        if s.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == s.resources()[key].metadata.uid {
            assert(false);
        } else {
            assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
            assert(false);
        }
    }
}

// One step of the cluster keeps the mirror object as it is, or removes it.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_mirror_object_after_step(cluster: Cluster, s: ClusterState, s_prime: ClusterState, key: ObjectRef, parent_uid: Uid, uid: Uid)
    requires
        cluster.next()(s, s_prime),
        cluster.type_is_installed_in_cluster::<InnerWidgetView>(),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime),
        cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s_prime),
        every_mirror_is_bound()(s),
        every_in_flight_inner_update_preserves_identity()(s),
        mirror_object_is(key, parent_uid, uid)(s),
    ensures present_or_gone(key, parent_uid, uid)(s_prime),
{
    let cr = s.resources()[key];
    let inner = InnerWidgetView::unmarshal(cr)->Ok_0;
    assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    assert(cr.kind == InnerWidgetView::kind());
    assert(cr.object_ref() == key);
    assert(key.kind == InnerWidgetView::kind());
    assert(mirror_is_bound(key)(s));
    assert(snapshot_is_mirror(cr));
    assert(snapshot_parent(cr) == parent_uid_annotation(inner));
    assert(janitor_snapshot_is_sound(cr, key)(s));
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            lemma_snapshot_soundness_preserved_by_api_server_step(cluster, s, s_prime, msg, cr, key);
            lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
            if s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == Some(uid) {
                lemma_well_formed_inner_unmarshals(cluster, s_prime, key);
                let new_obj = s_prime.resources()[key];
                let new_inner = InnerWidgetView::unmarshal(new_obj)->Ok_0;
                assert(preserves_mirror_identity(cr.metadata, new_obj.metadata));
                assert(new_inner.metadata == new_obj.metadata);
                assert(has_mirror_identity(new_inner));
                assert(parent_uid_annotation(new_inner) == parent_uid_annotation(inner));
                assert(mirror_object_is(key, parent_uid, uid)(s_prime));
            } else {
                assert(uid < s.api_server.uid_counter);
                assert(gone(key, uid)(s_prime));
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
            assert(mirror_object_is(key, parent_uid, uid)(s_prime));
        },
    }
}

// Once the mirror object is there it stays there as that mirror until it is
// removed, and it never comes back.
pub proof fn lemma_mirror_leads_to_always_present_or_gone(
    spec: TempPred<ClusterState>, cluster: Cluster, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<InnerWidgetView>(),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()))),
        spec.entails(always(lift_state(every_mirror_is_bound()))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity()))),
    ensures spec.entails(lift_state(mirror_object_is(key, parent_uid, uid)).leads_to(always(lift_state(present_or_gone(key, parent_uid, uid))))),
{
    let post = present_or_gone(key, parent_uid, uid);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime)
        &&& cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()(s_prime)
        &&& every_mirror_is_bound()(s)
        &&& every_in_flight_inner_update_preserves_identity()(s)
    };
    always_to_always_later(spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_to_always_later(spec, lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>()));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        later(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        later(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<InnerWidgetView>())),
        lift_state(every_mirror_is_bound()),
        lift_state(every_in_flight_inner_update_preserves_identity())
    );
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        if mirror_object_is(key, parent_uid, uid)(s) {
            lemma_mirror_object_after_step(cluster, s, s_prime, key, parent_uid, uid);
        } else {
            lemma_next_only_grows_by_fresh_uids(cluster, s, s_prime);
            lemma_gone_is_stable(key, uid, s, s_prime);
        }
    }
    entails_implies_leads_to(spec, lift_state(mirror_object_is(key, parent_uid, uid)), lift_state(post));
    leads_to_stable(spec, lift_action(stronger_next), lift_state(mirror_object_is(key, parent_uid, uid)), lift_state(post));
}

// ---------------------------------------------------------------------------
// Phase I: failures are eventually disabled for good.
// ---------------------------------------------------------------------------

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
// Phase II (a): the scheduled snapshot for the key is the mirror object.
// ---------------------------------------------------------------------------

// Scheduling copies the stored object; while the mirror is there, that is the
// mirror. The schedule action is always enabled while the object exists, so no
// termination argument is needed.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_true_leads_to_always_scheduled_ok_or_gone(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(present_or_gone(key, parent_uid, uid)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(scheduled_ok_or_gone(controller_id, key, parent_uid, uid))))),
{
    let ok = scheduled_snapshot_ok(controller_id, key, parent_uid, uid);
    let q = present_or_gone(key, parent_uid, uid);
    let post = scheduled_ok_or_gone(controller_id, key, parent_uid, uid);
    let pre = |s: ClusterState| mirror_object_is(key, parent_uid, uid)(s) && !ok(s);
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
    assert forall |s: ClusterState| mirror_object_is(key, parent_uid, uid)(s) && Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    implies #[trigger] snapshot_of_mirror(s.resources()[key], key, parent_uid, uid) by {
        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        assert(q(s_prime));
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.schedule_controller_reconcile().forward((controller_id, key))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
        assert(snapshot_of_mirror(s.resources()[key], key, parent_uid, uid));
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
            lemma_gone_is_stable(key, uid, s, s_prime);
        } else {
            assert(mirror_object_is(key, parent_uid, uid)(s));
            assert(ok(s));
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ScheduleControllerReconcileStep(input) => {
                    if input.0 == controller_id && input.1 == key {
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
                        assert(snapshot_of_mirror(s.resources()[key], key, parent_uid, uid));
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
pub proof fn lemma_list_answered_while_parent_absent(s: ClusterState, req: ListRequest, key: ObjectRef, parent_uid: Uid)
    requires
        parent_absent(key, parent_uid)(s),
        parent_uid_string_is_bound_to_key(int_to_string_view(parent_uid), outer_key_of(key))(s),
    ensures !parent_listed(handle_list_request(req, s.api_server).res->Ok_0, int_to_string_view(parent_uid)),
{
    let parent = int_to_string_view(parent_uid);
    let selected = s.resources().values().filter(|o: DynamicObjectView| {
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    });
    let objs = selected.to_seq();
    assert(handle_list_request(req, s.api_server).res->Ok_0 == objs);
    if parent_listed(objs, parent) {
        let i = choose |i: int| 0 <= i < objs.len()
            && (#[trigger] objs[i]).metadata.uid is Some
            && int_to_string_view(objs[i].metadata.uid->0) == parent;
        let o = objs[i];
        assert(objs.contains(o));
        lemma_set_to_seq_contains_all_elements(selected);
        assert(selected.contains(o));
        assert(s.resources().values().contains(o));
        let k = choose |k: ObjectRef| #[trigger] s.resources().dom().contains(k) && s.resources()[k] == o;
        assert(s.resources().contains_key(k));
        assert(k == outer_key_of(key));
        int_to_string_view_injectivity();
        assert(o.metadata.uid->0 == parent_uid);
        assert(false);
    }
}

#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
pub proof fn lemma_list_responses_are_fresh_preserved(
    cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, s: ClusterState, s_prime: ClusterState
)
    requires
        key.kind == InnerWidgetView::kind(),
        cluster.next()(s, s_prime),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        Cluster::crash_disabled(controller_id)(s),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s),
        Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id)(s),
        janitor_triggering_crs_are_sound(controller_id)(s),
        janitor_decisions_are_sound(controller_id)(s),
        parent_absent(key, parent_uid)(s),
        list_responses_are_fresh(controller_id, key, parent_uid)(s),
    ensures list_responses_are_fresh(controller_id, key, parent_uid)(s_prime),
{
    let parent = int_to_string_view(parent_uid);
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    InnerWidgetView::marshal_preserves_integrity();
    if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
        let reconcile_prime = s_prime.ongoing_reconciles(controller_id)[key];
        let step_prime = WidgetJanitorReconcileState::unmarshal(reconcile_prime.local_state)->Ok_0.reconcile_step;
        if step_prime is AfterListOuter
            && snapshot_is_mirror(reconcile_prime.triggering_cr)
            && snapshot_parent(reconcile_prime.triggering_cr) == parent
            && reconcile_prime.pending_req_msg is Some
        {
            let pending = reconcile_prime.pending_req_msg->0;
            assert forall |resp: Message| {
                &&& #[trigger] s_prime.in_flight().contains(resp)
                &&& ok_list_resp_for(resp, pending)
            } implies !parent_listed(resp.content.get_list_response().res->Ok_0, parent) by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        let msg = input->0;
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        let reconcile = s.ongoing_reconciles(controller_id)[key];
                        assert(janitor_reconcile_is_sound(controller_id, key)(s));
                        assert(pending.content.is_list_request());
                        if !s.in_flight().contains(resp) {
                            assert(resp == transition_by_etcd(cluster.installed_types, msg, s.api_server).1);
                            assert(resp.content->APIResponse_0 is ListResponse);
                            match msg.content->APIRequest_0 {
                                APIRequest::ListRequest(req) => {
                                    assert(resp.content.get_list_response() == handle_list_request(req, s.api_server));
                                    assert(janitor_snapshot_is_sound(reconcile.triggering_cr, key)(s));
                                    assert(parent_uid_string_is_bound_to_key(parent, outer_key_of(key))(s));
                                    lemma_list_answered_while_parent_absent(s, req, key, parent_uid);
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
                        assert(janitor_reconcile_is_sound(controller_id, key)(s));
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

pub proof fn lemma_true_leads_to_always_list_responses_are_fresh(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))),
        spec.entails(always(lift_state(Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id)))),
        spec.entails(always(lift_state(janitor_triggering_crs_are_sound(controller_id)))),
        spec.entails(always(lift_state(janitor_decisions_are_sound(controller_id)))),
        spec.entails(always(lift_state(parent_absent(key, parent_uid)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(list_responses_are_fresh(controller_id, key, parent_uid))))),
{
    let post = list_responses_are_fresh(controller_id, key, parent_uid);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id)(s)
        &&& janitor_triggering_crs_are_sound(controller_id)(s)
        &&& janitor_decisions_are_sound(controller_id)(s)
        &&& parent_absent(key, parent_uid)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::cr_states_are_unmarshallable::<WidgetJanitorReconcileState, InnerWidgetView>(controller_id)),
        lift_state(janitor_triggering_crs_are_sound(controller_id)),
        lift_state(janitor_decisions_are_sound(controller_id)),
        lift_state(parent_absent(key, parent_uid))
    );
    entails_implies_leads_to(spec, lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    leads_to_trans(spec, true_pred(), lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        lemma_list_responses_are_fresh_preserved(cluster, controller_id, key, parent_uid, s, s_prime);
    }
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(post));
}


// ---------------------------------------------------------------------------
// The walk through the janitor's reconcile, one step per lemma. Each step is a
// WF1 application; "or gone" absorbs the removal of the object by anyone else.
// ---------------------------------------------------------------------------

// idle ~> scheduled \/ gone: the schedule action is enabled while the object exists.
pub proof fn lemma_idle_leads_to_scheduled_or_gone(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(present_or_gone(key, parent_uid, uid)))),
    ensures
        spec.entails(lift_state(st_idle(controller_id, key))
            .leads_to(lift_state(st_scheduled(controller_id, key)).or(lift_state(gone(key, uid))))),
{
    let q = present_or_gone(key, parent_uid, uid);
    let idle = st_idle(controller_id, key);
    let scheduled = st_scheduled(controller_id, key);
    let g = gone(key, uid);
    let pre = |s: ClusterState| idle(s) && !scheduled(s) && mirror_object_is(key, parent_uid, uid)(s);
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
            assert(mirror_object_is(key, parent_uid, uid)(s_prime));
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
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_scheduled_leads_to_init_or_gone(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(scheduled_ok_or_gone(controller_id, key, parent_uid, uid)))),
    ensures
        spec.entails(lift_state(st_scheduled(controller_id, key))
            .leads_to(lift_state(st_init(controller_id, key, parent_uid, uid)).or(lift_state(gone(key, uid))))),
{
    let pre = st_scheduled(controller_id, key);
    let init = st_init(controller_id, key, parent_uid, uid);
    let g = gone(key, uid);
    let post = |s: ClusterState| init(s) || g(s);
    let input = (None::<Message>, Some(key));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& scheduled_ok_or_gone(controller_id, key, parent_uid, uid)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(scheduled_ok_or_gone(controller_id, key, parent_uid, uid))
    );
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        lemma_next_only_grows_by_fresh_uids(cluster, s, s_prime);
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
            // The scheduled reconcile of the key was run.
            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg is None);
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == reconcile_init_state().marshal());
            if g(s) {
                lemma_gone_is_stable(key, uid, s, s_prime);
            } else {
                assert(scheduled_snapshot_ok(controller_id, key, parent_uid, uid)(s));
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
        assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == reconcile_init_state().marshal());
        if g(s) {
            lemma_gone_is_stable(key, uid, s, s_prime);
        } else {
            assert(scheduled_snapshot_ok(controller_id, key, parent_uid, uid)(s));
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
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_init_leads_to_list_req_in_flight(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
    ensures
        spec.entails(lift_state(st_init(controller_id, key, parent_uid, uid))
            .leads_to(lift_state(st_list_req_in_flight(controller_id, key, parent_uid, uid)))),
{
    let pre = st_init(controller_id, key, parent_uid, uid);
    let post = st_list_req_in_flight(controller_id, key, parent_uid, uid);
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
    InnerWidgetView::marshal_preserves_integrity();
    // What the janitor sends from Init on a mirror snapshot.
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        let inner = InnerWidgetView::unmarshal(cr)->Ok_0;
        assert(has_mirror_identity(inner));
        assert(inner.metadata.namespace->0 == key.namespace);
        let req = APIRequest::ListRequest(ListRequest { kind: OuterWidgetView::kind(), namespace: inner.metadata.namespace->0 });
        let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
        assert(s_prime.in_flight().contains(msg));
        assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == at_step(WidgetJanitorStepView::AfterListOuter).marshal());
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
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_list_req_leads_to_list_resp(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)))),
    ensures
        spec.entails(lift_state(st_list_req_in_flight(controller_id, key, parent_uid, uid))
            .leads_to(lift_state(st_list_resp_in_flight(controller_id, key, parent_uid, uid)))),
{
    let post = st_list_resp_in_flight(controller_id, key, parent_uid, uid);
    let pre_of = |msg: Message| lift_state(st_list_req_msg_in_flight(controller_id, key, parent_uid, uid, msg));
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
        let pre = st_list_req_msg_in_flight(controller_id, key, parent_uid, uid, msg);
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
    assert_by(tla_exists(pre_of) == lift_state(st_list_req_in_flight(controller_id, key, parent_uid, uid)), {
        assert forall |ex| #[trigger] lift_state(st_list_req_in_flight(controller_id, key, parent_uid, uid)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let msg = ex.head().ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_list_req_in_flight(controller_id, key, parent_uid, uid)));
    });
}

// An Ok List response in flight ~> the Delete is in flight. The response was
// answered while the parent was absent (phase II), so the janitor deletes.
#[verifier(rlimit(300))]
#[verifier(spinoff_prover)]
pub proof fn lemma_list_resp_leads_to_delete_req_in_flight(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(list_responses_are_fresh(controller_id, key, parent_uid)))),
    ensures
        spec.entails(lift_state(st_list_resp_in_flight(controller_id, key, parent_uid, uid))
            .leads_to(lift_state(st_delete_req_in_flight(controller_id, key, parent_uid, uid)))),
{
    let post = st_delete_req_in_flight(controller_id, key, parent_uid, uid);
    let pre_of = |resp: Message| lift_state(st_list_resp_msg_in_flight(controller_id, key, parent_uid, uid, resp));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& list_responses_are_fresh(controller_id, key, parent_uid)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(list_responses_are_fresh(controller_id, key, parent_uid))
    );
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    InnerWidgetView::marshal_preserves_integrity();
    assert forall |resp: Message| spec.entails(#[trigger] pre_of(resp).leads_to(lift_state(post))) by {
        let pre = st_list_resp_msg_in_flight(controller_id, key, parent_uid, uid, resp);
        let input = (Some(resp), Some(key));
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
            let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
            let inner = InnerWidgetView::unmarshal(cr)->Ok_0;
            let objs = resp.content.get_list_response().res->Ok_0;
            assert(has_mirror_identity(inner));
            assert(parent_uid_annotation(inner) == int_to_string_view(parent_uid));
            assert(!parent_listed(objs, int_to_string_view(parent_uid)));
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
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == at_step(WidgetJanitorStepView::AfterDeleteInner).marshal());
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
    assert_by(tla_exists(pre_of) == lift_state(st_list_resp_in_flight(controller_id, key, parent_uid, uid)), {
        assert forall |ex| #[trigger] lift_state(st_list_resp_in_flight(controller_id, key, parent_uid, uid)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            let resp = choose |resp: Message| #[trigger] s.in_flight().contains(resp) && ok_list_resp_for(resp, msg);
            assert(pre_of(resp).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_list_resp_in_flight(controller_id, key, parent_uid, uid)));
    });
}

// The Delete in flight ~> the object is terminating or gone.
#[verifier(rlimit(300))]
#[verifier(spinoff_prover)]
pub proof fn lemma_delete_req_leads_to_terminating_or_gone(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)))),
        spec.entails(always(lift_state(present_or_gone(key, parent_uid, uid)))),
    ensures
        spec.entails(lift_state(st_delete_req_in_flight(controller_id, key, parent_uid, uid))
            .leads_to(lift_state(st_terminating(key, uid)).or(lift_state(gone(key, uid))))),
{
    let g = gone(key, uid);
    let post = |s: ClusterState| st_terminating(key, uid)(s) || g(s);
    let pre_of = |msg: Message| lift_state(st_delete_req_msg_in_flight(controller_id, key, parent_uid, uid, msg));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& present_or_gone(key, parent_uid, uid)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)),
        lift_state(present_or_gone(key, parent_uid, uid))
    );
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_delete_req_msg_in_flight(controller_id, key, parent_uid, uid, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
            if g(s) {
                lemma_gone_is_stable(key, uid, s, s_prime);
            } else {
                assert(mirror_object_is(key, parent_uid, uid)(s));
                assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                let req = msg.content.get_delete_request();
                assert(req.key == key);
                assert(delete_request_admission_check(req, s.api_server) is None);
                let obj = s.resources()[key];
                if obj.metadata.finalizers is Some && obj.metadata.finalizers->0.len() > 0 {
                    assert(s_prime.resources().contains_key(key));
                    assert(s_prime.resources()[key].metadata.uid == Some(uid));
                    assert(s_prime.resources()[key].metadata.deletion_timestamp is Some);
                    assert(st_terminating(key, uid)(s_prime));
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
    assert_by(tla_exists(pre_of) == lift_state(st_delete_req_in_flight(controller_id, key, parent_uid, uid)), {
        assert forall |ex| #[trigger] lift_state(st_delete_req_in_flight(controller_id, key, parent_uid, uid)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let msg = ex.head().ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_delete_req_in_flight(controller_id, key, parent_uid, uid)));
    });
    temp_pred_equality(lift_state(post), lift_state(st_terminating(key, uid)).or(lift_state(g)));
}


// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

// spec |= p /\ q gives spec |= p and spec |= q.
pub proof fn entails_and_split(spec: TempPred<ClusterState>, p: TempPred<ClusterState>, q: TempPred<ClusterState>)
    requires spec.entails(p.and(q)),
    ensures spec.entails(p), spec.entails(q),
{
    assert(p.and(q).entails(p));
    assert(p.and(q).entails(q));
    entails_trans(spec, p.and(q), p);
    entails_trans(spec, p.and(q), q);
}

// The facts of the stable spec that the step lemmas use, spelled out.
#[verifier(rlimit(400))]
#[verifier(spinoff_prover)]
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

// The stable spec together with the premise of R3 for one object, made stable.
pub open spec fn janitor_spec_with_object(cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> TempPred<ClusterState> {
    janitor_stable_spec(cluster, controller_id)
    .and(always(lift_state(parent_absent(key, parent_uid))).and(always(lift_state(present_or_gone(key, parent_uid, uid)))))
}

pub proof fn janitor_spec_with_object_is_stable(cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid)
    ensures valid(stable(janitor_spec_with_object(cluster, controller_id, key, parent_uid, uid))),
{
    janitor_stable_spec_is_stable(cluster, controller_id);
    always_p_is_stable(lift_state(parent_absent(key, parent_uid)));
    always_p_is_stable(lift_state(present_or_gone(key, parent_uid, uid)));
    stable_and_n!(always(lift_state(parent_absent(key, parent_uid))), always(lift_state(present_or_gone(key, parent_uid, uid))));
    stable_and_n!(
        janitor_stable_spec(cluster, controller_id),
        always(lift_state(parent_absent(key, parent_uid))).and(always(lift_state(present_or_gone(key, parent_uid, uid))))
    );
}

pub open spec fn janitor_spec_with_phase_i(cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> TempPred<ClusterState> {
    janitor_spec_with_object(cluster, controller_id, key, parent_uid, uid).and(always(lift_state(phase_i(controller_id))))
}

pub proof fn janitor_spec_with_phase_i_is_stable(cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid)
    ensures valid(stable(janitor_spec_with_phase_i(cluster, controller_id, key, parent_uid, uid))),
{
    janitor_spec_with_object_is_stable(cluster, controller_id, key, parent_uid, uid);
    always_p_is_stable(lift_state(phase_i(controller_id)));
    stable_and_n!(janitor_spec_with_object(cluster, controller_id, key, parent_uid, uid), always(lift_state(phase_i(controller_id))));
}

pub open spec fn janitor_spec_with_phases(cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid) -> TempPred<ClusterState> {
    janitor_spec_with_phase_i(cluster, controller_id, key, parent_uid, uid).and(always(lift_state(phase_ii(controller_id, key, parent_uid, uid))))
}

// Under the stable spec, the premise and phase I: phase II eventually holds forever.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_true_leads_to_always_phase_ii(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(janitor_spec_with_phase_i(cluster, controller_id, key, parent_uid, uid)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(phase_ii(controller_id, key, parent_uid, uid))))),
{
    let spec_o = janitor_spec_with_object(cluster, controller_id, key, parent_uid, uid);
    entails_and_split(spec, spec_o, always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, janitor_stable_spec(cluster, controller_id), always(lift_state(parent_absent(key, parent_uid))).and(always(lift_state(present_or_gone(key, parent_uid, uid)))));
    entails_and_split(spec, always(lift_state(parent_absent(key, parent_uid))), always(lift_state(present_or_gone(key, parent_uid, uid))));
    lemma_janitor_stable_spec_facts(spec, cluster, controller_id);
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_tla_forall_apply(spec, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), key);

    // Termination of every reconcile of the janitor.
    terminate::janitor_reconcile_eventually_terminates(spec, cluster, controller_id);
    let idle_of = |key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)));
    spec_entails_tla_forall_apply(spec, idle_of, key);
    let idle_of_alt = |key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !(s.ongoing_reconciles(controller_id).contains_key(key))));
    assert forall |key: ObjectRef| #[trigger] idle_of(key) == idle_of_alt(key) by {
        temp_pred_equality(idle_of(key), idle_of_alt(key));
    }
    tla_forall_p_tla_forall_q_equality(idle_of, idle_of_alt);

    lemma_true_leads_to_always_scheduled_ok_or_gone(spec, cluster, controller_id, key, parent_uid, uid);
    cluster.lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(spec, controller_id, key);
    lemma_true_leads_to_always_list_responses_are_fresh(spec, cluster, controller_id, key, parent_uid);
    leads_to_always_and(
        spec, true_pred(),
        lift_state(scheduled_ok_or_gone(controller_id, key, parent_uid, uid)),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key))
    );
    leads_to_always_and(
        spec, true_pred(),
        lift_state(scheduled_ok_or_gone(controller_id, key, parent_uid, uid))
            .and(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key))),
        lift_state(list_responses_are_fresh(controller_id, key, parent_uid))
    );
    temp_pred_equality(
        lift_state(phase_ii(controller_id, key, parent_uid, uid)),
        lift_state(scheduled_ok_or_gone(controller_id, key, parent_uid, uid))
            .and(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)))
            .and(lift_state(list_responses_are_fresh(controller_id, key, parent_uid)))
    );
}

// Under the stable spec, the premise and both phases: the object is eventually gone.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_true_leads_to_gone_under_phases(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(janitor_spec_with_phases(cluster, controller_id, key, parent_uid, uid)),
    ensures spec.entails(true_pred().leads_to(lift_state(object_is_gone(key, uid)))),
{
    let phase_ii_state = phase_ii(controller_id, key, parent_uid, uid);
    entails_and_split(spec, janitor_spec_with_phase_i(cluster, controller_id, key, parent_uid, uid), always(lift_state(phase_ii_state)));
    entails_and_split(spec, janitor_spec_with_object(cluster, controller_id, key, parent_uid, uid), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, janitor_stable_spec(cluster, controller_id), always(lift_state(parent_absent(key, parent_uid))).and(always(lift_state(present_or_gone(key, parent_uid, uid)))));
    entails_and_split(spec, always(lift_state(parent_absent(key, parent_uid))), always(lift_state(present_or_gone(key, parent_uid, uid))));
    lemma_janitor_stable_spec_facts(spec, cluster, controller_id);
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::crash_disabled(controller_id)));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(controller_id)), lift_state(Cluster::pod_monkey_disabled()));
    always_weaken(spec, lift_state(phase_ii_state), lift_state(scheduled_ok_or_gone(controller_id, key, parent_uid, uid)));
    always_weaken(spec, lift_state(phase_ii_state), lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)));
    always_weaken(spec, lift_state(phase_ii_state), lift_state(list_responses_are_fresh(controller_id, key, parent_uid)));

    // true ~> idle
    terminate::janitor_reconcile_eventually_terminates(spec, cluster, controller_id);
    spec_entails_tla_forall_apply(spec, |key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key))), key);

    let idle = lift_state(st_idle(controller_id, key));
    let scheduled = lift_state(st_scheduled(controller_id, key));
    let init = lift_state(st_init(controller_id, key, parent_uid, uid));
    let list_req = lift_state(st_list_req_in_flight(controller_id, key, parent_uid, uid));
    let list_resp = lift_state(st_list_resp_in_flight(controller_id, key, parent_uid, uid));
    let delete_req = lift_state(st_delete_req_in_flight(controller_id, key, parent_uid, uid));
    let terminating = lift_state(st_terminating(key, uid));
    let g = lift_state(gone(key, uid));
    let target = lift_state(object_is_gone(key, uid));

    lemma_idle_leads_to_scheduled_or_gone(spec, cluster, controller_id, key, parent_uid, uid);
    lemma_scheduled_leads_to_init_or_gone(spec, cluster, controller_id, key, parent_uid, uid);
    lemma_init_leads_to_list_req_in_flight(spec, cluster, controller_id, key, parent_uid, uid);
    lemma_list_req_leads_to_list_resp(spec, cluster, controller_id, key, parent_uid, uid);
    lemma_list_resp_leads_to_delete_req_in_flight(spec, cluster, controller_id, key, parent_uid, uid);
    lemma_delete_req_leads_to_terminating_or_gone(spec, cluster, controller_id, key, parent_uid, uid);
    // D3 for this object.
    spec_entails_tla_forall_apply(
        spec,
        |i: (ObjectRef, Uid)| lift_state(inner_terminating_object(i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1))),
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
pub proof fn lemma_object_leads_to_gone(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        key.kind == InnerWidgetView::kind(),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(janitor_spec_with_object(cluster, controller_id, key, parent_uid, uid)),
    ensures spec.entails(true_pred().leads_to(lift_state(object_is_gone(key, uid)))),
{
    let target = lift_state(object_is_gone(key, uid));
    let spec_o = janitor_spec_with_object(cluster, controller_id, key, parent_uid, uid);
    let spec_i = janitor_spec_with_phase_i(cluster, controller_id, key, parent_uid, uid);
    let spec_ii = janitor_spec_with_phases(cluster, controller_id, key, parent_uid, uid);
    let phase_i_temp = always(lift_state(phase_i(controller_id)));
    let phase_ii_temp = always(lift_state(phase_ii(controller_id, key, parent_uid, uid)));

    // Under both phases.
    assert(spec_ii.entails(spec_ii));
    lemma_true_leads_to_gone_under_phases(spec_ii, cluster, controller_id, key, parent_uid, uid);
    // Move phase II from the spec to the premise.
    janitor_spec_with_phase_i_is_stable(cluster, controller_id, key, parent_uid, uid);
    unpack_conditions_from_spec(spec_i, phase_ii_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_ii_temp), phase_ii_temp);
    assert(spec_i.entails(spec_i));
    lemma_true_leads_to_always_phase_ii(spec_i, cluster, controller_id, key, parent_uid, uid);
    leads_to_trans(spec_i, true_pred(), phase_ii_temp, target);
    // Move phase I from the spec to the premise.
    janitor_spec_with_object_is_stable(cluster, controller_id, key, parent_uid, uid);
    unpack_conditions_from_spec(spec_o, phase_i_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_i_temp), phase_i_temp);
    assert(spec_o.entails(spec_o));
    lemma_janitor_stable_spec_facts(spec_o, cluster, controller_id);
    lemma_true_leads_to_always_phase_i(spec_o, cluster, controller_id);
    leads_to_trans(spec_o, true_pred(), phase_i_temp, target);
    entails_trans(spec, spec_o, true_pred().leads_to(target));
}

// R3 for one object under the stable spec.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
pub proof fn lemma_mirror_eventually_collected_per_object(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, parent_uid: Uid, uid: Uid
)
    requires
        spec.entails(janitor_stable_spec(cluster, controller_id)),
        cluster.type_is_installed_in_cluster::<InnerWidgetView>(),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
    ensures spec.entails(widget_mirror_eventually_collected_per_object(key, parent_uid, uid)),
{
    let stable_spec = janitor_stable_spec(cluster, controller_id);
    let p = lift_state(parent_absent(key, parent_uid));
    let m = lift_state(mirror_object_is(key, parent_uid, uid));
    let q = lift_state(present_or_gone(key, parent_uid, uid));
    let target = lift_state(object_is_gone(key, uid));
    assert(stable_spec.entails(stable_spec));
    lemma_janitor_stable_spec_facts(stable_spec, cluster, controller_id);
    if key.kind != InnerWidgetView::kind() {
        // A mirror object never sits at a key of another kind.
        let wf = lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed());
        assert forall |ex: Execution<ClusterState>| !(#[trigger] always(p).and(m).and(wf).satisfied_by(ex)) by {
            if m.satisfied_by(ex) && wf.satisfied_by(ex) {
                let s = ex.head();
                assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                assert(s.resources()[key].kind == InnerWidgetView::kind());
                assert(s.resources()[key].object_ref() == key);
                assert(false);
            }
        }
        temp_pred_equality(always(p).and(m).and(wf), false_pred());
        vacuous_leads_to(stable_spec, always(p).and(m), target, wf);
    } else {
        lemma_mirror_leads_to_always_present_or_gone(stable_spec, cluster, key, parent_uid, uid);
        leads_to_with_always(stable_spec, m, always(q), p);
        let spec_o = janitor_spec_with_object(cluster, controller_id, key, parent_uid, uid);
        assert(spec_o.entails(spec_o));
        lemma_object_leads_to_gone(spec_o, cluster, controller_id, key, parent_uid, uid);
        janitor_stable_spec_is_stable(cluster, controller_id);
        unpack_conditions_from_spec(stable_spec, always(p).and(always(q)), true_pred(), target);
        temp_pred_equality(true_pred().and(always(p).and(always(q))), always(q).and(always(p)));
        leads_to_trans(stable_spec, m.and(always(p)), always(q).and(always(p)), target);
        temp_pred_equality(always(p).and(m), m.and(always(p)));
    }
    entails_trans(spec, stable_spec, always(p).and(m).leads_to(target));
}

// R3: the janitor eventually removes every mirror whose parent is gone for good.
pub proof fn janitor_eventually_collects_mirrors(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(janitor_next_with_wf(cluster, controller_id)),
        cluster.type_is_installed_in_cluster::<InnerWidgetView>(),
        cluster.type_is_installed_in_cluster::<OuterWidgetView>(),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(always(lifted_janitor_rely_condition(cluster, controller_id))),
        spec.entails(inner_releases_terminating_objects()),
    ensures spec.entails(widget_mirrors_eventually_collected()),
{
    assert(janitor_next_with_wf(cluster, controller_id).entails(always(lift_action(cluster.next()))));
    entails_trans(spec, janitor_next_with_wf(cluster, controller_id), always(lift_action(cluster.next())));
    janitor_invariants_hold(spec, cluster, controller_id);
    entails_and_n!(
        spec,
        janitor_next_with_wf(cluster, controller_id),
        always(lifted_janitor_rely_condition(cluster, controller_id)),
        inner_releases_terminating_objects(),
        janitor_invariants(cluster, controller_id)
    );
    let per_object = |i: (ObjectRef, Uid, Uid)| widget_mirror_eventually_collected_per_object(i.0, i.1, i.2);
    assert forall |i: (ObjectRef, Uid, Uid)| spec.entails(#[trigger] per_object(i)) by {
        lemma_mirror_eventually_collected_per_object(spec, cluster, controller_id, i.0, i.1, i.2);
    }
    spec_entails_tla_forall(spec, per_object);
}

}
