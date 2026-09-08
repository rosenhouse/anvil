// Every reconcile of either Widget reconciler terminates: for every key,
// true ~> the reconciler is idle on that key. Both reconcilers are straight-line
// state machines with at most one pending request per step, so termination is a
// chain of the cluster's generic step lemmas.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::temporal_rules::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::widget_sync_controller::{
    model::{install::*, janitor_reconciler::*, sync_reconciler::*},
    proof::predicate::*,
    trusted::{liveness_theorem::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The sync reconciler.
// ---------------------------------------------------------------------------

pub proof fn sync_reconcile_eventually_terminates(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(controller_id)))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError)))))),
    ensures
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key))))),
{
    let post = |key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)));
    assert forall |key: ObjectRef| spec.entails(#[trigger] post(key)) by {
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), key);
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))), key);
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner))), key);
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner))), key);
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner))), key);
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus))), key);
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError))), key);
        if key.kind == OuterWidgetView::kind() {
            sync_reconcile_eventually_terminates_on_key(spec, cluster, controller_id, key);
        } else {
            // The sync reconciler only ever reconciles keys of its own kind.
            always_weaken(
                spec,
                lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<OuterWidgetView>(controller_id)),
                lift_state(Cluster::reconcile_idle(controller_id, key))
            );
            always_to_true_leads_to(spec, lift_state(Cluster::reconcile_idle(controller_id, key)));
        }
    }
    spec_entails_tla_forall(spec, post);
}

pub proof fn sync_reconcile_eventually_terminates_on_key(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef
)
    requires
        key.kind == OuterWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))),
        spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError))))),
    ensures
        spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)))),
{
    let idle = lift_state(Cluster::reconcile_idle(controller_id, key));
    WidgetSyncReconcileState::marshal_preserves_integrity();
    OuterWidgetView::marshal_preserves_integrity();

    // Done and Error end the reconcile.
    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, key);
    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, key);
    temp_pred_equality(
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Done)),
        lift_state(cluster.reconciler_reconcile_done(controller_id, key))
    );
    temp_pred_equality(
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Error)),
        lift_state(cluster.reconciler_reconcile_error(controller_id, key))
    );
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, key, sync_step_is_terminal())),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Done)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Error));
        idle
    );

    // The status write of the outer copy, and the one that reports a failure, end
    // in Done or Error whatever the response is.
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchOuterStatus), sync_step_is_terminal());
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterReportError), sync_step_is_terminal());

    // The Create and the Patch of the mirror end in Done, or report their failure first.
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, key, sync_step_after_mirror_write())),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterReportError)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Done)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Error));
        idle
    );
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterCreateInner), sync_step_after_mirror_write());
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterPatchInner), sync_step_after_mirror_write());

    // After the Get of the mirror, the reconciler is at one of those steps, or done.
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, key, sync_step_after_get_inner())),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterCreateInner)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterPatchInner)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterPatchOuterStatus)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterReportError)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Done)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Error));
        idle
    );
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::AfterGetInner), sync_step_after_get_inner());

    // Init sends the Get.
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(spec, controller_id, key, at_sync_step_closure(WidgetSyncStepView::Init), at_sync_step_closure(WidgetSyncStepView::AfterGetInner));

    // Every state is idle or at one of the steps.
    entails_implies_leads_to(spec, idle, idle);
    lemma_true_equal_to_sync_idle_or_at_any_step(controller_id, key);
    or_leads_to_combine_and_equality!(
        spec, true_pred(),
        idle,
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Init)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterGetInner)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterCreateInner)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterPatchInner)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterPatchOuterStatus)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterReportError)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Done)),
        lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Error));
        idle
    );
}

proof fn lemma_true_equal_to_sync_idle_or_at_any_step(controller_id: int, key: ObjectRef)
    ensures
        true_pred::<ClusterState>() == lift_state(Cluster::reconcile_idle(controller_id, key))
            .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Init)))
            .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterGetInner)))
            .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterCreateInner)))
            .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterPatchInner)))
            .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterPatchOuterStatus)))
            .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterReportError)))
            .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Done)))
            .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Error))),
{
    let rhs = lift_state(Cluster::reconcile_idle(controller_id, key))
        .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Init)))
        .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterGetInner)))
        .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterCreateInner)))
        .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterPatchInner)))
        .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterPatchOuterStatus)))
        .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::AfterReportError)))
        .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Done)))
        .or(lift_state(at_sync_step(controller_id, key, WidgetSyncStepView::Error)));
    assert forall |ex| #![auto] true_pred::<ClusterState>().satisfied_by(ex) implies rhs.satisfied_by(ex) by {
        let s = ex.head();
        if s.ongoing_reconciles(controller_id).contains_key(key) {
            let step = WidgetSyncReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap().reconcile_step;
            match step {
                WidgetSyncStepView::Init => {},
                WidgetSyncStepView::AfterGetInner => {},
                WidgetSyncStepView::AfterCreateInner => {},
                WidgetSyncStepView::AfterPatchInner => {},
                WidgetSyncStepView::AfterPatchOuterStatus => {},
                WidgetSyncStepView::AfterReportError => {},
                WidgetSyncStepView::Done => {},
                WidgetSyncStepView::Error => {},
            }
        }
    }
    temp_pred_equality(true_pred::<ClusterState>(), rhs);
}

// ---------------------------------------------------------------------------
// The janitor reconciler.
// ---------------------------------------------------------------------------

pub proof fn janitor_reconcile_eventually_terminates(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int
)
    requires
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(controller_id)))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter)))))),
        spec.entails(always(tla_forall(|key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner)))))),
    ensures
        spec.entails(tla_forall(|key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key))))),
{
    let post = |key: ObjectRef| true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)));
    assert forall |key: ObjectRef| spec.entails(#[trigger] post(key)) by {
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)), key);
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init))), key);
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter))), key);
        always_tla_forall_apply::<ClusterState, ObjectRef>(spec, |key: ObjectRef| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner))), key);
        if key.kind == InnerWidgetView::kind() {
            janitor_reconcile_eventually_terminates_on_key(spec, cluster, controller_id, key);
        } else {
            always_weaken(
                spec,
                lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<InnerWidgetView>(controller_id)),
                lift_state(Cluster::reconcile_idle(controller_id, key))
            );
            always_to_true_leads_to(spec, lift_state(Cluster::reconcile_idle(controller_id, key)));
        }
    }
    spec_entails_tla_forall(spec, post);
}

pub proof fn janitor_reconcile_eventually_terminates_on_key(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef
)
    requires
        key.kind == InnerWidgetView::kind(),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model()),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))),
        spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner))))),
    ensures
        spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)))),
{
    let idle = lift_state(Cluster::reconcile_idle(controller_id, key));
    WidgetJanitorReconcileState::marshal_preserves_integrity();
    InnerWidgetView::marshal_preserves_integrity();

    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, key);
    cluster.lemma_reconcile_error_leads_to_reconcile_idle(spec, controller_id, key);
    temp_pred_equality(
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Done)),
        lift_state(cluster.reconciler_reconcile_done(controller_id, key))
    );
    temp_pred_equality(
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Error)),
        lift_state(cluster.reconciler_reconcile_error(controller_id, key))
    );
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, key, janitor_step_is_terminal())),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Done)),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Error));
        idle
    );

    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterDeleteInner), janitor_step_is_terminal());

    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, key, janitor_step_after_list_outer())),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::AfterDeleteInner)),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Done)),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Error));
        idle
    );
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::AfterListOuter), janitor_step_after_list_outer());

    // Init either sends the List or, for an object without mirror identity, is done.
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, key, janitor_step_after_init())),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::AfterListOuter)),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Done));
        idle
    );
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(spec, controller_id, key, at_janitor_step_closure(WidgetJanitorStepView::Init), janitor_step_after_init());

    entails_implies_leads_to(spec, idle, idle);
    lemma_true_equal_to_janitor_idle_or_at_any_step(controller_id, key);
    or_leads_to_combine_and_equality!(
        spec, true_pred(),
        idle,
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Init)),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::AfterListOuter)),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::AfterDeleteInner)),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Done)),
        lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Error));
        idle
    );
}

proof fn lemma_true_equal_to_janitor_idle_or_at_any_step(controller_id: int, key: ObjectRef)
    ensures
        true_pred::<ClusterState>() == lift_state(Cluster::reconcile_idle(controller_id, key))
            .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Init)))
            .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::AfterListOuter)))
            .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::AfterDeleteInner)))
            .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Done)))
            .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Error))),
{
    let rhs = lift_state(Cluster::reconcile_idle(controller_id, key))
        .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Init)))
        .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::AfterListOuter)))
        .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::AfterDeleteInner)))
        .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Done)))
        .or(lift_state(at_janitor_step(controller_id, key, WidgetJanitorStepView::Error)));
    assert forall |ex| #![auto] true_pred::<ClusterState>().satisfied_by(ex) implies rhs.satisfied_by(ex) by {
        let s = ex.head();
        if s.ongoing_reconciles(controller_id).contains_key(key) {
            let step = WidgetJanitorReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap().reconcile_step;
            match step {
                WidgetJanitorStepView::Init => {},
                WidgetJanitorStepView::AfterListOuter => {},
                WidgetJanitorStepView::AfterDeleteInner => {},
                WidgetJanitorStepView::Done => {},
                WidgetJanitorStepView::Error => {},
            }
        }
    }
    temp_pred_equality(true_pred::<ClusterState>(), rhs);
}

}
