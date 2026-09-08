// State predicates shared by the Widget sync example's proofs.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*,
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::widget_sync_controller::{
    model::{install::*, janitor_reconciler::WidgetJanitorReconcileState, sync_reconciler::WidgetSyncReconcileState},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// The rely conditions of every other controller, as one state predicate each.

pub open spec fn lifted_sync_rely_condition(k: SyncKind, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_state(|s| {
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] widget_sync_rely(k, other_id)(s)
    })
}

pub open spec fn lifted_janitor_rely_condition(k: SyncKind, cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    lift_state(|s| {
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> #[trigger] widget_janitor_rely(k, other_id)(s)
    })
}

// Closures over the marshalled local state of the sync reconciler.

pub open spec fn at_sync_step_closure(step: WidgetSyncStepView) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| WidgetSyncReconcileState::unmarshal(s).unwrap().reconcile_step == step
}

pub open spec fn sync_step_is_terminal() -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let step = WidgetSyncReconcileState::unmarshal(s).unwrap().reconcile_step;
        ||| step == WidgetSyncStepView::Done
        ||| step == WidgetSyncStepView::Error
    }
}

// Every step the sync reconciler can be at right after its first transition: the
// Get of the mirror; when the outer copy names no inner cluster, the status write
// that reports the rejection (or Done, when that status is already there); and,
// when it names a binding the reconciler does not serve, the status write that
// reports the inner cluster as unreachable (or Error, when that status is already
// there).
pub open spec fn sync_step_after_init() -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let step = WidgetSyncReconcileState::unmarshal(s).unwrap().reconcile_step;
        ||| step == WidgetSyncStepView::AfterGetInner
        ||| step == WidgetSyncStepView::AfterPatchOuterStatus
        ||| step == WidgetSyncStepView::AfterReportError
        ||| step == WidgetSyncStepView::Done
        ||| step == WidgetSyncStepView::Error
    }
}

// Every step the sync reconciler can be at right after answering the Get of the mirror.
pub open spec fn sync_step_after_get_inner() -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let step = WidgetSyncReconcileState::unmarshal(s).unwrap().reconcile_step;
        ||| step == WidgetSyncStepView::AfterCreateInner
        ||| step == WidgetSyncStepView::AfterPatchInner
        ||| step == WidgetSyncStepView::AfterPatchOuterStatus
        ||| step == WidgetSyncStepView::AfterReportError
        ||| step == WidgetSyncStepView::Done
        ||| step == WidgetSyncStepView::Error
    }
}

// Every step the sync reconciler can be at right after answering the Create or the
// Patch of the mirror: done, or reporting the failure before ending in Error.
pub open spec fn sync_step_after_mirror_write() -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let step = WidgetSyncReconcileState::unmarshal(s).unwrap().reconcile_step;
        ||| step == WidgetSyncStepView::AfterReportError
        ||| step == WidgetSyncStepView::Done
        ||| step == WidgetSyncStepView::Error
    }
}

pub open spec fn at_sync_step(controller_id: int, key: ObjectRef, step: WidgetSyncStepView) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, key, at_sync_step_closure(step))
}

// Closures over the marshalled local state of the janitor reconciler.

pub open spec fn at_janitor_step_closure(step: WidgetJanitorStepView) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| WidgetJanitorReconcileState::unmarshal(s).unwrap().reconcile_step == step
}

pub open spec fn janitor_step_is_terminal() -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let step = WidgetJanitorReconcileState::unmarshal(s).unwrap().reconcile_step;
        ||| step == WidgetJanitorStepView::Done
        ||| step == WidgetJanitorStepView::Error
    }
}

// Every step the janitor can be at right after its first transition.
pub open spec fn janitor_step_after_init() -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let step = WidgetJanitorReconcileState::unmarshal(s).unwrap().reconcile_step;
        ||| step == WidgetJanitorStepView::AfterListOuter
        ||| step == WidgetJanitorStepView::Done
    }
}

// Every step the janitor can be at right after answering the List of the outer copies.
pub open spec fn janitor_step_after_list_outer() -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let step = WidgetJanitorReconcileState::unmarshal(s).unwrap().reconcile_step;
        ||| step == WidgetJanitorStepView::AfterDeleteInner
        ||| step == WidgetJanitorStepView::Done
        ||| step == WidgetJanitorStepView::Error
    }
}

pub open spec fn at_janitor_step(controller_id: int, key: ObjectRef, step: WidgetJanitorStepView) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, key, at_janitor_step_closure(step))
}

}
