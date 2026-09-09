// Model of an inner implementation: the controller a workload cluster runs for a
// mirrored kind. It is what the return path of the design exists for -- the sync
// controller copies a spec in, something in the inner cluster acts on it and
// writes a status, and the sync controller carries that status back out.
//
// Until this model there was no such controller anywhere in the repository. The
// disturber (disturber_reconciler.rs) edits and deletes mirrors but writes no
// status, so `inner_settled` -- the premise of R2 -- and D3 held of no modelled
// execution, and doc/widget_sync_design.md section 2.3 listed inner status writes
// as covered "as another controller under the rely" with nothing to point at.
//
// On each reconcile it patches the status of the mirror it was triggered by,
// stamping observedGeneration with that mirror's own generation and reporting
// Ready. It tests the generation it observed, so a patch that arrives after the
// spec moved on does not claim to have observed the newer one. It reads nothing
// and reports on nothing else: what a real implementation computes is its own
// business, and the pair's properties are stated over whatever status it writes.
//
// Its guarantee (proof/inner_impl.rs) implies the relies of both reconcilers: a
// status patch of a mirror is a request the sync reconciler's rely permits
// (`req.kind != k.outer_kind`) and one the janitor's rely does not constrain.
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::reconciler::spec::io::*;
use crate::widget_sync_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

pub enum WidgetInnerImplStepView {
    Init,
    AfterPatchStatus,
    Done,
}

pub struct WidgetInnerImplReconcileState {
    pub reconcile_step: WidgetInnerImplStepView,
}

pub open spec fn reconcile_init_state() -> WidgetInnerImplReconcileState {
    WidgetInnerImplReconcileState {
        reconcile_step: WidgetInnerImplStepView::Init,
    }
}

pub open spec fn reconcile_done(state: WidgetInnerImplReconcileState) -> bool {
    state.reconcile_step is Done
}

// The implementation does not care how its status write fares: a failed patch is
// retried by the next reconcile, as the sync controller's own status write is.
pub open spec fn reconcile_error(state: WidgetInnerImplReconcileState) -> bool {
    false
}

pub open spec fn at_step(step: WidgetInnerImplStepView) -> WidgetInnerImplReconcileState {
    WidgetInnerImplReconcileState { reconcile_step: step }
}

// The condition an implementation reports about its own work. `Ready=True` with
// no reason is the cheapest witness: the sync controller merges the inner Ready
// and Stalled into the outer status (spec_types::outer_status_for), so a status
// carrying Ready is one the merge has something to carry.
pub open spec fn inner_ready_condition(generation: Option<int>) -> SyncedConditionView {
    SyncedConditionView {
        type_: ready_condition_type(),
        status: condition_true(),
        observed_generation: generation,
        reason: None,
        message: None,
    }
}

// The status the implementation writes for a mirror at `generation`: caught up
// with that generation, reporting Ready, and mirroring nothing else.
pub open spec fn inner_impl_status(generation: Option<int>) -> SyncedStatusView {
    SyncedStatusView {
        observed_generation: generation,
        conditions: Some(seq![inner_ready_condition(generation)]),
        rest: empty_status_rest(),
    }
}

// The status patch, pinned to the generation the reconcile observed. Without the
// test a patch delayed past a spec change would stamp observedGeneration with a
// generation it never saw, which is the one thing an implementation must not do:
// inner_caught_up would then hold of a status computed for an older spec.
pub open spec fn inner_status_patch(kind: Kind, inner: SyncedObjectView) -> PatchStatusRequest {
    PatchStatusRequest {
        namespace: inner.metadata.namespace->0,
        name: inner.metadata.name->0,
        kind: kind,
        tests: PatchTestsView::default()
            .with_uid_from_object_meta(inner.metadata)
            .with_generation_from_object_meta(inner.metadata),
        status: marshal_status(Some(inner_impl_status(inner.metadata.generation))),
    }
}

pub open spec fn reconcile_core(kind: Kind, inner: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetInnerImplReconcileState) -> (WidgetInnerImplReconcileState, Option<RequestView<VoidEReqView>>) {
    match state.reconcile_step {
        WidgetInnerImplStepView::Init => {
            let req = APIRequest::PatchStatusRequest(inner_status_patch(kind, inner));
            (at_step(WidgetInnerImplStepView::AfterPatchStatus), Some(RequestView::KRequest(req)))
        },
        WidgetInnerImplStepView::AfterPatchStatus => {
            (at_step(WidgetInnerImplStepView::Done), None)
        },
        _ => (state, None),
    }
}

}
