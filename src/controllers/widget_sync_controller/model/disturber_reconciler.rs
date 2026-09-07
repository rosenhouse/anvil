// Model of an out-of-band actor in the inner cluster: something outside the
// Widget pair that edits and deletes mirrors at will. It stands for a
// `kubectl edit` or `kubectl delete` of a mirror, or for an inner cluster that
// was rebuilt. It is an ordinary controller model triggered by inner Widgets,
// with no fairness assumed: it may act at any moment and may stop at any moment.
//
// On each reconcile it patches the mirror's spec, testing nothing, and then
// deletes the mirror, with no precondition, ignoring every response. Its
// guarantee (proof/disturber.rs) implies the relies of both reconcilers, so the
// pair keeps R1, R2, R3 and R3s with the disturber in the cluster
// (composition/widget_disturber_reconciler.rs). The premise of R1 and R2 then
// says what "the disturbance has stopped" means: no edit of the mirror's spec
// and no delete that would land on the live mirror is in flight.
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::widget_sync_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

pub enum WidgetDisturberStepView {
    Init,
    AfterPatchInner,
    AfterDeleteInner,
    Done,
}

pub struct WidgetDisturberReconciler {}

pub struct WidgetDisturberReconcileState {
    pub reconcile_step: WidgetDisturberStepView,
}

impl Reconciler<WidgetDisturberReconcileState, InnerWidgetView, VoidEReqView, VoidERespView> for WidgetDisturberReconciler {
    open spec fn reconcile_init_state() -> WidgetDisturberReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(inner: InnerWidgetView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetDisturberReconcileState) -> (WidgetDisturberReconcileState, Option<RequestView<VoidEReqView>>) {
        reconcile_core(inner, resp_o, state)
    }

    open spec fn reconcile_done(state: WidgetDisturberReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: WidgetDisturberReconcileState) -> bool {
        reconcile_error(state)
    }
}

pub open spec fn reconcile_init_state() -> WidgetDisturberReconcileState {
    WidgetDisturberReconcileState {
        reconcile_step: WidgetDisturberStepView::Init,
    }
}

pub open spec fn reconcile_done(state: WidgetDisturberReconcileState) -> bool {
    state.reconcile_step is Done
}

// The disturber does not care how its requests fare.
pub open spec fn reconcile_error(state: WidgetDisturberReconcileState) -> bool {
    false
}

pub open spec fn at_step(step: WidgetDisturberStepView) -> WidgetDisturberReconcileState {
    WidgetDisturberReconcileState { reconcile_step: step }
}

// The edit: a different spec that is still valid.
pub open spec fn disturbed_spec(spec: WidgetSpecView) -> WidgetSpecView {
    WidgetSpecView { count: spec.count + 1, ..spec }
}

// The spec patch, testing nothing: it lands whatever the mirror looks like now.
pub open spec fn disturbing_patch(inner: InnerWidgetView) -> PatchRequest {
    PatchRequest {
        namespace: inner.metadata.namespace->0,
        name: inner.metadata.name->0,
        kind: InnerWidgetView::kind(),
        tests: PatchTestsView::default(),
        spec: inner.with_spec(disturbed_spec(inner.spec)).marshal().spec,
    }
}

// The delete, with no precondition: it removes whatever is at the key now.
pub open spec fn disturbing_delete(inner: InnerWidgetView) -> DeleteRequest {
    DeleteRequest {
        key: inner.object_ref(),
        preconditions: None,
    }
}

pub open spec fn reconcile_core(inner: InnerWidgetView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetDisturberReconcileState) -> (WidgetDisturberReconcileState, Option<RequestView<VoidEReqView>>) {
    match state.reconcile_step {
        WidgetDisturberStepView::Init => {
            let req = APIRequest::PatchRequest(disturbing_patch(inner));
            (at_step(WidgetDisturberStepView::AfterPatchInner), Some(RequestView::KRequest(req)))
        },
        WidgetDisturberStepView::AfterPatchInner => {
            let req = APIRequest::DeleteRequest(disturbing_delete(inner));
            (at_step(WidgetDisturberStepView::AfterDeleteInner), Some(RequestView::KRequest(req)))
        },
        WidgetDisturberStepView::AfterDeleteInner => {
            (at_step(WidgetDisturberStepView::Done), None)
        },
        _ => (state, None),
    }
}

}
