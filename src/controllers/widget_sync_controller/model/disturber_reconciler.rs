// Model of an out-of-band actor in an inner cluster: something outside the Widget
// pair that edits and deletes mirrors of one inner kind at will. It stands for a
// `kubectl edit` or `kubectl delete` of a mirror, or for an inner cluster that was
// rebuilt. It is an ordinary controller model triggered by objects of that kind,
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
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

pub enum WidgetDisturberStepView {
    Init,
    AfterPatchInner,
    AfterDeleteInner,
    Done,
}

pub struct WidgetDisturberReconcileState {
    pub reconcile_step: WidgetDisturberStepView,
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

// The edit: some other value written over the mirror's spec. Nothing the pair
// proves depends on which value it is, only that it is not the one that was
// there, so the definition is the cheapest value with that property and stays
// closed: outside this module the edit is still an opaque function of the spec,
// known only through disturbed_spec_changes_the_spec.
pub closed spec fn disturbed_spec(spec: Value) -> Value { spec.push('x') }

// The disturber's edit is really an edit: it never writes back the value it
// found. Without this nothing would rule out the identity, and a disturber that
// leaves the spec alone is not a disturbance -- the premise of R1 and R2, "no
// edit of the mirror's spec is in flight", would be met by a Patch that changes
// nothing. A Value is a sequence of characters, so the witness is one character
// longer than what it replaces.
pub proof fn disturbed_spec_changes_the_spec()
    ensures forall |v: Value| #[trigger] disturbed_spec(v) != v,
{
    assert forall |v: Value| #[trigger] disturbed_spec(v) != v by {
        assert(disturbed_spec(v).len() == v.len() + 1);
    }
}

// The spec patch, testing nothing: it lands whatever the mirror looks like now.
pub open spec fn disturbing_patch(kind: Kind, inner: SyncedObjectView) -> PatchRequest {
    PatchRequest {
        namespace: inner.metadata.namespace->0,
        name: inner.metadata.name->0,
        kind: kind,
        tests: PatchTestsView::default(),
        spec: disturbed_spec(inner.spec),
    }
}

// The delete, with no precondition: it removes whatever is at the key now.
pub open spec fn disturbing_delete(inner: SyncedObjectView) -> DeleteRequest {
    DeleteRequest {
        key: inner.object_ref(),
        preconditions: None,
    }
}

pub open spec fn reconcile_core(kind: Kind, inner: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetDisturberReconcileState) -> (WidgetDisturberReconcileState, Option<RequestView<VoidEReqView>>) {
    match state.reconcile_step {
        WidgetDisturberStepView::Init => {
            let req = APIRequest::PatchRequest(disturbing_patch(kind, inner));
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
