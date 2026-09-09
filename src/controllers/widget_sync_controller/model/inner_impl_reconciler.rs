// Model of an inner implementation: the controller a workload cluster runs for a
// mirrored kind. It is what the return path of the design exists for -- the sync
// controller copies a spec in, something in the inner cluster acts on it and
// writes a status, and the sync controller carries that status back out. It is
// another controller under the rely, as the disturber is
// (doc/widget_sync_design.md, section 2.5).
//
// On each reconcile it patches the status of the mirror it was triggered by,
// stamping observedGeneration with the generation it read off that mirror and
// reporting Ready. It reads nothing else and reports on nothing else: what a real
// implementation computes is its own business, and the pair's properties are
// stated over whatever status it writes.
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

// The status patch, pinned to the uid and the generation the reconcile read.
//
// The two tests do different jobs. The uid test is the safety one: generations
// restart at 1 with each incarnation, so a patch delayed past a delete and a
// recreate would otherwise pass the generation test and make inner_caught_up
// hold of a status computed for the previous incarnation's spec. The generation
// test buys stability rather than safety -- the stamp is the generation this
// reconcile read, so a delayed patch is stale, not wrong -- but without it a late
// patch would overwrite a settled status with an older one, and R2's premise is
// `always(inner_settled)`, not one instant of it.
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

// The status the implementation writes is one that reports the mirror as caught
// up with the generation the patch tested. This is the load-bearing half of
// "the premise of R2 is producible" (doc/widget_sync_design.md, section 2.5):
// the other half is that a status write keeps the metadata and the spec, so
// spec_synced survives it, which is the API server's own rule
// (status_updated_object).
pub proof fn lemma_inner_impl_status_is_caught_up(inner: SyncedObjectView)
    requires inner.metadata.generation is Some,
    ensures inner_caught_up(SyncedObjectView {
        status: Some(inner_impl_status(inner.metadata.generation)),
        ..inner
    }),
{
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
