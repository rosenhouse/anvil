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
// It owns a finalizer, or none (`finalizer`). With one, it takes the finalizer
// on a live mirror before it writes a status, and on a terminating mirror it
// releases the finalizer instead of writing one: that release is what D3 asks of
// the inner side, and the cluster running this model beside the pair proves D3
// from it (composition/widget_inner_impl_reconciler.rs). With none, it never
// touches finalizers, no mirror of its kind ever terminates, and D3 holds
// vacuously there.
//
// Its guarantee (proof/inner_impl.rs) implies the relies of both reconcilers: a
// status patch of a mirror is a request the sync reconciler's rely permits
// (`req.kind != k.outer_kind`) and one the janitor's rely does not constrain, and
// an update of the finalizers keeps the mirror's identity.
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

pub enum WidgetInnerImplStepView {
    Init,
    AfterAddFinalizer,
    AfterRemoveFinalizer,
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

// The implementation does not care how its write fares: a failed patch or update
// is retried by the next reconcile, as the sync controller's own writes are.
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

// The Update that takes (`add`) or releases the finalizer `f` on the snapshot
// `inner` the reconcile runs on, the sync controller's way
// (sync_reconciler::outer_finalizer_update): everything else, the resource
// version included, is the snapshot's, so the update lands only if nobody wrote
// the mirror since the snapshot was taken.
pub open spec fn inner_finalizer_update(inner: SyncedObjectView, f: StringView, add: bool) -> UpdateRequest {
    let metadata = if add { with_finalizer(inner.metadata, f) } else { without_finalizer(inner.metadata, f) };
    UpdateRequest {
        namespace: inner.metadata.namespace->0,
        name: inner.metadata.name->0,
        obj: marshal(inner.with_metadata(metadata)),
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

pub open spec fn reconcile_core(kind: Kind, finalizer: Option<StringView>, inner: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetInnerImplReconcileState) -> (WidgetInnerImplReconcileState, Option<RequestView<VoidEReqView>>) {
    match state.reconcile_step {
        WidgetInnerImplStepView::Init => {
            if finalizer is Some && inner.metadata.deletion_timestamp is Some {
                if has_finalizer(inner.metadata, finalizer->0) {
                    // The mirror is going away: release it. Whatever a real
                    // implementation tears down first is not modelled.
                    let req = APIRequest::UpdateRequest(inner_finalizer_update(inner, finalizer->0, false));
                    (at_step(WidgetInnerImplStepView::AfterRemoveFinalizer), Some(RequestView::KRequest(req)))
                } else {
                    (at_step(WidgetInnerImplStepView::Done), None)
                }
            } else if finalizer is Some && !has_finalizer(inner.metadata, finalizer->0) {
                // Take the finalizer before doing any work on the mirror.
                let req = APIRequest::UpdateRequest(inner_finalizer_update(inner, finalizer->0, true));
                (at_step(WidgetInnerImplStepView::AfterAddFinalizer), Some(RequestView::KRequest(req)))
            } else {
                let req = APIRequest::PatchStatusRequest(inner_status_patch(kind, inner));
                (at_step(WidgetInnerImplStepView::AfterPatchStatus), Some(RequestView::KRequest(req)))
            }
        },
        WidgetInnerImplStepView::AfterAddFinalizer => {
            (at_step(WidgetInnerImplStepView::Done), None)
        },
        WidgetInnerImplStepView::AfterRemoveFinalizer => {
            (at_step(WidgetInnerImplStepView::Done), None)
        },
        WidgetInnerImplStepView::AfterPatchStatus => {
            (at_step(WidgetInnerImplStepView::Done), None)
        },
        _ => (state, None),
    }
}

}
