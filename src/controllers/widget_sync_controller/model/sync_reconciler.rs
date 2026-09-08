// Model of the sync reconciler of a configured kind `k`: reconciles an outer copy
// by keeping a mirror of it (same namespace, name and spec) in the inner cluster
// its selector names, and copying the mirror's status back. One controller per
// kind (doc/widget_sync_fanout_design.md, section 3.2).
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct WidgetSyncReconcileState {
    pub reconcile_step: WidgetSyncStepView,
}

pub open spec fn reconcile_init_state() -> WidgetSyncReconcileState {
    WidgetSyncReconcileState {
        reconcile_step: WidgetSyncStepView::Init,
    }
}

pub open spec fn reconcile_done(state: WidgetSyncReconcileState) -> bool {
    state.reconcile_step is Done
}

pub open spec fn reconcile_error(state: WidgetSyncReconcileState) -> bool {
    state.reconcile_step is Error
}

pub open spec fn at_step(step: WidgetSyncStepView) -> WidgetSyncReconcileState {
    WidgetSyncReconcileState { reconcile_step: step }
}

// The JSON patch that replaces the mirror's spec, pinned to the mirror's uid and
// generation as read: it lands only if nobody changed the mirror's spec since.
pub open spec fn inner_spec_patch(k: SyncKind, inner: SyncedObjectView, outer: SyncedObjectView) -> PatchRequest {
    PatchRequest {
        namespace: outer.metadata.namespace->0,
        name: outer.metadata.name->0,
        kind: inner_key(k, outer).kind,
        tests: PatchTestsView::default()
            .with_uid_from_object_meta(inner.metadata)
            .with_generation_from_object_meta(inner.metadata),
        spec: outer.spec,
    }
}

// The JSON patch that writes the outer copy's status, pinned to the snapshot's uid
// and generation: it lands only while the outer copy still has the spec the
// reconcile was based on.
pub open spec fn outer_status_patch(k: SyncKind, outer: SyncedObjectView, status: SyncedStatusView) -> PatchStatusRequest {
    PatchStatusRequest {
        namespace: outer.metadata.namespace->0,
        name: outer.metadata.name->0,
        kind: k.outer_kind,
        tests: PatchTestsView::default()
            .with_uid_from_object_meta(outer.metadata)
            .with_generation_from_object_meta(outer.metadata),
        status: marshal_status(Some(status)),
    }
}

// Write `status` to the outer copy unless it already has it.
pub open spec fn write_outer_status_or_done(k: SyncKind, outer: SyncedObjectView, status: SyncedStatusView) -> (WidgetSyncReconcileState, Option<RequestView<VoidEReqView>>) {
    if outer.status == Some(status) {
        (at_step(WidgetSyncStepView::Done), None)
    } else {
        (at_step(WidgetSyncStepView::AfterPatchOuterStatus), Some(RequestView::KRequest(APIRequest::PatchStatusRequest(outer_status_patch(k, outer, status)))))
    }
}

// The status that reports `outcome` without consulting the inner status: the
// mirrored remainder as previously reported, stamped with the snapshot's generation.
pub open spec fn reported_status(outer: SyncedObjectView, outcome: SyncOutcomeView) -> SyncedStatusView {
    outer_status_for(outer.metadata.generation, status_or_default(outer.status), outcome)
}

// The status that reports the failure of a request answered with `err`.
pub open spec fn failure_status(outer: SyncedObjectView, err: APIError, answering_create: bool) -> SyncedStatusView {
    reported_status(outer, SyncOutcomeView::Failed(error_reason(err, answering_create)))
}

// Report a failed request in the outer status, then end in Error: write `status`
// unless the outer copy already has it. The write is not retried if it fails, and
// the reconcile ends in Error either way, so the shim requeues it.
pub open spec fn report_error(k: SyncKind, outer: SyncedObjectView, status: SyncedStatusView) -> (WidgetSyncReconcileState, Option<RequestView<VoidEReqView>>) {
    if outer.status == Some(status) {
        (at_step(WidgetSyncStepView::Error), None)
    } else {
        (at_step(WidgetSyncStepView::AfterReportError), Some(RequestView::KRequest(APIRequest::PatchStatusRequest(outer_status_patch(k, outer, status)))))
    }
}

pub open spec fn reconcile_core(k: SyncKind, outer: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetSyncReconcileState) -> (WidgetSyncReconcileState, Option<RequestView<VoidEReqView>>) {
    let error = (at_step(WidgetSyncStepView::Error), None::<RequestView<VoidEReqView>>);
    let done = (at_step(WidgetSyncStepView::Done), None::<RequestView<VoidEReqView>>);
    match state.reconcile_step {
        WidgetSyncStepView::Init => {
            if cluster_of(k.selector, outer) is None {
                // The object names no inner cluster: a permanent rejection, and the
                // reconcile ends. The boot shape check rules this out for stored
                // objects; the model does not assume it.
                write_outer_status_or_done(k, outer, reported_status(outer, SyncOutcomeView::Failed(FailureReasonView::Rejected)))
            } else {
                let req = APIRequest::GetRequest(GetRequest { key: inner_key(k, outer) });
                (at_step(WidgetSyncStepView::AfterGetInner), Some(RequestView::KRequest(req)))
            }
        },
        WidgetSyncStepView::AfterGetInner => {
            if !is_some_k_get_resp_view(resp_o) {
                error
            } else {
                let res = extract_some_k_get_resp_view(resp_o);
                if res is Err {
                    if res->Err_0 is ObjectNotFound {
                        // No mirror: create it.
                        let req = APIRequest::CreateRequest(CreateRequest {
                            namespace: outer.metadata.namespace->0,
                            obj: marshal(make_inner(k, outer)),
                        });
                        (at_step(WidgetSyncStepView::AfterCreateInner), Some(RequestView::KRequest(req)))
                    } else {
                        // The Get failed: report why, then requeue.
                        report_error(k, outer, failure_status(outer, res->Err_0, false))
                    }
                } else {
                    let unmarshalled = unmarshal(inner_key(k, outer).kind, res->Ok_0);
                    if unmarshalled is Err {
                        error
                    } else {
                        let inner = unmarshalled->Ok_0;
                        if inner.metadata.deletion_timestamp is Some {
                            // Absent-in-progress: wait for the inner side to release it.
                            write_outer_status_or_done(k, outer, reported_status(outer, SyncOutcomeView::InnerTerminating))
                        } else if !is_mirror_of(inner, outer) {
                            // Not ours: never touch it, report the conflict. A mirror of another
                            // incarnation of the outer copy (label and annotation present, other
                            // parent uid) is stale and the janitor removes it; anything else is foreign.
                            let outcome = if has_mirror_identity(inner) { SyncOutcomeView::StaleMirror } else { SyncOutcomeView::ForeignObject };
                            write_outer_status_or_done(k, outer, reported_status(outer, outcome))
                        } else if inner.spec != outer.spec {
                            // Propagate the spec, pinned to the mirror's generation.
                            let req = APIRequest::PatchRequest(inner_spec_patch(k, inner, outer));
                            (at_step(WidgetSyncStepView::AfterPatchInner), Some(RequestView::KRequest(req)))
                        } else if inner_caught_up(inner) {
                            // The inner status observes the mirror's current generation:
                            // copy it back, stamped with the outer generation.
                            write_outer_status_or_done(k, outer, outer_status_for(outer.metadata.generation, inner.status->0, SyncOutcomeView::Synced))
                        } else {
                            // The inner status is for an older generation of the mirror: keep
                            // the previously reported fields and report InnerConverging.
                            write_outer_status_or_done(k, outer, reported_status(outer, SyncOutcomeView::InnerConverging))
                        }
                    }
                }
            }
        },
        WidgetSyncStepView::AfterCreateInner => {
            if !is_some_k_create_resp_view(resp_o) {
                error
            } else {
                let res = extract_some_k_create_resp_view(resp_o);
                if res is Ok {
                    done
                } else {
                    // The Create failed: report why, then requeue.
                    report_error(k, outer, failure_status(outer, res->Err_0, true))
                }
            }
        },
        WidgetSyncStepView::AfterPatchInner => {
            if !is_some_k_patch_resp_view(resp_o) {
                error
            } else {
                let res = extract_some_k_patch_resp_view(resp_o);
                if res is Ok {
                    done
                } else {
                    // The Patch failed: report why, then requeue.
                    report_error(k, outer, failure_status(outer, res->Err_0, false))
                }
            }
        },
        WidgetSyncStepView::AfterPatchOuterStatus => {
            if is_some_k_patch_status_resp_view(resp_o) && extract_some_k_patch_status_resp_view(resp_o) is Ok {
                done
            } else {
                error
            }
        },
        // The status write that reported a failure is not retried: whatever its
        // answer, the reconcile ends in Error and is requeued.
        WidgetSyncStepView::AfterReportError => error,
        _ => (state, None),
    }
}

}
