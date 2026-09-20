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

// The Update that adds (`add`) or removes the sync finalizer on the snapshot
// `outer` the reconcile runs on. Everything else, the resource version included,
// is the snapshot's, so the update lands only if nobody wrote the outer copy
// since the snapshot was taken; otherwise a later reconcile starts from a newer
// snapshot and tries again.
pub open spec fn outer_finalizer_update(outer: SyncedObjectView, add: bool) -> UpdateRequest {
    let metadata = if add { with_sync_finalizer(outer.metadata) } else { without_sync_finalizer(outer.metadata) };
    UpdateRequest {
        namespace: outer.metadata.namespace->0,
        name: outer.metadata.name->0,
        obj: marshal(outer.with_metadata(metadata)),
    }
}

// The List that reads the mirror key: the mirror's kind, namespace and name. A
// successful empty answer is what confirms the mirror gone; a Get answered
// NotFound would not, because an uninstalled kind is answered the same way.
pub open spec fn mirror_list(k: SyncKind, outer: SyncedObjectView) -> ListRequest {
    ListRequest {
        kind: inner_key(k, outer).kind,
        namespace: outer.metadata.namespace->0,
        name: Some(outer.metadata.name->0),
    }
}

// The Delete of `inner`, the mirror of `outer` as read at the mirror key, pinned
// to its uid.
pub open spec fn mirror_delete(k: SyncKind, outer: SyncedObjectView, inner: SyncedObjectView) -> DeleteRequest {
    DeleteRequest {
        key: inner_key(k, outer),
        preconditions: Some(PreconditionsView::default().with_uid_from_object_meta(inner.metadata)),
    }
}

// `o` is stored at `key`: same kind, namespace and name.
pub open spec fn is_at(o: DynamicObjectView, key: ObjectRef) -> bool {
    &&& o.kind == key.kind
    &&& o.metadata.namespace == Some(key.namespace)
    &&& o.metadata.name == Some(key.name)
}

// Some object of `objs` is stored at `key`. A List answer is read as a set: which
// object it is does not matter here, and the Get that follows names it.
pub open spec fn listed_at(objs: Seq<DynamicObjectView>, key: ObjectRef) -> bool {
    exists |i: int| 0 <= i < objs.len() && is_at(#[trigger] objs[i], key)
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
            if outer.metadata.deletion_timestamp is Some {
                if !has_sync_finalizer(outer.metadata) {
                    // Terminating without the sync finalizer: not this controller's
                    // to tear down, and a status write would only prolong it.
                    done
                } else if cluster_of(k.selector, outer) is None || !serves(k, outer) {
                    // No inner cluster this controller can address: the copy names
                    // none, or names a binding this controller holds no credential
                    // for. Nothing here can ever confirm the mirror gone, so the
                    // copy is released rather than held for ever. A binding that is
                    // bound but unreachable, or refused, is not this case: it is
                    // served, and the teardown below waits for it.
                    let req = APIRequest::UpdateRequest(outer_finalizer_update(outer, false));
                    (at_step(WidgetSyncStepView::AfterRemoveFinalizer), Some(RequestView::KRequest(req)))
                } else {
                    // Teardown: read the mirror key.
                    let req = APIRequest::ListRequest(mirror_list(k, outer));
                    (at_step(WidgetSyncStepView::AfterListMirror), Some(RequestView::KRequest(req)))
                }
            } else if cluster_of(k.selector, outer) is None {
                // The object names no inner cluster: a permanent rejection, and the
                // reconcile ends. The boot shape check rules this out for stored
                // objects; the model does not assume it.
                write_outer_status_or_done(k, outer, reported_status(outer, SyncOutcomeView::Failed(FailureReasonView::Rejected)))
            } else if !serves(k, outer) {
                // The object names a binding this controller does not know: report
                // the inner cluster as unreachable and requeue, without addressing
                // it and without taking ownership. Exec side `k.bindings` is the
                // snapshot of the bound clusters this reconcile was built with, so a
                // binding that appears later is served by a later reconcile.
                report_error(k, outer, reported_status(outer, SyncOutcomeView::Failed(FailureReasonView::InnerUnreachable)))
            } else if !has_sync_finalizer(outer.metadata) {
                // Take ownership before any mirror exists.
                let req = APIRequest::UpdateRequest(outer_finalizer_update(outer, true));
                (at_step(WidgetSyncStepView::AfterAddFinalizer), Some(RequestView::KRequest(req)))
            } else {
                let req = APIRequest::GetRequest(GetRequest { key: inner_key(k, outer) });
                (at_step(WidgetSyncStepView::AfterGetInner), Some(RequestView::KRequest(req)))
            }
        },
        // The Update of the finalizers either landed or did not. A Conflict means
        // the copy was written since the snapshot was taken: nothing to report,
        // the next reconcile starts from the copy as it is now. Any other failure
        // ends in Error, which the shim logs and retries; a status write would
        // itself be a write of a copy this reconciler does not own, or is
        // releasing.
        WidgetSyncStepView::AfterAddFinalizer => {
            if is_some_k_update_resp_view(resp_o) && extract_some_k_update_resp_view(resp_o) is Ok {
                // Owned: the next reconcile syncs the mirror.
                done
            } else {
                error
            }
        },
        WidgetSyncStepView::AfterRemoveFinalizer => {
            if is_some_k_update_resp_view(resp_o) && extract_some_k_update_resp_view(resp_o) is Ok {
                done
            } else {
                error
            }
        },
        WidgetSyncStepView::AfterGetInner => {
            if !is_some_k_get_resp_view(resp_o) {
                error
            } else {
                let res = extract_some_k_get_resp_view(resp_o);
                if res is Err {
                    if res->Err_0 is ObjectNotFound {
                        if !serves(k, outer) {
                            // Never reached: Init refuses an outer copy whose binding
                            // this controller does not know, so no Get of such a
                            // mirror is ever sent. Stated here so that the mirror the
                            // model creates always carries a mirror kind of
                            // `k.bindings`, which a concrete cluster installs.
                            error
                        } else {
                            // No mirror: create it.
                            let req = APIRequest::CreateRequest(CreateRequest {
                                namespace: outer.metadata.namespace->0,
                                obj: marshal(make_inner(k, outer)),
                            });
                            (at_step(WidgetSyncStepView::AfterCreateInner), Some(RequestView::KRequest(req)))
                        }
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
                if res is Err {
                    // The Patch failed: report why, then requeue.
                    report_error(k, outer, failure_status(outer, res->Err_0, false))
                } else {
                    let unmarshalled = unmarshal(inner_key(k, outer).kind, res->Ok_0);
                    if unmarshalled is Err {
                        error
                    } else if unmarshalled->Ok_0.spec != outer.spec {
                        // The Patch landed and the inner cluster stored another
                        // spec: admission or defaulting there rewrote it, and
                        // patching again would only repeat that. The model's API
                        // server stores what a Patch writes, so this is reachable
                        // only against a real one.
                        write_outer_status_or_done(k, outer, reported_status(outer, SyncOutcomeView::Failed(FailureReasonView::SpecRewritten)))
                    } else {
                        done
                    }
                }
            }
        },
        WidgetSyncStepView::AfterListMirror => {
            if !is_some_k_list_resp_view(resp_o) {
                error
            } else {
                let res = extract_some_k_list_resp_view(resp_o);
                if res is Err {
                    // Including a NotFound for the kind itself: nothing is confirmed.
                    // A teardown writes no status: the copy is going away, and the
                    // failure is logged and retried from Error.
                    error
                } else if !listed_at(res->Ok_0, inner_key(k, outer)) {
                    // Confirmed gone: release.
                    let req = APIRequest::UpdateRequest(outer_finalizer_update(outer, false));
                    (at_step(WidgetSyncStepView::AfterRemoveFinalizer), Some(RequestView::KRequest(req)))
                } else {
                    // Something is at the mirror key: read it.
                    let req = APIRequest::GetRequest(GetRequest { key: inner_key(k, outer) });
                    (at_step(WidgetSyncStepView::AfterGetMirror), Some(RequestView::KRequest(req)))
                }
            }
        },
        WidgetSyncStepView::AfterGetMirror => {
            if !is_some_k_get_resp_view(resp_o) {
                error
            } else {
                let res = extract_some_k_get_resp_view(resp_o);
                if res is Err {
                    if res->Err_0 is ObjectNotFound {
                        // Gone since the List: the next reconcile confirms that with a
                        // List of its own.
                        done
                    } else {
                        error
                    }
                } else {
                    let unmarshalled = unmarshal(inner_key(k, outer).kind, res->Ok_0);
                    if unmarshalled is Err {
                        error
                    } else {
                        let inner = unmarshalled->Ok_0;
                        if !is_mirror_of(inner, outer) {
                            // Not ours, so nothing of ours is left at the key: a stale
                            // mirror is the janitor's, anything else is foreign. Release.
                            let req = APIRequest::UpdateRequest(outer_finalizer_update(outer, false));
                            (at_step(WidgetSyncStepView::AfterRemoveFinalizer), Some(RequestView::KRequest(req)))
                        } else if inner.metadata.deletion_timestamp is Some {
                            // Being released by the inner side: wait for it.
                            done
                        } else if inner.metadata.uid is None {
                            // A mirror is deleted by uid only; a stored object has one.
                            error
                        } else {
                            let req = APIRequest::DeleteRequest(mirror_delete(k, outer, inner));
                            (at_step(WidgetSyncStepView::AfterDeleteMirror), Some(RequestView::KRequest(req)))
                        }
                    }
                }
            }
        },
        WidgetSyncStepView::AfterDeleteMirror => {
            if !is_some_k_delete_resp_view(resp_o) {
                error
            } else {
                let res = extract_some_k_delete_resp_view(resp_o);
                if res is Ok || res->Err_0 is ObjectNotFound {
                    // Deleted, or gone already: the next reconcile confirms and releases.
                    done
                } else {
                    error
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
