// Model of the sync reconciler: reconciles an outer Widget by keeping a mirror of
// it (same namespace, name and spec) in the inner cluster and copying the mirror's
// status back.
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct WidgetSyncReconciler {}

pub struct WidgetSyncReconcileState {
    pub reconcile_step: WidgetSyncStepView,
}

impl Reconciler<WidgetSyncReconcileState, OuterWidgetView, VoidEReqView, VoidERespView> for WidgetSyncReconciler {
    open spec fn reconcile_init_state() -> WidgetSyncReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(outer: OuterWidgetView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetSyncReconcileState) -> (WidgetSyncReconcileState, Option<RequestView<VoidEReqView>>) {
        reconcile_core(outer, resp_o, state)
    }

    open spec fn reconcile_done(state: WidgetSyncReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: WidgetSyncReconcileState) -> bool {
        reconcile_error(state)
    }
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

// The key of the mirror of `outer` in the inner cluster: same namespace and name,
// the inner cluster's model kind.
pub open spec fn inner_key(outer: OuterWidgetView) -> ObjectRef {
    ObjectRef {
        kind: InnerWidgetView::kind(),
        namespace: outer.metadata.namespace->0,
        name: outer.metadata.name->0,
    }
}

// The parent-uid annotation value: the outer copy's uid, copied as a string. Uids
// are opaque tokens; the controller only ever compares them for equality.
pub open spec fn parent_uid_of(outer: OuterWidgetView) -> StringView {
    int_to_string_view(outer.metadata.uid->0)
}

// The mirror the sync controller creates: same name and namespace, the identifying
// label and annotation, the outer spec, no owner references, no finalizers.
pub open spec fn make_inner(outer: OuterWidgetView) -> InnerWidgetView {
    InnerWidgetView {
        metadata: ObjectMetaView::default()
            .with_name(outer.metadata.name->0)
            .with_namespace(outer.metadata.namespace->0)
            .add_label(managed_by_key(), managed_by_value())
            .add_annotation(parent_uid_key(), parent_uid_of(outer)),
        spec: outer.spec,
        status: None,
    }
}

// An inner object is the mirror of `outer` iff it carries the managed-by label and
// its parent-uid annotation equals the outer copy's uid. Anything else is refused.
pub open spec fn is_mirror_of(inner: InnerWidgetView, outer: OuterWidgetView) -> bool {
    &&& inner.metadata.labels is Some
    &&& inner.metadata.labels->0.contains_key(managed_by_key())
    &&& inner.metadata.labels->0[managed_by_key()] == managed_by_value()
    &&& inner.metadata.annotations is Some
    &&& inner.metadata.annotations->0.contains_key(parent_uid_key())
    &&& inner.metadata.annotations->0[parent_uid_key()] == parent_uid_of(outer)
}

// The inner implementation has processed the mirror's current spec.
pub open spec fn inner_caught_up(inner: InnerWidgetView) -> bool {
    &&& inner.status is Some
    &&& inner.status->0.observed_generation is Some
    &&& inner.metadata.generation is Some
    &&& inner.status->0.observed_generation == inner.metadata.generation
}

// The JSON patch that replaces the mirror's spec, pinned to the mirror's uid and
// generation as read: it lands only if nobody changed the mirror's spec since.
pub open spec fn inner_spec_patch(inner: InnerWidgetView, outer: OuterWidgetView) -> PatchRequest {
    PatchRequest {
        namespace: outer.metadata.namespace->0,
        name: outer.metadata.name->0,
        kind: InnerWidgetView::kind(),
        tests: PatchTestsView::default()
            .with_uid_from_object_meta(inner.metadata)
            .with_generation_from_object_meta(inner.metadata),
        spec: inner.with_spec(outer.spec).marshal().spec,
    }
}

// The JSON patch that writes the outer copy's status, pinned to the snapshot's uid
// and generation: it lands only while the outer copy still has the spec the
// reconcile was based on.
pub open spec fn outer_status_patch(outer: OuterWidgetView, status: WidgetStatusView) -> PatchStatusRequest {
    PatchStatusRequest {
        namespace: outer.metadata.namespace->0,
        name: outer.metadata.name->0,
        kind: OuterWidgetView::kind(),
        tests: PatchTestsView::default()
            .with_uid_from_object_meta(outer.metadata)
            .with_generation_from_object_meta(outer.metadata),
        status: outer.with_status(status).marshal().status,
    }
}

// Write `status` to the outer copy unless it already has it.
pub open spec fn write_outer_status_or_done(outer: OuterWidgetView, status: WidgetStatusView) -> (WidgetSyncReconcileState, Option<RequestView<VoidEReqView>>) {
    if outer.status == Some(status) {
        (at_step(WidgetSyncStepView::Done), None)
    } else {
        (at_step(WidgetSyncStepView::AfterPatchOuterStatus), Some(RequestView::KRequest(APIRequest::PatchStatusRequest(outer_status_patch(outer, status)))))
    }
}

pub open spec fn reconcile_core(outer: OuterWidgetView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetSyncReconcileState) -> (WidgetSyncReconcileState, Option<RequestView<VoidEReqView>>) {
    let error = (at_step(WidgetSyncStepView::Error), None::<RequestView<VoidEReqView>>);
    let done = (at_step(WidgetSyncStepView::Done), None::<RequestView<VoidEReqView>>);
    match state.reconcile_step {
        WidgetSyncStepView::Init => {
            let req = APIRequest::GetRequest(GetRequest { key: inner_key(outer) });
            (at_step(WidgetSyncStepView::AfterGetInner), Some(RequestView::KRequest(req)))
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
                            obj: make_inner(outer).marshal(),
                        });
                        (at_step(WidgetSyncStepView::AfterCreateInner), Some(RequestView::KRequest(req)))
                    } else {
                        error
                    }
                } else {
                    let unmarshalled = InnerWidgetView::unmarshal(res->Ok_0);
                    if unmarshalled is Err {
                        error
                    } else {
                        let inner = unmarshalled->Ok_0;
                        if inner.metadata.deletion_timestamp is Some {
                            // Absent-in-progress: wait for the inner side to release it.
                            write_outer_status_or_done(outer, outer_status_without_inner(outer.metadata.generation, outer.status, reason_inner_terminating()))
                        } else if !is_mirror_of(inner, outer) {
                            // Not ours: never touch it, report the conflict.
                            write_outer_status_or_done(outer, outer_status_without_inner(outer.metadata.generation, outer.status, reason_foreign_object()))
                        } else if inner.spec != outer.spec {
                            // Propagate the spec, pinned to the mirror's generation.
                            let req = APIRequest::PatchRequest(inner_spec_patch(inner, outer));
                            (at_step(WidgetSyncStepView::AfterPatchInner), Some(RequestView::KRequest(req)))
                        } else if inner_caught_up(inner) {
                            // Spec is in place and the inner implementation has observed this
                            // very generation of it: mirror the status back and stamp the
                            // outer generation.
                            write_outer_status_or_done(outer, outer_status_for(outer.metadata.generation, inner.status->0, true, reason_synced()))
                        } else {
                            // Spec is in place but the inner status was computed for an older
                            // generation of the mirror, possibly a mistaken edit that has since
                            // been overwritten: never copy such fields. Keep what was reported
                            // before and say the inner side is converging.
                            write_outer_status_or_done(outer, outer_status_without_inner(outer.metadata.generation, outer.status, reason_inner_converging()))
                        }
                    }
                }
            }
        },
        WidgetSyncStepView::AfterCreateInner => {
            if is_some_k_create_resp_view(resp_o) && extract_some_k_create_resp_view(resp_o) is Ok {
                done
            } else {
                error
            }
        },
        WidgetSyncStepView::AfterPatchInner => {
            if is_some_k_patch_resp_view(resp_o) && extract_some_k_patch_resp_view(resp_o) is Ok {
                done
            } else {
                error
            }
        },
        WidgetSyncStepView::AfterPatchOuterStatus => {
            if is_some_k_patch_status_resp_view(resp_o) && extract_some_k_patch_status_resp_view(resp_o) is Ok {
                done
            } else {
                error
            }
        },
        _ => (state, None),
    }
}

}
