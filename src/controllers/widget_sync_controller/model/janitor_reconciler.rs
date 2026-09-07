// Model of the janitor reconciler: reconciles a mirror (inner Widget) by deleting
// it once its parent no longer exists in the outer cluster.
//
// Absence of the parent is established only by a successful List of the outer
// copies in the mirror's namespace that contains no object with the mirror's
// parent uid. A Get answering NotFound is never taken as absence: the model's
// fault injection can produce that answer for an existing object, and in reality
// a CRD reinstall window or a misrouted kubeconfig answers NotFound for every key.
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct WidgetJanitorReconciler {}

pub struct WidgetJanitorReconcileState {
    pub reconcile_step: WidgetJanitorStepView,
}

impl Reconciler<WidgetJanitorReconcileState, InnerWidgetView, VoidEReqView, VoidERespView> for WidgetJanitorReconciler {
    open spec fn reconcile_init_state() -> WidgetJanitorReconcileState {
        reconcile_init_state()
    }

    open spec fn reconcile_core(inner: InnerWidgetView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetJanitorReconcileState) -> (WidgetJanitorReconcileState, Option<RequestView<VoidEReqView>>) {
        reconcile_core(inner, resp_o, state)
    }

    open spec fn reconcile_done(state: WidgetJanitorReconcileState) -> bool {
        reconcile_done(state)
    }

    open spec fn reconcile_error(state: WidgetJanitorReconcileState) -> bool {
        reconcile_error(state)
    }
}

pub open spec fn reconcile_init_state() -> WidgetJanitorReconcileState {
    WidgetJanitorReconcileState {
        reconcile_step: WidgetJanitorStepView::Init,
    }
}

pub open spec fn reconcile_done(state: WidgetJanitorReconcileState) -> bool {
    state.reconcile_step is Done
}

pub open spec fn reconcile_error(state: WidgetJanitorReconcileState) -> bool {
    state.reconcile_step is Error
}

pub open spec fn at_step(step: WidgetJanitorStepView) -> WidgetJanitorReconcileState {
    WidgetJanitorReconcileState { reconcile_step: step }
}

// A mirror is one the sync controller created: it carries the managed-by label and
// a parent-uid annotation. Objects without both are left alone.
pub open spec fn has_mirror_identity(inner: InnerWidgetView) -> bool {
    &&& inner.metadata.labels is Some
    &&& inner.metadata.labels->0.contains_key(managed_by_key())
    &&& inner.metadata.labels->0[managed_by_key()] == managed_by_value()
    &&& inner.metadata.annotations is Some
    &&& inner.metadata.annotations->0.contains_key(parent_uid_key())
}

pub open spec fn parent_uid_annotation(inner: InnerWidgetView) -> StringView {
    inner.metadata.annotations->0[parent_uid_key()]
}

// The listed outer copies contain the mirror's parent: some object's uid, as a
// string, equals the parent-uid annotation. Uids are compared for equality only.
pub open spec fn parent_listed(objs: Seq<DynamicObjectView>, parent_uid: StringView) -> bool {
    exists |i: int| 0 <= i < objs.len()
        && (#[trigger] objs[i]).metadata.uid is Some
        && int_to_string_view(objs[i].metadata.uid->0) == parent_uid
}

pub open spec fn reconcile_core(inner: InnerWidgetView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetJanitorReconcileState) -> (WidgetJanitorReconcileState, Option<RequestView<VoidEReqView>>) {
    let error = (at_step(WidgetJanitorStepView::Error), None::<RequestView<VoidEReqView>>);
    let done = (at_step(WidgetJanitorStepView::Done), None::<RequestView<VoidEReqView>>);
    match state.reconcile_step {
        WidgetJanitorStepView::Init => {
            if !has_mirror_identity(inner) {
                done
            } else {
                let req = APIRequest::ListRequest(ListRequest {
                    kind: OuterWidgetView::kind(),
                    namespace: inner.metadata.namespace->0,
                });
                (at_step(WidgetJanitorStepView::AfterListOuter), Some(RequestView::KRequest(req)))
            }
        },
        WidgetJanitorStepView::AfterListOuter => {
            if !(is_some_k_list_resp_view(resp_o) && extract_some_k_list_resp_view(resp_o) is Ok) {
                // Any failure, including a type-level NotFound, is a retry, never a deletion.
                error
            } else {
                let objs = extract_some_k_list_resp_view(resp_o)->Ok_0;
                if parent_listed(objs, parent_uid_annotation(inner)) {
                    done
                } else {
                    let req = APIRequest::DeleteRequest(DeleteRequest {
                        key: inner.object_ref(),
                        preconditions: Some(PreconditionsView::default().with_uid_from_object_meta(inner.metadata)),
                    });
                    (at_step(WidgetJanitorStepView::AfterDeleteInner), Some(RequestView::KRequest(req)))
                }
            }
        },
        WidgetJanitorStepView::AfterDeleteInner => {
            if is_some_k_delete_resp_view(resp_o)
                && (extract_some_k_delete_resp_view(resp_o) is Ok || extract_some_k_delete_resp_view(resp_o)->Err_0 is ObjectNotFound) {
                done
            } else {
                error
            }
        },
        _ => (state, None),
    }
}

}
