// Model of the janitor reconciler of a kind `k` and a binding `b`: reconciles a
// mirror in `b`'s inner cluster by deleting it once its parent no longer exists in
// the outer cluster. One controller per (kind, binding)
// (doc/widget_sync_fanout_design.md, section 3.3).
//
// Absence of the parent is established only by a successful List of the outer
// copies in the mirror's namespace that contains no object with the mirror's
// parent uid whose selector names `b`. A Get answering NotFound is never taken as
// absence: the model's fault injection can produce that answer for an existing
// object, and in reality a CRD reinstall window or a misrouted kubeconfig answers
// NotFound for every key. The cluster conjunct is what keeps the janitor of one
// binding from collecting the mirror of a parent that moved to another; under the
// selector field's immutability rule it is redundant, and the proofs do not
// depend on that rule.
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::reconciler::spec::io::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::{spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct WidgetJanitorReconcileState {
    pub reconcile_step: WidgetJanitorStepView,
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

// The listed outer copies contain the mirror's parent: some outer copy's uid, as
// a string, equals the parent-uid annotation, and that copy's selector names this
// binding's inner cluster. Uids are compared for equality only, and only outer
// copies are looked at.
pub open spec fn parent_listed(k: SyncKind, b: Binding, objs: Seq<DynamicObjectView>, parent_uid: StringView) -> bool {
    exists |i: int| 0 <= i < objs.len()
        && (#[trigger] objs[i]).kind == k.outer_kind
        && objs[i].metadata.uid is Some
        && int_to_string_view(objs[i].metadata.uid->0) == parent_uid
        && cluster_of_dynamic(k.selector, objs[i]) == Some(b.name)
}

pub open spec fn reconcile_core(k: SyncKind, b: Binding, inner: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetJanitorReconcileState) -> (WidgetJanitorReconcileState, Option<RequestView<VoidEReqView>>) {
    let error = (at_step(WidgetJanitorStepView::Error), None::<RequestView<VoidEReqView>>);
    let done = (at_step(WidgetJanitorStepView::Done), None::<RequestView<VoidEReqView>>);
    match state.reconcile_step {
        WidgetJanitorStepView::Init => {
            if !has_mirror_identity(inner) {
                done
            } else {
                let req = APIRequest::ListRequest(ListRequest {
                    kind: k.outer_kind,
                    namespace: inner.metadata.namespace->0,
                });
                (at_step(WidgetJanitorStepView::AfterListOuter), Some(RequestView::KRequest(req)))
            }
        },
        WidgetJanitorStepView::AfterListOuter => {
            if !has_mirror_identity(inner) {
                // Cannot happen (the triggering object is fixed for the whole reconcile);
                // stated so that parent_uid_annotation below is only read off a mirror.
                error
            } else if !(is_some_k_list_resp_view(resp_o) && extract_some_k_list_resp_view(resp_o) is Ok) {
                // Any failure, including a type-level NotFound, is a retry, never a deletion.
                error
            } else {
                let objs = extract_some_k_list_resp_view(resp_o)->Ok_0;
                if parent_listed(k, b, objs, parent_uid_annotation(inner)) {
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
