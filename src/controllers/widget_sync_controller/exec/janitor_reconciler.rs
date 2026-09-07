// Exec implementation of the janitor reconciler; every function is proved to
// conform to its counterpart in model::janitor_reconciler.
use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::model::janitor_reconciler as model;
use crate::widget_sync_controller::trusted::spec_types;
use crate::widget_sync_controller::trusted::{exec_types::*, spec_types::*, step::*};
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

pub struct WidgetJanitorReconcileState {
    pub reconcile_step: WidgetJanitorStep,
}

impl View for WidgetJanitorReconcileState {
    type V = model::WidgetJanitorReconcileState;

    open spec fn view(&self) -> model::WidgetJanitorReconcileState {
        model::WidgetJanitorReconcileState {
            reconcile_step: self.reconcile_step@,
        }
    }
}

pub struct WidgetJanitorReconciler {}

impl Reconciler for WidgetJanitorReconciler {
    type S = WidgetJanitorReconcileState;
    type K = InnerWidget;
    type EReq = VoidEReq;
    type EResp = VoidEResp;
    type M = model::WidgetJanitorReconciler;

    fn reconcile_init_state() -> Self::S {
        reconcile_init_state()
    }

    fn reconcile_core(inner: &Self::K, resp_o: Option<Response<Self::EResp>>, state: Self::S) -> (Self::S, Option<Request<Self::EReq>>) {
        reconcile_core(inner, resp_o, state)
    }

    fn reconcile_done(state: &Self::S) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(state: &Self::S) -> bool {
        reconcile_error(state)
    }
}

pub fn reconcile_init_state() -> (state: WidgetJanitorReconcileState)
    ensures state@ == model::reconcile_init_state(),
{
    WidgetJanitorReconcileState {
        reconcile_step: WidgetJanitorStep::Init,
    }
}

pub fn reconcile_done(state: &WidgetJanitorReconcileState) -> (res: bool)
    ensures res == model::reconcile_done(state@),
{
    match state.reconcile_step {
        WidgetJanitorStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &WidgetJanitorReconcileState) -> (res: bool)
    ensures res == model::reconcile_error(state@),
{
    match state.reconcile_step {
        WidgetJanitorStep::Error => true,
        _ => false,
    }
}

fn at_step(step: WidgetJanitorStep) -> (state: WidgetJanitorReconcileState)
    ensures state@ == model::at_step(step@),
{
    WidgetJanitorReconcileState { reconcile_step: step }
}

pub fn reconcile_core(inner: &InnerWidget, resp_o: Option<Response<VoidEResp>>, state: WidgetJanitorReconcileState) -> (res: (WidgetJanitorReconcileState, Option<Request<VoidEReq>>))
    requires inner@.well_formed(),
    ensures (res.0@, res.1.deep_view()) == model::reconcile_core(inner@, resp_o.deep_view(), state@),
{
    let namespace = inner.metadata().namespace().unwrap();
    let name = inner.metadata().name().unwrap();
    match state.reconcile_step {
        WidgetJanitorStep::Init => {
            if !has_mirror_identity(inner) {
                return (at_step(WidgetJanitorStep::Done), None);
            }
            let req = KubeAPIRequest::ListRequest(KubeListRequest {
                api_resource: OuterWidget::api_resource(),
                namespace: namespace,
            });
            return (at_step(WidgetJanitorStep::AfterListOuter), Some(Request::KRequest(req)));
        },
        WidgetJanitorStep::AfterListOuter => {
            if !has_mirror_identity(inner) {
                return (at_step(WidgetJanitorStep::Error), None);
            }
            if !(is_some_k_list_resp!(resp_o) && extract_some_k_list_resp_as_ref!(resp_o).is_ok()) {
                return (at_step(WidgetJanitorStep::Error), None);
            }
            let objs = extract_some_k_list_resp!(resp_o).unwrap();
            proof {
                assert(objs.deep_view() == extract_some_k_list_resp_view(resp_o.deep_view())->Ok_0);
            }
            let parent_uid = parent_uid_annotation(inner);
            if parent_listed(&objs, &parent_uid) {
                return (at_step(WidgetJanitorStep::Done), None);
            }
            let mut preconditions = Preconditions::default();
            preconditions.set_uid_from_object_meta(inner.metadata());
            let req = KubeAPIRequest::DeleteRequest(KubeDeleteRequest {
                api_resource: InnerWidget::api_resource(),
                name: name,
                namespace: namespace,
                preconditions: Some(preconditions),
            });
            return (at_step(WidgetJanitorStep::AfterDeleteInner), Some(Request::KRequest(req)));
        },
        WidgetJanitorStep::AfterDeleteInner => {
            if !is_some_k_delete_resp!(resp_o) {
                return (at_step(WidgetJanitorStep::Error), None);
            }
            let delete_result = extract_some_k_delete_resp!(resp_o);
            if delete_result.is_ok() {
                return (at_step(WidgetJanitorStep::Done), None);
            }
            if delete_result.unwrap_err().is_object_not_found() {
                return (at_step(WidgetJanitorStep::Done), None);
            }
            return (at_step(WidgetJanitorStep::Error), None);
        },
        _ => {
            return (state, None);
        },
    }
}

// Whether `inner` carries the label and annotation of a mirror. See spec_types::has_mirror_identity.
pub fn has_mirror_identity(inner: &InnerWidget) -> (b: bool)
    ensures b == spec_types::has_mirror_identity(inner@),
{
    let labels = inner.metadata().labels();
    let annotations = inner.metadata().annotations();
    if labels.is_none() || annotations.is_none() {
        return false;
    }
    let managed_by = labels.unwrap().get(&"anvil.dev/managed-by".to_string());
    if managed_by.is_none() {
        return false;
    }
    managed_by.unwrap().eq(&"widget-sync".to_string())
        && annotations.unwrap().contains_key(&"anvil.dev/parent-uid".to_string())
}

// The parent-uid annotation of a mirror. See spec_types::parent_uid_annotation.
pub fn parent_uid_annotation(inner: &InnerWidget) -> (parent_uid: String)
    requires spec_types::has_mirror_identity(inner@),
    ensures parent_uid@ == spec_types::parent_uid_annotation(inner@),
{
    inner.metadata().annotations().unwrap().get(&"anvil.dev/parent-uid".to_string()).unwrap()
}

// Whether some listed outer copy has `parent_uid` as its uid. See model::parent_listed.
pub fn parent_listed(objs: &Vec<DynamicObject>, parent_uid: &String) -> (b: bool)
    ensures b == model::parent_listed(objs.deep_view(), parent_uid@),
{
    let mut found = false;
    let mut i: usize = 0;
    while i < objs.len()
        invariant
            i <= objs.len(),
            found == exists |j: int| 0 <= j < i
                && (#[trigger] objs.deep_view()[j]).metadata.uid is Some
                && int_to_string_view(objs.deep_view()[j].metadata.uid->0) == parent_uid@,
        decreases objs.len() - i,
    {
        let uid = objs[i].metadata().uid();
        proof {
            assert(objs.deep_view()[i as int] == objs[i as int]@);
        }
        if uid.is_some() && uid.unwrap().matches_annotation_value(parent_uid) {
            found = true;
        }
        i = i + 1;
    }
    found
}

}
