// Exec implementation of the sync reconciler; every function is proved to conform
// to its counterpart in model::sync_reconciler, which carries the comments.
use crate::kubernetes_api_objects::error::APIError;
use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::model::sync_reconciler as model;
use crate::widget_sync_controller::trusted::spec_types;
use crate::widget_sync_controller::trusted::{exec_types::*, spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct WidgetSyncReconcileState {
    pub reconcile_step: WidgetSyncStep,
}

impl View for WidgetSyncReconcileState {
    type V = model::WidgetSyncReconcileState;

    open spec fn view(&self) -> model::WidgetSyncReconcileState {
        model::WidgetSyncReconcileState {
            reconcile_step: self.reconcile_step@,
        }
    }
}

pub struct WidgetSyncReconciler {}

impl Reconciler for WidgetSyncReconciler {
    type S = WidgetSyncReconcileState;
    type K = OuterWidget;
    type EReq = VoidEReq;
    type EResp = VoidEResp;
    type M = model::WidgetSyncReconciler;

    fn reconcile_init_state() -> Self::S {
        reconcile_init_state()
    }

    fn reconcile_core(outer: &Self::K, resp_o: Option<Response<Self::EResp>>, state: Self::S) -> (Self::S, Option<Request<Self::EReq>>) {
        reconcile_core(outer, resp_o, state)
    }

    fn reconcile_done(state: &Self::S) -> bool {
        reconcile_done(state)
    }

    fn reconcile_error(state: &Self::S) -> bool {
        reconcile_error(state)
    }
}

pub fn reconcile_init_state() -> (state: WidgetSyncReconcileState)
    ensures state@ == model::reconcile_init_state(),
{
    WidgetSyncReconcileState {
        reconcile_step: WidgetSyncStep::Init,
    }
}

pub fn reconcile_done(state: &WidgetSyncReconcileState) -> (res: bool)
    ensures res == model::reconcile_done(state@),
{
    match state.reconcile_step {
        WidgetSyncStep::Done => true,
        _ => false,
    }
}

pub fn reconcile_error(state: &WidgetSyncReconcileState) -> (res: bool)
    ensures res == model::reconcile_error(state@),
{
    match state.reconcile_step {
        WidgetSyncStep::Error => true,
        _ => false,
    }
}

fn at_step(step: WidgetSyncStep) -> (state: WidgetSyncReconcileState)
    ensures state@ == model::at_step(step@),
{
    WidgetSyncReconcileState { reconcile_step: step }
}

pub fn reconcile_core(outer: &OuterWidget, resp_o: Option<Response<VoidEResp>>, state: WidgetSyncReconcileState) -> (res: (WidgetSyncReconcileState, Option<Request<VoidEReq>>))
    requires outer@.well_formed(),
    ensures (res.0@, res.1.deep_view()) == model::reconcile_core(outer@, resp_o.deep_view(), state@),
{
    let namespace = outer.metadata().namespace().unwrap();
    let name = outer.metadata().name().unwrap();
    match state.reconcile_step {
        WidgetSyncStep::Init => {
            let req = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: InnerWidget::api_resource(),
                name: name,
                namespace: namespace,
            });
            return (at_step(WidgetSyncStep::AfterGetInner), Some(Request::KRequest(req)));
        },
        WidgetSyncStep::AfterGetInner => {
            if !is_some_k_get_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let get_result = extract_some_k_get_resp!(resp_o);
            if get_result.is_err() {
                let err = get_result.unwrap_err();
                if err.is_object_not_found() {
                    let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: InnerWidget::api_resource(),
                        namespace: namespace,
                        obj: make_inner(outer).marshal(),
                    });
                    return (at_step(WidgetSyncStep::AfterCreateInner), Some(Request::KRequest(req)));
                }
                return report_error(outer, failure_status(outer, &err, false));
            }
            let unmarshalled = InnerWidget::unmarshal(get_result.unwrap());
            if unmarshalled.is_err() {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let inner = unmarshalled.unwrap();
            if inner.metadata().has_deletion_timestamp() {
                return write_outer_status_or_done(outer, reported_status(outer, SyncOutcome::InnerTerminating));
            }
            if !is_mirror_of(&inner, outer) {
                let outcome = if has_mirror_identity(&inner) { SyncOutcome::StaleMirror } else { SyncOutcome::ForeignObject };
                return write_outer_status_or_done(outer, reported_status(outer, outcome));
            }
            if !inner.spec().eq(&outer.spec()) {
                let req = KubeAPIRequest::PatchRequest(inner_spec_patch(&inner, outer));
                return (at_step(WidgetSyncStep::AfterPatchInner), Some(Request::KRequest(req)));
            }
            if inner_caught_up(&inner) {
                let inner_status = match inner.status() {
                    Some(s) => s,
                    None => {
                        assert(false);
                        WidgetStatus::default()
                    },
                };
                let generation = outer.metadata().generation();
                proof {
                    assert(opt_i64_view(generation) == outer@.metadata.generation);
                }
                let status = WidgetStatus::outer_status_for(generation, &inner_status, &SyncOutcome::Synced);
                return write_outer_status_or_done(outer, status);
            }
            return write_outer_status_or_done(outer, reported_status(outer, SyncOutcome::InnerConverging));
        },
        WidgetSyncStep::AfterCreateInner => {
            if !is_some_k_create_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let create_result = extract_some_k_create_resp!(resp_o);
            if create_result.is_ok() {
                return (at_step(WidgetSyncStep::Done), None);
            }
            return report_error(outer, failure_status(outer, &create_result.unwrap_err(), true));
        },
        WidgetSyncStep::AfterPatchInner => {
            if !is_some_k_patch_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let patch_result = extract_some_k_patch_resp!(resp_o);
            if patch_result.is_ok() {
                return (at_step(WidgetSyncStep::Done), None);
            }
            return report_error(outer, failure_status(outer, &patch_result.unwrap_err(), false));
        },
        WidgetSyncStep::AfterPatchOuterStatus => {
            if is_some_k_patch_status_resp!(resp_o) && extract_some_k_patch_status_resp_as_ref!(resp_o).is_ok() {
                return (at_step(WidgetSyncStep::Done), None);
            }
            return (at_step(WidgetSyncStep::Error), None);
        },
        WidgetSyncStep::AfterReportError => {
            return (at_step(WidgetSyncStep::Error), None);
        },
        _ => {
            return (state, None);
        },
    }
}

// The mirror the sync controller creates for `outer`. See make_inner.
pub fn make_inner(outer: &OuterWidget) -> (inner: InnerWidget)
    requires outer@.well_formed(),
    ensures inner@ == spec_types::make_inner(outer@),
{
    let mut inner = InnerWidget::default();
    let mut metadata = ObjectMeta::default();
    metadata.set_name(outer.metadata().name().unwrap());
    metadata.set_namespace(outer.metadata().namespace().unwrap());
    metadata.add_label("anvil.dev/managed-by".to_string(), "widget-sync".to_string());
    metadata.add_annotation("anvil.dev/parent-uid".to_string(), outer.metadata().uid().unwrap().as_annotation_value());
    inner.set_metadata(metadata);
    inner.set_spec(outer.spec());
    inner
}

// Whether `inner` is the mirror of `outer`. See is_mirror_of.
pub fn is_mirror_of(inner: &InnerWidget, outer: &OuterWidget) -> (b: bool)
    requires outer@.metadata.uid is Some,
    ensures b == spec_types::is_mirror_of(inner@, outer@),
{
    let labels = inner.metadata().labels();
    let annotations = inner.metadata().annotations();
    if labels.is_none() || annotations.is_none() {
        return false;
    }
    let managed_by = labels.unwrap().get(&"anvil.dev/managed-by".to_string());
    let parent_uid = annotations.unwrap().get(&"anvil.dev/parent-uid".to_string());
    if managed_by.is_none() || parent_uid.is_none() {
        return false;
    }
    managed_by.unwrap().eq(&"widget-sync".to_string())
        && outer.metadata().uid().unwrap().matches_annotation_value(&parent_uid.unwrap())
}

// Whether `inner` carries the managed-by label and a parent-uid annotation, that
// is, is a mirror of some outer copy. See has_mirror_identity.
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

// Whether the inner implementation has processed the mirror's current spec.
// See inner_caught_up.
pub fn inner_caught_up(inner: &InnerWidget) -> (b: bool)
    ensures b == spec_types::inner_caught_up(inner@),
{
    let status = inner.status();
    if status.is_none() {
        return false;
    }
    let observed_generation = status.unwrap().observed_generation();
    let generation = inner.metadata().generation();
    observed_generation.is_some() && generation.is_some()
        && observed_generation.unwrap() == generation.unwrap()
}

// The JSON patch that propagates the outer spec to the mirror. See model::inner_spec_patch.
pub fn inner_spec_patch(inner: &InnerWidget, outer: &OuterWidget) -> (req: KubePatchRequest)
    requires outer@.well_formed(),
    ensures req@ == model::inner_spec_patch(inner@, outer@),
{
    let mut tests = PatchTests::default();
    tests.set_uid_from_object_meta(inner.metadata());
    tests.set_generation_from_object_meta(inner.metadata());
    let mut patched = inner.clone();
    patched.set_spec(outer.spec());
    KubePatchRequest {
        api_resource: InnerWidget::api_resource(),
        name: outer.metadata().name().unwrap(),
        namespace: outer.metadata().namespace().unwrap(),
        tests: tests,
        obj: patched.marshal(),
    }
}

// The JSON patch that writes `status` on the outer copy. See model::outer_status_patch.
pub fn outer_status_patch(outer: &OuterWidget, status: WidgetStatus) -> (req: KubePatchStatusRequest)
    requires outer@.well_formed(),
    ensures req@ == model::outer_status_patch(outer@, status@),
{
    let mut tests = PatchTests::default();
    tests.set_uid_from_object_meta(outer.metadata());
    tests.set_generation_from_object_meta(outer.metadata());
    let mut with_status = outer.clone();
    with_status.set_status(status);
    KubePatchStatusRequest {
        api_resource: OuterWidget::api_resource(),
        name: outer.metadata().name().unwrap(),
        namespace: outer.metadata().namespace().unwrap(),
        tests: tests,
        obj: with_status.marshal(),
    }
}

// The reason reported for an error response. See spec_types::error_reason.
pub fn error_reason(err: &APIError, answering_create: bool) -> (reason: FailureReason)
    ensures reason@ == spec_types::error_reason(*err, answering_create),
{
    match err {
        APIError::Forbidden => FailureReason::Forbidden,
        APIError::Timeout => FailureReason::InnerUnreachable,
        APIError::ServerTimeout => FailureReason::InnerUnreachable,
        APIError::InternalError => FailureReason::InnerUnreachable,
        APIError::ObjectNotFound => if answering_create { FailureReason::CreateFailed } else { FailureReason::RequestFailed },
        APIError::Invalid => FailureReason::Rejected,
        APIError::BadRequest => FailureReason::Rejected,
        APIError::NotSupported => FailureReason::Rejected,
        _ => FailureReason::RequestFailed,
    }
}

// The status that reports `outcome` without consulting the inner status. See
// model::reported_status.
pub fn reported_status(outer: &OuterWidget, outcome: SyncOutcome) -> (status: WidgetStatus)
    requires outer@.well_formed(),
    ensures status@ == model::reported_status(outer@, outcome@),
{
    let generation = outer.metadata().generation();
    proof {
        assert(opt_i64_view(generation) == outer@.metadata.generation);
    }
    let source = match outer.status() {
        Some(previous) => previous,
        None => WidgetStatus::default(),
    };
    proof {
        assert(source@ == status_or_default(outer@.status));
    }
    WidgetStatus::outer_status_for(generation, &source, &outcome)
}

// The status that reports a failed request. See model::failure_status.
pub fn failure_status(outer: &OuterWidget, err: &APIError, answering_create: bool) -> (status: WidgetStatus)
    requires outer@.well_formed(),
    ensures status@ == model::failure_status(outer@, *err, answering_create),
{
    reported_status(outer, SyncOutcome::Failed(error_reason(err, answering_create)))
}

// Report a failed request in the outer status, then end in Error. See model::report_error.
pub fn report_error(outer: &OuterWidget, status: WidgetStatus) -> (res: (WidgetSyncReconcileState, Option<Request<VoidEReq>>))
    requires outer@.well_formed(),
    ensures (res.0@, res.1.deep_view()) == model::report_error(outer@, status@),
{
    let current = outer.status();
    if current.is_some() && current.as_ref().unwrap().eq(&status) {
        (at_step(WidgetSyncStep::Error), None)
    } else {
        let req = KubeAPIRequest::PatchStatusRequest(outer_status_patch(outer, status));
        (at_step(WidgetSyncStep::AfterReportError), Some(Request::KRequest(req)))
    }
}

// Write `status` to the outer copy unless it already has it. See model::write_outer_status_or_done.
pub fn write_outer_status_or_done(outer: &OuterWidget, status: WidgetStatus) -> (res: (WidgetSyncReconcileState, Option<Request<VoidEReq>>))
    requires outer@.well_formed(),
    ensures (res.0@, res.1.deep_view()) == model::write_outer_status_or_done(outer@, status@),
{
    let current = outer.status();
    if current.is_some() && current.as_ref().unwrap().eq(&status) {
        (at_step(WidgetSyncStep::Done), None)
    } else {
        let req = KubeAPIRequest::PatchStatusRequest(outer_status_patch(outer, status));
        (at_step(WidgetSyncStep::AfterPatchOuterStatus), Some(Request::KRequest(req)))
    }
}

}
