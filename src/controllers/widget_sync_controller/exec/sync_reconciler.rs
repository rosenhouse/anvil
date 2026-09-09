// Exec implementation of the sync reconciler of a configured kind: a
// DynReconciler over the shape (exec::synced_object::SyncedObject), instantiated
// at boot with the kind's registry entry and cluster selector. Every function is
// proved to conform to its counterpart in model::sync_reconciler, which carries
// the comments.
use crate::kubernetes_api_objects::error::APIError;
use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::exec::{api_resource::*, registry::*, synced_object::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::spec::cluster::Cluster;
use crate::kubernetes_cluster::spec::controller::types::ReconcileModel;
use crate::kubernetes_cluster::spec::install_helpers::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::model::sync_reconciler;
use crate::widget_sync_controller::trusted::exec_types;
use crate::widget_sync_controller::trusted::spec_types;
use crate::widget_sync_controller::trusted::{exec_types::*, spec_types::*, step::*};
use vstd::prelude::*;

verus! {

pub struct WidgetSyncReconcileState {
    pub reconcile_step: WidgetSyncStep,
}

impl View for WidgetSyncReconcileState {
    type V = sync_reconciler::WidgetSyncReconcileState;

    open spec fn view(&self) -> sync_reconciler::WidgetSyncReconcileState {
        sync_reconciler::WidgetSyncReconcileState {
            reconcile_step: self.reconcile_step@,
        }
    }
}

// The reconciler of one configured kind.
pub struct SyncReconciler {
    pub kind: SyncKindExec,
}

// What the model's four closures compute on the marshalled forms; the two
// lemmas of install_helpers, instantiated at the sync reconciler's closures.
pub proof fn lemma_sync_model_transition(k: SyncKind, cr: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, s: sync_reconciler::WidgetSyncReconcileState)
    requires cr.kind == k.outer_kind, status_ok(cr.status),
    ensures
        (widget_sync_controller_model(k).reconcile_model.transition)(marshal(cr), marshal_response_view::<VoidERespView>(resp_o), s.marshal())
            == (sync_reconciler::reconcile_core(k, cr, resp_o, s).0.marshal(),
                marshal_request_view::<VoidEReqView>(sync_reconciler::reconcile_core(k, cr, resp_o, s).1)),
{
    lemma_synced_reconcile_model_transition::<sync_reconciler::WidgetSyncReconcileState, VoidEReqView, VoidERespView>(
        k.outer_kind,
        || sync_reconciler::reconcile_init_state(),
        |obj: SyncedObjectView, resp_o, s| sync_reconciler::reconcile_core(k, obj, resp_o, s),
        |s| sync_reconciler::reconcile_done(s),
        |s| sync_reconciler::reconcile_error(s),
        cr, resp_o, s,
    );
}

pub proof fn lemma_sync_model_init_done_error(k: SyncKind, s: sync_reconciler::WidgetSyncReconcileState)
    ensures
        (widget_sync_controller_model(k).reconcile_model.init)() == sync_reconciler::reconcile_init_state().marshal(),
        (widget_sync_controller_model(k).reconcile_model.done)(s.marshal()) == sync_reconciler::reconcile_done(s),
        (widget_sync_controller_model(k).reconcile_model.error)(s.marshal()) == sync_reconciler::reconcile_error(s),
{
    lemma_synced_reconcile_model_init_done_error::<sync_reconciler::WidgetSyncReconcileState, VoidEReqView, VoidERespView>(
        k.outer_kind,
        || sync_reconciler::reconcile_init_state(),
        |obj: SyncedObjectView, resp_o, s| sync_reconciler::reconcile_core(k, obj, resp_o, s),
        |s| sync_reconciler::reconcile_done(s),
        |s| sync_reconciler::reconcile_error(s),
        s,
    );
}

impl DynReconciler for SyncReconciler {
    type S = WidgetSyncReconcileState;
    type K = SyncedObject;
    type EReq = VoidEReq;
    type EResp = VoidEResp;

    open spec fn model(&self) -> ReconcileModel {
        widget_sync_controller_model(self.kind@).reconcile_model
    }

    fn reconcile_init_state(&self) -> (state: WidgetSyncReconcileState) {
        proof { lemma_sync_model_init_done_error(self.kind@, sync_reconciler::reconcile_init_state()); }
        WidgetSyncReconcileState { reconcile_step: WidgetSyncStep::Init }
    }

    fn reconcile_done(&self, state: &WidgetSyncReconcileState) -> (res: bool) {
        proof { lemma_sync_model_init_done_error(self.kind@, state@); }
        match state.reconcile_step {
            WidgetSyncStep::Done => true,
            _ => false,
        }
    }

    fn reconcile_error(&self, state: &WidgetSyncReconcileState) -> (res: bool) {
        proof { lemma_sync_model_init_done_error(self.kind@, state@); }
        match state.reconcile_step {
            WidgetSyncStep::Error => true,
            _ => false,
        }
    }

    fn reconcile_core(&self, outer: &SyncedObject, resp_o: Option<Response<VoidEResp>>, state: WidgetSyncReconcileState) -> (res: (WidgetSyncReconcileState, Option<Request<VoidEReq>>)) {
        proof {
            synced_object_status_is_representable(*outer);
            lemma_sync_model_transition(self.kind@, outer@, resp_o.deep_view(), state@);
        }
        let res = reconcile_core(&self.kind, outer, resp_o, state);
        res
    }
}

pub fn at_step(step: WidgetSyncStep) -> (state: WidgetSyncReconcileState)
    ensures state@ == sync_reconciler::at_step(step@),
{
    WidgetSyncReconcileState { reconcile_step: step }
}

// The binding of `outer`: its namespace and the cluster its selector names, or
// the empty name when it names none. See spec_types::binding_of.
pub fn binding_of(kind: &SyncKindExec, outer: &SyncedObject) -> (b: ClusterRef)
    requires outer@.metadata.well_formed_for_namespaced(),
    ensures b@ == spec_types::binding_of(kind@, outer@),
{
    let name = match outer.cluster_of(&kind.selector) {
        Some(c) => c,
        None => "".to_string(),
    };
    ClusterRef::new(outer.metadata().namespace().unwrap(), name)
}

pub fn reconcile_core(kind: &SyncKindExec, outer: &SyncedObject, resp_o: Option<Response<VoidEResp>>, state: WidgetSyncReconcileState) -> (res: (WidgetSyncReconcileState, Option<Request<VoidEReq>>))
    requires
        outer@.metadata.well_formed_for_namespaced(),
        outer@.kind == kind@.outer_kind,
    ensures (res.0@, res.1.deep_view()) == sync_reconciler::reconcile_core(kind@, outer@, resp_o.deep_view(), state@),
{
    let namespace = outer.metadata().namespace().unwrap();
    let name = outer.metadata().name().unwrap();
    match state.reconcile_step {
        WidgetSyncStep::Init => {
            let selected = outer.cluster_of(&kind.selector);
            if selected.is_none() {
                // The object names no inner cluster: report the rejection and end.
                return write_outer_status_or_done(kind, outer, reported_status(kind, outer, SyncOutcome::Failed(FailureReason::Rejected)));
            }
            let binding = binding_of(kind, outer);
            if !kind.knows(&binding) {
                // Not a binding this reconciler was built with: report the inner
                // cluster as unreachable and requeue, without addressing it.
                return report_error(kind, outer, reported_status(kind, outer, SyncOutcome::Failed(FailureReason::InnerUnreachable)));
            }
            let req = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: kind.inner_api_resource(&binding),
                name: name,
                namespace: namespace,
            });
            return (at_step(WidgetSyncStep::AfterGetInner), Some(Request::KRequest(req)));
        },
        WidgetSyncStep::AfterGetInner => {
            if !is_some_k_get_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let binding = binding_of(kind, outer);
            let inner_cluster = ClusterId::Remote(binding.clone());
            let get_result = extract_some_k_get_resp!(resp_o);
            if get_result.is_err() {
                let err = get_result.unwrap_err();
                if err.is_object_not_found() {
                    if !kind.knows(&binding) {
                        // Never reached: Init refused this binding, so no Get of its
                        // mirror was sent. See model::sync_reconciler.
                        return (at_step(WidgetSyncStep::Error), None);
                    }
                    let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                        api_resource: kind.entry.api_resource(&inner_cluster),
                        namespace: namespace,
                        obj: make_inner(kind, outer).marshal(),
                    });
                    return (at_step(WidgetSyncStep::AfterCreateInner), Some(Request::KRequest(req)));
                }
                return report_error(kind, outer, failure_status(kind, outer, &err, false));
            }
            let unmarshalled = SyncedObject::unmarshal(&kind.entry, &inner_cluster, get_result.unwrap());
            if unmarshalled.is_err() {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let inner = unmarshalled.unwrap();
            if inner.metadata().has_deletion_timestamp() {
                return write_outer_status_or_done(kind, outer, reported_status(kind, outer, SyncOutcome::InnerTerminating));
            }
            if !is_mirror_of(&inner, outer) {
                let outcome = if has_mirror_identity(&inner) { SyncOutcome::StaleMirror } else { SyncOutcome::ForeignObject };
                return write_outer_status_or_done(kind, outer, reported_status(kind, outer, outcome));
            }
            if !inner.spec().eq(&outer.spec()) {
                let req = KubeAPIRequest::PatchRequest(inner_spec_patch(kind, &inner, outer));
                return (at_step(WidgetSyncStep::AfterPatchInner), Some(Request::KRequest(req)));
            }
            if inner_caught_up(&inner) {
                let generation = outer.metadata().generation();
                let inner_status = inner.status();
                let status = exec_types::outer_status_for(generation, &inner_status, &SyncOutcome::Synced);
                return write_outer_status_or_done(kind, outer, status);
            }
            return write_outer_status_or_done(kind, outer, reported_status(kind, outer, SyncOutcome::InnerConverging));
        },
        WidgetSyncStep::AfterCreateInner => {
            if !is_some_k_create_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let create_result = extract_some_k_create_resp!(resp_o);
            if create_result.is_ok() {
                return (at_step(WidgetSyncStep::Done), None);
            }
            return report_error(kind, outer, failure_status(kind, outer, &create_result.unwrap_err(), true));
        },
        WidgetSyncStep::AfterPatchInner => {
            if !is_some_k_patch_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let patch_result = extract_some_k_patch_resp!(resp_o);
            if patch_result.is_ok() {
                return (at_step(WidgetSyncStep::Done), None);
            }
            return report_error(kind, outer, failure_status(kind, outer, &patch_result.unwrap_err(), false));
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

// The mirror the sync controller creates for `outer`. See spec_types::make_inner.
pub fn make_inner(kind: &SyncKindExec, outer: &SyncedObject) -> (inner: SyncedObject)
    requires
        outer@.metadata.well_formed_for_namespaced(),
        outer@.metadata.uid is Some,
    ensures inner@ == spec_types::make_inner(kind@, outer@),
{
    let mut metadata = ObjectMeta::default();
    metadata.set_name(outer.metadata().name().unwrap());
    metadata.set_namespace(outer.metadata().namespace().unwrap());
    metadata.add_label("anvil.dev/managed-by".to_string(), "widget-sync".to_string());
    metadata.add_annotation("anvil.dev/parent-uid".to_string(), outer.metadata().uid().unwrap().as_annotation_value());
    SyncedObject::new(&kind.entry, &ClusterId::Remote(binding_of(kind, outer)), metadata, outer.spec())
}

// Whether `inner` is the mirror of `outer`. See spec_types::is_mirror_of.
pub fn is_mirror_of(inner: &SyncedObject, outer: &SyncedObject) -> (b: bool)
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

// Whether `inner` carries the managed-by label and a parent-uid annotation.
// See spec_types::has_mirror_identity.
pub fn has_mirror_identity(inner: &SyncedObject) -> (b: bool)
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
// See spec_types::inner_caught_up.
pub fn inner_caught_up(inner: &SyncedObject) -> (b: bool)
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
pub fn inner_spec_patch(kind: &SyncKindExec, inner: &SyncedObject, outer: &SyncedObject) -> (req: KubePatchRequest)
    requires
        outer@.metadata.well_formed_for_namespaced(),
        inner@.kind == spec_types::inner_key(kind@, outer@).kind,
    ensures req@ == sync_reconciler::inner_spec_patch(kind@, inner@, outer@),
{
    let mut tests = PatchTests::default();
    tests.set_uid_from_object_meta(inner.metadata());
    tests.set_generation_from_object_meta(inner.metadata());
    let mut patched = inner.clone();
    patched.set_spec(outer.spec());
    KubePatchRequest {
        api_resource: inner.api_resource(),
        name: outer.metadata().name().unwrap(),
        namespace: outer.metadata().namespace().unwrap(),
        tests: tests,
        obj: patched.marshal(),
    }
}

// The JSON patch that writes `status` on the outer copy. See model::outer_status_patch.
pub fn outer_status_patch(kind: &SyncKindExec, outer: &SyncedObject, status: SyncedStatus) -> (req: KubePatchStatusRequest)
    requires outer@.metadata.well_formed_for_namespaced(),
    ensures req@ == sync_reconciler::outer_status_patch(kind@, outer@, status@),
{
    let mut tests = PatchTests::default();
    tests.set_uid_from_object_meta(outer.metadata());
    tests.set_generation_from_object_meta(outer.metadata());
    let mut with_status = outer.clone();
    with_status.set_status(status);
    KubePatchStatusRequest {
        api_resource: kind.outer_api_resource(),
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

// The status that reports `outcome` without consulting the inner status.
// See model::reported_status.
pub fn reported_status(kind: &SyncKindExec, outer: &SyncedObject, outcome: SyncOutcome) -> (status: SyncedStatus)
    ensures status@ == sync_reconciler::reported_status(outer@, outcome@),
{
    let generation = outer.metadata().generation();
    let source = outer.status();
    exec_types::outer_status_for(generation, &source, &outcome)
}

// The status that reports a failed request. See model::failure_status.
pub fn failure_status(kind: &SyncKindExec, outer: &SyncedObject, err: &APIError, answering_create: bool) -> (status: SyncedStatus)
    ensures status@ == sync_reconciler::failure_status(outer@, *err, answering_create),
{
    reported_status(kind, outer, SyncOutcome::Failed(error_reason(err, answering_create)))
}

// Report a failed request in the outer status, then end in Error. See model::report_error.
pub fn report_error(kind: &SyncKindExec, outer: &SyncedObject, status: SyncedStatus) -> (res: (WidgetSyncReconcileState, Option<Request<VoidEReq>>))
    requires outer@.metadata.well_formed_for_namespaced(),
    ensures (res.0@, res.1.deep_view()) == sync_reconciler::report_error(kind@, outer@, status@),
{
    let current = outer.status();
    if current.is_some() && current.as_ref().unwrap().eq(&status) {
        (at_step(WidgetSyncStep::Error), None)
    } else {
        let req = KubeAPIRequest::PatchStatusRequest(outer_status_patch(kind, outer, status));
        (at_step(WidgetSyncStep::AfterReportError), Some(Request::KRequest(req)))
    }
}

// Write `status` to the outer copy unless it already has it.
// See model::write_outer_status_or_done.
pub fn write_outer_status_or_done(kind: &SyncKindExec, outer: &SyncedObject, status: SyncedStatus) -> (res: (WidgetSyncReconcileState, Option<Request<VoidEReq>>))
    requires outer@.metadata.well_formed_for_namespaced(),
    ensures (res.0@, res.1.deep_view()) == sync_reconciler::write_outer_status_or_done(kind@, outer@, status@),
{
    let current = outer.status();
    if current.is_some() && current.as_ref().unwrap().eq(&status) {
        (at_step(WidgetSyncStep::Done), None)
    } else {
        let req = KubeAPIRequest::PatchStatusRequest(outer_status_patch(kind, outer, status));
        (at_step(WidgetSyncStep::AfterPatchOuterStatus), Some(Request::KRequest(req)))
    }
}

}
