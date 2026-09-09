// Exec implementation of the janitor reconciler of a configured kind and a
// binding: a DynReconciler over the shape, instantiated at boot with the kind's
// registry entry, its cluster selector and the binding. Every function is proved
// to conform to its counterpart in model::janitor_reconciler.
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
use crate::widget_sync_controller::exec::sync_reconciler::{has_mirror_identity};
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::model::janitor_reconciler;
use crate::widget_sync_controller::trusted::spec_types;
use crate::widget_sync_controller::trusted::{exec_types::*, spec_types::*, step::*};
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

pub struct WidgetJanitorReconcileState {
    pub reconcile_step: WidgetJanitorStep,
}

impl View for WidgetJanitorReconcileState {
    type V = janitor_reconciler::WidgetJanitorReconcileState;

    open spec fn view(&self) -> janitor_reconciler::WidgetJanitorReconcileState {
        janitor_reconciler::WidgetJanitorReconcileState {
            reconcile_step: self.reconcile_step@,
        }
    }
}

// The janitor of one configured kind in one binding.
pub struct JanitorReconciler {
    pub kind: SyncKindExec,
    pub binding: ClusterRef,
}

pub proof fn lemma_janitor_model_transition(k: SyncKind, b: Binding, cr: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, s: janitor_reconciler::WidgetJanitorReconcileState)
    requires cr.kind == inner_kind(k, b), status_ok(cr.status),
    ensures
        (widget_janitor_controller_model(k, b).reconcile_model.transition)(marshal(cr), marshal_response_view::<VoidERespView>(resp_o), s.marshal())
            == (janitor_reconciler::reconcile_core(k, b, cr, resp_o, s).0.marshal(),
                marshal_request_view::<VoidEReqView>(janitor_reconciler::reconcile_core(k, b, cr, resp_o, s).1)),
{
    lemma_synced_reconcile_model_transition::<janitor_reconciler::WidgetJanitorReconcileState, VoidEReqView, VoidERespView>(
        inner_kind(k, b),
        || janitor_reconciler::reconcile_init_state(),
        |obj: SyncedObjectView, resp_o, s| janitor_reconciler::reconcile_core(k, b, obj, resp_o, s),
        |s| janitor_reconciler::reconcile_done(s),
        |s| janitor_reconciler::reconcile_error(s),
        cr, resp_o, s,
    );
}

pub proof fn lemma_janitor_model_init_done_error(k: SyncKind, b: Binding, s: janitor_reconciler::WidgetJanitorReconcileState)
    ensures
        (widget_janitor_controller_model(k, b).reconcile_model.init)() == janitor_reconciler::reconcile_init_state().marshal(),
        (widget_janitor_controller_model(k, b).reconcile_model.done)(s.marshal()) == janitor_reconciler::reconcile_done(s),
        (widget_janitor_controller_model(k, b).reconcile_model.error)(s.marshal()) == janitor_reconciler::reconcile_error(s),
{
    lemma_synced_reconcile_model_init_done_error::<janitor_reconciler::WidgetJanitorReconcileState, VoidEReqView, VoidERespView>(
        inner_kind(k, b),
        || janitor_reconciler::reconcile_init_state(),
        |obj: SyncedObjectView, resp_o, s| janitor_reconciler::reconcile_core(k, b, obj, resp_o, s),
        |s| janitor_reconciler::reconcile_done(s),
        |s| janitor_reconciler::reconcile_error(s),
        s,
    );
}

impl DynReconciler for JanitorReconciler {
    type S = WidgetJanitorReconcileState;
    type K = SyncedObject;
    type EReq = VoidEReq;
    type EResp = VoidEResp;

    open spec fn model(&self) -> ReconcileModel {
        widget_janitor_controller_model(self.kind@, self.binding@).reconcile_model
    }

    fn reconcile_init_state(&self) -> (state: WidgetJanitorReconcileState) {
        proof { lemma_janitor_model_init_done_error(self.kind@, self.binding@, janitor_reconciler::reconcile_init_state()); }
        WidgetJanitorReconcileState { reconcile_step: WidgetJanitorStep::Init }
    }

    fn reconcile_done(&self, state: &WidgetJanitorReconcileState) -> (res: bool) {
        proof { lemma_janitor_model_init_done_error(self.kind@, self.binding@, state@); }
        match state.reconcile_step {
            WidgetJanitorStep::Done => true,
            _ => false,
        }
    }

    fn reconcile_error(&self, state: &WidgetJanitorReconcileState) -> (res: bool) {
        proof { lemma_janitor_model_init_done_error(self.kind@, self.binding@, state@); }
        match state.reconcile_step {
            WidgetJanitorStep::Error => true,
            _ => false,
        }
    }

    fn reconcile_core(&self, inner: &SyncedObject, resp_o: Option<Response<VoidEResp>>, state: WidgetJanitorReconcileState) -> (res: (WidgetJanitorReconcileState, Option<Request<VoidEReq>>)) {
        proof {
            synced_object_status_is_representable(*inner);
            lemma_janitor_model_transition(self.kind@, self.binding@, inner@, resp_o.deep_view(), state@);
        }
        let res = reconcile_core(&self.kind, &self.binding, inner, resp_o, state);
        res
    }
}

pub fn at_step(step: WidgetJanitorStep) -> (state: WidgetJanitorReconcileState)
    ensures state@ == janitor_reconciler::at_step(step@),
{
    WidgetJanitorReconcileState { reconcile_step: step }
}

pub fn reconcile_core(kind: &SyncKindExec, binding: &ClusterRef, inner: &SyncedObject, resp_o: Option<Response<VoidEResp>>, state: WidgetJanitorReconcileState) -> (res: (WidgetJanitorReconcileState, Option<Request<VoidEReq>>))
    requires inner@.metadata.well_formed_for_namespaced(),
    ensures (res.0@, res.1.deep_view()) == janitor_reconciler::reconcile_core(kind@, binding@, inner@, resp_o.deep_view(), state@),
{
    let namespace = inner.metadata().namespace().unwrap();
    let name = inner.metadata().name().unwrap();
    match state.reconcile_step {
        WidgetJanitorStep::Init => {
            if !has_mirror_identity(inner) {
                return (at_step(WidgetJanitorStep::Done), None);
            }
            let req = KubeAPIRequest::ListRequest(KubeListRequest {
                api_resource: kind.outer_api_resource(),
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
            if parent_listed(kind, binding, &objs, &parent_uid) {
                return (at_step(WidgetJanitorStep::Done), None);
            }
            let mut preconditions = Preconditions::default();
            preconditions.set_uid_from_object_meta(inner.metadata());
            let req = KubeAPIRequest::DeleteRequest(KubeDeleteRequest {
                api_resource: inner.api_resource(),
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

// The parent-uid annotation of a mirror. See spec_types::parent_uid_annotation.
pub fn parent_uid_annotation(inner: &SyncedObject) -> (parent_uid: String)
    requires spec_types::has_mirror_identity(inner@),
    ensures parent_uid@ == spec_types::parent_uid_annotation(inner@),
{
    inner.metadata().annotations().unwrap().get(&"anvil.dev/parent-uid".to_string()).unwrap()
}

// Whether some listed outer copy has `parent_uid` as its uid and names this
// binding's inner cluster; objects of any other kind are ignored.
// See model::parent_listed.
pub fn parent_listed(kind: &SyncKindExec, binding: &ClusterRef, objs: &Vec<DynamicObject>, parent_uid: &String) -> (b: bool)
    ensures b == janitor_reconciler::parent_listed(kind@, binding@, objs.deep_view(), parent_uid@),
{
    let mut found = false;
    let mut i: usize = 0;
    while i < objs.len()
        invariant
            i <= objs.len(),
            found == exists |j: int| 0 <= j < i
                && (#[trigger] objs.deep_view()[j]).kind == kind@.outer_kind
                && objs.deep_view()[j].metadata.uid is Some
                && int_to_string_view(objs.deep_view()[j].metadata.uid->0) == parent_uid@
                && crate::kubernetes_api_objects::spec::synced_object::cluster_of_dynamic(kind@.selector, objs.deep_view()[j]) == Some(binding@.name),
        decreases objs.len() - i,
    {
        // The registry's kind test, not DynamicObject::kind(): the latter reports
        // the API server's kind string, which for a custom resource is not the
        // model kind (see SyncedObject::has_kind).
        let primary = ClusterId::Primary;
        let is_outer = SyncedObject::has_kind(&kind.entry, &primary, &objs[i]);
        let uid = objs[i].metadata().uid();
        let cluster = crate::kubernetes_api_objects::exec::synced_object::cluster_of_dynamic(&kind.selector, &objs[i]);
        let uid_matches = match &uid {
            Some(u) => u.matches_annotation_value(parent_uid),
            None => false,
        };
        let cluster_matches = match &cluster {
            Some(c) => string_equal(c, binding.name.as_str()),
            None => false,
        };
        let hit = is_outer && uid_matches && cluster_matches;
        proof {
            let o = objs.deep_view()[i as int];
            assert(o == objs[i as int]@);
            assert(is_outer == (objs[i as int]@.kind == crate::kubernetes_api_objects::spec::model_kind::model_kind(kind.entry@, crate::kubernetes_api_objects::spec::api_resource::ClusterIdView::Primary)));
            assert(is_outer == (o.kind == kind@.outer_kind));
            assert(cluster.deep_view() == crate::kubernetes_api_objects::spec::synced_object::cluster_of_dynamic(kind@.selector, o));
            assert(cluster_matches == (crate::kubernetes_api_objects::spec::synced_object::cluster_of_dynamic(kind@.selector, o) == Some(binding@.name))) by {
                match &cluster {
                    Some(c) => { assert(cluster.deep_view() == Some(c@)); },
                    None => {},
                }
            }
            assert(uid_matches == (o.metadata.uid is Some && int_to_string_view(o.metadata.uid->0) == parent_uid@)) by {
                match &uid {
                    Some(u) => {},
                    None => {},
                }
            }
            assert(hit == (o.kind == kind@.outer_kind
                && o.metadata.uid is Some
                && int_to_string_view(o.metadata.uid->0) == parent_uid@
                && crate::kubernetes_api_objects::spec::synced_object::cluster_of_dynamic(kind@.selector, o) == Some(binding@.name)));
        }
        if hit {
            found = true;
        }
        i = i + 1;
    }
    found
}

}
