// Exec implementation of the sync reconciler of a configured kind: a
// DynReconciler over the shape (exec::synced_object::SyncedObject), instantiated
// at boot with the kind's registry entry and cluster selector. Every function is
// proved to conform to its counterpart in model::sync_reconciler, which carries
// the comments.
use crate::kubernetes_api_objects::error::APIError;
use crate::kubernetes_api_objects::exec::prelude::*;
use crate::kubernetes_api_objects::exec::{api_resource::*, registry::*, synced_object::*};
use crate::kubernetes_api_objects::spec::model_kind::*;
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
        proof { lemma_sync_model_transition(self.kind@, outer@, resp_o.deep_view(), state@); }
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
            if outer.metadata().has_deletion_timestamp() {
                if !has_sync_finalizer(&outer.metadata()) {
                    // Terminating without the sync finalizer: not ours to tear down.
                    return (at_step(WidgetSyncStep::Done), None);
                }
                let selected = outer.cluster_of(&kind.selector);
                let binding = binding_of(kind, outer);
                if selected.is_none() || !kind.knows(&binding) {
                    // No inner cluster this controller can address: release rather
                    // than hold the copy for ever.
                    let req = KubeAPIRequest::UpdateRequest(outer_finalizer_update(kind, outer, false));
                    return (at_step(WidgetSyncStep::AfterRemoveFinalizer), Some(Request::KRequest(req)));
                }
                // Teardown: read the mirror key.
                let req = KubeAPIRequest::ListRequest(mirror_list(kind, outer));
                return (at_step(WidgetSyncStep::AfterListMirror), Some(Request::KRequest(req)));
            }
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
            if !has_sync_finalizer(&outer.metadata()) {
                // Take ownership before any mirror exists.
                let req = KubeAPIRequest::UpdateRequest(outer_finalizer_update(kind, outer, true));
                return (at_step(WidgetSyncStep::AfterAddFinalizer), Some(Request::KRequest(req)));
            }
            let req = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: kind.inner_api_resource(&binding),
                name: name,
                namespace: namespace,
            });
            return (at_step(WidgetSyncStep::AfterGetInner), Some(Request::KRequest(req)));
        },
        // The Update of the finalizers either landed or did not. See the model.
        WidgetSyncStep::AfterAddFinalizer => {
            if !is_some_k_update_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            if extract_some_k_update_resp!(resp_o).is_ok() {
                return (at_step(WidgetSyncStep::Done), None);
            }
            return (at_step(WidgetSyncStep::Error), None);
        },
        WidgetSyncStep::AfterRemoveFinalizer => {
            if !is_some_k_update_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            if extract_some_k_update_resp!(resp_o).is_ok() {
                return (at_step(WidgetSyncStep::Done), None);
            }
            return (at_step(WidgetSyncStep::Error), None);
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
            if patch_result.is_err() {
                return report_error(kind, outer, failure_status(kind, outer, &patch_result.unwrap_err(), false));
            }
            let inner_cluster = ClusterId::Remote(binding_of(kind, outer));
            let unmarshalled = SyncedObject::unmarshal(&kind.entry, &inner_cluster, patch_result.unwrap());
            if unmarshalled.is_err() {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let patched = unmarshalled.unwrap();
            if !patched.spec().eq(&outer.spec()) {
                // The inner cluster stored another spec than the one written.
                return write_outer_status_or_done(kind, outer, reported_status(kind, outer, SyncOutcome::Failed(FailureReason::SpecRewritten)));
            }
            return (at_step(WidgetSyncStep::Done), None);
        },
        WidgetSyncStep::AfterListMirror => {
            if !is_some_k_list_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let list_result = extract_some_k_list_resp!(resp_o);
            if list_result.is_err() {
                // A teardown writes no status; see the model.
                return (at_step(WidgetSyncStep::Error), None);
            }
            let objs = list_result.unwrap();
            let binding = binding_of(kind, outer);
            let inner_cluster = ClusterId::Remote(binding.clone());
            let listed = listed_at(&kind.entry, &inner_cluster, &namespace, &name, &objs);
            proof {
                assert(ObjectRef { kind: model_kind(kind.entry@, inner_cluster@), namespace: namespace@, name: name@ } == spec_types::inner_key(kind@, outer@));
            }
            if !listed {
                // Confirmed gone: release.
                let req = KubeAPIRequest::UpdateRequest(outer_finalizer_update(kind, outer, false));
                return (at_step(WidgetSyncStep::AfterRemoveFinalizer), Some(Request::KRequest(req)));
            }
            // Something is at the mirror key: read it.
            let req = KubeAPIRequest::GetRequest(KubeGetRequest {
                api_resource: kind.inner_api_resource(&binding),
                name: name,
                namespace: namespace,
            });
            return (at_step(WidgetSyncStep::AfterGetMirror), Some(Request::KRequest(req)));
        },
        WidgetSyncStep::AfterGetMirror => {
            if !is_some_k_get_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let binding = binding_of(kind, outer);
            let inner_cluster = ClusterId::Remote(binding.clone());
            let get_result = extract_some_k_get_resp!(resp_o);
            if get_result.is_err() {
                let err = get_result.unwrap_err();
                if err.is_object_not_found() {
                    // Gone since the List: the next reconcile confirms that.
                    return (at_step(WidgetSyncStep::Done), None);
                }
                return (at_step(WidgetSyncStep::Error), None);
            }
            let unmarshalled = SyncedObject::unmarshal(&kind.entry, &inner_cluster, get_result.unwrap());
            if unmarshalled.is_err() {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let inner = unmarshalled.unwrap();
            if !is_mirror_of(&inner, outer) {
                // Not ours: nothing of ours is left at the key. Release.
                let req = KubeAPIRequest::UpdateRequest(outer_finalizer_update(kind, outer, false));
                return (at_step(WidgetSyncStep::AfterRemoveFinalizer), Some(Request::KRequest(req)));
            }
            if inner.metadata().has_deletion_timestamp() {
                // Being released by the inner side: wait for it.
                return (at_step(WidgetSyncStep::Done), None);
            }
            if inner.metadata().uid().is_none() {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let req = KubeAPIRequest::DeleteRequest(mirror_delete(kind, outer, &binding, &inner));
            return (at_step(WidgetSyncStep::AfterDeleteMirror), Some(Request::KRequest(req)));
        },
        WidgetSyncStep::AfterDeleteMirror => {
            if !is_some_k_delete_resp!(resp_o) {
                return (at_step(WidgetSyncStep::Error), None);
            }
            let delete_result = extract_some_k_delete_resp!(resp_o);
            if delete_result.is_ok() {
                return (at_step(WidgetSyncStep::Done), None);
            }
            if delete_result.unwrap_err().is_object_not_found() {
                return (at_step(WidgetSyncStep::Done), None);
            }
            return (at_step(WidgetSyncStep::Error), None);
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

// Whether `meta` carries the sync finalizer. See spec_types::has_sync_finalizer.
pub fn has_sync_finalizer(meta: &ObjectMeta) -> (b: bool)
    ensures b == spec_types::has_sync_finalizer(meta@),
{
    let finalizers = meta.finalizers();
    if finalizers.is_none() {
        return false;
    }
    let finalizers = finalizers.unwrap();
    let ghost all = meta@.finalizers->0;
    proof { assert(finalizers.deep_view() =~= all); }
    let mut i: usize = 0;
    while i < finalizers.len()
        invariant
            0 <= i <= finalizers.len(),
            meta@.finalizers is Some,
            all == meta@.finalizers->0,
            finalizers.deep_view() == all,
            forall |j: int| 0 <= j < i ==> #[trigger] all[j] != sync_finalizer(),
        decreases finalizers.len() - i,
    {
        let f = finalizers[i].clone();
        proof { assert(f@ == all[i as int]); }
        if f.eq(&"anvil.dev/widget-sync".to_string()) {
            proof {
                assert(all[i as int] == sync_finalizer());
                assert(all.contains(sync_finalizer()));
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        assert forall |j: int| 0 <= j < all.len() implies #[trigger] all[j] != sync_finalizer() by {}
        assert(!all.contains(sync_finalizer()));
    }
    false
}

// `meta` with the sync finalizer appended. See spec_types::with_sync_finalizer.
pub fn with_sync_finalizer(meta: &ObjectMeta) -> (res: ObjectMeta)
    ensures res@ == spec_types::with_sync_finalizer(meta@),
{
    let mut finalizers = match meta.finalizers() {
        Some(f) => f,
        None => Vec::new(),
    };
    proof { assert(finalizers.deep_view() =~= finalizers_or_empty(meta@)); }
    finalizers.push("anvil.dev/widget-sync".to_string());
    proof { assert(finalizers.deep_view() =~= finalizers_or_empty(meta@).push(sync_finalizer())); }
    let mut res = meta.clone();
    res.set_finalizers(finalizers);
    res
}

// `meta` without the sync finalizer. See spec_types::without_sync_finalizer.
pub fn without_sync_finalizer(meta: &ObjectMeta) -> (res: ObjectMeta)
    ensures res@ == spec_types::without_sync_finalizer(meta@),
{
    let finalizers = match meta.finalizers() {
        Some(f) => f,
        None => Vec::new(),
    };
    let ghost all = finalizers_or_empty(meta@);
    let ghost pred = not_sync_finalizer();
    proof { assert(finalizers.deep_view() =~= all); }
    let mut rest: Vec<String> = Vec::new();
    proof {
        reveal(Seq::filter);
        assert(all.subrange(0, 0) =~= Seq::<StringView>::empty());
        assert(rest.deep_view() =~= all.subrange(0, 0).filter(pred));
    }
    let mut i: usize = 0;
    while i < finalizers.len()
        invariant
            0 <= i <= finalizers.len(),
            all == finalizers_or_empty(meta@),
            finalizers.deep_view() == all,
            pred == not_sync_finalizer(),
            rest.deep_view() == all.subrange(0, i as int).filter(pred),
        decreases finalizers.len() - i,
    {
        let f = finalizers[i].clone();
        let ghost before = all.subrange(0, i as int);
        let ghost after = all.subrange(0, i as int + 1);
        proof {
            reveal(Seq::filter);
            assert(after.len() > 0);
            assert(after.drop_last() =~= before);
            assert(after.last() == all[i as int]);
            assert(f@ == all[i as int]);
        }
        if !f.eq(&"anvil.dev/widget-sync".to_string()) {
            rest.push(f);
            proof {
                reveal(Seq::filter);
                assert(pred(all[i as int]));
                assert(after.filter(pred) == before.filter(pred).push(all[i as int]));
                assert(rest.deep_view() =~= before.filter(pred).push(all[i as int]));
            }
        } else {
            proof {
                reveal(Seq::filter);
                assert(!pred(all[i as int]));
                assert(after.filter(pred) == before.filter(pred));
            }
        }
        i = i + 1;
    }
    proof { assert(all.subrange(0, all.len() as int) =~= all); }
    let mut res = meta.clone();
    if rest.len() == 0 {
        res.unset_finalizers();
    } else {
        res.set_finalizers(rest);
    }
    res
}

// The Update that adds or removes the sync finalizer on the snapshot `outer`.
// See model::outer_finalizer_update.
pub fn outer_finalizer_update(kind: &SyncKindExec, outer: &SyncedObject, add: bool) -> (req: KubeUpdateRequest)
    requires outer@.metadata.well_formed_for_namespaced(),
    ensures req@ == sync_reconciler::outer_finalizer_update(outer@, add),
{
    let metadata = if add { with_sync_finalizer(&outer.metadata()) } else { without_sync_finalizer(&outer.metadata()) };
    let mut updated = outer.clone();
    updated.set_metadata(metadata);
    KubeUpdateRequest {
        api_resource: kind.outer_api_resource(),
        name: outer.metadata().name().unwrap(),
        namespace: outer.metadata().namespace().unwrap(),
        obj: updated.marshal(),
    }
}

// The List that reads the mirror key. See model::mirror_list.
pub fn mirror_list(kind: &SyncKindExec, outer: &SyncedObject) -> (req: KubeListRequest)
    requires outer@.metadata.well_formed_for_namespaced(),
    ensures req@ == sync_reconciler::mirror_list(kind@, outer@),
{
    let binding = binding_of(kind, outer);
    KubeListRequest {
        api_resource: kind.inner_api_resource(&binding),
        namespace: outer.metadata().namespace().unwrap(),
        name: Some(outer.metadata().name().unwrap()),
    }
}

// The Delete of the mirror `inner`, pinned to its uid. See model::mirror_delete.
pub fn mirror_delete(kind: &SyncKindExec, outer: &SyncedObject, binding: &ClusterRef, inner: &SyncedObject) -> (req: KubeDeleteRequest)
    requires
        outer@.metadata.well_formed_for_namespaced(),
        binding@ == spec_types::binding_of(kind@, outer@),
    ensures req@ == sync_reconciler::mirror_delete(kind@, outer@, inner@),
{
    let mut preconditions = Preconditions::default();
    preconditions.set_uid_from_object_meta(inner.metadata());
    KubeDeleteRequest {
        api_resource: kind.inner_api_resource(binding),
        name: outer.metadata().name().unwrap(),
        namespace: outer.metadata().namespace().unwrap(),
        preconditions: Some(preconditions),
    }
}

// Whether some object of `objs` is stored at the key of the entry's kind in
// `cluster`, `namespace` and `name`. See model::listed_at.
pub fn listed_at(entry: &RegistryEntry, cluster: &ClusterId, namespace: &String, name: &String, objs: &Vec<DynamicObject>) -> (res: bool)
    ensures res == sync_reconciler::listed_at(objs.deep_view(), ObjectRef { kind: model_kind(entry@, cluster@), namespace: namespace@, name: name@ }),
{
    let ghost key = ObjectRef { kind: model_kind(entry@, cluster@), namespace: namespace@, name: name@ };
    let ghost all = objs.deep_view();
    let mut i: usize = 0;
    while i < objs.len()
        invariant
            0 <= i <= objs.len(),
            key == (ObjectRef { kind: model_kind(entry@, cluster@), namespace: namespace@, name: name@ }),
            all == objs.deep_view(),
            forall |j: int| 0 <= j < i ==> !sync_reconciler::is_at(#[trigger] all[j], key),
        decreases objs.len() - i,
    {
        let obj = &objs[i];
        let metadata = obj.metadata();
        let obj_namespace = metadata.namespace();
        let obj_name = metadata.name();
        let kind_ok = SyncedObject::has_kind(entry, cluster, obj);
        proof { assert(kind_ok == (obj@.kind == model_kind(entry@, cluster@))); }
        let namespace_ok = match &obj_namespace {
            Some(ns) => ns.eq(namespace),
            None => false,
        };
        let name_ok = match &obj_name {
            Some(n) => n.eq(name),
            None => false,
        };
        proof {
            assert(all[i as int] == obj@);
            assert(metadata@ == obj@.metadata);
            assert(kind_ok == (obj@.kind == key.kind));
            assert(namespace_ok == (obj@.metadata.namespace == Some(key.namespace)));
            assert(name_ok == (obj@.metadata.name == Some(key.name)));
        }
        if kind_ok && namespace_ok && name_ok {
            proof { assert(sync_reconciler::is_at(all[i as int], key)); }
            return true;
        }
        proof { assert(!sync_reconciler::is_at(all[i as int], key)); }
        i = i + 1;
    }
    false
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
