// Rely and guarantee conditions of the Widget sync example (section 3.3 of
// discussion/multi-cluster/sync_controller_evaluation.md).
//
// The sync reconciler and the janitor reconciler are composed with each other,
// so "other controllers" below means every controller id except those two. In
// the real deployment the other controllers are: whatever runs against the outer
// cluster, and the inner cluster's own Widget implementation together with
// everything else that runs there.
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::model::{janitor_reconciler, sync_reconciler};
use crate::widget_sync_controller::trusted::spec_types::*;
use verus_temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// Rely conditions.

// If `old_meta` identifies a mirror (label and parent-uid annotation), `new_meta`
// identifies the same mirror. Other labels, annotations and finalizers are free:
// this admits an inner implementation that labels, annotates or finalizes the
// objects it works on, as long as it does not replace metadata wholesale.
pub open spec fn preserves_mirror_identity(old_meta: ObjectMetaView, new_meta: ObjectMetaView) -> bool {
    &&& (old_meta.labels is Some && old_meta.labels->0.contains_key(managed_by_key())) ==> {
        &&& new_meta.labels is Some
        &&& new_meta.labels->0.contains_key(managed_by_key())
        &&& new_meta.labels->0[managed_by_key()] == old_meta.labels->0[managed_by_key()]
    }
    &&& (old_meta.annotations is Some && old_meta.annotations->0.contains_key(parent_uid_key())) ==> {
        &&& new_meta.annotations is Some
        &&& new_meta.annotations->0.contains_key(parent_uid_key())
        &&& new_meta.annotations->0[parent_uid_key()] == old_meta.annotations->0[parent_uid_key()]
    }
}

// Nobody else creates mirrors.
pub open spec fn widget_rely_create_req(req: CreateRequest) -> bool {
    req.obj.kind != InnerWidgetView::kind()
}

// An update of a mirror by another controller carries a resource version, and if
// it is going to land (the resource version matches the store) it changes neither
// the spec nor the owner references and keeps the mirror's identity. Stated
// conditionally on the store, in the style of vd_rely_update_req, so that stale
// updates, which the API server rejects, are unconstrained.
pub open spec fn widget_rely_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        req.obj.kind == InnerWidgetView::kind() ==> {
            &&& req.obj.metadata.resource_version is Some
            &&& (s.resources().contains_key(req.key())
                && etcd_obj.metadata.resource_version == req.obj.metadata.resource_version) ==> {
                &&& req.obj.spec == etcd_obj.spec
                &&& req.obj.metadata.owner_references == etcd_obj.metadata.owner_references
                &&& preserves_mirror_identity(etcd_obj.metadata, req.obj.metadata)
            }
        }
    }
}

// The transactional form of the same condition. (A mirror has no owner
// references, so such a request fails its owner check anyway; the clause keeps
// the rely honest rather than relying on that.)
pub open spec fn widget_rely_get_then_update_req(req: GetThenUpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        req.obj.kind == InnerWidgetView::kind() ==> {
            s.resources().contains_key(req.key()) ==> {
                &&& req.obj.spec == etcd_obj.spec
                &&& req.obj.metadata.owner_references == etcd_obj.metadata.owner_references
                &&& preserves_mirror_identity(etcd_obj.metadata, req.obj.metadata)
            }
        }
    }
}

// Nobody else patches the spec of a mirror. (Status patches are free: that is
// how the inner implementation is expected to report.)
pub open spec fn widget_rely_patch_req(req: PatchRequest) -> bool {
    req.kind != InnerWidgetView::kind()
}

// Nobody else writes the status of an outer copy.
pub open spec fn widget_rely_update_status_req(req: UpdateStatusRequest) -> bool {
    req.obj.kind != OuterWidgetView::kind()
}

pub open spec fn widget_rely_get_then_update_status_req(req: GetThenUpdateStatusRequest) -> bool {
    req.obj.kind != OuterWidgetView::kind()
}

pub open spec fn widget_rely_patch_status_req(req: PatchStatusRequest) -> bool {
    req.kind != OuterWidgetView::kind()
}

// Nobody else deletes mirrors.
pub open spec fn widget_rely_delete_req(req: DeleteRequest) -> bool {
    req.key.kind != InnerWidgetView::kind()
}

pub open spec fn widget_rely_get_then_delete_req(req: GetThenDeleteRequest) -> bool {
    req.key.kind != InnerWidgetView::kind()
}

pub open spec fn widget_rely(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::CreateRequest(req) => widget_rely_create_req(req),
            APIRequest::UpdateRequest(req) => widget_rely_update_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => widget_rely_get_then_update_req(req)(s),
            APIRequest::PatchRequest(req) => widget_rely_patch_req(req),
            APIRequest::UpdateStatusRequest(req) => widget_rely_update_status_req(req),
            APIRequest::GetThenUpdateStatusRequest(req) => widget_rely_get_then_update_status_req(req),
            APIRequest::PatchStatusRequest(req) => widget_rely_patch_status_req(req),
            APIRequest::DeleteRequest(req) => widget_rely_delete_req(req),
            APIRequest::GetThenDeleteRequest(req) => widget_rely_get_then_delete_req(req),
            _ => true,
        }
    }
}

// Guarantee conditions.

// Every request the sync reconciler sends is one of:
//   Get of the mirror key of some outer copy;
//   Create of a mirror: provided name, no owner references, no finalizers, our
//     label, parent-uid equal to the uid of an outer copy, and that copy's spec;
//   Patch of a mirror's spec, testing the mirror's uid and generation;
//   PatchStatus of an outer copy, testing that copy's uid and generation and
//     writing status.observedGeneration equal to the tested generation (G-gen).
// It never deletes, never writes an outer copy's spec or metadata, never writes a
// mirror's status, and never touches any other kind.
pub open spec fn widget_sync_guarantee_create_req(req: CreateRequest) -> bool {
    &&& req.obj.kind == InnerWidgetView::kind()
    &&& InnerWidgetView::unmarshal(req.obj) is Ok
    &&& exists |outer: OuterWidgetView| #[trigger] sync_reconciler::make_inner(outer) == InnerWidgetView::unmarshal(req.obj)->Ok_0
}

pub open spec fn widget_sync_guarantee_patch_req(req: PatchRequest) -> bool {
    &&& req.kind == InnerWidgetView::kind()
    &&& req.tests.uid is Some
    &&& req.tests.generation is Some
}

pub open spec fn widget_sync_guarantee_patch_status_req(req: PatchStatusRequest) -> bool {
    let status = OuterWidgetView::unmarshal_status(req.status);
    &&& req.kind == OuterWidgetView::kind()
    &&& req.tests.uid is Some
    &&& req.tests.generation is Some
    &&& status is Ok
    &&& status->Ok_0 is Some
    // G-gen: the written observedGeneration is the generation the patch tests for.
    &&& status->Ok_0->0.observed_generation == req.tests.generation
    &&& status->Ok_0->0.synced_condition() is Some
    &&& status->Ok_0->0.synced_condition()->0.observed_generation == req.tests.generation
}

pub open spec fn widget_sync_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::GetRequest(req) => req.key.kind == InnerWidgetView::kind(),
            APIRequest::CreateRequest(req) => widget_sync_guarantee_create_req(req),
            APIRequest::PatchRequest(req) => widget_sync_guarantee_patch_req(req),
            APIRequest::PatchStatusRequest(req) => widget_sync_guarantee_patch_status_req(req),
            _ => false,
        }
    }
}

// Every request the janitor reconciler sends is a List of outer copies in some
// namespace or a Delete of a mirror with a uid precondition.
pub open spec fn widget_janitor_guarantee_delete_req(req: DeleteRequest) -> bool {
    &&& req.key.kind == InnerWidgetView::kind()
    &&& req.preconditions is Some
    &&& req.preconditions->0.uid is Some
}

pub open spec fn widget_janitor_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::ListRequest(req) => req.kind == OuterWidgetView::kind(),
            APIRequest::DeleteRequest(req) => widget_janitor_guarantee_delete_req(req),
            _ => false,
        }
    }
}

}
