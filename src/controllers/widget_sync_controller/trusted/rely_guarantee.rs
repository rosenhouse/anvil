// Rely and guarantee conditions of the Widget sync example (section 3.3 of
// discussion/multi-cluster/sync_controller_evaluation.md).
//
// The sync reconciler and the janitor reconciler are separate controllers in the
// model; each relies on every other controller, the other one of the pair
// included, and each guarantee is what the other one's rely needs from it. In the
// real deployment the other controllers are: whatever runs against the outer
// cluster, and the inner cluster's own Widget implementation together with
// everything else that runs there.
//
// Two clauses are state-dependent, in the style of vd_rely_update_req:
//   - a Create of a mirror carries a parent uid that no object other than the one
//     at the outer key has (mirror_create_req), which is what lets the janitor
//     trust a parent uid it reads off a mirror;
//   - a Delete of a mirror is only sent once its parent is gone for good
//     (mirror_delete_req), which is what lets the sync reconciler keep a mirror
//     whose parent exists.
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::model::{janitor_reconciler, sync_reconciler};
use crate::widget_sync_controller::trusted::{liveness_theorem::*, spec_types::*};
use verus_temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// The key of the mirror of the outer copy at `outer_key`.
pub open spec fn inner_key_of(outer_key: ObjectRef) -> ObjectRef {
    ObjectRef { kind: InnerWidgetView::kind(), ..outer_key }
}

// `parent_uid` has been issued, and the only object that may carry it is the one at
// `outer_key`. Uids are never reused, so this is stable once true.
pub open spec fn parent_uid_is_bound_to_key(parent_uid: Uid, outer_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& parent_uid < s.api_server.uid_counter
        &&& forall |k: ObjectRef| #[trigger] s.resources().contains_key(k) && s.resources()[k].metadata.uid == Some(parent_uid)
            ==> k == outer_key
    }
}

// A Create of a mirror: the object the sync reconciler builds for some outer copy at
// `outer_key`, whose uid is bound to that key.
pub open spec fn mirror_create_req(req: CreateRequest, outer_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        exists |outer: OuterWidgetView| {
            &&& outer.object_ref() == outer_key
            &&& outer.metadata.uid is Some
            &&& req.namespace == outer_key.namespace
            &&& req.obj == #[trigger] sync_reconciler::make_inner(outer).marshal()
            &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s)
        }
    }
}

// A Delete of a mirror the janitor's way: with a uid precondition. Why such a
// delete never removes a mirror whose parent exists is not a property of the
// message but of the janitor's state machine (it decides from a List of the outer
// copies); the sync reconciler's proof establishes it from the janitor's model,
// which is why the sync reconciler's spec names the janitor as a member of the
// cluster rather than as an anonymous other controller.
pub open spec fn mirror_delete_req(req: DeleteRequest) -> bool {
    &&& req.key.kind == InnerWidgetView::kind()
    &&& req.preconditions is Some
    &&& req.preconditions->0.uid is Some
}

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

// An update of a mirror by another controller carries a resource version, and if
// it is going to land (the resource version matches the store) it changes neither
// the owner references nor the mirror's identity. Stale updates, which the API
// server rejects, are unconstrained.
//
// The spec is deliberately left free: a mistaken (fat-finger) edit of a mirror's
// spec is something the sync reconciler must tolerate. It overwrites such an edit
// (the mirror's spec is compared with the outer copy's on every reconcile), and it
// never copies status fields the inner side computed for it (fields are copied only
// when the inner status observes the mirror's current generation). Convergence
// (R1, R2) is then stated for the time after such edits stop, see
// mirror_spec_undisturbed in liveness_theorem.rs.
pub open spec fn mirror_update_req(req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        req.obj.kind == InnerWidgetView::kind() ==> {
            &&& req.obj.metadata.resource_version is Some
            &&& (s.resources().contains_key(req.key())
                && etcd_obj.metadata.resource_version == req.obj.metadata.resource_version) ==> {
                &&& req.obj.metadata.owner_references == etcd_obj.metadata.owner_references
                &&& preserves_mirror_identity(etcd_obj.metadata, req.obj.metadata)
            }
        }
    }
}

// The transactional form of the same condition. (A mirror has no owner
// references, so such a request fails its owner check anyway; the clause keeps
// the rely honest rather than relying on that.)
pub open spec fn mirror_get_then_update_req(req: GetThenUpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        req.obj.kind == InnerWidgetView::kind() ==> {
            s.resources().contains_key(req.key()) ==> {
                &&& req.obj.metadata.owner_references == etcd_obj.metadata.owner_references
                &&& preserves_mirror_identity(etcd_obj.metadata, req.obj.metadata)
            }
        }
    }
}

// The sync reconciler's rely on every other controller (the janitor included).
pub open spec fn widget_sync_rely(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> match msg.content->APIRequest_0 {
            // Nobody else creates mirrors.
            APIRequest::CreateRequest(req) => req.obj.kind != InnerWidgetView::kind(),
            APIRequest::UpdateRequest(req) => mirror_update_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(req)(s),
            // Patches of a mirror's spec are tolerated (fat-finger edits, see
            // mirror_update_req); a patch never changes identity. Status patches are
            // how the inner implementation is expected to report.
            APIRequest::PatchRequest(_) => true,
            // Nobody else writes the status of an outer copy.
            APIRequest::UpdateStatusRequest(req) => req.obj.kind != OuterWidgetView::kind(),
            APIRequest::GetThenUpdateStatusRequest(req) => req.obj.kind != OuterWidgetView::kind(),
            APIRequest::PatchStatusRequest(req) => req.kind != OuterWidgetView::kind(),
            // Nobody else deletes mirrors. (The janitor does, but it is not an
            // anonymous other controller to the sync reconciler: its spec names the
            // janitor and its proof reasons about the janitor's state machine.)
            APIRequest::DeleteRequest(req) => req.key.kind != InnerWidgetView::kind(),
            APIRequest::GetThenDeleteRequest(req) => req.key.kind != InnerWidgetView::kind(),
            _ => true,
        }
    }
}

// The janitor's rely on every other controller (the sync reconciler included):
// mirrors are created only the sync reconciler's way, and updates keep their
// identity.
pub open spec fn widget_janitor_rely(other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::CreateRequest(req) => req.obj.kind == InnerWidgetView::kind() ==> {
                &&& req.obj.metadata.name is Some
                &&& mirror_create_req(req, ObjectRef {
                    kind: OuterWidgetView::kind(),
                    namespace: req.namespace,
                    name: req.obj.metadata.name->0,
                })(s)
            },
            APIRequest::UpdateRequest(req) => mirror_update_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(req)(s),
            _ => true,
        }
    }
}

// Guarantee conditions.

// The status patch the sync reconciler sends for the outer copy at `outer_key`:
// it tests the copy's uid and generation, and (G-gen) the status it writes carries
// observedGeneration equal to the tested generation, as does its Synced condition.
pub open spec fn sync_status_patch_req(req: PatchStatusRequest, outer_key: ObjectRef) -> bool {
    let status = OuterWidgetView::unmarshal_status(req.status);
    &&& req.kind == OuterWidgetView::kind()
    &&& req.namespace == outer_key.namespace
    &&& req.name == outer_key.name
    &&& req.tests.uid is Some
    &&& req.tests.generation is Some
    &&& status is Ok
    &&& status->Ok_0 is Some
    &&& status->Ok_0->0.observed_generation == req.tests.generation
    &&& status->Ok_0->0.synced_condition() is Some
    &&& status->Ok_0->0.synced_condition()->0.observed_generation == req.tests.generation
}

// Every request the sync reconciler sends while reconciling the outer copy at
// `outer_key` is one of: Get of its mirror; Create of its mirror; Patch of its
// mirror's spec; PatchStatus of the outer copy itself. It never deletes, never
// writes an outer copy's spec or metadata, never writes a mirror's status, and
// never touches any other key.
pub open spec fn widget_sync_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> {
            let outer_key = msg.src->Controller_1;
            match msg.content->APIRequest_0 {
                APIRequest::GetRequest(req) => req.key == inner_key_of(outer_key),
                APIRequest::CreateRequest(req) => mirror_create_req(req, outer_key)(s),
                APIRequest::PatchRequest(req) => {
                    &&& req.kind == InnerWidgetView::kind()
                    &&& req.namespace == outer_key.namespace
                    &&& req.name == outer_key.name
                },
                APIRequest::PatchStatusRequest(req) => sync_status_patch_req(req, outer_key),
                _ => false,
            }
        }
    }
}

// Every request the janitor sends while reconciling the mirror at `inner_key` is a
// List of the outer copies in its namespace or a Delete of that mirror.
pub open spec fn widget_janitor_guarantee(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> {
            let inner_key = msg.src->Controller_1;
            match msg.content->APIRequest_0 {
                APIRequest::ListRequest(req) => {
                    &&& req.kind == OuterWidgetView::kind()
                    &&& req.namespace == inner_key.namespace
                },
                APIRequest::DeleteRequest(req) => {
                    &&& req.key == inner_key
                    &&& mirror_delete_req(req)
                },
                _ => false,
            }
        }
    }
}

}
