// Rely and guarantee conditions of the Widget sync example, with the kind and the
// binding as data (doc/widget_sync_design.md, section 3;
// doc/widget_sync_fanout_design.md, sections 3.2, 3.3 and 5.1). The sync
// reconciler of a kind and each of its janitors are separate controllers; each
// relies on every other controller, and each guarantee is what the others' relies
// need from it. In a deployment the other controllers are whatever runs against
// the outer cluster and each inner cluster's own implementation of the kind.
//
// mirror_create_req is state-dependent, in the style of vd_rely_update_req: a
// Create of a mirror carries a parent uid that no object other than the one at
// the outer key has, which is what lets a janitor trust a parent uid it reads
// off a mirror.
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::{liveness_theorem::*, spec_types::*};
use verus_temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// `parent_uid` has been issued, and the only object that may carry it is the one at
// `outer_key`. Uids are never reused, so this is stable once true.
pub open spec fn parent_uid_is_bound_to_key(parent_uid: Uid, outer_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& parent_uid < s.api_server.uid_counter
        &&& forall |k: ObjectRef| #[trigger] s.resources().contains_key(k) && s.resources()[k].metadata.uid == Some(parent_uid)
            ==> k == outer_key
    }
}

// A Create of a mirror: the object the sync reconciler of `k` builds for some
// outer copy at `outer_key`, whose uid is bound to that key. The mirror's kind
// names the binding the outer copy's selector picks.
pub open spec fn mirror_create_req(k: SyncKind, req: CreateRequest, outer_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        exists |outer: SyncedObjectView| {
            &&& outer.kind == k.outer_kind
            &&& outer.object_ref() == outer_key
            &&& outer.metadata.uid is Some
            &&& req.namespace == outer_key.namespace
            &&& req.obj == #[trigger] marshal(make_inner(k, outer))
            &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s)
        }
    }
}

// A Delete of a mirror the janitor's way: with a uid precondition. That such a
// delete never removes a mirror whose parent exists holds only under the janitor's
// rely and is part of the janitor's ESR (janitor_deletes_are_sound).
pub open spec fn mirror_delete_req(k: SyncKind, b: Binding, req: DeleteRequest) -> bool {
    &&& req.key.kind == inner_kind(k, b)
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
// server rejects, are unconstrained. The spec is not constrained: the sync
// reconciler overwrites other writers' spec edits, and R1 and R2 are stated for
// the time after such edits stop (mirror_spec_undisturbed in liveness_theorem.rs).
pub open spec fn mirror_update_req(k: SyncKind, req: UpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        is_inner_kind(k, req.obj.kind) ==> {
            &&& req.obj.metadata.resource_version is Some
            &&& (s.resources().contains_key(req.key())
                && etcd_obj.metadata.resource_version == req.obj.metadata.resource_version) ==> {
                &&& req.obj.metadata.owner_references == etcd_obj.metadata.owner_references
                &&& preserves_mirror_identity(etcd_obj.metadata, req.obj.metadata)
            }
        }
    }
}

// The transactional form of the same condition. A mirror has no owner references,
// so such a request fails its owner check anyway; the clause is stated so the rely
// does not depend on that.
pub open spec fn mirror_get_then_update_req(k: SyncKind, req: GetThenUpdateRequest) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let etcd_obj = s.resources()[req.key()];
        is_inner_kind(k, req.obj.kind) ==> {
            s.resources().contains_key(req.key()) ==> {
                &&& req.obj.metadata.owner_references == etcd_obj.metadata.owner_references
                &&& preserves_mirror_identity(etcd_obj.metadata, req.obj.metadata)
            }
        }
    }
}

// The sync reconciler's rely on every other controller (its janitors included). It
// constrains only what would break identity or forge a mirror; edits of a
// mirror's spec, of its other labels and annotations, and deletes of mirrors are
// all admitted, and R1 and R2 promise convergence for the time after they stop.
pub open spec fn widget_sync_rely(k: SyncKind, other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> match msg.content->APIRequest_0 {
            // Nobody else creates mirrors, in any binding.
            APIRequest::CreateRequest(req) => !is_inner_kind(k, req.obj.kind),
            APIRequest::UpdateRequest(req) => mirror_update_req(k, req)(s),
            APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(k, req)(s),
            // A patch never changes identity; a spec patch is an out-of-band edit the
            // sync reconciler overwrites (see mirror_update_req).
            APIRequest::PatchRequest(_) => true,
            // Nobody else writes the status of an outer copy.
            APIRequest::UpdateStatusRequest(req) => req.obj.kind != k.outer_kind,
            APIRequest::GetThenUpdateStatusRequest(req) => req.obj.kind != k.outer_kind,
            APIRequest::PatchStatusRequest(req) => req.kind != k.outer_kind,
            // Deletes are free, mirrors included: an out-of-band delete of a mirror
            // is recovered from (NotFound, then Create), and R1 and R2 are stated for
            // the time after such deletes stop landing on the live mirror
            // (mirror_undeleted in liveness_theorem.rs). A transactional delete never
            // removes a mirror, which has no owner references.
            _ => true,
        }
    }
}

// The janitors' rely on every other controller (the sync reconciler included):
// mirrors are created only the sync reconciler's way, and updates keep their
// identity. One condition for the kind: it constrains every binding's mirrors, so
// every janitor of `k` relies on the same thing.
pub open spec fn widget_janitor_rely(k: SyncKind, other_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(other_id)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::CreateRequest(req) => is_inner_kind(k, req.obj.kind) ==> {
                &&& req.obj.metadata.name is Some
                &&& mirror_create_req(k, req, ObjectRef {
                    kind: k.outer_kind,
                    namespace: req.namespace,
                    name: req.obj.metadata.name->0,
                })(s)
            },
            APIRequest::UpdateRequest(req) => mirror_update_req(k, req)(s),
            APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(k, req)(s),
            _ => true,
        }
    }
}

// Guarantee conditions.

// The status patch the sync reconciler sends for the outer copy at `outer_key`:
// it tests the copy's uid and generation, and (G-gen) the status it writes carries
// observedGeneration equal to the tested generation, as do its Synced, Ready and
// Stalled conditions.
pub open spec fn sync_status_patch_req(k: SyncKind, req: PatchStatusRequest, outer_key: ObjectRef) -> bool {
    let status = unmarshal_status(req.status);
    &&& req.kind == k.outer_kind
    &&& req.namespace == outer_key.namespace
    &&& req.name == outer_key.name
    &&& req.tests.uid is Some
    &&& req.tests.generation is Some
    &&& status is Ok
    &&& status->Ok_0 is Some
    &&& status->Ok_0->0.observed_generation == req.tests.generation
    &&& status->Ok_0->0.synced_condition() is Some
    &&& status->Ok_0->0.synced_condition()->0.observed_generation == req.tests.generation
    &&& status->Ok_0->0.ready_condition() is Some
    &&& status->Ok_0->0.ready_condition()->0.observed_generation == req.tests.generation
    &&& status->Ok_0->0.stalled_condition() is Some
    &&& status->Ok_0->0.stalled_condition()->0.observed_generation == req.tests.generation
}

// Every request the sync reconciler of `k` sends while reconciling the outer copy
// at `outer_key` is one of: Get of its mirror; Create of its mirror; Patch of its
// mirror's spec; PatchStatus of the outer copy itself. Every mirror request names
// the outer copy's namespace and name and a mirror kind of `k`. It never deletes,
// never writes an outer copy's spec or metadata, never writes a mirror's status,
// and never touches any other key.
pub open spec fn widget_sync_guarantee(k: SyncKind, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> {
            let outer_key = msg.src->Controller_1;
            match msg.content->APIRequest_0 {
                APIRequest::GetRequest(req) => {
                    &&& is_inner_kind(k, req.key.kind)
                    &&& req.key.namespace == outer_key.namespace
                    &&& req.key.name == outer_key.name
                },
                APIRequest::CreateRequest(req) => mirror_create_req(k, req, outer_key)(s),
                APIRequest::PatchRequest(req) => {
                    &&& is_inner_kind(k, req.kind)
                    &&& req.namespace == outer_key.namespace
                    &&& req.name == outer_key.name
                },
                APIRequest::PatchStatusRequest(req) => sync_status_patch_req(k, req, outer_key),
                _ => false,
            }
        }
    }
}

// Every request the janitor of `(k, b)` sends while reconciling the mirror at
// `inner_key` is a List of the outer copies in its namespace or a Delete of that
// mirror.
pub open spec fn widget_janitor_guarantee(k: SyncKind, b: Binding, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> {
            let inner_key = msg.src->Controller_1;
            match msg.content->APIRequest_0 {
                APIRequest::ListRequest(req) => {
                    &&& req.kind == k.outer_kind
                    &&& req.namespace == inner_key.namespace
                },
                APIRequest::DeleteRequest(req) => {
                    &&& req.key == inner_key
                    &&& mirror_delete_req(k, b, req)
                },
                _ => false,
            }
        }
    }
}

}
