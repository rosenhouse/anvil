// What one step of the cluster does at the keys the proofs watch, under the
// invariants and the step context of spec.rs: our mirror is kept (identity,
// lifecycle and uid; its generation moves only with its spec); the mirror key
// stays absent, stays ours or gains our mirror, and never swaps one object for
// another; a synced spec stays synced; a spec change of our mirror is a write of
// the outer spec; a mirror object stays as it is or is removed for good.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::api_server::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{set_lib::*, string_view::*};
use crate::widget_sync_controller::{
    model::{install::*, janitor_reconciler, sync_reconciler, janitor_reconciler::WidgetJanitorReconcileState, sync_reconciler::WidgetSyncReconcileState},
    proof::{
        guarantee::*, helper_invariants::*, janitor_invariants::*,
        liveness::{spec::*},
        predicate::*, sync_invariants::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Nobody touches our mirror: neither its identity nor its lifecycle.
// ---------------------------------------------------------------------------

// One step of the API server keeps our mirror in the store, with its uid and
// without a deletion timestamp: a Delete of the mirror key misses it by uid (the
// premise), a transactional delete skips an object without owner references, and
// no other request removes an object or stamps it.
proof fn lemma_ours_kept_after_api_server_step(k: SyncKind, b: Binding, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, msg: Message, outer: SyncedObjectView
)
    requires
        bs.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, bs, spec_ok, cluster, controller_id, janitor_id),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s_prime),
        every_mirror_is_bound(k, b)(s),
        every_in_flight_inner_update_preserves_identity(k)(s),
        janitor_deletes_are_sound(k, b, janitor_id)(s),
        builtin_deletes_never_target_mirrors(k, b)(s),
        sync_rely_with_janitor(k, b, bs, spec_ok, cluster, controller_id, janitor_id)(s),
        widget_sync_guarantee(k, controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s),
        Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s),
        Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s),
        Cluster::synced_desired_state_is(outer)(s),
        mirror_undeleted(k, outer)(s),
        mirror_is_ours(k, b, bs, spec_ok, outer)(s),
    ensures
        s_prime.resources().contains_key(inner_key(k, outer)),
        s_prime.resources()[inner_key(k, outer)].metadata.uid == s.resources()[inner_key(k, outer)].metadata.uid,
        s_prime.resources()[inner_key(k, outer)].metadata.deletion_timestamp is None,
{
    let ikey = inner_key(k, outer);
    let key = outer.object_ref();
    let cr = s.resources()[ikey];
    let inner = unmarshal(inner_kind(k, b), cr)->Ok_0;
    lemma_weakly_well_formed_implies_kinds_match(s);
    assert(Cluster::etcd_object_is_weakly_well_formed(ikey)(s));
    assert(cr.kind == inner_kind(k, b));
    assert(cr.object_ref() == ikey);
    assert(mirror_is_bound(k, ikey)(s));
    assert(cr.metadata.owner_references is None);
    assert(s.in_flight().contains(msg));
    assert(msg.content is APIRequest);
    lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
    // The parent uid on our mirror is the outer copy's, which exists.
    assert(parent_uid_annotation(inner) == parent_uid_of(outer));
    assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    assert(s.resources()[key].metadata.uid is Some);
    assert(outer.metadata.uid is Some);
    match msg.content->APIRequest_0 {
        APIRequest::DeleteRequest(req) => {
            if req.key == ikey {
                // Whoever sent it (the janitor, a garbage collector, an anonymous
                // controller deleting mirrors out of band), the premise says a
                // Delete of the mirror key in flight names a uid other than our
                // mirror's, so the API server rejects it.
                assert(delete_misses_mirror(k, req, outer)(s));
                assert(req.preconditions->0.uid != cr.metadata.uid);
                assert(delete_request_admission_check(req, s.api_server) is Some);
                assert(s_prime.api_server == s.api_server);
            } else {
                assert(s_prime.resources()[ikey] == cr);
            }
        },
        APIRequest::GetThenDeleteRequest(req) => {
            // A mirror has no owner references, so the transactional delete does nothing.
            assert(s_prime.resources()[ikey] == cr);
        },
        APIRequest::UpdateRequest(req) => {
            if req.key() == ikey {
                if s_prime.api_server != s.api_server {
                    assert(s_prime.resources()[ikey].metadata.uid == cr.metadata.uid);
                    assert(s_prime.resources()[ikey].metadata.deletion_timestamp == cr.metadata.deletion_timestamp);
                }
            } else {
                assert(s_prime.resources()[ikey] == cr);
            }
        },
        APIRequest::GetThenUpdateRequest(_) => {
            lemma_get_then_update_keeps_unowned_objects(cluster.installed_types, msg, s.api_server, ikey);
        },
        APIRequest::GetThenUpdateStatusRequest(req) => {
            assert(s_prime.resources()[ikey] == cr);
        },
        APIRequest::PatchRequest(req) => {
            lemma_patch_request_keeps_identity_and_lifecycle(cluster.installed_types, req, s.api_server);
            if req.key() == ikey {
                assert(keeps_identity_and_lifecycle(s.api_server, s_prime.api_server));
            } else {
                assert(s_prime.resources()[ikey] == cr);
            }
        },
        APIRequest::PatchStatusRequest(req) => {
            lemma_patch_status_request_keeps_identity(cluster.installed_types, req, s.api_server);
            if req.key() != ikey {
                assert(s_prime.resources()[ikey] == cr);
            }
        },
        APIRequest::UpdateStatusRequest(req) => {
            lemma_update_status_keeps_identity(cluster.installed_types, req, s.api_server);
            if req.key() != ikey {
                assert(s_prime.resources()[ikey] == cr);
            }
        },
        APIRequest::CreateRequest(req) => {
            assert(s_prime.resources()[ikey] == cr);
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// The store facts a step of the API server keeps for our mirror.
pub proof fn lemma_ours_after_api_server_step(k: SyncKind, b: Binding, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, msg: Message, outer: SyncedObjectView
)
    requires
        bs.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, bs, spec_ok, cluster, controller_id, janitor_id),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s_prime),
        every_mirror_is_bound(k, b)(s),
        every_in_flight_inner_update_preserves_identity(k)(s),
        janitor_deletes_are_sound(k, b, janitor_id)(s),
        builtin_deletes_never_target_mirrors(k, b)(s),
        sync_rely_with_janitor(k, b, bs, spec_ok, cluster, controller_id, janitor_id)(s),
        widget_sync_guarantee(k, controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s),
        Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s),
        Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s),
        Cluster::synced_desired_state_is(outer)(s),
        mirror_undeleted(k, outer)(s),
        mirror_is_ours(k, b, bs, spec_ok, outer)(s),
    ensures
        mirror_is_ours(k, b, bs, spec_ok, outer)(s_prime),
        s_prime.resources()[inner_key(k, outer)].metadata.uid == s.resources()[inner_key(k, outer)].metadata.uid,
        s_prime.resources()[inner_key(k, outer)].metadata.generation == s.resources()[inner_key(k, outer)].metadata.generation
            || s_prime.resources()[inner_key(k, outer)].spec != s.resources()[inner_key(k, outer)].spec,
{
    let ikey = inner_key(k, outer);
    let key = outer.object_ref();
    let cr = s.resources()[ikey];
    let inner = unmarshal(inner_kind(k, b), cr)->Ok_0;
    lemma_weakly_well_formed_implies_kinds_match(s);
    assert(Cluster::etcd_object_is_weakly_well_formed(ikey)(s));
    assert(cr.kind == inner_kind(k, b));
    assert(cr.object_ref() == ikey);
    assert(mirror_is_bound(k, ikey)(s));
    assert(cr.metadata.owner_references is None);
    assert(s.in_flight().contains(msg));
    assert(msg.content is APIRequest);
    lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
    // The parent uid on our mirror is the outer copy's, which exists.
    assert(parent_uid_annotation(inner) == parent_uid_of(outer));
    assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    assert(s.resources()[key].metadata.uid is Some);
    assert(outer.metadata.uid is Some);
    // Step 1: the object is still there, with its uid, and no deletion timestamp appeared.
    lemma_ours_kept_after_api_server_step(k, b, bs, spec_ok, cluster, controller_id, janitor_id, s, s_prime, msg, outer);

    // Step 2: identity is kept.
    assert(snapshot_is_mirror(inner_kind(k, b), cr));
    assert(janitor_snapshot_is_sound(k, b, cr, ikey)(s));
    lemma_snapshot_soundness_preserved_by_api_server_step(cluster, k, b, s, s_prime, msg, cr, ikey);
    lemma_well_formed_inner_unmarshals(cluster, inner_kind(k, b), spec_ok, k.selector, s_prime, ikey);
    let new_obj = s_prime.resources()[ikey];
    let new_inner = unmarshal(inner_kind(k, b), new_obj)->Ok_0;
    assert(preserves_mirror_identity(cr.metadata, new_obj.metadata));
    assert(new_inner.metadata == new_obj.metadata);
    assert(is_mirror_of(new_inner, outer));
    // Step 3: the generation changes only with the spec (no deletion stamp landed).
    assert(new_obj.metadata.generation == cr.metadata.generation || new_obj.spec != cr.spec) by {
        match msg.content->APIRequest_0 {
            APIRequest::UpdateRequest(req) => {
                if req.key() == ikey && s_prime.api_server != s.api_server {
                    assert(new_obj.metadata.generation == next_generation(cr, req.obj.spec));
                }
            },
            APIRequest::PatchRequest(req) => {
                if req.key() == ikey && s_prime.api_server != s.api_server {
                    assert(new_obj.metadata.generation == next_generation(cr, req.spec));
                }
            },
            _ => {},
        }
    }
}

// Any step of the cluster keeps our mirror.
pub proof fn lemma_ours_after_step(k: SyncKind, b: Binding, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        bs.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, bs, spec_ok, cluster, controller_id, janitor_id),
        cluster.next()(s, s_prime),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s_prime),
        every_mirror_is_bound(k, b)(s),
        every_in_flight_inner_update_preserves_identity(k)(s),
        janitor_deletes_are_sound(k, b, janitor_id)(s),
        builtin_deletes_never_target_mirrors(k, b)(s),
        sync_rely_with_janitor(k, b, bs, spec_ok, cluster, controller_id, janitor_id)(s),
        widget_sync_guarantee(k, controller_id)(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s),
        Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s),
        Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s),
        Cluster::synced_desired_state_is(outer)(s),
        mirror_undeleted(k, outer)(s),
        mirror_is_ours(k, b, bs, spec_ok, outer)(s),
    ensures
        mirror_is_ours(k, b, bs, spec_ok, outer)(s_prime),
        s_prime.resources()[inner_key(k, outer)].metadata.uid == s.resources()[inner_key(k, outer)].metadata.uid,
        s_prime.resources()[inner_key(k, outer)].metadata.generation == s.resources()[inner_key(k, outer)].metadata.generation
            || s_prime.resources()[inner_key(k, outer)].spec != s.resources()[inner_key(k, outer)].spec,
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            lemma_ours_after_api_server_step(k, b, bs, spec_ok, cluster, controller_id, janitor_id, s, s_prime, input->0, outer);
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}


// The mirror key after one step: our mirror stays ours; an absent mirror stays
// absent or becomes ours (only the sync reconciler's current reconcile creates
// one); an existing object is never replaced by another.
pub proof fn lemma_mirror_key_after_step(k: SyncKind, b: Binding, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        bs.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, bs, spec_ok, cluster, controller_id, janitor_id),
        sync_step_next(k, b, bs, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
    ensures
        mirror_is_ours(k, b, bs, spec_ok, outer)(s) ==> mirror_is_ours(k, b, bs, spec_ok, outer)(s_prime),
        mirror_absent(k, b, bs, spec_ok, outer)(s) ==> mirror_absent(k, b, bs, spec_ok, outer)(s_prime) || mirror_is_ours(k, b, bs, spec_ok, outer)(s_prime),
        s.resources().contains_key(inner_key(k, outer)) && s_prime.resources().contains_key(inner_key(k, outer))
            ==> s_prime.resources()[inner_key(k, outer)].metadata.uid == s.resources()[inner_key(k, outer)].metadata.uid,
{
    let ikey = inner_key(k, outer);
    let key = outer.object_ref();
    unmarshal_of_marshal();
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    if mirror_is_ours(k, b, bs, spec_ok, outer)(s) {
        lemma_ours_after_step(k, b, bs, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    }
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            assert(msg.content is APIRequest);
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => {
                    if s.resources().contains_key(ikey) {
                        // A create never replaces an existing object.
                        assert(s_prime.resources()[ikey] == s.resources()[ikey]);
                    } else if s_prime.resources().contains_key(ikey) {
                        // The mirror was just created: by the sync reconciler's reconcile of the outer copy.
                        let created = s_prime.resources()[ikey];
                        assert(create_request_admission_check(cluster.installed_types, req, s.api_server) is None);
                        assert(created.kind == req.obj.kind);
                        assert(req.obj.kind == inner_kind(k, b));
                        assert(req.obj.metadata.name is Some);
                        assert(created.metadata.name == req.obj.metadata.name);
                        assert(created.metadata.namespace == Some(req.namespace));
                        assert(created.metadata.labels == req.obj.metadata.labels);
                        assert(created.metadata.annotations == req.obj.metadata.annotations);
                        assert(created.metadata.deletion_timestamp is None);
                        assert(req.namespace == key.namespace);
                        assert(req.obj.metadata.name->0 == key.name);
                        match msg.src {
                            HostId::Controller(id, okey) => {
                                assert(cluster.controller_models.contains_key(id));
                                if id == controller_id {
                                    assert(sync_request_is_guaranteed(k, msg, s));
                                    assert(mirror_create_req(k, req, okey)(s));
                                    let outer_k = choose |outer_k: SyncedObjectView| {
                                        &&& outer_k.kind == k.outer_kind
                                        &&& outer_k.object_ref() == okey
                                        &&& outer_k.metadata.uid is Some
                                        &&& req.namespace == okey.namespace
                                        &&& req.obj == #[trigger] marshal(make_inner(k, outer_k))
                                        &&& parent_uid_is_bound_to_key(outer_k.metadata.uid->0, okey)(s)
                                    };
                                    marshal_preserves_metadata();
                                    assert(req.obj.metadata == make_inner(k, outer_k).metadata);
                                    assert(okey.kind == k.outer_kind);
                                    assert(okey.namespace == key.namespace);
                                    assert(okey.name == key.name);
                                    assert(okey == key);
                                    // It is the pending request of the current reconcile of the outer copy.
                                    assert(s.ongoing_reconciles(controller_id).contains_key(key));
                                    let reconcile = s.ongoing_reconciles(controller_id)[key];
                                    assert(reconcile.pending_req_msg == Some(msg));
                                    assert(sync_pending_request_is(k, controller_id, key, reconcile));
                                    let cr_outer = unmarshal(k.outer_kind, reconcile.triggering_cr)->Ok_0;
                                    let step = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
                                    assert(!(step is Init));
                                    assert(!(step is Done));
                                    assert(!(step is Error));
                                    assert(step is AfterCreateInner);
                                    assert(req == CreateRequest { namespace: cr_outer.metadata.namespace->0, obj: make_inner(k, cr_outer).marshal() });
                                    // The snapshot has the outer copy's uid.
                                    assert(reconcile.triggering_cr.metadata.uid == outer.metadata.uid);
                                    assert(cr_outer.metadata == reconcile.triggering_cr.metadata);
                                    assert(parent_uid_of(cr_outer) == parent_uid_of(outer));
                                    assert(req.obj.metadata == make_inner(k, cr_outer).metadata);
                                    lemma_well_formed_inner_unmarshals(cluster, inner_kind(k, b), spec_ok, k.selector, s_prime, ikey);
                                    let created_inner = unmarshal(inner_kind(k, b), created)->Ok_0;
                                    assert(created_inner.metadata == created.metadata);
                                    assert(created.metadata.labels == make_inner(k, cr_outer).metadata.labels);
                                    assert(created.metadata.annotations == make_inner(k, cr_outer).metadata.annotations);
                                    assert(is_mirror_of(created_inner, outer));
                                    assert(mirror_is_ours(k, b, bs, spec_ok, outer)(s_prime));
                                } else if id == janitor_id {
                                    assert(janitor_request_is_guaranteed(k, b, msg));
                                    assert(false);
                                } else {
                                    assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                    assert(widget_sync_rely(k, id)(s));
                                    assert(req.obj.kind != inner_kind(k, b));
                                    assert(false);
                                }
                            },
                            HostId::BuiltinController => { assert(false); },
                            HostId::PodMonkey => {
                                assert(req.key().kind == Kind::PodKind);
                                assert(false);
                            },
                            _ => { assert(false); },
                        }
                    }
                },
                _ => {
                    // No other request creates an object at a key.
                    if !s.resources().contains_key(ikey) {
                        assert(!s_prime.resources().contains_key(ikey));
                    }
                    if s.resources().contains_key(ikey) && s_prime.resources().contains_key(ikey) {
                        lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
                        assert(s_prime.resources()[ikey].metadata.uid == s.resources()[ikey].metadata.uid);
                    }
                },
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// ---------------------------------------------------------------------------
// spec_synced is stable once reached.
// ---------------------------------------------------------------------------

pub proof fn lemma_spec_synced_after_step(k: SyncKind, b: Binding, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        bs.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, bs, spec_ok, cluster, controller_id, janitor_id),
        sync_step_next(k, b, bs, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        spec_synced(k, outer)(s),
    ensures spec_synced(k, outer)(s_prime),
{
    let ikey = inner_key(k, outer);
    assert(mirror_is_ours(k, b, bs, spec_ok, outer)(s));
    lemma_ours_after_step(k, b, bs, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            let old_obj = s.resources()[ikey];
            let new_obj = s_prime.resources()[ikey];
            lemma_weakly_well_formed_implies_kinds_match(s);
            match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => {
                    if req.key() == ikey && s_prime.api_server != s.api_server {
                        assert(new_obj.spec == req.obj.spec);
                        assert(writes_outer_spec(req.obj.spec, outer));
                    } else {
                        assert(new_obj.spec == old_obj.spec);
                    }
                },
                APIRequest::PatchRequest(req) => {
                    if req.key() == ikey && s_prime.api_server != s.api_server {
                        assert(new_obj.spec == req.spec);
                        assert(writes_outer_spec(req.spec, outer));
                    } else {
                        assert(new_obj.spec == old_obj.spec);
                    }
                },
                APIRequest::GetThenUpdateRequest(_) => {
                    lemma_get_then_update_keeps_unowned_objects(cluster.installed_types, msg, s.api_server, ikey);
                    assert(new_obj.spec == old_obj.spec);
                },
                APIRequest::UpdateStatusRequest(req) => {
                    lemma_update_status_keeps_identity(cluster.installed_types, req, s.api_server);
                    assert(new_obj.spec == old_obj.spec);
                },
                APIRequest::PatchStatusRequest(req) => {
                    lemma_patch_status_request_keeps_identity(cluster.installed_types, req, s.api_server);
                    assert(new_obj.spec == old_obj.spec);
                },
                _ => {
                    assert(new_obj.spec == old_obj.spec);
                },
            }
            let new_inner = unmarshal(inner_kind(k, b), new_obj)->Ok_0;
            assert(new_inner.spec == new_obj.spec);
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// While our mirror is there, its spec changes only by a write of the outer spec.
pub proof fn lemma_spec_change_means_synced(k: SyncKind, b: Binding, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        bs.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, bs, spec_ok, cluster, controller_id, janitor_id),
        sync_step_next(k, b, bs, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        mirror_is_ours(k, b, bs, spec_ok, outer)(s),
        s_prime.resources()[inner_key(k, outer)].spec != s.resources()[inner_key(k, outer)].spec,
    ensures spec_synced(k, outer)(s_prime),
{
    let ikey = inner_key(k, outer);
    lemma_ours_after_step(k, b, bs, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
                    lemma_weakly_well_formed_implies_kinds_match(s);
            match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => {
                    assert(req.key() == ikey);
                    assert(s_prime.resources()[ikey].spec == req.obj.spec);
                    assert(writes_outer_spec(req.obj.spec, outer));
                },
                APIRequest::PatchRequest(req) => {
                    assert(req.key() == ikey);
                    assert(s_prime.resources()[ikey].spec == req.spec);
                    assert(writes_outer_spec(req.spec, outer));
                },
                APIRequest::GetThenUpdateRequest(_) => {
                    lemma_get_then_update_keeps_unowned_objects(cluster.installed_types, msg, s.api_server, ikey);
                    assert(false);
                },
                APIRequest::UpdateStatusRequest(req) => {
                    lemma_update_status_keeps_identity(cluster.installed_types, req, s.api_server);
                    assert(false);
                },
                APIRequest::PatchStatusRequest(req) => {
                    lemma_patch_status_request_keeps_identity(cluster.installed_types, req, s.api_server);
                    assert(false);
                },
                _ => { assert(false); },
            }
            let new_inner = unmarshal(inner_kind(k, b), s_prime.resources()[ikey])->Ok_0;
            assert(new_inner.spec == outer.spec);
        },
        _ => { assert(false); },
    }
}

// ---------------------------------------------------------------------------
// Stability of the object-level facts.
// ---------------------------------------------------------------------------

pub proof fn lemma_gone_is_stable(k: SyncKind, b: Binding, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, key: ObjectRef, uid: Uid, s: ClusterState, s_prime: ClusterState)
    requires
        bs.contains(b),
        gone(k, b, bs, spec_ok, key, uid)(s),
        store_only_grows_by_fresh_uids(s, s_prime),
    ensures gone(k, b, bs, spec_ok, key, uid)(s_prime),
{
    if s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == Some(uid) {
        if s.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == s.resources()[key].metadata.uid {
            assert(false);
        } else {
            assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
            assert(false);
        }
    }
}

// One step of the cluster keeps the mirror object as it is, or removes it.
pub proof fn lemma_mirror_object_after_step(k: SyncKind, b: Binding, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, s: ClusterState, s_prime: ClusterState, key: ObjectRef, parent_uid: Uid, uid: Uid)
    requires
        bs.contains(b),
        cluster.next()(s, s_prime),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime),
        cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s_prime),
        every_mirror_is_bound(k, b)(s),
        every_in_flight_inner_update_preserves_identity(k)(s),
        mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s),
    ensures present_or_gone(k, b, bs, spec_ok, key, parent_uid, uid)(s_prime),
{
    let cr = s.resources()[key];
    let inner = unmarshal(inner_kind(k, b), cr)->Ok_0;
    assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    assert(cr.kind == inner_kind(k, b));
    assert(cr.object_ref() == key);
    assert(key.kind == inner_kind(k, b));
    assert(mirror_is_bound(k, key)(s));
    assert(snapshot_is_mirror(inner_kind(k, b), cr));
    assert(snapshot_parent(inner_kind(k, b), cr) == parent_uid_annotation(inner));
    assert(janitor_snapshot_is_sound(k, b, cr, key)(s));
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            lemma_snapshot_soundness_preserved_by_api_server_step(cluster, k, b, s, s_prime, msg, cr, key);
            lemma_api_server_step_only_grows_by_fresh_uids(cluster, s, s_prime, msg);
            if s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == Some(uid) {
                lemma_well_formed_inner_unmarshals(cluster, inner_kind(k, b), spec_ok, k.selector, s_prime, key);
                let new_obj = s_prime.resources()[key];
                let new_inner = unmarshal(inner_kind(k, b), new_obj)->Ok_0;
                assert(preserves_mirror_identity(cr.metadata, new_obj.metadata));
                assert(new_inner.metadata == new_obj.metadata);
                assert(has_mirror_identity(new_inner));
                assert(parent_uid_annotation(new_inner) == parent_uid_annotation(inner));
                assert(mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s_prime));
            } else {
                assert(uid < s.api_server.uid_counter);
                assert(gone(k, b, bs, spec_ok, key, uid)(s_prime));
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
            assert(mirror_object_is(inner_kind(k, b), key, parent_uid, uid)(s_prime));
        },
    }
}

}
