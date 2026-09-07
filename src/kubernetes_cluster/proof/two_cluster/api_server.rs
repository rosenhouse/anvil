// The API server of one side, seen through the abstraction, is the one-store API
// server: each handler applied to a relabeled request on the union of the stores
// gives the relabeled result of the handler on the request's store, provided the
// counter the store would allocate relabels to the global counter.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::two_cluster::relabel::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, api_server::types::*, cluster::*, message::*, two_cluster::*,
};
use crate::vstd_ext::string_view::*;
use vstd::{map_lib::*, multiset::*, prelude::*, seq_lib::*, set_lib::*};

verus! {

// The hypotheses every commutation lemma shares.
pub open spec fn relabel_hyps(tc: TwoCluster, r: Relabeling) -> bool {
    &&& injective(r)
    &&& installed_types_ignore_metadata(tc.cluster.installed_types)
    &&& installed_types_coherent(tc.cluster.installed_types)
}

// s with the API server state of `side` replaced.
pub open spec fn with_store(s: TwoClusterState, side: Side, st: APIServerState) -> TwoClusterState {
    TwoClusterState {
        primary: if (side is Primary) { st } else { s.primary },
        remote: if (side is Remote) { st } else { s.remote },
        ..s
    }
}

// The global counters after a step that takes the store of `side` from s.store(side) to st.
pub open spec fn uid_after(s: TwoClusterState, side: Side, st: APIServerState, uid_next: Uid) -> Uid {
    uid_next + (st.uid_counter - s.store(side).uid_counter)
}

pub open spec fn rv_after(s: TwoClusterState, side: Side, st: APIServerState, rv_next: ResourceVersion) -> ResourceVersion {
    rv_next + (st.resource_version_counter - s.store(side).resource_version_counter)
}

// If the step allocates from a counter of the store, the value it allocates
// relabels to the global counter.
pub open spec fn alloc_compatible(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, st: APIServerState, uid_next: Uid, rv_next: ResourceVersion) -> bool {
    &&& st.uid_counter > s.store(side).uid_counter ==> (r.uid)(side, s.store(side).uid_counter) == uid_next
    &&& st.resource_version_counter > s.store(side).resource_version_counter ==> (r.rv)(side, s.store(side).resource_version_counter) == rv_next
}

pub open spec fn abs_after(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, st: APIServerState, uid_next: Uid, rv_next: ResourceVersion) -> APIServerState {
    abs_api_server(tc, r, with_store(s, side, st), uid_after(s, side, st, uid_next), rv_after(s, side, st, rv_next))
}

// ---------------------------------------------------------------------------
// Reads.
// ---------------------------------------------------------------------------

pub proof fn lemma_get_relabel(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, req: GetRequest, uid_next: Uid, rv_next: ResourceVersion)
    requires
        stores_sided(tc, s),
        tc.side_of_kind(req.key.kind) == side,
    ensures ({
        handle_get_request(req, abs_api_server(tc, r, s, uid_next, rv_next))
            == GetResponse { res: relabel_obj_result(tc, r, handle_get_request(req, s.store(side)).res) }
    }),
{
    lemma_abs_store_index(tc, r, s, req.key);
}

pub proof fn lemma_list_relabel(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, req: ListRequest, uid_next: Uid, rv_next: ResourceVersion)
    requires
        stores_sided(tc, s),
        tc.side_of_kind(req.kind) == side,
    ensures ({
        handle_list_request(req, abs_api_server(tc, r, s, uid_next, rv_next))
            == ListResponse { res: Ok(relabel_list(tc, r, handle_list_request(req, s.store(side)).res->Ok_0)) }
    }),
{
    lemma_abs_store_list(tc, r, s, req.namespace, req.kind);
    let sel = |o: DynamicObjectView| {
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    };
    let f = |o: DynamicObjectView| relabel_obj(tc, r, o);
    let selected = s.store(side).resources.values().filter(sel);
    selected.lemma_to_seq_to_set_id();
    assert(abs_store(tc, r, s).values().filter(sel) == selected.map(f));
    assert(selected.to_seq().to_set() == selected);
}

// ---------------------------------------------------------------------------
// Create and delete.
// ---------------------------------------------------------------------------

pub proof fn lemma_create_relabel(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, req: CreateRequest, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        tc.side_of_kind(req.obj.kind) == side,
        tc.request_ok(APIRequest::CreateRequest(req)),
        alloc_compatible(tc, r, s, side, handle_create_request(tc.cluster.installed_types, req, s.store(side)).0, uid_next, rv_next),
    ensures ({
        let (s1, resp) = handle_create_request(tc.cluster.installed_types, req, s.store(side));
        let req1 = CreateRequest { obj: relabel_obj(tc, r, req.obj), ..req };
        &&& handle_create_request(tc.cluster.installed_types, req1, abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), CreateResponse { res: relabel_obj_result(tc, r, resp.res) })
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let obj = req.obj;
    let obj1 = relabel_obj(tc, r, obj);
    let req1 = CreateRequest { obj: obj1, ..req };
    let (s1, resp) = handle_create_request(it, req, st);
    lemma_relabel_obj_keeps_identity(tc, r, obj);
    lemma_unmarshallable_object_relabel(tc, r, obj);
    let key = obj.with_namespace(req.namespace).object_ref();
    assert(obj1.with_namespace(req.namespace).object_ref() == key);
    lemma_abs_store_index(tc, r, s, key);
    assert(create_request_admission_check(it, req1, a) == create_request_admission_check(it, req, st));
    if create_request_admission_check(it, req, st) is None {
        let created = DynamicObjectView {
            kind: obj.kind,
            metadata: ObjectMetaView {
                name: obj.metadata.name,
                namespace: Some(req.namespace),
                resource_version: Some(st.resource_version_counter),
                uid: Some(st.uid_counter),
                generation: initial_generation(obj.kind),
                deletion_timestamp: None,
                ..obj.metadata
            },
            spec: obj.spec,
            status: marshalled_default_status(obj.kind, it),
        };
        let created1 = DynamicObjectView {
            kind: obj1.kind,
            metadata: ObjectMetaView {
                name: obj1.metadata.name,
                namespace: Some(req.namespace),
                resource_version: Some(a.resource_version_counter),
                uid: Some(a.uid_counter),
                generation: initial_generation(obj1.kind),
                deletion_timestamp: None,
                ..obj1.metadata
            },
            spec: obj1.spec,
            status: marshalled_default_status(obj1.kind, it),
        };
        assert(created1.object_ref() == created.object_ref());
        lemma_abs_store_index(tc, r, s, created.object_ref());
        let rc = relabel_obj(tc, r, created);
        // created1 is the relabeled created object up to its uid and resource version.
        assert(created1.metadata == ObjectMetaView { uid: created1.metadata.uid, resource_version: created1.metadata.resource_version, ..rc.metadata });
        lemma_metadata_validity_check_relabel(tc, r, created);
        assert(metadata_validity_check(created1) == metadata_validity_check(rc));
        lemma_valid_object_ignores_metadata(tc, created, created1.metadata);
        assert(created_object_validity_check(created1, it) == created_object_validity_check(created, it));
        if !st.resources.contains_key(created.object_ref()) && created_object_validity_check(created, it) is None {
            assert(s1.uid_counter > st.uid_counter);
            assert(created1 == rc);
            lemma_created_object_unmarshallable(tc, created);
            lemma_abs_store_insert(tc, r, s, with_store(s, side, s1), side, created.object_ref(), created);
        }
    }
}

pub proof fn lemma_delete_relabel(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, req: DeleteRequest, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        tc.side_of_kind(req.key.kind) == side,
        alloc_compatible(tc, r, s, side, handle_delete_request(req, s.store(side)).0, uid_next, rv_next),
    ensures ({
        let (s1, resp) = handle_delete_request(req, s.store(side));
        let req1 = DeleteRequest { preconditions: relabel_preconditions(r, side, req.preconditions), ..req };
        &&& handle_delete_request(req1, abs_api_server(tc, r, s, uid_next, rv_next)) == (abs_after(tc, r, s, side, s1, uid_next, rv_next), resp)
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let req1 = DeleteRequest { preconditions: relabel_preconditions(r, side, req.preconditions), ..req };
    let (s1, resp) = handle_delete_request(req, st);
    lemma_abs_store_index(tc, r, s, req.key);
    assert(delete_request_admission_check(req1, a) == delete_request_admission_check(req, st)) by {
        if st.resources.contains_key(req.key) && req.preconditions is Some {
            let obj = st.resources[req.key];
            let pre = req.preconditions->0;
            match (pre.uid, obj.metadata.uid) {
                (Some(x), Some(y)) => { if (r.uid)(side, x) == (r.uid)(side, y) { assert(x == y); } },
                _ => {},
            }
            match (pre.resource_version, obj.metadata.resource_version) {
                (Some(x), Some(y)) => { if (r.rv)(side, x) == (r.rv)(side, y) { assert(x == y); } },
                _ => {},
            }
        }
    }
    if delete_request_admission_check(req, st) is None {
        let obj = st.resources[req.key];
        let obj1 = relabel_obj(tc, r, obj);
        lemma_relabel_obj_keeps_identity(tc, r, obj);
        if obj.metadata.finalizers is Some && obj.metadata.finalizers->0.len() > 0 {
            if obj.metadata.deletion_timestamp is None {
                let stamped = obj.with_deletion_timestamp(deletion_timestamp()).with_resource_version(st.resource_version_counter).with_generation(bumped_generation(obj));
                let stamped1 = obj1.with_deletion_timestamp(deletion_timestamp()).with_resource_version(a.resource_version_counter).with_generation(bumped_generation(obj1));
                assert(s1.resource_version_counter > st.resource_version_counter);
                assert(stamped1 == relabel_obj(tc, r, stamped));
                lemma_abs_store_insert(tc, r, s, with_store(s, side, s1), side, req.key, stamped);
            }
        } else {
            lemma_abs_store_remove(tc, r, s, with_store(s, side, s1), side, req.key);
        }
    }
}

// ---------------------------------------------------------------------------
// Update and update status.
// ---------------------------------------------------------------------------

pub proof fn lemma_update_admission_relabel(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, name: StringView, namespace: StringView, obj: DynamicObjectView, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        tc.side_of_kind(obj.kind) == side,
    ensures
        update_request_admission_check_helper(tc.cluster.installed_types, name, namespace, relabel_obj(tc, r, obj), abs_api_server(tc, r, s, uid_next, rv_next))
            == update_request_admission_check_helper(tc.cluster.installed_types, name, namespace, obj, s.store(side)),
{
    let st = s.store(side);
    let key = ObjectRef { kind: obj.kind, namespace: namespace, name: name };
    lemma_relabel_obj_keeps_identity(tc, r, obj);
    lemma_unmarshallable_object_relabel(tc, r, obj);
    lemma_abs_store_index(tc, r, s, key);
    if st.resources.contains_key(key) {
        let old = st.resources[key];
        match (obj.metadata.resource_version, old.metadata.resource_version) {
            (Some(x), Some(y)) => { if (r.rv)(side, x) == (r.rv)(side, y) { assert(x == y); } },
            _ => {},
        }
        match (obj.metadata.uid, old.metadata.uid) {
            (Some(x), Some(y)) => { if (r.uid)(side, x) == (r.uid)(side, y) { assert(x == y); } },
            _ => {},
        }
    }
}

pub proof fn lemma_update_relabel(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, req: UpdateRequest, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        tc.side_of_kind(req.obj.kind) == side,
        tc.object_ok(req.obj),
        alloc_compatible(tc, r, s, side, handle_update_request(tc.cluster.installed_types, req, s.store(side)).0, uid_next, rv_next),
    ensures ({
        let (s1, resp) = handle_update_request(tc.cluster.installed_types, req, s.store(side));
        let req1 = UpdateRequest { obj: relabel_obj(tc, r, req.obj), ..req };
        &&& handle_update_request(tc.cluster.installed_types, req1, abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), UpdateResponse { res: relabel_obj_result(tc, r, resp.res) })
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let req1 = UpdateRequest { obj: relabel_obj(tc, r, req.obj), ..req };
    let (s1, resp) = handle_update_request(it, req, st);
    let key = req.key();
    assert(req1.key() == key);
    lemma_update_admission_relabel(tc, r, s, side, req.name, req.namespace, req.obj, uid_next, rv_next);
    lemma_abs_store_index(tc, r, s, key);
    lemma_relabel_obj_keeps_identity(tc, r, req.obj);
    if update_request_admission_check(it, req, st) is None {
        let old = st.resources[key];
        let old1 = relabel_obj(tc, r, old);
        lemma_relabel_obj_keeps_identity(tc, r, old);
        let updated = updated_object(req, old);
        let updated1 = updated_object(req1, old1);
        assert(updated1 == relabel_obj(tc, r, updated));
        if updated == old {
        } else {
            assert(updated1 != old1) by {
                if updated1 == old1 { lemma_relabel_obj_injective(tc, r, updated, old); }
            }
            let u = updated.with_resource_version(st.resource_version_counter);
            let u1 = updated1.with_resource_version(a.resource_version_counter);
            let ru = relabel_obj(tc, r, u);
            assert(u1.metadata == ObjectMetaView { resource_version: u1.metadata.resource_version, ..ru.metadata });
            lemma_metadata_validity_check_relabel(tc, r, u);
            assert(metadata_validity_check(u1) == metadata_validity_check(ru));
            lemma_metadata_transition_validity_check_relabel(tc, r, u, old);
            assert(metadata_transition_validity_check(u1, old1) == metadata_transition_validity_check(ru, old1));
            lemma_valid_object_ignores_metadata(tc, u, u1.metadata);
            lemma_valid_transition_ignores_metadata(tc, u, old, u1.metadata, old1.metadata);
            assert(updated_object_validity_check(u1, old1, it) == updated_object_validity_check(u, old, it));
            if updated_object_validity_check(u, old, it) is None {
                assert(s1.resource_version_counter > st.resource_version_counter);
                assert(u1 == ru);
                if u.metadata.deletion_timestamp is None || (u.metadata.finalizers is Some && u.metadata.finalizers->0.len() > 0) {
                    lemma_abs_store_insert(tc, r, s, with_store(s, side, s1), side, key, u);
                } else {
                    assert(u.object_ref() == key);
                    lemma_abs_store_remove(tc, r, s, with_store(s, side, s1), side, key);
                }
            }
        }
    }
}

pub proof fn lemma_update_status_relabel(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, req: UpdateStatusRequest, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        tc.side_of_kind(req.obj.kind) == side,
        alloc_compatible(tc, r, s, side, handle_update_status_request(tc.cluster.installed_types, req, s.store(side)).0, uid_next, rv_next),
    ensures ({
        let (s1, resp) = handle_update_status_request(tc.cluster.installed_types, req, s.store(side));
        let req1 = UpdateStatusRequest { obj: relabel_obj(tc, r, req.obj), ..req };
        &&& handle_update_status_request(tc.cluster.installed_types, req1, abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), UpdateStatusResponse { res: relabel_obj_result(tc, r, resp.res) })
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let req1 = UpdateStatusRequest { obj: relabel_obj(tc, r, req.obj), ..req };
    let (s1, resp) = handle_update_status_request(it, req, st);
    let key = req.key();
    assert(req1.key() == key);
    lemma_update_admission_relabel(tc, r, s, side, req.name, req.namespace, req.obj, uid_next, rv_next);
    lemma_abs_store_index(tc, r, s, key);
    lemma_relabel_obj_keeps_identity(tc, r, req.obj);
    if update_status_request_admission_check(it, req, st) is None {
        let old = st.resources[key];
        let old1 = relabel_obj(tc, r, old);
        lemma_relabel_obj_keeps_identity(tc, r, old);
        let updated = status_updated_object(req, old);
        let updated1 = status_updated_object(req1, old1);
        assert(updated1 == relabel_obj(tc, r, updated));
        if updated == old {
        } else {
            assert(updated1 != old1) by {
                if updated1 == old1 { lemma_relabel_obj_injective(tc, r, updated, old); }
            }
            let u = updated.with_resource_version(st.resource_version_counter);
            let u1 = updated1.with_resource_version(a.resource_version_counter);
            let ru = relabel_obj(tc, r, u);
            assert(u1.metadata == ObjectMetaView { resource_version: u1.metadata.resource_version, ..ru.metadata });
            lemma_metadata_validity_check_relabel(tc, r, u);
            assert(metadata_validity_check(u1) == metadata_validity_check(ru));
            lemma_metadata_transition_validity_check_relabel(tc, r, u, old);
            assert(metadata_transition_validity_check(u1, old1) == metadata_transition_validity_check(ru, old1));
            lemma_valid_object_ignores_metadata(tc, u, u1.metadata);
            lemma_valid_transition_ignores_metadata(tc, u, old, u1.metadata, old1.metadata);
            assert(updated_object_validity_check(u1, old1, it) == updated_object_validity_check(u, old, it));
            if updated_object_validity_check(u, old, it) is None {
                assert(s1.resource_version_counter > st.resource_version_counter);
                assert(u1 == ru);
                lemma_abs_store_insert(tc, r, s, with_store(s, side, s1), side, key, u);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The message-level handlers.
// ---------------------------------------------------------------------------

proof fn lemma_etcd_get(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is GetRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->GetRequest_0;
    lemma_get_relabel(tc, r, s, side, req, uid_next, rv_next);
    lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
}

proof fn lemma_etcd_list(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is ListRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->ListRequest_0;
    lemma_list_relabel(tc, r, s, side, req, uid_next, rv_next);
    lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
}

proof fn lemma_etcd_create(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is CreateRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->CreateRequest_0;
    lemma_create_relabel(tc, r, s, side, req, uid_next, rv_next);
}

proof fn lemma_etcd_delete(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is DeleteRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->DeleteRequest_0;
    lemma_delete_relabel(tc, r, s, side, req, uid_next, rv_next);
}

proof fn lemma_etcd_update(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is UpdateRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->UpdateRequest_0;
    lemma_update_relabel(tc, r, s, side, req, uid_next, rv_next);
}

proof fn lemma_etcd_update_status(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is UpdateStatusRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->UpdateStatusRequest_0;
    lemma_update_status_relabel(tc, r, s, side, req, uid_next, rv_next);
}

proof fn lemma_etcd_get_then_delete(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is GetThenDeleteRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->GetThenDeleteRequest_0;
    let req1 = GetThenDeleteRequest { owner_ref: relabel_owner_ref(tc, r, req.owner_ref), ..req };
    lemma_abs_store_index(tc, r, s, req.key);
    if req.well_formed() && st.resources.contains_key(req.key) {
        let cur = st.resources[req.key];
        lemma_relabel_obj_keeps_identity(tc, r, cur);
        match cur.metadata.owner_references {
            Some(refs) => { lemma_relabel_owner_refs_contains(tc, r, refs, req.owner_ref); },
            None => {},
        }
        assert(relabel_obj(tc, r, cur).metadata.owner_references_contains(req1.owner_ref) == cur.metadata.owner_references_contains(req.owner_ref));
        if cur.metadata.owner_references_contains(req.owner_ref) {
            let delete_req = DeleteRequest { key: req.key, preconditions: None };
            lemma_delete_relabel(tc, r, s, side, delete_req, uid_next, rv_next);
        } else {
            lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
        }
    } else {
        lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
    }
}

proof fn lemma_etcd_get_then_update(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is GetThenUpdateRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->GetThenUpdateRequest_0;
    let req1 = GetThenUpdateRequest { owner_ref: relabel_owner_ref(tc, r, req.owner_ref), obj: relabel_obj(tc, r, req.obj), ..req };
    let key = req.key();
    assert(req1.key() == key);
    lemma_abs_store_index(tc, r, s, key);
    lemma_relabel_obj_keeps_identity(tc, r, req.obj);
    if req.well_formed() && st.resources.contains_key(key) {
        let cur = st.resources[key];
        lemma_relabel_obj_keeps_identity(tc, r, cur);
        match cur.metadata.owner_references {
            Some(refs) => { lemma_relabel_owner_refs_contains(tc, r, refs, req.owner_ref); },
            None => {},
        }
        assert(relabel_obj(tc, r, cur).metadata.owner_references_contains(req1.owner_ref) == cur.metadata.owner_references_contains(req.owner_ref));
        if cur.metadata.owner_references_contains(req.owner_ref) {
            let new_obj = DynamicObjectView {
                metadata: ObjectMetaView {
                    resource_version: cur.metadata.resource_version,
                    uid: cur.metadata.uid,
                    ..req.obj.metadata
                },
                ..req.obj
            };
            let update_req = UpdateRequest { name: req.name, namespace: req.namespace, obj: new_obj };
            assert(cur.kind == req.obj.kind);
            assert(relabel_obj(tc, r, new_obj) == DynamicObjectView {
                metadata: ObjectMetaView {
                    resource_version: relabel_obj(tc, r, cur).metadata.resource_version,
                    uid: relabel_obj(tc, r, cur).metadata.uid,
                    ..relabel_obj(tc, r, req.obj).metadata
                },
                ..relabel_obj(tc, r, req.obj)
            });
            lemma_update_relabel(tc, r, s, side, update_req, uid_next, rv_next);
        } else {
            lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
        }
    } else {
        lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
    }
}

proof fn lemma_etcd_get_then_update_status(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is GetThenUpdateStatusRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->GetThenUpdateStatusRequest_0;
    let req1 = GetThenUpdateStatusRequest { owner_ref: relabel_owner_ref(tc, r, req.owner_ref), obj: relabel_obj(tc, r, req.obj), ..req };
    let key = req.key();
    assert(req1.key() == key);
    lemma_abs_store_index(tc, r, s, key);
    lemma_relabel_obj_keeps_identity(tc, r, req.obj);
    if req.well_formed() && st.resources.contains_key(key) {
        let cur = st.resources[key];
        lemma_relabel_obj_keeps_identity(tc, r, cur);
        match cur.metadata.owner_references {
            Some(refs) => { lemma_relabel_owner_refs_contains(tc, r, refs, req.owner_ref); },
            None => {},
        }
        assert(relabel_obj(tc, r, cur).metadata.owner_references_contains(req1.owner_ref) == cur.metadata.owner_references_contains(req.owner_ref));
        if cur.metadata.owner_references_contains(req.owner_ref) {
            let new_obj = DynamicObjectView {
                metadata: cur.metadata,
                spec: cur.spec,
                status: req.obj.status,
                ..cur
            };
            let update_status_req = UpdateStatusRequest { name: req.name, namespace: req.namespace, obj: new_obj };
            assert(cur.kind == req.obj.kind);
            assert(relabel_obj(tc, r, new_obj) == DynamicObjectView {
                metadata: relabel_obj(tc, r, cur).metadata,
                spec: relabel_obj(tc, r, cur).spec,
                status: relabel_obj(tc, r, req.obj).status,
                ..relabel_obj(tc, r, cur)
            });
            lemma_update_status_relabel(tc, r, s, side, update_status_req, uid_next, rv_next);
        } else {
            lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
        }
    } else {
        lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
    }
}

proof fn lemma_etcd_patch(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is PatchRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->PatchRequest_0;
    let req1 = PatchRequest { tests: relabel_tests(r, side, req.tests), ..req };
    let key = req.key();
    assert(req1.key() == key);
    lemma_abs_store_index(tc, r, s, key);
    if st.resources.contains_key(key) {
        let old = st.resources[key];
        let old1 = relabel_obj(tc, r, old);
        lemma_relabel_obj_keeps_identity(tc, r, old);
        assert(req1.tests.pass(old1) == req.tests.pass(old)) by {
            match (req.tests.uid, old.metadata.uid) {
                (Some(x), Some(y)) => { if (r.uid)(side, x) == (r.uid)(side, y) { assert(x == y); } },
                _ => {},
            }
        }
        if req.tests.pass(old) {
            let update_req = UpdateRequest { namespace: req.namespace, name: req.name, obj: old.with_spec(req.spec) };
            assert(relabel_obj(tc, r, old.with_spec(req.spec)) == old1.with_spec(req.spec));
            lemma_update_relabel(tc, r, s, side, update_req, uid_next, rv_next);
        } else {
            lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
        }
    } else {
        lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
    }
}

proof fn lemma_etcd_patch_status(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
        msg.content->APIRequest_0 is PatchStatusRequest,
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    let it = tc.cluster.installed_types;
    let st = s.store(side);
    let a = abs_api_server(tc, r, s, uid_next, rv_next);
    let msg1 = relabel_msg(tc, r, msg);
    let (s1, resp) = transition_by_etcd(it, msg, st);
    let req = msg.content->APIRequest_0->PatchStatusRequest_0;
    let req1 = PatchStatusRequest { tests: relabel_tests(r, side, req.tests), ..req };
    let key = req.key();
    assert(req1.key() == key);
    lemma_abs_store_index(tc, r, s, key);
    if st.resources.contains_key(key) {
        let old = st.resources[key];
        let old1 = relabel_obj(tc, r, old);
        lemma_relabel_obj_keeps_identity(tc, r, old);
        assert(req1.tests.pass(old1) == req.tests.pass(old)) by {
            match (req.tests.uid, old.metadata.uid) {
                (Some(x), Some(y)) => { if (r.uid)(side, x) == (r.uid)(side, y) { assert(x == y); } },
                _ => {},
            }
        }
        if req.tests.pass(old) {
            let update_status_req = UpdateStatusRequest { namespace: req.namespace, name: req.name, obj: old.with_status(req.status) };
            assert(relabel_obj(tc, r, old.with_status(req.status)) == old1.with_status(req.status));
            lemma_update_status_relabel(tc, r, s, side, update_status_req, uid_next, rv_next);
        } else {
            lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
        }
    } else {
        lemma_abs_store_unchanged(tc, r, s, with_store(s, side, s1));
    }
}

pub proof fn lemma_transition_by_etcd_relabel(tc: TwoCluster, r: Relabeling, s: TwoClusterState, side: Side, msg: Message, uid_next: Uid, rv_next: ResourceVersion)
    requires
        relabel_hyps(tc, r),
        stores_sided(tc, s),
        msg.content is APIRequest,
        tc.side_of_msg(msg) == side,
        tc.request_ok(msg.content->APIRequest_0),
        alloc_compatible(tc, r, s, side, transition_by_etcd(tc.cluster.installed_types, msg, s.store(side)).0, uid_next, rv_next),
    ensures ({
        let (s1, resp) = transition_by_etcd(tc.cluster.installed_types, msg, s.store(side));
        &&& transition_by_etcd(tc.cluster.installed_types, relabel_msg(tc, r, msg), abs_api_server(tc, r, s, uid_next, rv_next))
            == (abs_after(tc, r, s, side, s1, uid_next, rv_next), relabel_msg(tc, r, resp))
        &&& stores_sided(tc, with_store(s, side, s1))
    }),
{
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(_) => { lemma_etcd_get(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::ListRequest(_) => { lemma_etcd_list(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::CreateRequest(_) => { lemma_etcd_create(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::DeleteRequest(_) => { lemma_etcd_delete(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::UpdateRequest(_) => { lemma_etcd_update(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::UpdateStatusRequest(_) => { lemma_etcd_update_status(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::GetThenDeleteRequest(_) => { lemma_etcd_get_then_delete(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::GetThenUpdateRequest(_) => { lemma_etcd_get_then_update(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::GetThenUpdateStatusRequest(_) => { lemma_etcd_get_then_update_status(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::PatchRequest(_) => { lemma_etcd_patch(tc, r, s, side, msg, uid_next, rv_next); },
        APIRequest::PatchStatusRequest(_) => { lemma_etcd_patch_status(tc, r, s, side, msg, uid_next, rv_next); },
    }
}

}
