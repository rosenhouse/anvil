use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{types::*, state_machine::*}, message::*, cluster::*
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{

pub proof fn generated_name_reflects_prefix(s: APIServerState, generate_name_field: StringView, prefix: StringView)
ensures
    (exists |suffix| generate_name_field == prefix + "-"@ + suffix)
    <==> (exists |suffix| #[trigger] generated_name(s, generate_name_field) == prefix + "-"@ + suffix)
{
    generated_name_spec(s, generate_name_field);
    let generate_name = generated_name(s, generate_name_field);
    if exists |suffix| #[trigger] generated_name(s, generate_name_field) == prefix + "-"@ + suffix {
        let suffix = choose |suffix| generate_name == prefix + "-"@ + suffix;
        dash_char_view_eq_str_view();
        let suffix2 = choose |suffix2| generate_name == generate_name_field + suffix2 && #[trigger] dash_free(suffix2);
        dash_char_view_eq_str_view();
        if prefix.len() >= generate_name_field.len() {
            assert(generate_name[prefix.len() as int] == '-'@);
            assert(suffix2 == generate_name.subrange(generate_name_field.len() as int, generate_name.len() as int));
            assert(suffix2[prefix.len() - generate_name_field.len()] == '-'@);
            assert(false);
        }
        assert(generate_name_field == generate_name.take(generate_name_field.len() as int));
        assert(prefix + "-"@ == generate_name_field.take(prefix.len() as int + 1));
        assert(generate_name_field == prefix + "-"@ + generate_name_field.subrange(prefix.len() as int + 1, generate_name_field.len() as int));
        assert(exists |suffix| generate_name_field == prefix + "-"@ + suffix);
    }
    if exists |suffix| generate_name_field == prefix + "-"@ + suffix {
        let suffix = choose |suffix| generate_name_field == prefix + "-"@ + suffix;
        let suffix2 = choose |suffix2| generate_name == generate_name_field + suffix2 && #[trigger] dash_free(suffix2);
        assert(generate_name == prefix + "-"@ + (suffix + suffix2));
    }
}

// ---------------------------------------------------------------------------
// What each kind of request leaves alone. These lemmas spell out, per request,
// the parts of a stored object that a request cannot change, so that controller
// proofs do not have to unfold the handlers themselves.
// ---------------------------------------------------------------------------

// Every stored object has the kind of its key (part of weak well-formedness).
pub open spec fn stored_kinds_match_keys(s: APIServerState) -> bool {
    forall |key: ObjectRef| #[trigger] s.resources.contains_key(key) ==> s.resources[key].kind == key.kind
}

pub proof fn lemma_weakly_well_formed_implies_kinds_match(s: ClusterState)
    requires Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    ensures stored_kinds_match_keys(s.api_server),
{
    assert forall |key: ObjectRef| #[trigger] s.api_server.resources.contains_key(key) implies s.api_server.resources[key].kind == key.kind by {
        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    }
}

// The stored object at `key` keeps the parts of its metadata a controller
// identifies it by: uid, labels, annotations, owner references.
pub open spec fn keeps_identity(before: APIServerState, after: APIServerState) -> bool {
    &&& after.uid_counter == before.uid_counter
    &&& forall |key: ObjectRef| #[trigger] after.resources.contains_key(key) ==> {
        &&& before.resources.contains_key(key)
        &&& after.resources[key].kind == before.resources[key].kind
        &&& after.resources[key].metadata.uid == before.resources[key].metadata.uid
        &&& after.resources[key].metadata.labels == before.resources[key].metadata.labels
        &&& after.resources[key].metadata.annotations == before.resources[key].metadata.annotations
        &&& after.resources[key].metadata.owner_references == before.resources[key].metadata.owner_references
    }
}

// The stored object at `key` additionally keeps its finalizers, deletion
// timestamp and status.
pub open spec fn keeps_identity_and_lifecycle(before: APIServerState, after: APIServerState) -> bool {
    &&& keeps_identity(before, after)
    &&& forall |key: ObjectRef| #[trigger] after.resources.contains_key(key) ==> {
        &&& after.resources[key].metadata.finalizers == before.resources[key].metadata.finalizers
        &&& after.resources[key].metadata.deletion_timestamp == before.resources[key].metadata.deletion_timestamp
        &&& after.resources[key].status == before.resources[key].status
    }
}

// An update that goes through with an object whose metadata is the stored one
// (as a patch does) changes the spec and the generation only.
pub proof fn lemma_update_with_stored_metadata_keeps_identity_and_lifecycle(installed_types: InstalledTypes, req: UpdateRequest, s: APIServerState)
    requires
        s.resources.contains_key(req.key()),
        req.obj.metadata == s.resources[req.key()].metadata,
        req.obj.kind == s.resources[req.key()].kind,
        req.obj.status == s.resources[req.key()].status,
    ensures keeps_identity_and_lifecycle(s, handle_update_request(installed_types, req, s).0),
{
    let s_prime = handle_update_request(installed_types, req, s).0;
    let old_obj = s.resources[req.key()];
    if update_request_admission_check(installed_types, req, s) is Some {
        assert(s_prime == s);
    } else {
        let updated_obj = updated_object(req, old_obj);
        assert(updated_obj.metadata.uid == old_obj.metadata.uid);
        assert(updated_obj.metadata.labels == old_obj.metadata.labels);
        assert(updated_obj.metadata.annotations == old_obj.metadata.annotations);
        assert(updated_obj.metadata.owner_references == old_obj.metadata.owner_references);
        assert(updated_obj.metadata.finalizers == old_obj.metadata.finalizers);
        assert(updated_obj.metadata.deletion_timestamp == old_obj.metadata.deletion_timestamp);
        assert(updated_obj.status == old_obj.status);
        assert(updated_obj.kind == old_obj.kind);
        if updated_obj == old_obj {
            assert(s_prime == s);
        } else {
            let with_rv = updated_obj.with_resource_version(s.resource_version_counter);
            if updated_object_validity_check(with_rv, old_obj, installed_types) is Some {
                assert(s_prime == s);
            } else if with_rv.metadata.deletion_timestamp is None
                || (with_rv.metadata.finalizers is Some && with_rv.metadata.finalizers->0.len() > 0) {
                assert(s_prime.resources == s.resources.insert(req.key(), with_rv));
                assert(s_prime.uid_counter == s.uid_counter);
            } else {
                assert(s_prime.resources == s.resources.remove(with_rv.object_ref()));
                assert(s_prime.uid_counter == s.uid_counter);
            }
        }
    }
}

// A status update changes the status only.
pub proof fn lemma_update_status_keeps_identity(installed_types: InstalledTypes, req: UpdateStatusRequest, s: APIServerState)
    ensures
        keeps_identity(s, handle_update_status_request(installed_types, req, s).0),
        ({
            let s_prime = handle_update_status_request(installed_types, req, s).0;
            forall |key: ObjectRef| #[trigger] s_prime.resources.contains_key(key) ==> {
                &&& s_prime.resources[key].metadata.finalizers == s.resources[key].metadata.finalizers
                &&& s_prime.resources[key].metadata.deletion_timestamp == s.resources[key].metadata.deletion_timestamp
                &&& s_prime.resources[key].metadata.generation == s.resources[key].metadata.generation
                &&& s_prime.resources[key].spec == s.resources[key].spec
            }
        }),
{
    let s_prime = handle_update_status_request(installed_types, req, s).0;
    if update_status_request_admission_check(installed_types, req, s) is Some {
        assert(s_prime == s);
    } else {
        let old_obj = s.resources[req.key()];
        let updated_obj = status_updated_object(req, old_obj);
        assert(updated_obj.metadata == old_obj.metadata);
        assert(updated_obj.spec == old_obj.spec);
        assert(updated_obj.kind == old_obj.kind);
        if updated_obj == old_obj {
            assert(s_prime == s);
        } else {
            let with_rv = updated_obj.with_resource_version(s.resource_version_counter);
            if updated_object_validity_check(with_rv, old_obj, installed_types) is Some {
                assert(s_prime == s);
            } else {
                assert(s_prime.resources == s.resources.insert(req.key(), with_rv));
                assert(s_prime.uid_counter == s.uid_counter);
            }
        }
    }
}

// A delete removes the object or stamps its deletion timestamp (bumping the
// generation of a custom resource); it changes nothing else.
pub proof fn lemma_delete_keeps_identity(req: DeleteRequest, s: APIServerState)
    ensures
        keeps_identity(s, handle_delete_request(req, s).0),
        ({
            let s_prime = handle_delete_request(req, s).0;
            forall |key: ObjectRef| #[trigger] s_prime.resources.contains_key(key) ==> {
                &&& s_prime.resources[key].metadata.finalizers == s.resources[key].metadata.finalizers
                &&& s_prime.resources[key].spec == s.resources[key].spec
                &&& s_prime.resources[key].status == s.resources[key].status
            }
        }),
{
    let s_prime = handle_delete_request(req, s).0;
    if delete_request_admission_check(req, s) is Some {
        assert(s_prime == s);
    } else {
        let obj = s.resources[req.key];
        if obj.metadata.finalizers is Some && obj.metadata.finalizers->0.len() > 0 {
            if obj.metadata.deletion_timestamp is Some {
                assert(s_prime == s);
            } else {
                let stamped = obj.with_deletion_timestamp(deletion_timestamp())
                    .with_resource_version(s.resource_version_counter)
                    .with_generation(bumped_generation(obj));
                assert(s_prime.resources == s.resources.insert(req.key, stamped));
                assert(s_prime.uid_counter == s.uid_counter);
            }
        } else {
            assert(s_prime.resources == s.resources.remove(req.key));
            assert(s_prime.uid_counter == s.uid_counter);
        }
    }
}

// A patch replaces the spec of the stored object and nothing else that the
// controller proofs care about.
pub proof fn lemma_patch_request_keeps_identity_and_lifecycle(installed_types: InstalledTypes, req: PatchRequest, s: APIServerState)
    requires stored_kinds_match_keys(s),
    ensures keeps_identity_and_lifecycle(s, handle_patch_request(installed_types, req, s).0),
{
    let s_prime = handle_patch_request(installed_types, req, s).0;
    if !s.resources.contains_key(req.key()) {
        assert(s_prime == s);
    } else if !req.tests.pass(s.resources[req.key()]) {
        assert(s_prime == s);
    } else {
        let old_obj = s.resources[req.key()];
        let update_req = UpdateRequest { namespace: req.namespace, name: req.name, obj: old_obj.with_spec(req.spec) };
        assert(update_req.key() == req.key());
        lemma_update_with_stored_metadata_keeps_identity_and_lifecycle(installed_types, update_req, s);
    }
}

// A status patch replaces the status of the stored object and nothing else.
pub proof fn lemma_patch_status_request_keeps_identity(installed_types: InstalledTypes, req: PatchStatusRequest, s: APIServerState)
    ensures
        keeps_identity(s, handle_patch_status_request(installed_types, req, s).0),
        ({
            let s_prime = handle_patch_status_request(installed_types, req, s).0;
            forall |key: ObjectRef| #[trigger] s_prime.resources.contains_key(key) ==> {
                &&& s_prime.resources[key].metadata.finalizers == s.resources[key].metadata.finalizers
                &&& s_prime.resources[key].metadata.deletion_timestamp == s.resources[key].metadata.deletion_timestamp
                &&& s_prime.resources[key].metadata.generation == s.resources[key].metadata.generation
                &&& s_prime.resources[key].spec == s.resources[key].spec
            }
        }),
{
    let s_prime = handle_patch_status_request(installed_types, req, s).0;
    if !s.resources.contains_key(req.key()) {
        assert(s_prime == s);
    } else if !req.tests.pass(s.resources[req.key()]) {
        assert(s_prime == s);
    } else {
        let old_obj = s.resources[req.key()];
        let update_status_req = UpdateStatusRequest { namespace: req.namespace, name: req.name, obj: old_obj.with_status(req.status) };
        lemma_update_status_keeps_identity(installed_types, update_status_req, s);
    }
}

// Every request other than a create, an update and a transactional update keeps
// the identity of every stored object and issues no uid.
pub proof fn lemma_other_requests_keep_identity(installed_types: InstalledTypes, msg: Message, s: APIServerState)
    requires
        stored_kinds_match_keys(s),
        msg.content is APIRequest,
        !msg.content.is_create_request(),
        !msg.content.is_update_request(),
        !msg.content.is_get_then_update_request(),
    ensures keeps_identity(s, transition_by_etcd(installed_types, msg, s).0),
{
    let s_prime = transition_by_etcd(installed_types, msg, s).0;
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(_) => { assert(s_prime == s); },
        APIRequest::ListRequest(_) => { assert(s_prime == s); },
        APIRequest::DeleteRequest(req) => { lemma_delete_keeps_identity(req, s); },
        APIRequest::UpdateStatusRequest(req) => { lemma_update_status_keeps_identity(installed_types, req, s); },
        APIRequest::GetThenDeleteRequest(req) => {
            if !req.well_formed() {
                assert(s_prime == s);
            } else if !s.resources.contains_key(req.key()) {
                assert(s_prime == s);
            } else if s.resources[req.key()].metadata.owner_references_contains(req.owner_ref) {
                let delete_req = DeleteRequest { key: req.key, preconditions: None };
                lemma_delete_keeps_identity(delete_req, s);
            } else {
                assert(s_prime == s);
            }
        },
        APIRequest::GetThenUpdateStatusRequest(req) => {
            if !req.well_formed() {
                assert(s_prime == s);
            } else if !s.resources.contains_key(req.key()) {
                assert(s_prime == s);
            } else if s.resources[req.key()].metadata.owner_references_contains(req.owner_ref) {
                let current_obj = s.resources[req.key()];
                let new_obj = DynamicObjectView {
                    metadata: current_obj.metadata,
                    spec: current_obj.spec,
                    status: req.obj.status,
                    ..current_obj
                };
                let update_status_req = UpdateStatusRequest { name: req.name, namespace: req.namespace, obj: new_obj };
                lemma_update_status_keeps_identity(installed_types, update_status_req, s);
            } else {
                assert(s_prime == s);
            }
        },
        APIRequest::PatchRequest(req) => { lemma_patch_request_keeps_identity_and_lifecycle(installed_types, req, s); },
        APIRequest::PatchStatusRequest(req) => { lemma_patch_status_request_keeps_identity(installed_types, req, s); },
        _ => { assert(false); },
    }
}

// A transactional update never touches an object without owner references.
pub proof fn lemma_get_then_update_keeps_unowned_objects(installed_types: InstalledTypes, msg: Message, s: APIServerState, key: ObjectRef)
    requires
        stored_kinds_match_keys(s),
        msg.content is APIRequest,
        msg.content.is_get_then_update_request(),
        s.resources.contains_key(key),
        s.resources[key].metadata.owner_references is None,
    ensures ({
        let s_prime = transition_by_etcd(installed_types, msg, s).0;
        &&& s_prime.uid_counter == s.uid_counter
        &&& s_prime.resources.contains_key(key)
        &&& s_prime.resources[key] == s.resources[key]
    }),
{
    let req = msg.content.get_get_then_update_request();
    let s_prime = transition_by_etcd(installed_types, msg, s).0;
    if !req.well_formed() {
        assert(s_prime == s);
    } else if !s.resources.contains_key(req.key()) {
        assert(s_prime == s);
    } else if s.resources[req.key()].metadata.owner_references_contains(req.owner_ref) {
        assert(req.key() != key);
        let current_obj = s.resources[req.key()];
        let new_obj = DynamicObjectView {
            metadata: ObjectMetaView {
                resource_version: current_obj.metadata.resource_version,
                uid: current_obj.metadata.uid,
                ..req.obj.metadata
            },
            ..req.obj
        };
        let update_req = UpdateRequest { name: req.name, namespace: req.namespace, obj: new_obj };
        let s_prime2 = handle_update_request(installed_types, update_req, s).0;
        assert(s_prime == s_prime2);
        if update_request_admission_check(installed_types, update_req, s) is Some {
            assert(s_prime2 == s);
        } else {
            let old_obj = s.resources[update_req.key()];
            let updated_obj = updated_object(update_req, old_obj);
            if updated_obj == old_obj {
                assert(s_prime2 == s);
            } else {
                let with_rv = updated_obj.with_resource_version(s.resource_version_counter);
                if updated_object_validity_check(with_rv, old_obj, installed_types) is Some {
                    assert(s_prime2 == s);
                } else if with_rv.metadata.deletion_timestamp is None
                    || (with_rv.metadata.finalizers is Some && with_rv.metadata.finalizers->0.len() > 0) {
                    assert(s_prime2.resources == s.resources.insert(update_req.key(), with_rv));
                    assert(update_req.key() == req.key());
                } else {
                    assert(s_prime2.resources == s.resources.remove(with_rv.object_ref()));
                    assert(with_rv.object_ref() == req.key());
                }
            }
        }
    } else {
        assert(s_prime == s);
    }
}

}
