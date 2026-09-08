// Safety invariants shared by the proofs of the sync reconciler and of the janitor.
//
// The central one is every_mirror_is_bound: every object of the mirror kind in the
// store is a mirror (label, parent-uid annotation, no owner references) whose
// parent uid is "bound" to the outer key of the same name: no object other than
// the outer copy at that key can ever carry that uid. Each side derives its
// premises (what in-flight creates and updates of mirrors look like) from its own
// rely and guarantee; this file works from those premises.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::api_server::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::{
    model::install::*,
    proof::predicate::*,
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Premises: what in-flight writes of mirrors look like, whoever sent them.
// ---------------------------------------------------------------------------

pub open spec fn every_in_flight_inner_create_is_a_mirror_create(k: SyncKind) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
            &&& msg.content.is_create_request()
            &&& is_inner_kind(k, msg.content.get_create_request().obj.kind)
        } ==> {
            let req = msg.content.get_create_request();
            &&& req.obj.metadata.name is Some
            &&& mirror_create_req(k, req, ObjectRef {
                kind: k.outer_kind,
                namespace: req.namespace,
                name: req.obj.metadata.name->0,
            })(s)
        }
    }
}

pub open spec fn every_in_flight_inner_update_preserves_identity(k: SyncKind) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        } ==> {
            &&& msg.content.is_update_request() ==> mirror_update_req(k, msg.content.get_update_request())(s)
            &&& msg.content.is_get_then_update_request() ==> mirror_get_then_update_req(k, msg.content.get_get_then_update_request())(s)
        }
    }
}

// ---------------------------------------------------------------------------
// The store invariant.
// ---------------------------------------------------------------------------

// The string form of parent_uid_is_bound_to_key: the annotation value `parent`
// names no uid the API server may still issue, and the only object whose uid it
// names is the outer copy at `outer_key`.
pub open spec fn parent_uid_string_is_bound_to_key(parent: StringView, outer_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |u: int| u >= s.api_server.uid_counter ==> #[trigger] int_to_string_view(u) != parent
        &&& forall |k: ObjectRef| #[trigger] s.resources().contains_key(k)
            && s.resources()[k].metadata.uid is Some
            && int_to_string_view(s.resources()[k].metadata.uid->0) == parent
            ==> k == outer_key
    }
}

pub proof fn lemma_parent_uid_bound_implies_string_bound(parent_uid: Uid, outer_key: ObjectRef, s: ClusterState)
    requires parent_uid_is_bound_to_key(parent_uid, outer_key)(s),
    ensures parent_uid_string_is_bound_to_key(int_to_string_view(parent_uid), outer_key)(s),
{
    int_to_string_view_injectivity();
    let parent = int_to_string_view(parent_uid);
    assert forall |u: int| u >= s.api_server.uid_counter implies #[trigger] int_to_string_view(u) != parent by {
        if int_to_string_view(u) == parent {
            assert(u == parent_uid);
        }
    }
    assert forall |k: ObjectRef| #[trigger] s.resources().contains_key(k)
        && s.resources()[k].metadata.uid is Some
        && int_to_string_view(s.resources()[k].metadata.uid->0) == parent
    implies k == outer_key by {
        assert(s.resources()[k].metadata.uid->0 == parent_uid);
        assert(s.resources()[k].metadata.uid == Some(parent_uid));
    }
}

pub open spec fn mirror_is_bound(k: SyncKind, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[key];
        let inner = unmarshal(key.kind, obj)->Ok_0;
        &&& unmarshal(key.kind, obj) is Ok
        &&& has_mirror_identity(inner)
        &&& obj.metadata.owner_references is None
        &&& parent_uid_string_is_bound_to_key(parent_uid_annotation(inner), outer_key_of(k, key))(s)
        // The annotation is the string form of some uid (the parent's).
        &&& exists |p: Uid| parent_uid_annotation(inner) == #[trigger] int_to_string_view(p)
    }
}

pub open spec fn every_mirror_is_bound(k: SyncKind, b: Binding) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.resources().contains_key(key) && key.kind == inner_kind(k, b)
            ==> mirror_is_bound(k, key)(s)
    }
}

// A well-formed object of the mirror kind unmarshals.
pub proof fn lemma_well_formed_inner_unmarshals(cluster: Cluster, kind: Kind, spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector, s: ClusterState, key: ObjectRef)
    requires
        cluster.synced_type_is_installed(kind, spec_ok, selector),
        cluster.each_synced_object_in_etcd_is_well_formed(kind)(s),
        s.resources().contains_key(key),
        key.kind == kind,
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    ensures unmarshal(key.kind, s.resources()[key]) is Ok,
{
    let obj = s.resources()[key];
    assert(cluster.etcd_object_is_well_formed(key)(s));
    assert(obj.kind == key.kind);
    assert(unmarshallable_object(obj, cluster.installed_types));
}

pub proof fn lemma_always_every_mirror_is_bound(spec: TempPred<ClusterState>, cluster: Cluster, k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        spec.entails(always(lift_state(every_in_flight_inner_create_is_a_mirror_create(k)))),
        spec.entails(always(lift_state(every_in_flight_inner_update_preserves_identity(k)))),
    ensures spec.entails(always(lift_state(every_mirror_is_bound(k, b)))),
{
    let kind = inner_kind(k, b);
    let inv = every_mirror_is_bound(k, b);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_synced_object_in_etcd_is_well_formed(spec, kind, spec_ok, k.selector);
    always_to_always_later(spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()));
    always_to_always_later(spec, lift_state(cluster.each_synced_object_in_etcd_is_well_formed(kind)));
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& every_in_flight_inner_create_is_a_mirror_create(k)(s)
        &&& every_in_flight_inner_update_preserves_identity(k)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s_prime)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(kind)(s)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(kind)(s_prime)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(every_in_flight_inner_create_is_a_mirror_create(k)),
        lift_state(every_in_flight_inner_update_preserves_identity(k)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        later(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())),
        lift_state(cluster.each_synced_object_in_etcd_is_well_formed(kind)),
        later(lift_state(cluster.each_synced_object_in_etcd_is_well_formed(kind)))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        int_to_string_view_injectivity();
        assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && key.kind == inner_kind(k, b)
        implies mirror_is_bound(k, key)(s_prime) by {
            lemma_well_formed_inner_unmarshals(cluster, kind, spec_ok, k.selector, s_prime, key);
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    let msg = input->0;
                    match msg.content->APIRequest_0 {
                        APIRequest::CreateRequest(req) => {
                            lemma_mirror_is_bound_preserved_by_create(cluster, k, b, s, s_prime, msg, key);
                        },
                        APIRequest::UpdateRequest(req) => {
                            lemma_mirror_is_bound_preserved_by_update(cluster, k, b, s, s_prime, msg, key);
                        },
                        APIRequest::GetThenUpdateRequest(req) => {
                            lemma_mirror_is_bound_preserved_by_get_then_update(cluster, k, b, s, s_prime, msg, key);
                        },
                        _ => {
                            lemma_mirror_is_bound_preserved_by_other_requests(cluster, k, b, s, s_prime, msg, key);
                        },
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                    assert(s.resources().contains_key(key));
                    assert(mirror_is_bound(k, key)(s));
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// The metadata fields a mirror's identity is read from.
pub open spec fn same_identity_and_owners(m1: ObjectMetaView, m2: ObjectMetaView) -> bool {
    &&& m1.labels == m2.labels
    &&& m1.annotations == m2.annotations
    &&& m1.owner_references == m2.owner_references
}

// Bound-ness of an existing mirror carries over to a state whose store only lost
// objects, changed objects without changing their uids, or gained one object with
// the current uid counter as its uid.
pub proof fn lemma_string_bound_preserved(parent: StringView, outer_key: ObjectRef, s: ClusterState, s_prime: ClusterState)
    requires
        parent_uid_string_is_bound_to_key(parent, outer_key)(s),
        s_prime.api_server.uid_counter >= s.api_server.uid_counter,
        forall |k: ObjectRef| #[trigger] s_prime.resources().contains_key(k) ==> {
            ||| (s.resources().contains_key(k) && s_prime.resources()[k].metadata.uid == s.resources()[k].metadata.uid)
            ||| s_prime.resources()[k].metadata.uid == Some(s.api_server.uid_counter)
        },
    ensures parent_uid_string_is_bound_to_key(parent, outer_key)(s_prime),
{
    assert forall |k: ObjectRef| #[trigger] s_prime.resources().contains_key(k)
        && s_prime.resources()[k].metadata.uid is Some
        && int_to_string_view(s_prime.resources()[k].metadata.uid->0) == parent
    implies k == outer_key by {
        if s.resources().contains_key(k) && s_prime.resources()[k].metadata.uid == s.resources()[k].metadata.uid {
        } else {
            assert(s_prime.resources()[k].metadata.uid == Some(s.api_server.uid_counter));
            assert(int_to_string_view(s.api_server.uid_counter) != parent);
        }
    }
}

proof fn lemma_mirror_is_bound_preserved_by_create(cluster: Cluster, k: SyncKind, b: Binding, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        msg.content.is_create_request(),
        every_in_flight_inner_create_is_a_mirror_create(k)(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        every_mirror_is_bound(k, b)(s),
        s_prime.resources().contains_key(key),
        key.kind == inner_kind(k, b),
        unmarshal(key.kind, s_prime.resources()[key]) is Ok,
    ensures mirror_is_bound(k, key)(s_prime),
{
    int_to_string_view_injectivity();
    let req = msg.content.get_create_request();
    let resp = transition_by_etcd(cluster.installed_types, msg, s.api_server).1;
    if s.resources().contains_key(key) {
        // An existing mirror; a create elsewhere issues the current uid counter.
        assert(mirror_is_bound(k, key)(s));
        if s_prime.resources() == s.resources() {
            assert(s_prime.api_server.uid_counter == s.api_server.uid_counter);
        } else {
            assert(s_prime.resources()[key] == s.resources()[key]);
            lemma_string_bound_preserved(parent_uid_annotation(unmarshal(key.kind, s.resources()[key])->Ok_0), outer_key_of(k, key), s, s_prime);
        }
    } else {
        // The mirror was just created: the request is a mirror create.
        assert(s.in_flight().contains(msg));
        assert(is_inner_kind(k, req.obj.kind));
        let outer_key = ObjectRef { kind: k.outer_kind, namespace: req.namespace, name: req.obj.metadata.name->0 };
        assert(mirror_create_req(k, req, outer_key)(s));
        let outer = choose |outer: SyncedObjectView| {
            &&& outer.kind == k.outer_kind
            &&& outer.object_ref() == outer_key
            &&& outer.metadata.uid is Some
            &&& req.namespace == outer_key.namespace
            &&& req.obj == #[trigger] marshal(make_inner(k, outer))
            &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s)
        };
        let created = s_prime.resources()[key];
        assert(created.metadata.labels == make_inner(k, outer).metadata.labels);
        assert(created.metadata.annotations == make_inner(k, outer).metadata.annotations);
        assert(created.metadata.owner_references == make_inner(k, outer).metadata.owner_references);
        let inner = unmarshal(key.kind, created)->Ok_0;
        assert(inner.metadata == created.metadata);
        assert(has_mirror_identity(inner));
        assert(parent_uid_annotation(inner) == int_to_string_view(outer.metadata.uid->0));
        assert(outer_key_of(k, key) == outer_key);
        lemma_parent_uid_bound_implies_string_bound(outer.metadata.uid->0, outer_key, s);
        lemma_string_bound_preserved(int_to_string_view(outer.metadata.uid->0), outer_key, s, s_prime);
    }
}

proof fn lemma_mirror_is_bound_preserved_by_update(cluster: Cluster, k: SyncKind, b: Binding, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        msg.content.is_update_request(),
        every_in_flight_inner_update_preserves_identity(k)(s),
        every_mirror_is_bound(k, b)(s),
        s_prime.resources().contains_key(key),
        key.kind == inner_kind(k, b),
        unmarshal(key.kind, s_prime.resources()[key]) is Ok,
    ensures mirror_is_bound(k, key)(s_prime),
{
    let req = msg.content.get_update_request();
    assert(s.in_flight().contains(msg));
    assert(mirror_update_req(k, req)(s));
    // An update never creates, so the mirror existed before.
    assert(s.resources().contains_key(key));
    assert(mirror_is_bound(k, key)(s));
    let old_obj = s.resources()[key];
    let new_obj = s_prime.resources()[key];
    if new_obj != old_obj {
        // The update landed on this mirror: its rv matched, so identity and owners are kept.
        assert(req.key() == key);
        assert(is_inner_kind(k, req.obj.kind));
        assert(req.obj.metadata.resource_version == old_obj.metadata.resource_version);
        assert(preserves_mirror_identity(old_obj.metadata, req.obj.metadata));
        assert(new_obj.metadata.owner_references == req.obj.metadata.owner_references);
        assert(new_obj.metadata.labels == req.obj.metadata.labels);
        assert(new_obj.metadata.annotations == req.obj.metadata.annotations);
    }
    assert(new_obj.metadata.uid == old_obj.metadata.uid);
    let old_inner = unmarshal(key.kind, old_obj)->Ok_0;
    let new_inner = unmarshal(key.kind, new_obj)->Ok_0;
    assert(has_mirror_identity(new_inner));
    assert(parent_uid_annotation(new_inner) == parent_uid_annotation(old_inner));
    assert(s_prime.api_server.uid_counter == s.api_server.uid_counter);
    lemma_string_bound_preserved(parent_uid_annotation(old_inner), outer_key_of(k, key), s, s_prime);
}

proof fn lemma_mirror_is_bound_preserved_by_get_then_update(cluster: Cluster, k: SyncKind, b: Binding, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        msg.content.is_get_then_update_request(),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        every_mirror_is_bound(k, b)(s),
        s_prime.resources().contains_key(key),
        key.kind == inner_kind(k, b),
        unmarshal(key.kind, s_prime.resources()[key]) is Ok,
    ensures mirror_is_bound(k, key)(s_prime),
{
    lemma_weakly_well_formed_implies_kinds_match(s);
    assert(s.resources().contains_key(key));
    assert(mirror_is_bound(k, key)(s));
    let old_obj = s.resources()[key];
    // A mirror has no owner references, so a transactional update never touches it.
    lemma_get_then_update_keeps_unowned_objects(cluster.installed_types, msg, s.api_server, key);
    assert(s_prime.api_server == transition_by_etcd(cluster.installed_types, msg, s.api_server).0);
    assert(s_prime.resources()[key] == old_obj);
    assert(s_prime.api_server.uid_counter == s.api_server.uid_counter);
    let old_inner = unmarshal(key.kind, old_obj)->Ok_0;
    assert forall |k: ObjectRef| #[trigger] s_prime.resources().contains_key(k) implies {
        ||| (s.resources().contains_key(k) && s_prime.resources()[k].metadata.uid == s.resources()[k].metadata.uid)
        ||| s_prime.resources()[k].metadata.uid == Some(s.api_server.uid_counter)
    } by {
        lemma_get_then_update_only_changes_owned_object(cluster.installed_types, msg, s.api_server, k);
    }
    lemma_string_bound_preserved(parent_uid_annotation(old_inner), outer_key_of(k, key), s, s_prime);
}

// A transactional update keeps the uid of every object it leaves in the store.
proof fn lemma_get_then_update_only_changes_owned_object(installed_types: InstalledTypes, msg: Message, s: APIServerState, k: ObjectRef)
    requires
        msg.content is APIRequest,
        msg.content.is_get_then_update_request(),
        transition_by_etcd(installed_types, msg, s).0.resources.contains_key(k),
    ensures
        s.resources.contains_key(k),
        transition_by_etcd(installed_types, msg, s).0.resources[k].metadata.uid == s.resources[k].metadata.uid,
{
    let req = msg.content.get_get_then_update_request();
    let s_prime = transition_by_etcd(installed_types, msg, s).0;
    if !req.well_formed() {
        assert(s_prime == s);
    } else if !s.resources.contains_key(req.key()) {
        assert(s_prime == s);
    } else if s.resources[req.key()].metadata.owner_references_contains(req.owner_ref) {
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
        if update_request_admission_check(installed_types, update_req, s) is Some {
            assert(s_prime == s);
        } else {
            let old_obj = s.resources[update_req.key()];
            let updated_obj = updated_object(update_req, old_obj);
            assert(updated_obj.metadata.uid == old_obj.metadata.uid);
            if updated_obj == old_obj {
                assert(s_prime == s);
            } else {
                let with_rv = updated_obj.with_resource_version(s.resource_version_counter);
                if updated_object_validity_check(with_rv, old_obj, installed_types) is Some {
                    assert(s_prime == s);
                } else if with_rv.metadata.deletion_timestamp is None
                    || (with_rv.metadata.finalizers is Some && with_rv.metadata.finalizers->0.len() > 0) {
                    assert(s_prime.resources == s.resources.insert(update_req.key(), with_rv));
                } else {
                    assert(s_prime.resources == s.resources.remove(with_rv.object_ref()));
                }
            }
        }
    } else {
        assert(s_prime == s);
    }
}

proof fn lemma_mirror_is_bound_preserved_by_other_requests(cluster: Cluster, k: SyncKind, b: Binding, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        !msg.content.is_create_request(),
        !msg.content.is_update_request(),
        !msg.content.is_get_then_update_request(),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        every_mirror_is_bound(k, b)(s),
        s_prime.resources().contains_key(key),
        key.kind == inner_kind(k, b),
        unmarshal(key.kind, s_prime.resources()[key]) is Ok,
    ensures mirror_is_bound(k, key)(s_prime),
{
    // None of the remaining requests creates an object or changes labels,
    // annotations, owner references or uids.
    lemma_weakly_well_formed_implies_kinds_match(s);
    lemma_other_requests_keep_identity(cluster.installed_types, msg, s.api_server);
    assert(s_prime.api_server == transition_by_etcd(cluster.installed_types, msg, s.api_server).0);
    assert(keeps_identity(s.api_server, s_prime.api_server));
    assert(s.resources().contains_key(key));
    assert(mirror_is_bound(k, key)(s));
    let old_obj = s.resources()[key];
    let new_obj = s_prime.resources()[key];
    assert(same_identity_and_owners(new_obj.metadata, old_obj.metadata));
    assert(new_obj.metadata.uid == old_obj.metadata.uid);
    assert(s_prime.api_server.uid_counter == s.api_server.uid_counter);
    let old_inner = unmarshal(key.kind, old_obj)->Ok_0;
    let new_inner = unmarshal(key.kind, new_obj)->Ok_0;
    assert(has_mirror_identity(new_inner));
    assert(parent_uid_annotation(new_inner) == parent_uid_annotation(old_inner));
    let p = choose |p: Uid| parent_uid_annotation(old_inner) == #[trigger] int_to_string_view(p);
    assert(parent_uid_annotation(new_inner) == int_to_string_view(p));
    lemma_string_bound_preserved(parent_uid_annotation(old_inner), outer_key_of(k, key), s, s_prime);
}

}
