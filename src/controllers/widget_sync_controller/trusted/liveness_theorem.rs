// The properties the Widget sync example is verified against (R1, R2, R3, R3s)
// and its one liveness assumption about the inner side (D3), with the kind `k`
// and the binding `b` as parameters. Motivation: doc/widget_sync_design.md,
// section 3, and doc/widget_sync_fanout_design.md, section 5.1.
//
// Every cluster is one logical store in this model: the outer copy has kind
// `k.outer_kind` and the mirror in binding `b` has kind `inner_kind(k, b)`, at the
// same namespace and name. The reading on two stores, with the outer copy in one
// and one binding's mirrors in the other, is
// widget_sync_controller::proof::two_cluster.
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::spec::{cluster::*, esr::*, message::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::spec_types::*;
use verus_temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// R1, forward eventually stable reconciliation: once the outer copy's spec stops
// changing, the mirror eventually exists in the binding the copy names, is ours,
// and carries that spec.
pub open spec fn widget_spec_eventually_synced(k: SyncKind, bs: Set<Binding>) -> TempPred<ClusterState> {
    tla_forall(|outer: SyncedObjectView| widget_spec_eventually_synced_per_cr(k, bs, outer))
}

pub open spec fn widget_spec_eventually_synced_per_cr(k: SyncKind, bs: Set<Binding>, outer: SyncedObjectView) -> TempPred<ClusterState> {
    always(lift_state(outer_spec_stable(k, bs, outer))).leads_to(always(lift_state(spec_synced(k, outer))))
}

// The premise of R1: the outer copy is one of `k`, it names an inner cluster, it
// exists with this uid and spec and is not terminating, every in-flight write of
// the mirror's spec writes `outer.spec`, and no in-flight Delete would remove a
// mirror of the outer copy. Convergence is promised for the time after the outer
// copy stops changing and out-of-band edits and deletes of the mirror stop. R1
// says nothing about status, so it does not need the outer copy's generation to be
// fixed.
pub open spec fn outer_spec_stable(k: SyncKind, bs: Set<Binding>, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& outer.kind == k.outer_kind
        &&& cluster_of(k.selector, outer) is Some
        &&& bs.contains(binding_of(k, outer))
        &&& Cluster::synced_desired_state_is(outer)(s)
        &&& mirror_spec_undisturbed(k, outer)(s)
        &&& mirror_undeleted(k, outer)(s)
    }
}

// The premise of R2: R1's premise, and the outer copy's generation is
// `outer.metadata.generation`, which the status R2 promises is stamped with.
pub open spec fn outer_stable(k: SyncKind, bs: Set<Binding>, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& outer_spec_stable(k, bs, outer)(s)
        &&& s.resources()[outer.object_ref()].metadata.generation == outer.metadata.generation
    }
}

// While a mirror of `outer` is at the mirror key, every in-flight Delete of that
// key names, by uid precondition, an object other than that mirror. This is the
// delete counterpart of mirror_spec_undisturbed: the rely lets any other
// controller delete mirrors (an out-of-band `kubectl delete`, a rebuilt inner
// cluster), and R1 and R2 promise convergence once such deletes stop landing on
// the live mirror. A Delete a janitor sends satisfies the clause whenever the
// outer copy exists (janitor_deletes_are_sound), as does a stale Delete of an
// earlier mirror and a Delete arriving while no mirror of `outer` is at the key.
pub open spec fn mirror_undeleted(k: SyncKind, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #[trigger] s.in_flight().contains(msg) && msg.content is APIRequest ==> match msg.content->APIRequest_0 {
            APIRequest::DeleteRequest(req) => req.key == inner_key(k, outer) ==> delete_misses_mirror(k, req, outer)(s),
            _ => true,
        }
    }
}

pub open spec fn delete_misses_mirror(k: SyncKind, req: DeleteRequest, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = inner_key(k, outer);
        let obj = s.resources()[key];
        (s.resources().contains_key(key)
            && unmarshal(key.kind, obj) is Ok
            && is_mirror_of(unmarshal(key.kind, obj)->Ok_0, outer))
        ==> {
            &&& req.preconditions is Some
            &&& req.preconditions->0.uid is Some
            &&& req.preconditions->0.uid != obj.metadata.uid
        }
    }
}

// Every request in flight that writes the spec of the mirror writes the outer
// copy's spec (the sync reconciler's own patches included).
pub open spec fn mirror_spec_undisturbed(k: SyncKind, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #[trigger] s.in_flight().contains(msg) && msg.content is APIRequest ==> match msg.content->APIRequest_0 {
            APIRequest::UpdateRequest(req) => req.key() == inner_key(k, outer) ==> writes_outer_spec(req.obj.spec, outer),
            APIRequest::GetThenUpdateRequest(req) => req.key() == inner_key(k, outer) ==> writes_outer_spec(req.obj.spec, outer),
            APIRequest::PatchRequest(req) => req.key() == inner_key(k, outer) ==> writes_outer_spec(req.spec, outer),
            _ => true,
        }
    }
}

// The spec of an object of the shape is copied verbatim, so writing it is equality.
pub open spec fn writes_outer_spec(spec: Value, outer: SyncedObjectView) -> bool {
    spec == outer.spec
}

pub open spec fn spec_synced(k: SyncKind, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = inner_key(k, outer);
        let obj = s.resources()[key];
        let inner = unmarshal(key.kind, obj)->Ok_0;
        &&& s.resources().contains_key(key)
        &&& obj.metadata.deletion_timestamp is None
        &&& unmarshal(key.kind, obj) is Ok
        &&& is_mirror_of(inner, outer)
        &&& inner.spec == outer.spec
    }
}

// R2, backward eventually stable reconciliation: once the outer copy's spec stops
// changing and the inner implementation has settled on a status for it, the outer
// copy eventually and stably carries the status the sync controller derives from
// it, outer_status_for(g, settled, Synced): the mirrored remainder of the inner
// status, its Ready and Stalled conditions merged with a true Synced condition,
// all stamped with the outer copy's own generation g.
//
// The premise fixes the inner status (its mirrored remainder and its conditions;
// its observed_generation is fixed by inner_caught_up) instead of assuming that
// the inner implementation is live, so R2 does not depend on which implementation
// runs in the inner cluster.
pub open spec fn widget_status_eventually_mirrored(k: SyncKind, bs: Set<Binding>) -> TempPred<ClusterState> {
    tla_forall(|i: (SyncedObjectView, SyncedStatusView)| widget_status_eventually_mirrored_per_cr(k, bs, i.0, i.1))
}

pub open spec fn widget_status_eventually_mirrored_per_cr(k: SyncKind, bs: Set<Binding>, outer: SyncedObjectView, settled: SyncedStatusView) -> TempPred<ClusterState> {
    always(lift_state(outer_stable(k, bs, outer)).and(lift_state(inner_settled(k, outer, settled))))
        .leads_to(always(lift_state(status_synced(k, outer, settled))))
}

// The inner implementation has processed the mirror's current spec and reports
// the mirrored remainder and the conditions of `settled` for it.
pub open spec fn inner_settled(k: SyncKind, outer: SyncedObjectView, settled: SyncedStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = inner_key(k, outer);
        let inner = unmarshal(key.kind, s.resources()[key])->Ok_0;
        &&& spec_synced(k, outer)(s)
        &&& inner_caught_up(inner)
        &&& inner.status->0.mirrored() == settled.mirrored()
        &&& inner.status->0.conditions == settled.conditions
    }
}

// The outer copy's status is exactly the one the sync controller derives from
// `settled` for a synced mirror at the copy's current generation.
pub open spec fn status_synced(k: SyncKind, outer: SyncedObjectView, settled: SyncedStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[outer.object_ref()];
        let stored = unmarshal(k.outer_kind, obj)->Ok_0;
        &&& s.resources().contains_key(outer.object_ref())
        &&& unmarshal(k.outer_kind, obj) is Ok
        &&& stored.status == Some(outer_status_for(stored.metadata.generation, settled, SyncOutcomeView::Synced))
    }
}

// R3, cleanup (the janitor's ESR): once no outer copy with the parent uid that
// names this binding exists at the mirror's namespace and name, a mirror object in
// this binding pointing at that parent is eventually gone. Stated per mirror
// object; R3s below is the stable form, which needs the sync reconciler too. R3
// needs D3: a Delete of an object with finalizers only stamps the deletion
// timestamp.
pub open spec fn widget_mirrors_eventually_collected(k: SyncKind, b: Binding) -> TempPred<ClusterState> {
    tla_forall(|i: (ObjectRef, Uid, Uid)| widget_mirror_eventually_collected_per_object(k, b, i.0, i.1, i.2))
}

pub open spec fn widget_mirror_eventually_collected_per_object(k: SyncKind, b: Binding, key: ObjectRef, parent_uid: Uid, uid: Uid) -> TempPred<ClusterState> {
    always(lift_state(parent_absent(k, b, key, parent_uid))).and(lift_state(mirror_object_is(inner_kind(k, b), key, parent_uid, uid)))
        .leads_to(lift_state(object_is_gone(key, uid)))
}

// The object at `key` is the mirror with uid `uid` pointing at `parent_uid`.
pub open spec fn mirror_object_is(kind: Kind, key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& key.kind == kind
        &&& s.resources().contains_key(key)
        &&& s.resources()[key].metadata.uid == Some(uid)
        &&& mirror_of_parent(kind, s.resources()[key], parent_uid)
    }
}

// No object with uid `uid` is at `key` (it was removed; uids are never reused).
pub open spec fn object_is_gone(key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        !(s.resources().contains_key(key) && s.resources()[key].metadata.uid == Some(uid))
    }
}

// The outer copy a mirror at `key` would belong to is absent: no object with uid
// `parent_uid` whose selector names this binding's inner cluster is at that key.
// A parent that moved to another binding is absent for this one, which is what
// keeps a janitor from holding on to a mirror the parent no longer wants.
pub open spec fn parent_absent(k: SyncKind, b: Binding, key: ObjectRef, parent_uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let outer_key = outer_key_of(k, key);
        !(s.resources().contains_key(outer_key)
            && s.resources()[outer_key].metadata.uid == Some(parent_uid)
            && cluster_of_dynamic(k.selector, s.resources()[outer_key]) == Some(b.name))
    }
}

// `obj` is a mirror of kind `kind` that points at `parent_uid`.
pub open spec fn mirror_of_parent(kind: Kind, obj: DynamicObjectView, parent_uid: Uid) -> bool {
    let inner = unmarshal(kind, obj)->Ok_0;
    &&& unmarshal(kind, obj) is Ok
    &&& has_mirror_identity(inner)
    &&& parent_uid_annotation(inner) == int_to_string_view(parent_uid)
}

pub open spec fn mirror_collected(kind: Kind, key: ObjectRef, parent_uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        !(s.resources().contains_key(key) && mirror_of_parent(kind, s.resources()[key], parent_uid))
    }
}

// R3s, stable cleanup: once no outer copy with uid `parent_uid` naming this
// binding exists at the parent key of `key`, eventually and stably no mirror at
// `key` points at it. R3 removes each such mirror object; R3s adds that the sync
// reconciler stops creating them. It is part of the sync reconciler's ESR (which
// has the janitors' ESRs as its liveness dependency).
pub open spec fn widget_mirrors_stably_collected(k: SyncKind, bs: Set<Binding>) -> TempPred<ClusterState> {
    tla_forall(|i: (Binding, ObjectRef, Uid)| widget_mirror_stably_collected_per_key(k, bs, i.0, i.1, i.2))
}

pub open spec fn widget_mirror_stably_collected_per_key(k: SyncKind, bs: Set<Binding>, b: Binding, key: ObjectRef, parent_uid: Uid) -> TempPred<ClusterState> {
    always(lift_state(bound_parent_absent(k, bs, b, key, parent_uid))).leads_to(always(lift_state(mirror_collected(inner_kind(k, b), key, parent_uid))))
}

// R3s's premise: `key` is a mirror key of a bound binding whose parent is absent.
pub open spec fn bound_parent_absent(k: SyncKind, bs: Set<Binding>, b: Binding, key: ObjectRef, parent_uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& bs.contains(b)
        &&& key.kind == inner_kind(k, b)
        &&& parent_absent(k, b, key, parent_uid)(s)
    }
}

// D3, the liveness dependency on the inner side: a terminating mirror object of
// any binding of `k` is eventually removed, that is, the inner side removes every
// finalizer it owns from an object with a deletion timestamp (and nothing adds
// finalizers to such an object; the API server rejects that anyway), after which
// the API server removes the object. An axiom in this version; an inner
// implementation verified in Anvil would discharge it in its own guarantee.
pub open spec fn is_bound_inner_kind(k: SyncKind, bs: Set<Binding>, kind: Kind) -> bool {
    exists |b: Binding| bs.contains(b) && kind == #[trigger] inner_kind(k, b)
}

pub open spec fn inner_terminating_object(k: SyncKind, bs: Set<Binding>, key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& is_bound_inner_kind(k, bs, key.kind)
        &&& s.resources().contains_key(key)
        &&& s.resources()[key].metadata.uid == Some(uid)
        &&& s.resources()[key].metadata.deletion_timestamp is Some
    }
}

pub open spec fn inner_releases_terminating_objects(k: SyncKind, bs: Set<Binding>) -> TempPred<ClusterState> {
    tla_forall(|i: (ObjectRef, Uid)| lift_state(inner_terminating_object(k, bs, i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1))))
}

// The janitor's Deletes are sound: a Delete the janitor of `(k, b)` has in flight
// tests a uid that has been issued, and if the object it would remove is a mirror,
// that mirror's parent is absent for good. This is what the sync reconciler needs
// to know about the janitors. It is part of a janitor's ESR rather than of its
// guarantee because it holds only under the janitor's rely (nobody forges the
// parent-uid annotation), and guarantees are unconditional.
pub open spec fn snapshot_is_mirror(kind: Kind, cr: DynamicObjectView) -> bool {
    &&& unmarshal(kind, cr) is Ok
    &&& has_mirror_identity(unmarshal(kind, cr)->Ok_0)
}

pub open spec fn snapshot_parent(kind: Kind, cr: DynamicObjectView) -> StringView {
    parent_uid_annotation(unmarshal(kind, cr)->Ok_0)
}

// No object that names this binding's inner cluster carries the parent uid
// `parent`, and none ever will.
pub open spec fn parent_absent_forever(k: SyncKind, b: Binding, parent: StringView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |u: int| u >= s.api_server.uid_counter ==> #[trigger] int_to_string_view(u) != parent
        &&& forall |key: ObjectRef| #[trigger] s.resources().contains_key(key) && s.resources()[key].metadata.uid is Some
            && cluster_of_dynamic(k.selector, s.resources()[key]) == Some(b.name)
            ==> int_to_string_view(s.resources()[key].metadata.uid->0) != parent
    }
}

pub open spec fn janitor_delete_is_sound(k: SyncKind, b: Binding, msg: Message, s: ClusterState) -> bool {
    let req = msg.content.get_delete_request();
    let obj = s.resources()[req.key];
    &&& req.preconditions is Some
    &&& req.preconditions->0.uid is Some
    &&& req.preconditions->0.uid->0 < s.api_server.uid_counter
    &&& (s.resources().contains_key(req.key) && obj.metadata.uid == req.preconditions->0.uid && snapshot_is_mirror(inner_kind(k, b), obj))
        ==> parent_absent_forever(k, b, snapshot_parent(inner_kind(k, b), obj))(s)
}

pub open spec fn janitor_deletes_are_sound(k: SyncKind, b: Binding, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.content is APIRequest
            &&& msg.content.is_delete_request()
        } ==> janitor_delete_is_sound(k, b, msg, s)
    }
}

// What a janitor promises under its rely: R3, and sound deletes throughout.
pub open spec fn widget_janitor_esr(k: SyncKind, b: Binding, controller_id: int) -> TempPred<ClusterState> {
    widget_mirrors_eventually_collected(k, b).and(always(lift_state(janitor_deletes_are_sound(k, b, controller_id))))
}

}
