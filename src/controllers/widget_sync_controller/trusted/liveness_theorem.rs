// The properties the Widget sync example is verified against (R1, R2, R3, R3s)
// and its one liveness assumption about the inner side (D3). Motivation:
// doc/widget_sync_design.md, section 3.
//
// Both clusters are one logical store in this model; the outer copy has kind
// OuterWidgetView::kind() and the mirror has kind InnerWidgetView::kind(), at the
// same namespace and name. The reading on two stores, with the outer copy in
// one and the mirror in the other, is widget_sync_controller::proof::two_cluster.
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, esr::*, message::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::spec_types::*;
use verus_temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

// R1, forward eventually stable reconciliation: once the outer copy's spec stops
// changing, the mirror eventually exists, is ours, and carries that spec.
pub open spec fn widget_spec_eventually_synced() -> TempPred<ClusterState> {
    tla_forall(|outer: OuterWidgetView| widget_spec_eventually_synced_per_cr(outer))
}

pub open spec fn widget_spec_eventually_synced_per_cr(outer: OuterWidgetView) -> TempPred<ClusterState> {
    always(lift_state(outer_spec_stable(outer))).leads_to(always(lift_state(spec_synced(outer))))
}

// The premise of R1: the outer copy exists with this uid and spec and is not
// terminating, every in-flight write of the mirror's spec writes `outer.spec`, and
// no in-flight Delete would remove a mirror of the outer copy. Convergence is
// promised for the time after the outer copy stops changing and out-of-band edits
// and deletes of the mirror stop. R1 says nothing about status, so it does not
// need the outer copy's generation to be fixed.
pub open spec fn outer_spec_stable(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::desired_state_is(outer)(s)
        &&& mirror_spec_undisturbed(outer)(s)
        &&& mirror_undeleted(outer)(s)
    }
}

// The premise of R2: R1's premise, and the outer copy's generation is
// `outer.metadata.generation`, which the status R2 promises is stamped with.
pub open spec fn outer_stable(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::desired_state_is(outer)(s)
        &&& s.resources()[outer.object_ref()].metadata.generation == outer.metadata.generation
        &&& mirror_spec_undisturbed(outer)(s)
        &&& mirror_undeleted(outer)(s)
    }
}

// While a mirror of `outer` is at the mirror key, every in-flight Delete of that
// key names, by uid precondition, an object other than that mirror. This is the
// delete counterpart of mirror_spec_undisturbed: the rely lets any other
// controller delete mirrors (an out-of-band `kubectl delete`, a rebuilt inner
// cluster), and R1 and R2 promise convergence once such deletes stop landing on
// the live mirror. A Delete the janitor sends satisfies the clause whenever the
// outer copy exists (janitor_deletes_are_sound), as does a stale Delete of an
// earlier mirror and a Delete arriving while no mirror of `outer` is at the key.
pub open spec fn mirror_undeleted(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #[trigger] s.in_flight().contains(msg) && msg.content is APIRequest ==> match msg.content->APIRequest_0 {
            APIRequest::DeleteRequest(req) => req.key == inner_key(outer) ==> delete_misses_mirror(req, outer)(s),
            _ => true,
        }
    }
}

pub open spec fn delete_misses_mirror(req: DeleteRequest, outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[inner_key(outer)];
        (s.resources().contains_key(inner_key(outer))
            && InnerWidgetView::unmarshal(obj) is Ok
            && is_mirror_of(InnerWidgetView::unmarshal(obj)->Ok_0, outer))
        ==> {
            &&& req.preconditions is Some
            &&& req.preconditions->0.uid is Some
            &&& req.preconditions->0.uid != obj.metadata.uid
        }
    }
}

// Every request in flight that writes the spec of the mirror writes the outer
// copy's spec (the sync reconciler's own patches included).
pub open spec fn mirror_spec_undisturbed(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #[trigger] s.in_flight().contains(msg) && msg.content is APIRequest ==> match msg.content->APIRequest_0 {
            APIRequest::UpdateRequest(req) => req.key() == inner_key(outer) ==> writes_outer_spec(req.obj.spec, outer),
            APIRequest::GetThenUpdateRequest(req) => req.key() == inner_key(outer) ==> writes_outer_spec(req.obj.spec, outer),
            APIRequest::PatchRequest(req) => req.key() == inner_key(outer) ==> writes_outer_spec(req.spec, outer),
            _ => true,
        }
    }
}

pub open spec fn writes_outer_spec(spec: Value, outer: OuterWidgetView) -> bool {
    &&& InnerWidgetView::unmarshal_spec(spec) is Ok
    &&& InnerWidgetView::unmarshal_spec(spec)->Ok_0 == outer.spec
}

pub open spec fn spec_synced(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = inner_key(outer);
        let obj = s.resources()[key];
        let inner = InnerWidgetView::unmarshal(obj)->Ok_0;
        &&& s.resources().contains_key(key)
        &&& obj.metadata.deletion_timestamp is None
        &&& InnerWidgetView::unmarshal(obj) is Ok
        &&& is_mirror_of(inner, outer)
        &&& inner.spec == outer.spec
    }
}

// R2, backward eventually stable reconciliation: once the outer copy's spec stops
// changing and the inner implementation has settled on a status for it, the outer
// copy eventually and stably carries the mirrored fields of that status, stamped
// with its own generation and a true Synced condition at that generation.
//
// The premise fixes the inner status instead of assuming that the inner
// implementation is live, so R2 does not depend on which implementation runs in
// the inner cluster.
pub open spec fn widget_status_eventually_mirrored() -> TempPred<ClusterState> {
    tla_forall(|i: (OuterWidgetView, WidgetStatusView)| widget_status_eventually_mirrored_per_cr(i.0, i.1))
}

pub open spec fn widget_status_eventually_mirrored_per_cr(outer: OuterWidgetView, mirrored: WidgetStatusView) -> TempPred<ClusterState> {
    always(lift_state(outer_stable(outer)).and(lift_state(inner_settled(outer, mirrored))))
        .leads_to(always(lift_state(status_synced(outer, mirrored))))
}

// The inner implementation has processed the mirror's current spec and reports
// `mirrored` (a status with only the mirrored fields set) for it.
pub open spec fn inner_settled(outer: OuterWidgetView, mirrored: WidgetStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let inner = InnerWidgetView::unmarshal(s.resources()[inner_key(outer)])->Ok_0;
        &&& spec_synced(outer)(s)
        &&& inner_caught_up(inner)
        &&& inner.status->0.mirrored() == mirrored
    }
}

pub open spec fn status_synced(outer: OuterWidgetView, mirrored: WidgetStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[outer.object_ref()];
        let stored = OuterWidgetView::unmarshal(obj)->Ok_0;
        let status = stored.status->0;
        &&& s.resources().contains_key(outer.object_ref())
        &&& OuterWidgetView::unmarshal(obj) is Ok
        &&& stored.status is Some
        &&& status.mirrored() == mirrored
        &&& status.observed_generation == stored.metadata.generation
        &&& status.synced_condition() is Some
        &&& status.synced_condition()->0.status == condition_true()
        &&& status.synced_condition()->0.observed_generation == stored.metadata.generation
    }
}

// R3, cleanup (the janitor's ESR): once no outer copy with the parent uid exists
// at the mirror's namespace and name, a mirror object pointing at that parent is
// eventually gone. Stated per mirror object; R3s below is the stable form, which
// needs the sync reconciler too. R3 needs D3: a Delete of an object with
// finalizers only stamps the deletion timestamp.
pub open spec fn widget_mirrors_eventually_collected() -> TempPred<ClusterState> {
    tla_forall(|i: (ObjectRef, Uid, Uid)| widget_mirror_eventually_collected_per_object(i.0, i.1, i.2))
}

pub open spec fn widget_mirror_eventually_collected_per_object(key: ObjectRef, parent_uid: Uid, uid: Uid) -> TempPred<ClusterState> {
    always(lift_state(parent_absent(key, parent_uid))).and(lift_state(mirror_object_is(key, parent_uid, uid)))
        .leads_to(lift_state(object_is_gone(key, uid)))
}

// The object at `key` is the mirror with uid `uid` pointing at `parent_uid`.
pub open spec fn mirror_object_is(key: ObjectRef, parent_uid: Uid, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resources().contains_key(key)
        &&& s.resources()[key].metadata.uid == Some(uid)
        &&& mirror_of_parent(s.resources()[key], parent_uid)
    }
}

// No object with uid `uid` is at `key` (it was removed; uids are never reused).
pub open spec fn object_is_gone(key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        !(s.resources().contains_key(key) && s.resources()[key].metadata.uid == Some(uid))
    }
}

// The key of the outer copy a mirror at `key` would belong to.
pub open spec fn outer_key_of(key: ObjectRef) -> ObjectRef {
    ObjectRef { kind: OuterWidgetView::kind(), ..key }
}

pub open spec fn parent_absent(key: ObjectRef, parent_uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        !(s.resources().contains_key(outer_key_of(key))
            && s.resources()[outer_key_of(key)].metadata.uid == Some(parent_uid))
    }
}

// `obj` is a mirror that points at `parent_uid`.
pub open spec fn mirror_of_parent(obj: DynamicObjectView, parent_uid: Uid) -> bool {
    let inner = InnerWidgetView::unmarshal(obj)->Ok_0;
    &&& InnerWidgetView::unmarshal(obj) is Ok
    &&& has_mirror_identity(inner)
    &&& parent_uid_annotation(inner) == int_to_string_view(parent_uid)
}

pub open spec fn mirror_collected(key: ObjectRef, parent_uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        !(s.resources().contains_key(key) && mirror_of_parent(s.resources()[key], parent_uid))
    }
}

// R3s, stable cleanup: once no outer copy with uid `parent_uid` exists at the
// parent key of `key`, eventually and stably no mirror at `key` points at it.
// R3 removes each such mirror object; R3s adds that the sync reconciler stops
// creating them. It is part of the sync reconciler's ESR (which has R3 as its
// liveness dependency).
pub open spec fn widget_mirrors_stably_collected() -> TempPred<ClusterState> {
    tla_forall(|i: (ObjectRef, Uid)| widget_mirror_stably_collected_per_key(i.0, i.1))
}

pub open spec fn widget_mirror_stably_collected_per_key(key: ObjectRef, parent_uid: Uid) -> TempPred<ClusterState> {
    always(lift_state(parent_absent(key, parent_uid))).leads_to(always(lift_state(mirror_collected(key, parent_uid))))
}

// D3, the liveness dependency on the inner side: a terminating mirror object is
// eventually removed, that is, the inner side removes every finalizer it owns from
// an object with a deletion timestamp (and nothing adds finalizers to such an
// object; the API server rejects that anyway), after which the API server removes
// the object. An axiom in this version; an inner implementation verified in Anvil
// would discharge it in its own guarantee.
pub open spec fn inner_terminating_object(key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& key.kind == InnerWidgetView::kind()
        &&& s.resources().contains_key(key)
        &&& s.resources()[key].metadata.uid == Some(uid)
        &&& s.resources()[key].metadata.deletion_timestamp is Some
    }
}

pub open spec fn inner_releases_terminating_objects() -> TempPred<ClusterState> {
    tla_forall(|i: (ObjectRef, Uid)| lift_state(inner_terminating_object(i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1))))
}

// The janitor's Deletes are sound: a Delete the janitor has in flight tests a uid
// that has been issued, and if the object it would remove is a mirror, that
// mirror's parent is absent for good. This is what the sync reconciler needs to
// know about the janitor. It is part of the janitor's ESR rather than of its
// guarantee because it holds only under the janitor's rely (nobody forges the
// parent-uid annotation), and guarantees are unconditional.
pub open spec fn snapshot_is_mirror(cr: DynamicObjectView) -> bool {
    &&& InnerWidgetView::unmarshal(cr) is Ok
    &&& has_mirror_identity(InnerWidgetView::unmarshal(cr)->Ok_0)
}

pub open spec fn snapshot_parent(cr: DynamicObjectView) -> StringView {
    parent_uid_annotation(InnerWidgetView::unmarshal(cr)->Ok_0)
}

// No object carries the parent uid `parent`, and none ever will.
pub open spec fn parent_absent_forever(parent: StringView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |u: int| u >= s.api_server.uid_counter ==> #[trigger] int_to_string_view(u) != parent
        &&& forall |k: ObjectRef| #[trigger] s.resources().contains_key(k) && s.resources()[k].metadata.uid is Some
            ==> int_to_string_view(s.resources()[k].metadata.uid->0) != parent
    }
}

pub open spec fn janitor_delete_is_sound(msg: Message, s: ClusterState) -> bool {
    let req = msg.content.get_delete_request();
    let obj = s.resources()[req.key];
    &&& req.preconditions is Some
    &&& req.preconditions->0.uid is Some
    &&& req.preconditions->0.uid->0 < s.api_server.uid_counter
    &&& (s.resources().contains_key(req.key) && obj.metadata.uid == req.preconditions->0.uid && snapshot_is_mirror(obj))
        ==> parent_absent_forever(snapshot_parent(obj))(s)
}

pub open spec fn janitor_deletes_are_sound(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.content is APIRequest
            &&& msg.content.is_delete_request()
        } ==> janitor_delete_is_sound(msg, s)
    }
}

// What the janitor promises under its rely: R3, and sound deletes throughout.
pub open spec fn widget_janitor_esr(controller_id: int) -> TempPred<ClusterState> {
    widget_mirrors_eventually_collected().and(always(lift_state(janitor_deletes_are_sound(controller_id))))
}

}
