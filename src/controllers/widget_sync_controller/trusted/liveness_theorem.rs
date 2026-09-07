// The properties the Widget sync example is verified against, in the notation of
// the other controllers' trusted/liveness_theorem.rs files. Section 5 of
// discussion/multi-cluster/sync_controller_evaluation.md motivates each one.
//
// Both clusters are one logical store in the model; the outer copy has kind
// OuterWidgetView::kind() and the mirror has kind InnerWidgetView::kind(), at the
// same namespace and name.
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, esr::*, message::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::model::{janitor_reconciler, sync_reconciler};
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
    always(lift_state(outer_stable(outer))).leads_to(always(lift_state(spec_synced(outer))))
}

// The premise of R1 and R2: the outer copy has the spec `outer.spec` (and its uid,
// and is not being deleted), and nobody is writing anything but that spec to the
// mirror any more. The second half tolerates mistaken (fat-finger) edits of the
// mirror's spec: the sync reconciler overwrites them, and convergence is promised
// for the time after they stop, exactly as it is promised for the time after the
// outer copy stops changing.
pub open spec fn outer_stable(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::desired_state_is(outer)(s)
        &&& mirror_spec_undisturbed(outer)(s)
    }
}

// Every request in flight that writes the spec of the mirror writes the outer
// copy's spec (the sync reconciler's own patches included).
pub open spec fn mirror_spec_undisturbed(outer: OuterWidgetView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #[trigger] s.in_flight().contains(msg) && msg.content is APIRequest ==> match msg.content->APIRequest_0 {
            APIRequest::UpdateRequest(req) => req.key() == sync_reconciler::inner_key(outer) ==> writes_outer_spec(req.obj.spec, outer),
            APIRequest::GetThenUpdateRequest(req) => req.key() == sync_reconciler::inner_key(outer) ==> writes_outer_spec(req.obj.spec, outer),
            APIRequest::PatchRequest(req) => req.key() == sync_reconciler::inner_key(outer) ==> writes_outer_spec(req.spec, outer),
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
        let key = sync_reconciler::inner_key(outer);
        let obj = s.resources()[key];
        let inner = InnerWidgetView::unmarshal(obj)->Ok_0;
        &&& s.resources().contains_key(key)
        &&& obj.metadata.deletion_timestamp is None
        &&& InnerWidgetView::unmarshal(obj) is Ok
        &&& sync_reconciler::is_mirror_of(inner, outer)
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
        let inner = InnerWidgetView::unmarshal(s.resources()[sync_reconciler::inner_key(outer)])->Ok_0;
        &&& spec_synced(outer)(s)
        &&& sync_reconciler::inner_caught_up(inner)
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

// R3, cleanup (the janitor's own property): once no outer copy with the parent
// uid exists at the mirror's namespace and name, a mirror object pointing at that
// parent is eventually gone.
//
// The property is stated per mirror object (its uid): the janitor's job is to
// remove that object, and it does so even if the inner side holds the object with
// finalizers for a while. Whether another mirror with the same parent uid can be
// created afterwards depends on whoever creates mirrors (the sync reconciler,
// whose reconciles triggered by an older copy of the outer object drain in finite
// time), not on the janitor; the stable form is a property of the two reconcilers
// together and is what R1's proof establishes for the parent uids it cares about.
//
// R3 needs D3 below: the janitor's Delete stamps the deletion timestamp of an
// object with finalizers, the inner side then removes its finalizers, and the
// update that removes the last finalizer removes the object.
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
    &&& janitor_reconciler::has_mirror_identity(inner)
    &&& janitor_reconciler::parent_uid_annotation(inner) == int_to_string_view(parent_uid)
}

pub open spec fn mirror_collected(key: ObjectRef, parent_uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        !(s.resources().contains_key(key) && mirror_of_parent(s.resources()[key], parent_uid))
    }
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

}
