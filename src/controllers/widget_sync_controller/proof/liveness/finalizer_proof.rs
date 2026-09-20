// The finalizer layer of R1 and R2: under the premise of R1, the sync finalizer
// is eventually and forever on the stored outer copy, and every snapshot the
// sync reconciler works from is live and carries it. Once that holds, a
// reconcile of the outer copy starts with the Get of the mirror, which is where
// the walks of sync_spec_proof.rs and sync_status_proof.rs pick up.
//
// The layer is built in four steps under phase II:
// 1. every snapshot is live, and a snapshot carrying the finalizer means the
//    stored copy carries it (a stale snapshot is consumed, a fresh one is a
//    copy of the store);
// 2. every snapshot carries the stored copy's resource version, unless the
//    copy carries the finalizer: the only writes that land on the copy, once
//    the snapshot was taken, carry the finalizer (the premise), or are status
//    writes of a reconcile that owns the copy;
// 3. the stored copy eventually carries the finalizer: a reconcile of a copy
//    without it sends the Update that adds it, built from its snapshot, and the
//    Update lands unless a write carrying the finalizer landed first;
// 4. every snapshot carries the finalizer, by the same argument as 1.
//
// Steps 1, 2 and 4 are one lemma about snapshots, stated for any property of a
// snapshot and the state (spec.rs) that the store satisfies for good and that
// a step never takes away.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::{api_server::*, temporal_rules::*};
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{set_lib::*, string_view::*};
use crate::widget_sync_controller::{
    model::{install::*, sync_reconciler, sync_reconciler::WidgetSyncReconcileState},
    proof::{
        guarantee::*, helper_invariants::*, janitor_invariants::*,
        liveness::{api_actions::*, spec::*, sync_spec_proof::*, terminate},
        predicate::*, sync_invariants::*,
    },
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Snapshots eventually satisfy what the store satisfies for good.
// ---------------------------------------------------------------------------

// The scheduled snapshot eventually and forever satisfies the property: a stale
// one is run (the reconciler is fair and, being idle eventually, takes it), and
// scheduling copies the stored object.
pub proof fn lemma_true_leads_to_always_scheduled_satisfies(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, pred: spec_fn(DynamicObjectView, ClusterState) -> bool
)
    requires
        cluster.controller_models.contains_key(controller_id),
        cluster.reconcile_model(controller_id).kind == key.kind,
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(stored_satisfies(key, pred)))),
        spec.entails(always(lift_action(preserves(pred)))),
        spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(scheduled_satisfies(controller_id, key, pred))))),
{
    let good = scheduled_satisfies(controller_id, key, pred);
    let bad = |s: ClusterState| !good(s);
    let idle = Cluster::reconcile_idle(controller_id, key);
    let next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& stored_satisfies(key, pred)(s_prime)
        &&& preserves(pred)(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    always_to_always_later(spec, lift_state(stored_satisfies(key, pred)));
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(cluster.next()),
        later(lift_state(stored_satisfies(key, pred))),
        lift_action(preserves(pred)),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    // The scheduled snapshot of `key` after a step: unchanged, removed, or a copy of the store.
    assert forall |s, s_prime: ClusterState| #[trigger] next(s, s_prime) && s_prime.scheduled_reconciles(controller_id).contains_key(key)
        implies (s.resources().contains_key(key) && s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key] && s_prime.resources() == s.resources())
            || (s.scheduled_reconciles(controller_id).contains_key(key) && s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ScheduleControllerReconcileStep(input) => {
                if input.0 == controller_id && input.1 == key {
                    assert(s.resources().contains_key(key));
                    assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
                } else {
                    assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                }
            },
            Step::ControllerStep(input) => {
                assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
            },
            Step::RestartControllerStep(id) => {
                assert(id != controller_id);
                assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
            },
            _ => {
                assert(s_prime.scheduled_reconciles(controller_id) == s.scheduled_reconciles(controller_id));
            },
        }
    }
    // good is stable.
    assert forall |s, s_prime: ClusterState| good(s) && #[trigger] next(s, s_prime) implies good(s_prime) by {
        if s_prime.scheduled_reconciles(controller_id).contains_key(key) {
            if s.resources().contains_key(key) && s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key] && s_prime.resources() == s.resources() {
                assert(s_prime.resources().contains_key(key));
                assert(pred(s_prime.resources()[key], s_prime));
            } else {
                assert(pred(s.scheduled_reconciles(controller_id)[key], s));
            }
        }
    }
    // bad /\ idle ~> good: the reconciler runs the scheduled snapshot.
    let pre = |s: ClusterState| bad(s) && idle(s);
    let input = (None::<Message>, Some(key));
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || good(s_prime) by {
        if !good(s_prime) {
            // Only running the scheduled snapshot of `key` starts a reconcile of it, and that removes the snapshot.
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(i) => {
                    if i.0 == controller_id && i.2 == Some(key) {
                        assert(!s_prime.scheduled_reconciles(controller_id).contains_key(key));
                        assert(false);
                    } else {
                        assert(!s_prime.ongoing_reconciles(controller_id).contains_key(key));
                    }
                },
                _ => {
                    assert(!s_prime.ongoing_reconciles(controller_id).contains_key(key));
                },
            }
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies good(s_prime) by {
        assert(!s_prime.scheduled_reconciles(controller_id).contains_key(key));
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::RunScheduledReconcile, (controller_id, input.0, input.1))(s) by {
        assert(s.scheduled_reconciles(controller_id).contains_key(key));
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, next, ControllerStep::RunScheduledReconcile, pre, good);
    // bad ~> idle ~> pre \/ good ~> good.
    leads_to_weaken(spec, true_pred(), lift_state(idle), lift_state(bad), lift_state(idle));
    entails_implies_leads_to(spec, lift_state(idle), lift_state(pre).or(lift_state(good)));
    leads_to_trans(spec, lift_state(bad), lift_state(idle), lift_state(pre).or(lift_state(good)));
    entails_implies_leads_to(spec, lift_state(good), lift_state(good));
    or_leads_to(spec, lift_state(pre), lift_state(good), lift_state(good));
    leads_to_trans(spec, lift_state(bad), lift_state(pre).or(lift_state(good)), lift_state(good));
    or_leads_to(spec, lift_state(bad), lift_state(good), lift_state(good));
    temp_pred_equality(true_pred(), lift_state(bad).or(lift_state(good)));
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(good));
}

// The snapshot of the ongoing reconcile eventually and forever satisfies the
// property, once the scheduled one does: a reconcile ends, and the next one is
// started from the scheduled snapshot.
pub proof fn lemma_true_leads_to_always_ongoing_satisfies(
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, pred: spec_fn(DynamicObjectView, ClusterState) -> bool
)
    requires
        cluster.controller_models.contains_key(controller_id),
        cluster.reconcile_model(controller_id).kind == key.kind,
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_action(preserves(pred)))),
        spec.entails(always(lift_state(scheduled_satisfies(controller_id, key, pred)))),
        spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(ongoing_satisfies(controller_id, key, pred))))),
{
    let good = ongoing_satisfies(controller_id, key, pred);
    let idle = Cluster::reconcile_idle(controller_id, key);
    let next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& scheduled_satisfies(controller_id, key, pred)(s)
        &&& preserves(pred)(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(cluster.next()),
        lift_state(scheduled_satisfies(controller_id, key, pred)),
        lift_action(preserves(pred)),
        lift_state(Cluster::there_is_the_controller_state(controller_id))
    );
    assert forall |s, s_prime: ClusterState| good(s) && #[trigger] next(s, s_prime) implies good(s_prime) by {
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(i) => {
                    if i.0 == controller_id && i.2 == Some(key) {
                        if s.ongoing_reconciles(controller_id).contains_key(key) {
                            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.ongoing_reconciles(controller_id)[key].triggering_cr);
                        } else {
                            // Started from the scheduled snapshot.
                            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
                            assert(pred(s.scheduled_reconciles(controller_id)[key], s));
                        }
                    } else {
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    }
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                },
            }
        }
    }
    // idle ==> good, and true ~> idle.
    entails_implies_leads_to(spec, lift_state(idle), lift_state(good));
    leads_to_trans(spec, true_pred(), lift_state(idle), lift_state(good));
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(good));
}

// ---------------------------------------------------------------------------
// One step at the outer copy's key, under the premise of R1.
// ---------------------------------------------------------------------------

// The sync finalizer, once on the stored outer copy, stays there: every write that
// lands carries it (the premise), and no other request touches finalizers.
pub proof fn lemma_outer_owned_after_step(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        sync_step_next(k, b, cluster, controller_id, janitor_id, outer)(s, s_prime),
        Cluster::synced_desired_state_is(outer)(s_prime),
        outer_owned(outer)(s),
    ensures outer_owned(outer)(s_prime),
{
    let key = outer.object_ref();
    let old = s.resources()[key];
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            assert(msg.content is APIRequest);
            match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        // It landed, so it carries the stored version and, by the premise, the finalizer.
                        assert(req.obj.metadata.resource_version == old.metadata.resource_version);
                        assert(has_sync_finalizer(req.obj.metadata));
                        assert(s_prime.resources()[key].metadata.finalizers == req.obj.metadata.finalizers);
                    }
                },
                APIRequest::GetThenUpdateRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(has_sync_finalizer(req.obj.metadata));
                        assert(s_prime.resources()[key].metadata.finalizers == req.obj.metadata.finalizers);
                    }
                },
                APIRequest::PatchRequest(req) => {
                    lemma_patch_request_keeps_identity_and_lifecycle(cluster.installed_types, req, s.api_server);
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(keeps_identity_and_lifecycle(s.api_server, s_prime.api_server));
                    }
                },
                APIRequest::DeleteRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        // A delete that lands stamps or removes the copy, which the premise rules out at s_prime.
                        assert(false);
                    }
                },
                APIRequest::GetThenDeleteRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(false);
                    }
                },
                APIRequest::UpdateStatusRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(s_prime.resources()[key].metadata.finalizers == old.metadata.finalizers);
                    }
                },
                APIRequest::GetThenUpdateStatusRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(s_prime.resources()[key].metadata.finalizers == old.metadata.finalizers);
                    }
                },
                APIRequest::PatchStatusRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(s_prime.resources()[key].metadata.finalizers == old.metadata.finalizers);
                    }
                },
                APIRequest::CreateRequest(_) => {
                    assert(s_prime.resources()[key] == old);
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                },
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// Every request the sync reconciler has in flight for `key` is not a status write.
pub open spec fn no_status_write_in_flight_for(controller_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            &&& s.in_flight().contains(msg)
            &&& msg.src == HostId::Controller(controller_id, key)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
        } ==> !(msg.content->APIRequest_0 is PatchStatusRequest)
    }
}

// While the sync reconciler has no status write of the copy in flight, a step that
// changes the stored outer copy is a write that carries the finalizer: nothing
// else writes the copy. So the copy is either as it was or owned.
pub proof fn lemma_outer_copy_unchanged_or_owned_after_step(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        sync_step_next(k, b, cluster, controller_id, janitor_id, outer)(s, s_prime),
        Cluster::synced_desired_state_is(outer)(s_prime),
        no_status_write_in_flight_for(controller_id, outer.object_ref())(s),
    ensures
        s_prime.resources()[outer.object_ref()] == s.resources()[outer.object_ref()] || outer_owned(outer)(s_prime),
{
    let key = outer.object_ref();
    let old = s.resources()[key];
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            assert(msg.content is APIRequest);
            match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(req.obj.metadata.resource_version == old.metadata.resource_version);
                        assert(has_sync_finalizer(req.obj.metadata));
                        assert(s_prime.resources()[key].metadata.finalizers == req.obj.metadata.finalizers);
                    }
                },
                APIRequest::GetThenUpdateRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(has_sync_finalizer(req.obj.metadata));
                        assert(s_prime.resources()[key].metadata.finalizers == req.obj.metadata.finalizers);
                    }
                },
                APIRequest::PatchRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        // A patch of the spec that lands writes the outer spec (the premise), so it changes nothing.
                        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                        assert(old.metadata.namespace == Some(req.namespace));
                        assert(old.spec == outer.spec);
                        assert(s_prime.resources()[key].spec == req.spec);
                        assert(s_prime.resources()[key].spec == outer.spec);
                        assert(req.spec == old.spec);
                        assert(old.with_spec(req.spec) == old);
                        assert(false);
                    }
                },
                APIRequest::DeleteRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(false);
                    }
                },
                APIRequest::GetThenDeleteRequest(req) => {
                    if req.key() == key && s_prime.api_server != s.api_server {
                        assert(false);
                    }
                },
                APIRequest::PatchStatusRequest(req) => {
                    if req.key() == key {
                        // Nobody writes the outer copy's status now: not this reconcile (the
                        // hypothesis), not another key's (the guarantee), not another
                        // controller (the rely), and the rest send no status writes.
                        match msg.src {
                            HostId::Controller(id, okey) => {
                                if id == controller_id {
                                    assert(widget_sync_guarantee(k, controller_id)(s));
                                    assert(sync_status_patch_req(k, req, okey));
                                    assert(req.namespace == okey.namespace && req.name == okey.name && req.kind == k.outer_kind);
                                    assert(okey.kind == k.outer_kind);
                                    assert(okey == key);
                                    assert(false);
                                } else if id == janitor_id {
                                    assert(false);
                                } else {
                                    assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                    assert(widget_sync_rely(k, id)(s));
                                    assert(req.kind != k.outer_kind);
                                    assert(false);
                                }
                            },
                            _ => { assert(false); },
                        }
                    }
                },
                APIRequest::UpdateStatusRequest(req) => {
                    if req.key() == key {
                        match msg.src {
                            HostId::Controller(id, okey) => {
                                if id == controller_id {
                                    assert(widget_sync_guarantee(k, controller_id)(s));
                                    assert(false);
                                } else if id == janitor_id {
                                    assert(false);
                                } else {
                                    assert(widget_sync_rely(k, id)(s));
                                    assert(req.obj.kind != k.outer_kind);
                                    assert(false);
                                }
                            },
                            _ => { assert(false); },
                        }
                    }
                },
                APIRequest::GetThenUpdateStatusRequest(req) => {
                    if req.key() == key {
                        match msg.src {
                            HostId::Controller(id, okey) => {
                                if id == controller_id {
                                    assert(widget_sync_guarantee(k, controller_id)(s));
                                    assert(false);
                                } else if id == janitor_id {
                                    assert(false);
                                } else {
                                    assert(widget_sync_rely(k, id)(s));
                                    assert(req.obj.kind != k.outer_kind);
                                    assert(false);
                                }
                            },
                            _ => { assert(false); },
                        }
                    }
                },
                APIRequest::CreateRequest(_) => {
                    assert(s_prime.resources()[key] == old);
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                },
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}


// While the stored copy is not owned, the sync reconciler has no status write of
// it in flight: a status is written by a reconcile that owns the copy, which then
// is owned (step 1), or that refuses it, which the premise rules out.
pub proof fn lemma_no_status_write_in_flight_unless_owned(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        sync_step_ctx(k, b, cluster, controller_id, janitor_id, outer)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)(s),
        snapshots_satisfy(controller_id, outer.object_ref(), snapshot_live_and_owned_if_marked(outer))(s),
        !outer_owned(outer)(s),
    ensures no_status_write_in_flight_for(controller_id, outer.object_ref())(s),
{
    let key = outer.object_ref();
    assert forall |m: Message| #![trigger s.in_flight().contains(m)] {
        &&& s.in_flight().contains(m)
        &&& m.src == HostId::Controller(controller_id, key)
        &&& m.dst is APIServer
        &&& m.content is APIRequest
    } implies !(m.content->APIRequest_0 is PatchStatusRequest) by {
        assert(s.ongoing_reconciles(controller_id).contains_key(key));
        assert(Cluster::pending_req_msg_is(controller_id, s, key, m));
        let reconcile = s.ongoing_reconciles(controller_id)[key];
        assert(sync_pending_request_is(k, controller_id, key, reconcile));
        lemma_current_reconcile_of_outer(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
        let cr = reconcile.triggering_cr;
        let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
        let step = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
        if m.content->APIRequest_0 is PatchStatusRequest {
            // Only a status write is a status write.
            assert(step is AfterPatchOuterStatus || step is AfterReportError) by {
                assert(!(step is Init));
                assert(!(step is Done) && !(step is Error));
            }
            // The copy is one the reconciler addresses, so its reconcile owns it.
            assert(cluster_of(k.selector, cr_outer) == cluster_of(k.selector, outer));
            assert(binding_of(k, cr_outer) == binding_of(k, outer));
            assert(serves(k, cr_outer));
            assert(has_sync_finalizer(cr_outer.metadata));
            assert(snapshot_live_and_owned_if_marked(outer)(cr, s));
            assert(outer_owned(outer)(s));
            assert(false);
        }
    }
}

// ---------------------------------------------------------------------------
// The states of the walk that adds the finalizer.
// ---------------------------------------------------------------------------

// A snapshot carries the stored copy's version, or the copy is owned.
pub open spec fn snapshot_current_or_owned(outer: SyncedObjectView) -> spec_fn(DynamicObjectView, ClusterState) -> bool {
    |o: DynamicObjectView, s: ClusterState| {
        ||| o.metadata.resource_version == s.resources()[outer.object_ref()].metadata.resource_version
        ||| outer_owned(outer)(s)
    }
}

// The Update that adds the finalizer, built from the snapshot `cr` of the outer copy.
pub open spec fn add_req_msg_for(k: SyncKind, controller_id: int, outer: SyncedObjectView, msg: Message, cr: DynamicObjectView) -> bool {
    &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& msg.content->APIRequest_0 == APIRequest::UpdateRequest(sync_reconciler::outer_finalizer_update(unmarshal(k.outer_kind, cr)->Ok_0, true))
}

// The Update is in flight, and the stored copy is owned by now or still carries
// the snapshot's version, in which case the Update lands.
pub open spec fn st_add_req_msg_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        &&& at_sync_step(controller_id, key, WidgetSyncStepView::AfterAddFinalizer)(s)
        &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg)
        &&& add_req_msg_for(k, controller_id, outer, msg, cr)
        &&& s.in_flight().contains(msg)
        &&& outer_owned(outer)(s) || s.resources()[key].metadata.resource_version == cr.metadata.resource_version
    }
}

pub open spec fn st_add_req_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |msg: Message| #[trigger] st_add_req_msg_in_flight(k, controller_id, outer, msg)(s)
}

// The facts the walk's step lemmas share, beyond sync_step_next.
pub open spec fn add_walk_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& sync_step_next(k, b, cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())(s)
        &&& Cluster::synced_desired_state_is(outer)(s_prime)
        &&& snapshots_satisfy(controller_id, outer.object_ref(), snapshot_live_and_owned_if_marked(outer))(s)
        &&& snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_owned(outer))(s)
        &&& snapshots_are_current(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)(s)
    }
}

pub proof fn lemma_always_add_walk_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_live_and_owned_if_marked(outer))))),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_owned(outer))))),
    ensures spec.entails(always(lift_action(add_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    let key = outer.object_ref();
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    always_to_always_later(spec, lift_state(Cluster::synced_desired_state_is(outer)));
    combine_spec_entails_always_n!(
        spec, lift_action(add_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_action(sync_step_next(k, b, cluster, controller_id, janitor_id, outer)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)),
        later(lift_state(Cluster::synced_desired_state_is(outer))),
        lift_state(snapshots_satisfy(controller_id, key, snapshot_live_and_owned_if_marked(outer))),
        lift_state(snapshots_satisfy(controller_id, key, snapshot_current_or_owned(outer))),
        lift_state(snapshots_are_current(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind))
    );
}

// ---------------------------------------------------------------------------
// The walk.
// ---------------------------------------------------------------------------

// Init ~> owned, or the Update that adds the finalizer is in flight.
pub proof fn lemma_init_leads_to_owned_or_add_req(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_live_and_owned_if_marked(outer))))),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_owned(outer))))),
    ensures
        spec.entails(lift_state(st_sync_init(controller_id, outer.object_ref()))
            .leads_to(lift_state(outer_owned(outer)).or(lift_state(st_add_req_in_flight(k, controller_id, outer))))),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
    let key = outer.object_ref();
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_add_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let pre = st_sync_init(controller_id, key);
    let post = |s: ClusterState| outer_owned(outer)(s) || st_add_req_in_flight(k, controller_id, outer)(s);
    let input = (None::<Message>, Some(key));
    let next = add_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
        && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        lemma_current_reconcile_of_outer(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
        assert(snapshot_live_and_owned_if_marked(outer)(cr, s));
        assert(snapshot_current_or_owned(outer)(cr, s));
        assert(cr_outer.metadata.deletion_timestamp is None);
        assert(s_prime.api_server == s.api_server);
        if has_sync_finalizer(cr_outer.metadata) {
            assert(outer_owned(outer)(s));
        } else {
            let req = APIRequest::UpdateRequest(sync_reconciler::outer_finalizer_update(cr_outer, true));
            let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == cr);
            assert(s_prime.in_flight().contains(msg));
            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == sync_reconciler::at_step(WidgetSyncStepView::AfterAddFinalizer).marshal());
            assert(add_req_msg_for(k, controller_id, outer, msg, cr));
            assert(st_add_req_msg_in_flight(k, controller_id, outer, msg)(s_prime));
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(i) => {
                if i.0 == controller_id && i.2 == Some(key) {
                    assert(i.1 is None);
                    assert(cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime));
                } else {
                    assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                }
            },
            _ => {
                assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            },
        }
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::ContinueReconcile, (controller_id, input.0, input.1))(s) by {
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, next, ControllerStep::ContinueReconcile, pre, post);
    temp_pred_equality(lift_state(post), lift_state(outer_owned(outer)).or(lift_state(st_add_req_in_flight(k, controller_id, outer))));
}

// The API server handles the Update: it lands, unless a write carrying the
// finalizer landed first.
proof fn lemma_add_req_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, msg: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        add_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        st_add_req_msg_in_flight(k, controller_id, outer, msg)(s),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures outer_owned(outer)(s_prime),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
    let key = outer.object_ref();
    marshal_status_preserves_integrity();
    marshal_preserves_metadata();
    marshal_preserves_kind();
    unmarshal_is_representable();
    if outer_owned(outer)(s) {
        lemma_outer_owned_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    } else {
        lemma_current_reconcile_of_outer(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
        let cr = s.ongoing_reconciles(controller_id)[key].triggering_cr;
        let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
        // The snapshot carries the stored version, so it is the stored object.
        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
        assert(cluster.etcd_object_is_well_formed(key)(s));
        let old = s.resources()[key];
        assert(snapshot_is_current_at(key, cr, s));
        assert(old == cr);
        assert(cr_outer.metadata == old.metadata);
        assert(cr_outer.spec == old.spec);
        let req = msg.content->APIRequest_0->UpdateRequest_0;
        let updated_meta = with_sync_finalizer(cr_outer.metadata);
        assert(req == sync_reconciler::outer_finalizer_update(cr_outer, true));
        assert(req.obj == marshal(cr_outer.with_metadata(updated_meta)));
        assert(req.obj.kind == k.outer_kind);
        assert(req.obj.metadata == updated_meta);
        assert(req.obj.spec == old.spec);
        assert(req.obj.status == marshal_status(cr_outer.status));
        assert(has_sync_finalizer(updated_meta)) by {
            let fs = finalizers_or_empty(cr_outer.metadata).push(sync_finalizer());
            assert(fs[fs.len() - 1] == sync_finalizer());
        }
        // Admission: the object names itself, unmarshals, exists, and carries the
        // stored version and uid.
        assert(req.key() == key);
        assert(key.kind is CustomResourceKind);
        assert(cluster.installed_types[key.kind->CustomResourceKind_0] == Cluster::synced_installed_type(spec_ok, k.selector));
        assert(unmarshallable_object(req.obj, cluster.installed_types)) by {
            assert(unmarshal_status(marshal_status(cr_outer.status)) is Ok);
        }
        assert(update_request_admission_check(cluster.installed_types, req, s.api_server) is None);
        let updated = updated_object(req, old);
        assert(updated.metadata.finalizers == updated_meta.finalizers);
        assert(updated != old);
        let with_rv = updated.with_resource_version(s.api_server.resource_version_counter);
        // Validity: the metadata is the stored one but for the finalizers, the
        // spec is the stored one, and the copy is not terminating.
        assert(old.metadata.deletion_timestamp is None);
        assert(metadata_validity_check(with_rv) is None);
        assert(metadata_transition_validity_check(with_rv, old) is None);
        assert(valid_object(old, cluster.installed_types));
        assert(valid_object(with_rv, cluster.installed_types));
        assert(valid_transition(with_rv, old, cluster.installed_types)) by {
            assert(with_rv.spec == old.spec);
        }
        assert(updated_object_validity_check(with_rv, old, cluster.installed_types) is None);
        assert(s_prime.resources()[key] == with_rv);
        assert(has_sync_finalizer(s_prime.resources()[key].metadata));
    }
}

// While another request is handled, the Update stays in flight and the copy
// stays owned or at the snapshot's version.
proof fn lemma_add_req_stays_in_flight(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, msg: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        add_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        st_add_req_msg_in_flight(k, controller_id, outer, msg)(s),
        !cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures st_add_req_msg_in_flight(k, controller_id, outer, msg)(s_prime),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
    let key = outer.object_ref();
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(i) => {
            assert(i->0 != msg);
            assert(s_prime.in_flight().contains(msg));
            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            if outer_owned(outer)(s) {
                lemma_outer_owned_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            } else {
                lemma_no_status_write_in_flight_unless_owned(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
                lemma_outer_copy_unchanged_or_owned_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            }
        },
        Step::ControllerStep(i) => {
            if i.0 == controller_id && i.2 == Some(key) {
                assert(i.1 is Some);
                assert(s.in_flight().contains(i.1->0) && resp_msg_matches_req_msg(i.1->0, msg));
                assert(false);
            } else {
                assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                assert(s_prime.in_flight().contains(msg));
                assert(s_prime.api_server == s.api_server);
            }
        },
        Step::RestartControllerStep(id) => {
            assert(id != controller_id);
            assert(s_prime.api_server == s.api_server);
        },
        _ => {
            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            assert(s_prime.in_flight().contains(msg));
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// One step from the Update in flight: it stays in flight, or the copy is owned.
proof fn lemma_add_req_msg_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, msg: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        add_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime),
        st_add_req_msg_in_flight(k, controller_id, outer, msg)(s),
    ensures
        st_add_req_msg_in_flight(k, controller_id, outer, msg)(s_prime) || outer_owned(outer)(s_prime),
        cluster.api_server_next().forward(Some(msg))(s, s_prime) ==> outer_owned(outer)(s_prime),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
    if cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))) {
        lemma_add_req_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
    } else {
        lemma_add_req_stays_in_flight(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
    }
}

// One Update in flight ~> owned.
proof fn lemma_add_req_msg_leads_to_owned(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, msg: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_live_and_owned_if_marked(outer))))),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_owned(outer))))),
    ensures
        spec.entails(lift_state(st_add_req_msg_in_flight(k, controller_id, outer, msg)).leads_to(lift_state(outer_owned(outer)))),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
    hide(sync_reconciler::reconcile_core);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_add_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    let next = add_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let pre = st_add_req_msg_in_flight(k, controller_id, outer, msg);
    let post = outer_owned(outer);
    let input = Some(msg);
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
        && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
        lemma_add_req_msg_next(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        lemma_add_req_msg_next(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, msg);
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {
        assert(add_req_msg_for(k, controller_id, outer, msg, s.ongoing_reconciles(controller_id)[outer.object_ref()].triggering_cr));
    }
    cluster.lemma_pre_leads_to_post_by_api_server(spec, input, next, APIServerStep::HandleRequest, pre, post);
}

// The Update in flight ~> owned.
pub proof fn lemma_add_req_leads_to_owned(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_live_and_owned_if_marked(outer))))),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_owned(outer))))),
    ensures
        spec.entails(lift_state(st_add_req_in_flight(k, controller_id, outer)).leads_to(lift_state(outer_owned(outer)))),
{
    let post = lift_state(outer_owned(outer));
    let pre_of = |msg: Message| lift_state(st_add_req_msg_in_flight(k, controller_id, outer, msg));
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(post)) by {
        lemma_add_req_msg_leads_to_owned(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, msg);
    }
    leads_to_exists_intro(spec, pre_of, post);
    assert_by(tla_exists(pre_of) == lift_state(st_add_req_in_flight(k, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_add_req_in_flight(k, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = choose |msg: Message| #[trigger] st_add_req_msg_in_flight(k, controller_id, outer, msg)(s);
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_add_req_in_flight(k, controller_id, outer)));
    });
}

// ---------------------------------------------------------------------------
// Assembly: the stored copy is eventually and forever owned.
// ---------------------------------------------------------------------------

pub proof fn lemma_true_leads_to_always_outer_owned(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_live_and_owned_if_marked(outer))))),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_owned(outer))))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(outer_owned(outer))))),
{
    let key = outer.object_ref();
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_add_walk_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    let idle = lift_state(Cluster::reconcile_idle(controller_id, key));
    let scheduled = lift_state(|s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
    });
    let init = lift_state(st_sync_init(controller_id, key));
    let owned = lift_state(outer_owned(outer));
    let add_req = lift_state(st_add_req_in_flight(k, controller_id, outer));
    lemma_sync_idle_leads_to_scheduled(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_scheduled_leads_to_init(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_init_leads_to_owned_or_add_req(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_add_req_leads_to_owned(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    entails_implies_leads_to(spec, owned, owned);
    or_leads_to(spec, owned, add_req, owned);
    leads_to_trans_n!(spec, true_pred(), idle, scheduled, init, owned.or(add_req), owned);
    // Stability.
    let next = add_walk_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert forall |s, s_prime: ClusterState| outer_owned(outer)(s) && #[trigger] next(s, s_prime) implies outer_owned(outer)(s_prime) by {
        lemma_outer_owned_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
    }
    leads_to_stable(spec, lift_action(next), true_pred(), owned);
}

// ---------------------------------------------------------------------------
// The layer: owned, and every snapshot live and owned.
// ---------------------------------------------------------------------------

// The action under which the snapshot properties of the layer are preserved.
spec fn layer_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& sync_step_next(k, b, cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& Cluster::synced_desired_state_is(outer)(s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)(s)
    }
}

proof fn lemma_always_layer_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(always(lift_action(layer_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)))),
{
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    always_to_always_later(spec, lift_state(Cluster::synced_desired_state_is(outer)));
    combine_spec_entails_always_n!(
        spec, lift_action(layer_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        lift_action(sync_step_next(k, b, cluster, controller_id, janitor_id, outer)),
        later(lift_state(Cluster::synced_desired_state_is(outer))),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id))
    );
}

// Step 1: true ~> [](every snapshot is live, and owned if marked), under phase II.
proof fn lemma_true_leads_to_always_snapshots_live(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        valid(stable(spec)),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_live_and_owned_if_marked(outer)))))),
{
    let key = outer.object_ref();
    let pred = snapshot_live_and_owned_if_marked(outer);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_layer_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    let next = layer_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert forall |s, s_prime: ClusterState| #[trigger] next(s, s_prime) implies preserves(pred)(s, s_prime) by {
        assert forall |o: DynamicObjectView| #[trigger] pred(o, s) implies pred(o, s_prime) by {
            if has_sync_finalizer(o.metadata) {
                lemma_outer_owned_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            }
        }
    }
    always_weaken(spec, lift_action(next), lift_action(preserves(pred)));
    assert forall |s: ClusterState| #[trigger] Cluster::synced_desired_state_is(outer)(s) implies stored_satisfies(key, pred)(s) by {}
    always_weaken(spec, lift_state(Cluster::synced_desired_state_is(outer)), lift_state(stored_satisfies(key, pred)));
    lemma_snapshots_eventually_satisfy(spec, cluster, controller_id, key, pred);
}

// Step 2: true ~> [](every snapshot is current, or the copy is owned), under
// phase II and step 1.
proof fn lemma_true_leads_to_always_snapshots_current(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        valid(stable(spec)),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_live_and_owned_if_marked(outer))))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_current_or_owned(outer)))))),
{
    let key = outer.object_ref();
    let pred = snapshot_current_or_owned(outer);
    let live = snapshots_satisfy(controller_id, key, snapshot_live_and_owned_if_marked(outer));
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_layer_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    let next = |s: ClusterState, s_prime: ClusterState| {
        &&& layer_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& live(s)
    };
    combine_spec_entails_always_n!(spec, lift_action(next), lift_action(layer_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer)), lift_state(live));
    assert forall |s, s_prime: ClusterState| #[trigger] next(s, s_prime) implies preserves(pred)(s, s_prime) by {
        assert forall |o: DynamicObjectView| #[trigger] pred(o, s) implies pred(o, s_prime) by {
            if outer_owned(outer)(s) {
                lemma_outer_owned_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            } else {
                lemma_no_status_write_in_flight_unless_owned(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
                lemma_outer_copy_unchanged_or_owned_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer);
            }
        }
    }
    always_weaken(spec, lift_action(next), lift_action(preserves(pred)));
    assert forall |s: ClusterState| #[trigger] Cluster::synced_desired_state_is(outer)(s) implies stored_satisfies(key, pred)(s) by {}
    always_weaken(spec, lift_state(Cluster::synced_desired_state_is(outer)), lift_state(stored_satisfies(key, pred)));
    lemma_snapshots_eventually_satisfy(spec, cluster, controller_id, key, pred);
}

// Step 4: true ~> [](every snapshot carries the finalizer), under phase II and
// an owned copy.
proof fn lemma_true_leads_to_always_snapshots_owned(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        valid(stable(spec)),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(always(lift_state(outer_owned(outer)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(snapshots_satisfy(controller_id, outer.object_ref(), snapshot_owned()))))),
{
    let key = outer.object_ref();
    let pred = snapshot_owned();
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    assert forall |s, s_prime: ClusterState| #[trigger] cluster.next()(s, s_prime) implies preserves(pred)(s, s_prime) by {}
    always_weaken(spec, lift_action(cluster.next()), lift_action(preserves(pred)));
    assert forall |s: ClusterState| #[trigger] outer_owned(outer)(s) implies stored_satisfies(key, pred)(s) by {}
    always_weaken(spec, lift_state(outer_owned(outer)), lift_state(stored_satisfies(key, pred)));
    lemma_snapshots_eventually_satisfy(spec, cluster, controller_id, key, pred);
}

// The two snapshot lemmas, chained: true ~> [](both snapshots satisfy `pred`).
pub proof fn lemma_snapshots_eventually_satisfy(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, key: ObjectRef, pred: spec_fn(DynamicObjectView, ClusterState) -> bool)
    requires
        valid(stable(spec)),
        cluster.controller_models.contains_key(controller_id),
        cluster.reconcile_model(controller_id).kind == key.kind,
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(stored_satisfies(key, pred)))),
        spec.entails(always(lift_action(preserves(pred)))),
        spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(snapshots_satisfy(controller_id, key, pred))))),
{
    let sched = lift_state(scheduled_satisfies(controller_id, key, pred));
    let ongoing = lift_state(ongoing_satisfies(controller_id, key, pred));
    lemma_true_leads_to_always_scheduled_satisfies(spec, cluster, controller_id, key, pred);
    // Under spec /\ []sched, the ongoing snapshot follows; then fold the layer back.
    let spec_s = spec.and(always(sched));
    assert(spec_s.entails(spec_s));
    entails_and_split(spec_s, spec, always(sched));
    entails_trans(spec_s, spec, always(lift_action(cluster.next())));
    entails_trans(spec_s, spec, tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1))));
    entails_trans(spec_s, spec, always(lift_state(Cluster::there_is_the_controller_state(controller_id))));
    entails_trans(spec_s, spec, always(lift_action(preserves(pred))));
    entails_trans(spec_s, spec, true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key))));
    lemma_true_leads_to_always_ongoing_satisfies(spec_s, cluster, controller_id, key, pred);
    unpack_conditions_from_spec(spec, always(sched), true_pred(), always(ongoing));
    temp_pred_equality(true_pred().and(always(sched)), always(sched));
    leads_to_trans(spec, true_pred(), always(sched), always(ongoing));
    leads_to_always_and(spec, true_pred(), sched, ongoing);
    temp_pred_equality(lift_state(snapshots_satisfy(controller_id, key, pred)), sched.and(ongoing));
}

pub proof fn lemma_true_leads_to_always_sync_finalizer_held(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool,
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(sync_finalizer_held(controller_id, outer))))),
{
    let key = outer.object_ref();
    let spec_ii = sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    let l = lift_state(snapshots_satisfy(controller_id, key, snapshot_live_and_owned_if_marked(outer)));
    let c = lift_state(snapshots_satisfy(controller_id, key, snapshot_current_or_owned(outer)));
    let g = lift_state(outer_owned(outer));
    let f = lift_state(snapshots_satisfy(controller_id, key, snapshot_owned()));
    sync_spec_with_phase_ii_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer);
    assert(spec_ii.entails(spec_ii));

    // Step 1, under spec_ii: true ~> []l.
    lemma_true_leads_to_always_snapshots_live(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id, outer);

    // Step 2, under spec_l = spec_ii /\ []l: true ~> []c.
    let spec_l = spec_ii.and(always(l));
    always_p_is_stable(l);
    stable_and_n!(spec_ii, always(l));
    assert(spec_l.entails(spec_l));
    entails_and_split(spec_l, spec_ii, always(l));
    lemma_true_leads_to_always_snapshots_current(k, b, spec_ok, spec_l, cluster, controller_id, janitor_id, outer);

    // Step 3, under spec_c = spec_l /\ []c: true ~> []g.
    let spec_c = spec_l.and(always(c));
    always_p_is_stable(c);
    stable_and_n!(spec_l, always(c));
    assert(spec_c.entails(spec_c));
    entails_and_split(spec_c, spec_l, always(c));
    entails_and_split(spec_c, spec_ii, always(l));
    lemma_true_leads_to_always_outer_owned(k, b, spec_ok, spec_c, cluster, controller_id, janitor_id, outer);

    // Step 4, under spec_g = spec_c /\ []g: true ~> []f.
    let spec_g = spec_c.and(always(g));
    always_p_is_stable(g);
    stable_and_n!(spec_c, always(g));
    assert(spec_g.entails(spec_g));
    entails_and_split(spec_g, spec_c, always(g));
    entails_and_split(spec_g, spec_l, always(c));
    entails_and_split(spec_g, spec_ii, always(l));
    lemma_true_leads_to_always_snapshots_owned(k, b, spec_ok, spec_g, cluster, controller_id, janitor_id, outer);

    // Fold back: spec_c |= true ~> [](g /\ f); spec_l |= true ~> [](g /\ f);
    // spec_ii |= true ~> [](l /\ g /\ f).
    unpack_conditions_from_spec(spec_c, always(g), true_pred(), always(f));
    temp_pred_equality(true_pred().and(always(g)), always(g));
    leads_to_trans(spec_c, true_pred(), always(g), always(f));
    leads_to_always_and(spec_c, true_pred(), g, f);
    unpack_conditions_from_spec(spec_l, always(c), true_pred(), always(g.and(f)));
    temp_pred_equality(true_pred().and(always(c)), always(c));
    leads_to_trans(spec_l, true_pred(), always(c), always(g.and(f)));
    unpack_conditions_from_spec(spec_ii, always(l), true_pred(), always(g.and(f)));
    temp_pred_equality(true_pred().and(always(l)), always(l));
    leads_to_trans(spec_ii, true_pred(), always(l), always(g.and(f)));
    leads_to_always_and(spec_ii, true_pred(), l, g.and(f));
    temp_pred_equality(lift_state(sync_finalizer_held(controller_id, outer)), l.and(g.and(f)));
    entails_trans(spec, spec_ii, true_pred().leads_to(always(lift_state(sync_finalizer_held(controller_id, outer)))));
}

}
