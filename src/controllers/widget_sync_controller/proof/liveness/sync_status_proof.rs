// R2: once the outer copy is stable and the inner side has settled on a status for
// the mirror, the outer copy eventually and forever carries the status the sync
// reconciler derives from it: the mirrored fields, the merged conditions, stamped
// with its own generation and a true Synced condition.
//
// The proof reuses the layers of R1 (the premise of R2 implies the premise of R1
// and a settled mirror) and adds, as a third phase, four eventual facts: the
// snapshots the sync reconciler works from carry the outer generation; every Get
// response it holds shows the settled mirror; every status write it has in flight
// writes the desired status; the snapshots' status is the stored status unless the
// stored status is already the desired one. Under them one reconcile of the outer
// copy writes the desired status (or finds it there), after which nothing but the
// desired status is ever written.
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
// The desired status and the premise.
// ---------------------------------------------------------------------------

// The status R2 promises: the one the sync reconciler derives from the settled
// inner status for a synced mirror at the outer copy's generation.
pub open spec fn desired_outer_status(status: SyncedStatusView, outer: SyncedObjectView, settled: SyncedStatusView) -> bool {
    status == outer_status_for(outer.metadata.generation, settled, SyncOutcomeView::Synced)
}

pub open spec fn stored_outer_status_desired(k: SyncKind, outer: SyncedObjectView, settled: SyncedStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[outer.object_ref()];
        let stored = unmarshal(k.outer_kind, obj)->Ok_0;
        &&& unmarshal(k.outer_kind, obj) is Ok
        &&& stored.status is Some
        &&& desired_outer_status(stored.status->0, outer, settled)
    }
}

pub open spec fn r2_premise(k: SyncKind, b: Binding, outer: SyncedObjectView, settled: SyncedStatusView) -> TempPred<ClusterState> {
    always(lift_state(outer_stable(k, b, outer)).and(lift_state(inner_settled(k, outer, settled))))
}

// The status the sync reconciler writes for a settled mirror is the desired one:
// outer_status_for reads only the mirrored fields and the conditions of its
// source, which the premise fixes.
pub proof fn lemma_written_status_is_desired(k: SyncKind, b: Binding, outer: SyncedObjectView, settled: SyncedStatusView, inner_status: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        inner_status.mirrored() == settled.mirrored(),
        inner_status.conditions == settled.conditions,
    ensures desired_outer_status(outer_status_for(outer.metadata.generation, inner_status, SyncOutcomeView::Synced), outer, settled),
{
    let g = outer.metadata.generation;
    assert(inner_status.rest == settled.rest);
    assert(inner_status.ready_condition() == settled.ready_condition());
    assert(inner_status.stalled_condition() == settled.stalled_condition());
    assert(ready_condition_for(g, inner_status, SyncOutcomeView::Synced) == ready_condition_for(g, settled, SyncOutcomeView::Synced));
    assert(stalled_condition_for(g, inner_status, SyncOutcomeView::Synced) == stalled_condition_for(g, settled, SyncOutcomeView::Synced));
    assert(outer_status_for(g, inner_status, SyncOutcomeView::Synced) == outer_status_for(g, settled, SyncOutcomeView::Synced));
}

// ---------------------------------------------------------------------------
// The layers of the spec.
// ---------------------------------------------------------------------------

pub open spec fn r2_spec_with_premise(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> TempPred<ClusterState> {
    sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id).and(r2_premise(k, b, outer, settled))
}

pub proof fn r2_spec_with_premise_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
    ensures valid(stable(r2_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled))),
{
    sync_stable_spec_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id);
    always_p_is_stable(lift_state(outer_stable(k, b, outer)).and(lift_state(inner_settled(k, outer, settled))));
    stable_and_n!(sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), r2_premise(k, b, outer, settled));
}

pub open spec fn r2_spec_with_phase_i(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> TempPred<ClusterState> {
    r2_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled).and(always(lift_state(phase_i(controller_id))))
}

pub proof fn r2_spec_with_phase_i_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
    ensures valid(stable(r2_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled))),
{
    r2_spec_with_premise_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    always_p_is_stable(lift_state(phase_i(controller_id)));
    stable_and_n!(r2_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled), always(lift_state(phase_i(controller_id))));
}

pub open spec fn r2_spec_with_phase_ii(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> TempPred<ClusterState> {
    r2_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled).and(always(lift_state(sync_phase_ii(controller_id, outer))))
}

pub proof fn r2_spec_with_phase_ii_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
    ensures valid(stable(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled))),
{
    r2_spec_with_phase_i_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    always_p_is_stable(lift_state(sync_phase_ii(controller_id, outer)));
    stable_and_n!(r2_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled), always(lift_state(sync_phase_ii(controller_id, outer))));
}

// The bridge to R1's layers: the premise of R2 gives the premise of R1 and a
// settled mirror.
pub proof fn lemma_r2_layers_imply_r1_layers(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
    ensures
        spec.entails(sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id)),
        spec.entails(always(lift_state(outer_stable(k, b, outer)))),
        spec.entails(always(lift_state(inner_settled(k, outer, settled)))),
        spec.entails(always(lift_state(mirror_settled(k, b, outer)))),
        spec.entails(always(lift_state(phase_i(controller_id)))),
        spec.entails(always(lift_state(sync_phase_ii(controller_id, outer)))),
        spec.entails(sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
        spec.entails(sync_spec_with_settled(k, b, spec_ok, cluster, controller_id, janitor_id, outer)),
{
    entails_and_split(spec, r2_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled), always(lift_state(sync_phase_ii(controller_id, outer))));
    entails_and_split(spec, r2_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled), always(lift_state(phase_i(controller_id))));
    entails_and_split(spec, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), r2_premise(k, b, outer, settled));
    always_weaken(spec, lift_state(outer_stable(k, b, outer)).and(lift_state(inner_settled(k, outer, settled))), lift_state(outer_stable(k, b, outer)));
    always_weaken(spec, lift_state(outer_stable(k, b, outer)).and(lift_state(inner_settled(k, outer, settled))), lift_state(inner_settled(k, outer, settled)));
    always_weaken(spec, lift_state(inner_settled(k, outer, settled)), lift_state(mirror_settled(k, b, outer)));
    always_weaken(spec, lift_state(outer_stable(k, b, outer)), lift_state(outer_spec_stable(k, b, outer)));
    entails_and(spec, sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id), always(lift_state(outer_spec_stable(k, b, outer))));
    entails_and(spec, sync_spec_with_desired(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(phase_i(controller_id))));
    entails_and(spec, sync_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(sync_phase_ii(controller_id, outer))));
    entails_and(spec, sync_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer), always(lift_state(mirror_settled(k, b, outer))));
}

// ---------------------------------------------------------------------------
// Facts about the outer copy under the premise, and its status after a step.
// ---------------------------------------------------------------------------

pub proof fn lemma_outer_object_facts(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, s: ClusterState, outer: SyncedObjectView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)(s),
        outer_stable(k, b, outer)(s),
    ensures
        ({
            let key = outer.object_ref();
            let obj = s.resources()[key];
            &&& s.resources().contains_key(key)
            &&& obj.object_ref() == key
            &&& obj.kind == k.outer_kind
            &&& obj.metadata.uid == outer.metadata.uid
            &&& obj.metadata.uid is Some
            &&& obj.metadata.generation == outer.metadata.generation
            &&& obj.metadata.generation is Some
            &&& obj.metadata.deletion_timestamp is None
            &&& obj.metadata.well_formed_for_namespaced()
            &&& unmarshal(k.outer_kind, obj) is Ok
            &&& unmarshal(k.outer_kind, obj)->Ok_0.spec == outer.spec
            &&& unmarshal(k.outer_kind, obj)->Ok_0.metadata == obj.metadata
            &&& unmarshallable_object(obj, cluster.installed_types)
            &&& valid_object(obj, cluster.installed_types)
        }),
{
    let key = outer.object_ref();
    
    assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    assert(key.kind == k.outer_kind);
    assert(cluster.etcd_object_is_well_formed(key)(s));
}

// The statuses the sync reconciler has in flight for the outer copy write the desired status.
pub open spec fn desired_status_patch(k: SyncKind, req: PatchStatusRequest, outer: SyncedObjectView, settled: SyncedStatusView) -> bool {
    let status = unmarshal_status(req.status);
    &&& req.kind == k.outer_kind
    &&& req.namespace == outer.object_ref().namespace
    &&& req.name == outer.object_ref().name
    &&& req.tests.uid == outer.metadata.uid
    &&& req.tests.generation == outer.metadata.generation
    &&& status is Ok
    &&& status->Ok_0 is Some
    &&& desired_outer_status(status->Ok_0->0, outer, settled)
}

// The reconcile of the outer copy is at no step from which a failure would be
// reported: once every Get is answered with the settled mirror, the reconciler
// neither creates nor patches the mirror, so it never writes an error status.
pub open spec fn sync_reports_no_error(controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        let step = WidgetSyncReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state)->Ok_0.reconcile_step;
        s.ongoing_reconciles(controller_id).contains_key(key) ==> {
            &&& !(step is AfterCreateInner)
            &&& !(step is AfterPatchInner)
            &&& !(step is AfterReportError)
        }
    }
}

pub open spec fn status_writes_are_desired(k: SyncKind, controller_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& sync_reports_no_error(controller_id, outer)(s)
        &&& forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
            &&& msg.content.is_patch_status_request()
        } ==> desired_status_patch(k, msg.content.get_patch_status_request(), outer, settled)
    }
}

// The outer copy's status after one step: unchanged, or the desired one.
pub proof fn lemma_outer_status_after_step(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, settled: SyncedStatusView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        sync_step_next(k, b, cluster, controller_id, janitor_id, outer)(s, s_prime),
        cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)(s),
        cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)(s_prime),
        outer_stable(k, b, outer)(s),
        outer_stable(k, b, outer)(s_prime),
        Cluster::every_in_flight_msg_from_controller_has_key_kind(k.outer_kind, controller_id)(s),
        status_writes_are_desired(k, controller_id, outer, settled)(s),
    ensures
        s_prime.resources()[outer.object_ref()].status == s.resources()[outer.object_ref()].status
            || stored_outer_status_desired(k, outer, settled)(s_prime),
{
    let key = outer.object_ref();
    lemma_outer_object_facts(k, b, spec_ok, cluster, s, outer);
    lemma_outer_object_facts(k, b, spec_ok, cluster, s_prime, outer);
    marshal_status_preserves_integrity();
    let old_obj = s.resources()[key];
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            assert(s.in_flight().contains(msg));
            assert(msg.content is APIRequest);
            lemma_weakly_well_formed_implies_kinds_match(s);
            match msg.content->APIRequest_0 {
                APIRequest::PatchStatusRequest(req) => {
                    if req.key() == key {
                        match msg.src {
                            HostId::Controller(id, okey) => {
                                assert(cluster.controller_models.contains_key(id));
                                if id == controller_id {
                                    assert(sync_request_is_guaranteed(k, msg, s));
                                    assert(sync_status_patch_req(k, req, okey));
                                    assert(msg.dst is APIServer);
                                    assert(okey.kind == k.outer_kind);
                                    assert(okey == key);
                                    assert(desired_status_patch(k, req, outer, settled));
                                    if s_prime.api_server != s.api_server {
                                        assert(s_prime.resources()[key].status == req.status);
                                        assert(stored_outer_status_desired(k, outer, settled)(s_prime));
                                    }
                                } else if id == janitor_id {
                                    assert(janitor_request_is_guaranteed(k, b, msg));
                                    assert(false);
                                } else {
                                    assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                    assert(widget_sync_rely(k, id)(s));
                                    assert(req.kind != k.outer_kind);
                                    assert(false);
                                }
                            },
                            HostId::BuiltinController => { assert(false); },
                            HostId::PodMonkey => { assert(false); },
                            _ => { assert(false); },
                        }
                    } else {
                        assert(s_prime.resources()[key] == old_obj);
                    }
                },
                APIRequest::UpdateStatusRequest(req) => {
                    if req.key() == key {
                        match msg.src {
                            HostId::Controller(id, okey) => {
                                assert(cluster.controller_models.contains_key(id));
                                if id == controller_id {
                                    assert(sync_request_is_guaranteed(k, msg, s));
                                    assert(false);
                                } else if id == janitor_id {
                                    assert(janitor_request_is_guaranteed(k, b, msg));
                                    assert(false);
                                } else {
                                    assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                    assert(widget_sync_rely(k, id)(s));
                                    assert(req.obj.kind != k.outer_kind);
                                    assert(false);
                                }
                            },
                            HostId::BuiltinController => { assert(false); },
                            HostId::PodMonkey => { assert(req.key().kind == Kind::PodKind); assert(false); },
                            _ => { assert(false); },
                        }
                    } else {
                        assert(s_prime.resources()[key] == old_obj);
                    }
                },
                APIRequest::GetThenUpdateStatusRequest(req) => {
                    if req.key() == key {
                        match msg.src {
                            HostId::Controller(id, okey) => {
                                assert(cluster.controller_models.contains_key(id));
                                if id == controller_id {
                                    assert(sync_request_is_guaranteed(k, msg, s));
                                    assert(false);
                                } else if id == janitor_id {
                                    assert(janitor_request_is_guaranteed(k, b, msg));
                                    assert(false);
                                } else {
                                    assert(cluster.controller_models.remove(controller_id).contains_key(id));
                                    assert(widget_sync_rely(k, id)(s));
                                    assert(req.obj.kind != k.outer_kind);
                                    assert(false);
                                }
                            },
                            HostId::BuiltinController => { assert(false); },
                            HostId::PodMonkey => { assert(false); },
                            _ => { assert(false); },
                        }
                    } else {
                        assert(s_prime.resources()[key] == old_obj);
                    }
                },
                APIRequest::UpdateRequest(req) => {
                    if req.key() == key {
                        assert(s_prime.resources()[key].status == old_obj.status);
                    } else {
                        assert(s_prime.resources()[key] == old_obj);
                    }
                },
                APIRequest::PatchRequest(req) => {
                    if req.key() == key {
                        assert(s_prime.resources()[key].status == old_obj.status);
                    } else {
                        assert(s_prime.resources()[key] == old_obj);
                    }
                },
                APIRequest::GetThenUpdateRequest(req) => {
                    if req.key() == key {
                        assert(s_prime.resources()[key].status == old_obj.status);
                    } else {
                        assert(s_prime.resources()[key] == old_obj);
                    }
                },
                APIRequest::DeleteRequest(req) => {
                    // The copy is still there without a deletion timestamp, so no delete landed.
                    if req.key() == key {
                        assert(s_prime.api_server == s.api_server);
                    } else {
                        assert(s_prime.resources()[key] == old_obj);
                    }
                },
                APIRequest::GetThenDeleteRequest(req) => {
                    if req.key() == key {
                        assert(s_prime.api_server == s.api_server);
                    } else {
                        assert(s_prime.resources()[key] == old_obj);
                    }
                },
                APIRequest::CreateRequest(_) => {
                    assert(s_prime.resources()[key] == old_obj);
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

// ---------------------------------------------------------------------------
// Phase III: the eventual facts of the status walk.
// ---------------------------------------------------------------------------

pub open spec fn scheduled_generation_ok(controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.scheduled_reconciles(controller_id).contains_key(outer.object_ref())
            ==> s.scheduled_reconciles(controller_id)[outer.object_ref()].metadata.generation == outer.metadata.generation
    }
}

pub open spec fn ongoing_generation_ok(controller_id: int, outer: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.ongoing_reconciles(controller_id).contains_key(outer.object_ref())
            ==> s.ongoing_reconciles(controller_id)[outer.object_ref()].triggering_cr.metadata.generation == outer.metadata.generation
    }
}

// The mirror as a Get response shows it once the inner side has settled.
pub open spec fn settled_response_obj(k: SyncKind, b: Binding, obj: DynamicObjectView, outer: SyncedObjectView, settled: SyncedStatusView) -> bool {
    let inner = unmarshal(inner_kind(k, b), obj)->Ok_0;
    &&& unmarshal(inner_kind(k, b), obj) is Ok
    &&& inner.metadata.deletion_timestamp is None
    &&& is_mirror_of(inner, outer)
    &&& inner.spec == outer.spec
    &&& inner_caught_up(inner)
    &&& inner.status->0.mirrored() == settled.mirrored()
    &&& inner.status->0.conditions == settled.conditions
}

pub open spec fn get_responses_are_settled(k: SyncKind, b: Binding, controller_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        let reconcile = s.ongoing_reconciles(controller_id)[key];
        let step = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0.reconcile_step;
        s.ongoing_reconciles(controller_id).contains_key(key)
        && step is AfterGetInner
        && reconcile.pending_req_msg is Some
        ==> forall |resp: Message| {
            &&& #[trigger] s.in_flight().contains(resp)
            &&& resp_msg_matches_req_msg(resp, reconcile.pending_req_msg->0)
        } ==> {
            &&& resp.content.get_get_response().res is Ok
            &&& settled_response_obj(k, b, resp.content.get_get_response().res->Ok_0, outer, settled)
        }
    }
}

pub open spec fn scheduled_status_current(k: SyncKind, controller_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        s.scheduled_reconciles(controller_id).contains_key(key)
            ==> s.scheduled_reconciles(controller_id)[key].status == s.resources()[key].status
                || stored_outer_status_desired(k, outer, settled)(s)
    }
}

pub open spec fn ongoing_status_current(k: SyncKind, controller_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = outer.object_ref();
        s.ongoing_reconciles(controller_id).contains_key(key)
            ==> s.ongoing_reconciles(controller_id)[key].triggering_cr.status == s.resources()[key].status
                || stored_outer_status_desired(k, outer, settled)(s)
    }
}

pub open spec fn r2_phase_iii(k: SyncKind, b: Binding, controller_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& scheduled_generation_ok(controller_id, outer)(s)
        &&& ongoing_generation_ok(controller_id, outer)(s)
        &&& get_responses_are_settled(k, b, controller_id, outer, settled)(s)
        &&& status_writes_are_desired(k, controller_id, outer, settled)(s)
        &&& scheduled_status_current(k, controller_id, outer, settled)(s)
        &&& ongoing_status_current(k, controller_id, outer, settled)(s)
    }
}

pub open spec fn r2_spec_with_phase_iii(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> TempPred<ClusterState> {
    r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled).and(always(lift_state(r2_phase_iii(k, b, controller_id, outer, settled))))
}

// The action under which the phase-III facts are preserved.
pub open spec fn r2_step_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& sync_step_next(k, b, cluster, controller_id, janitor_id, outer)(s, s_prime)
        &&& Cluster::crash_disabled(controller_id)(s)
        &&& Cluster::req_drop_disabled()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)(s)
        &&& Cluster::every_in_flight_msg_from_controller_has_key_kind(k.outer_kind, controller_id)(s)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)(s)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)(s_prime)
        &&& outer_stable(k, b, outer)(s)
        &&& outer_stable(k, b, outer)(s_prime)
        &&& inner_settled(k, outer, settled)(s)
    }
}

pub proof fn lemma_always_r2_step_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
    ensures spec.entails(always(lift_action(r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)))),
{
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_sync_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    always_to_always_later(spec, lift_state(cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)));
    always_to_always_later(spec, lift_state(outer_stable(k, b, outer)));
    combine_spec_entails_always_n!(
        spec, lift_action(r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        lift_action(sync_step_next(k, b, cluster, controller_id, janitor_id, outer)),
        lift_state(Cluster::crash_disabled(controller_id)),
        lift_state(Cluster::req_drop_disabled()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)),
        lift_state(Cluster::every_in_flight_msg_from_controller_has_key_kind(k.outer_kind, controller_id)),
        lift_state(cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)),
        later(lift_state(cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind))),
        lift_state(outer_stable(k, b, outer)),
        later(lift_state(outer_stable(k, b, outer))),
        lift_state(inner_settled(k, outer, settled))
    );
}

// (a) Snapshots carry the outer generation: scheduling copies the stored object.
pub proof fn lemma_true_leads_to_always_scheduled_generation_ok(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(scheduled_generation_ok(controller_id, outer))))),
{
    let key = outer.object_ref();
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r2_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    
    let next = r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    let post = scheduled_generation_ok(controller_id, outer);
    let pre = |s: ClusterState| !post(s);
    let d = outer_stable(k, b, outer);
    let stronger_pre = |s: ClusterState| pre(s) && d(s);
    assert forall |s, s_prime: ClusterState| stronger_pre(s) && #[trigger] next(s, s_prime)
        && cluster.schedule_controller_reconcile().forward((controller_id, key))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
    }
    assert forall |s: ClusterState| #[trigger] stronger_pre(s) implies cluster.schedule_controller_reconcile().pre((controller_id, key))(s) by {
        assert(s.resources().contains_key(key));
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, key, next, stronger_pre, post);
    temp_pred_equality(lift_state(pre).and(lift_state(d)), lift_state(stronger_pre));
    leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(d));
    entails_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), true_pred());
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] next(s, s_prime) implies post(s_prime) by {
        if s_prime.scheduled_reconciles(controller_id).contains_key(key) {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ScheduleControllerReconcileStep(input) => {
                    if input.0 == controller_id && input.1 == key {
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
                    } else {
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                    }
                },
                _ => {
                    assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                },
            }
        }
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(post));
}

pub proof fn lemma_true_leads_to_always_ongoing_generation_ok(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        spec.entails(always(lift_state(scheduled_generation_ok(controller_id, outer)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(ongoing_generation_ok(controller_id, outer))))),
{
    let key = outer.object_ref();
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r2_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    let post = ongoing_generation_ok(controller_id, outer);
    let next = |s, s_prime: ClusterState| {
        &&& r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime)
        &&& scheduled_generation_ok(controller_id, outer)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        lift_state(scheduled_generation_ok(controller_id, outer))
    );
    entails_implies_leads_to(spec, lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    leads_to_trans(spec, true_pred(), lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] next(s, s_prime) implies post(s_prime) by {
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
            if s.ongoing_reconciles(controller_id).contains_key(key) {
                assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.ongoing_reconciles(controller_id)[key].triggering_cr);
            } else {
                assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
            }
        }
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(post));
}

// (c) Get responses the sync reconciler holds show the settled mirror.
pub proof fn lemma_get_responses_are_settled_preserved(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, settled: SyncedStatusView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime),
        get_responses_are_settled(k, b, controller_id, outer, settled)(s),
    ensures get_responses_are_settled(k, b, controller_id, outer, settled)(s_prime),
{
    let key = outer.object_ref();
    let ikey = inner_key(k, outer);
    unmarshal_of_marshal();
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
        let reconcile_prime = s_prime.ongoing_reconciles(controller_id)[key];
        let step_prime = WidgetSyncReconcileState::unmarshal(reconcile_prime.local_state)->Ok_0.reconcile_step;
        if step_prime is AfterGetInner && reconcile_prime.pending_req_msg is Some {
            let pending = reconcile_prime.pending_req_msg->0;
            assert forall |resp: Message| {
                &&& #[trigger] s_prime.in_flight().contains(resp)
                &&& resp_msg_matches_req_msg(resp, pending)
            } implies {
                &&& resp.content.get_get_response().res is Ok
                &&& settled_response_obj(k, b, resp.content.get_get_response().res->Ok_0, outer, settled)
            } by {
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        let msg = input->0;
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        assert(sync_pending_request_is(k, controller_id, key, reconcile_prime));
                        assert(pending.content->APIRequest_0 == APIRequest::GetRequest(GetRequest { key: inner_key(k, unmarshal(k.outer_kind, reconcile_prime.triggering_cr)->Ok_0) }));
                        if !s.in_flight().contains(resp) {
                            assert(resp == transition_by_etcd(cluster.installed_types, msg, s.api_server).1);
                            assert(resp.rpc_id == msg.rpc_id);
                            assert(s.in_flight().contains(msg));
                            assert(msg == pending);
                            lemma_current_reconcile_of_outer(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
                            assert(msg.content.get_get_request().key == ikey);
                            assert(resp.content.get_get_response() == handle_get_request(GetRequest { key: ikey }, s.api_server));
                            assert(s.resources().contains_key(ikey));
                            assert(resp.content.get_get_response().res == Ok::<DynamicObjectView, APIError>(s.resources()[ikey]));
                            assert(settled_response_obj(k, b, s.resources()[ikey], outer, settled));
                        }
                    },
                    Step::ControllerStep(input) => {
                        if input.0 == controller_id && input.2 == Some(key) {
                            let reconcile = s.ongoing_reconciles(controller_id)[key];
                            if reconcile_prime == reconcile {
                                assert(s_prime.in_flight().contains(resp) && !s.in_flight().contains(resp) ==> false);
                            } else {
                                // Only Init moves into AfterGetInner, with a fresh rpc id.
                                assert(pending.rpc_id == s.rpc_id_allocator.rpc_id_counter);
                                assert(resp.rpc_id == pending.rpc_id);
                                if s.in_flight().contains(resp) {
                                    assert(resp.rpc_id < s.rpc_id_allocator.rpc_id_counter);
                                    assert(false);
                                } else {
                                    assert(resp == pending);
                                    assert(false);
                                }
                            }
                        } else {
                            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                            if !s.in_flight().contains(resp) {
                                assert(resp.content is APIRequest || resp.content is ExternalRequest);
                                assert(false);
                            }
                        }
                    },
                    Step::ExternalStep(input) => {
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        if !s.in_flight().contains(resp) {
                            assert(resp.content is ExternalResponse);
                            assert(false);
                        }
                    },
                    Step::RestartControllerStep(id) => {
                        assert(id != controller_id);
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        assert(s_prime.in_flight() == s.in_flight());
                    },
                    _ => {
                        // Requests are dropped only when request drops are disabled: not here.
                        assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                        if !s.in_flight().contains(resp) {
                            assert(resp.content is APIRequest);
                            assert(false);
                        }
                    },
                }
            }
        }
    }
}

pub proof fn lemma_true_leads_to_always_get_responses_are_settled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(get_responses_are_settled(k, b, controller_id, outer, settled))))),
{
    let key = outer.object_ref();
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r2_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    let post = get_responses_are_settled(k, b, controller_id, outer, settled);
    let next = r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    entails_implies_leads_to(spec, lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    leads_to_trans(spec, true_pred(), lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] next(s, s_prime) implies post(s_prime) by {
        lemma_get_responses_are_settled_preserved(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled);
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(post));
}

// (b) Status writes in flight write the desired status.

// One step of the reconcile of the outer copy under the phase-III facts: from Init
// it sends the Get; from AfterGetInner, whose response shows the settled mirror,
// it is done or sends the desired status patch; from AfterPatchOuterStatus it
// ends. It never reaches a step that reports a failure.
proof fn lemma_r2_reconcile_step(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, settled: SyncedStatusView,
    input: (int, Option<Message>, Option<ObjectRef>)
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime),
        ongoing_generation_ok(controller_id, outer)(s),
        get_responses_are_settled(k, b, controller_id, outer, settled)(s),
        sync_reports_no_error(controller_id, outer)(s),
        cluster.next_step(s, s_prime, Step::ControllerStep(input)),
        input.0 == controller_id,
        input.2 == Some(outer.object_ref()),
        s.ongoing_reconciles(controller_id).contains_key(outer.object_ref()),
    ensures
        s_prime.ongoing_reconciles(controller_id).contains_key(outer.object_ref()) ==> ({
            let reconcile_prime = s_prime.ongoing_reconciles(controller_id)[outer.object_ref()];
            let step_prime = WidgetSyncReconcileState::unmarshal(reconcile_prime.local_state)->Ok_0.reconcile_step;
            &&& !(step_prime is AfterCreateInner)
            &&& !(step_prime is AfterPatchInner)
            &&& !(step_prime is AfterReportError)
            &&& reconcile_prime.pending_req_msg is Some && reconcile_prime.pending_req_msg->0.content.is_patch_status_request()
                ==> desired_status_patch(k, reconcile_prime.pending_req_msg->0.content.get_patch_status_request(), outer, settled)
        }),
{
    let key = outer.object_ref();
    unmarshal_of_marshal();
    marshal_status_preserves_integrity();
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    lemma_current_reconcile_of_outer(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
    let reconcile = s.ongoing_reconciles(controller_id)[key];
    let cr = reconcile.triggering_cr;
    let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
    let state = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0;
    let resp_msg_opt = input.1;
    let resp_o = if resp_msg_opt is Some {
        if resp_msg_opt->0.content is APIResponse {
            Some(ResponseView::<VoidERespView>::KResponse(resp_msg_opt->0.content->APIResponse_0))
        } else {
            Some(ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(resp_msg_opt->0.content->ExternalResponse_0)->Ok_0))
        }
    } else {
        None
    };
    let (state_prime, req_o) = sync_reconciler::reconcile_core(k, cr_outer, resp_o, state);
    if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
        let reconcile_prime = s_prime.ongoing_reconciles(controller_id)[key];
        assert(reconcile_prime.local_state == state_prime.marshal());
        assert(WidgetSyncReconcileState::unmarshal(reconcile_prime.local_state)->Ok_0 == state_prime);
        assert(reconcile_prime.pending_req_msg is Some ==> req_o is Some && reconcile_prime.pending_req_msg->0.content->APIRequest_0 == req_o->0->KRequest_0);
        match state.reconcile_step {
            WidgetSyncStepView::Init => {
                assert(state_prime.reconcile_step is AfterGetInner);
            },
            WidgetSyncStepView::AfterGetInner => {
                if reconcile.pending_req_msg is None {
                    // Without a pending Get there is no response, and the model ends in Error.
                    assert(resp_msg_opt is None);
                    assert(state_prime.reconcile_step is Error);
                } else {
                    let resp_msg = resp_msg_opt->0;
                    assert(s.in_flight().contains(resp_msg));
                    assert(resp_msg_matches_req_msg(resp_msg, reconcile.pending_req_msg->0));
                    let res = resp_msg.content.get_get_response().res;
                    assert(res is Ok);
                    let obj = res->Ok_0;
                    assert(settled_response_obj(k, b, obj, outer, settled));
                    let inner = unmarshal(inner_kind(k, b), obj)->Ok_0;
                    assert(is_mirror_of(inner, cr_outer));
                    assert(inner.spec == cr_outer.spec);
                    assert(inner_caught_up(inner));
                    let status = outer_status_for(cr_outer.metadata.generation, inner.status->0, SyncOutcomeView::Synced);
                    assert(cr_outer.metadata.generation == outer.metadata.generation);
                    lemma_written_status_is_desired(k, b, outer, settled, inner.status->0);
                    if cr_outer.status == Some(status) {
                        assert(state_prime.reconcile_step is Done);
                    } else {
                        assert(state_prime.reconcile_step is AfterPatchOuterStatus);
                        let msg = reconcile_prime.pending_req_msg->0;
                        assert(msg.content.get_patch_status_request() == sync_reconciler::outer_status_patch(k, cr_outer, status));
                        let req = msg.content.get_patch_status_request();
                        assert(req.status == marshal_status(Some(status)));
                        assert(req.tests.uid == cr_outer.metadata.uid);
                        assert(req.tests.generation == cr_outer.metadata.generation);
                        assert(desired_status_patch(k, req, outer, settled));
                    }
                }
            },
            WidgetSyncStepView::AfterPatchOuterStatus => {
                assert(state_prime.reconcile_step is Done || state_prime.reconcile_step is Error);
            },
            WidgetSyncStepView::Done => {},
            WidgetSyncStepView::Error => {},
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn lemma_status_writes_are_desired_preserved(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, settled: SyncedStatusView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime),
        ongoing_generation_ok(controller_id, outer)(s),
        get_responses_are_settled(k, b, controller_id, outer, settled)(s),
        status_writes_are_desired(k, controller_id, outer, settled)(s),
    ensures status_writes_are_desired(k, controller_id, outer, settled)(s_prime),
{
    let key = outer.object_ref();
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let step = choose |step| cluster.next_step(s, s_prime, step);
    // The reconcile of the outer copy stays away from the failure-reporting steps.
    assert(sync_reports_no_error(controller_id, outer)(s_prime)) by {
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
            match step {
                Step::ControllerStep(input) => {
                    if input.0 == controller_id && input.2 == Some(key) {
                        if s.ongoing_reconciles(controller_id).contains_key(key) {
                            lemma_r2_reconcile_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled, input);
                        } else {
                            // A scheduled reconcile starts at Init.
                            assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == sync_reconciler::reconcile_init_state().marshal());
                        }
                    } else {
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    }
                },
                Step::RestartControllerStep(id) => {
                    assert(id != controller_id);
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                },
                _ => {
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                },
            }
        }
    }
    // A status patch newly in flight was just sent by that reconcile.
    assert forall |msg: Message| {
        &&& #[trigger] s_prime.in_flight().contains(msg)
        &&& msg.src == HostId::Controller(controller_id, key)
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
        &&& msg.content.is_patch_status_request()
    } implies desired_status_patch(k, msg.content.get_patch_status_request(), outer, settled) by {
        if s.in_flight().contains(msg) {
        } else {
            match step {
                Step::ControllerStep(input) => {
                    let (id, resp_msg_opt, cr_key_opt) = input;
                    assert(id == controller_id && cr_key_opt == Some(key));
                    assert(s.ongoing_reconciles(controller_id).contains_key(key));
                    assert(s_prime.ongoing_reconciles(controller_id).contains_key(key));
                    assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
                    lemma_r2_reconcile_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled, input);
                },
                _ => {
                    assert(false);
                },
            }
        }
    }
}

pub proof fn lemma_true_leads_to_always_status_writes_are_desired(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        spec.entails(always(lift_state(ongoing_generation_ok(controller_id, outer)))),
        spec.entails(always(lift_state(get_responses_are_settled(k, b, controller_id, outer, settled)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(status_writes_are_desired(k, controller_id, outer, settled))))),
{
    let key = outer.object_ref();
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r2_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    let post = status_writes_are_desired(k, controller_id, outer, settled);
    let next = |s, s_prime: ClusterState| {
        &&& r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime)
        &&& ongoing_generation_ok(controller_id, outer)(s)
        &&& get_responses_are_settled(k, b, controller_id, outer, settled)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        lift_state(ongoing_generation_ok(controller_id, outer)),
        lift_state(get_responses_are_settled(k, b, controller_id, outer, settled))
    );
    // At idle no request of the reconcile of the outer copy is in flight.
    let idle = Cluster::reconcile_idle(controller_id, key);
    let idle_and_msgs = |s: ClusterState| idle(s) && Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, key)(s);
    assert forall |s: ClusterState| #[trigger] idle_and_msgs(s) implies post(s) by {
        assert forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src == HostId::Controller(controller_id, key)
            &&& msg.dst is APIServer
            &&& msg.content is APIRequest
            &&& msg.content.is_patch_status_request()
        } implies desired_status_patch(k, msg.content.get_patch_status_request(), outer, settled) by {
            assert(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, key)(s));
            assert(s.ongoing_reconciles(controller_id).contains_key(key));
            assert(false);
        }
    }
    entails_implies_leads_to(spec, lift_state(idle_and_msgs), lift_state(post));
    temp_pred_equality(lift_state(idle).and(lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, key))), lift_state(idle_and_msgs));
    leads_to_by_borrowing_inv(spec, lift_state(idle), lift_state(post), lift_state(Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, key)));
    leads_to_trans(spec, true_pred(), lift_state(idle), lift_state(post));
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] next(s, s_prime) implies post(s_prime) by {
        lemma_status_writes_are_desired_preserved(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled);
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(post));
}

// (d) Snapshots' status is the stored status, unless the stored status is desired.
pub proof fn lemma_true_leads_to_always_scheduled_status_current(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        spec.entails(always(lift_state(status_writes_are_desired(k, controller_id, outer, settled)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(scheduled_status_current(k, controller_id, outer, settled))))),
{
    let key = outer.object_ref();
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r2_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    
    let post = scheduled_status_current(k, controller_id, outer, settled);
    let pre = |s: ClusterState| !post(s);
    let next = |s, s_prime: ClusterState| {
        &&& r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime)
        &&& status_writes_are_desired(k, controller_id, outer, settled)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        lift_state(status_writes_are_desired(k, controller_id, outer, settled))
    );
    let d = outer_stable(k, b, outer);
    let stronger_pre = |s: ClusterState| pre(s) && d(s);
    assert forall |s, s_prime: ClusterState| stronger_pre(s) && #[trigger] next(s, s_prime)
        && cluster.schedule_controller_reconcile().forward((controller_id, key))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
        assert(s_prime.api_server == s.api_server);
    }
    assert forall |s: ClusterState| #[trigger] stronger_pre(s) implies cluster.schedule_controller_reconcile().pre((controller_id, key))(s) by {
        assert(s.resources().contains_key(key));
        assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, key, next, stronger_pre, post);
    temp_pred_equality(lift_state(pre).and(lift_state(d)), lift_state(stronger_pre));
    leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(d));
    entails_implies_leads_to(spec, lift_state(post), lift_state(post));
    or_leads_to(spec, lift_state(pre), lift_state(post), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(post)), true_pred());
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] next(s, s_prime) implies post(s_prime) by {
        lemma_outer_status_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled);
        if s_prime.scheduled_reconciles(controller_id).contains_key(key) {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::ScheduleControllerReconcileStep(input) => {
                    if input.0 == controller_id && input.1 == key {
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
                        assert(s_prime.api_server == s.api_server);
                    } else {
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                        assert(s_prime.api_server == s.api_server);
                    }
                },
                _ => {
                    assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                },
            }
        }
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(post));
}

pub proof fn lemma_true_leads_to_always_ongoing_status_current(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        spec.entails(always(lift_state(status_writes_are_desired(k, controller_id, outer, settled)))),
        spec.entails(always(lift_state(scheduled_status_current(k, controller_id, outer, settled)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(ongoing_status_current(k, controller_id, outer, settled))))),
{
    let key = outer.object_ref();
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r2_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    let post = ongoing_status_current(k, controller_id, outer, settled);
    let next = |s, s_prime: ClusterState| {
        &&& r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime)
        &&& status_writes_are_desired(k, controller_id, outer, settled)(s)
        &&& scheduled_status_current(k, controller_id, outer, settled)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        lift_state(status_writes_are_desired(k, controller_id, outer, settled)),
        lift_state(scheduled_status_current(k, controller_id, outer, settled))
    );
    entails_implies_leads_to(spec, lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    leads_to_trans(spec, true_pred(), lift_state(Cluster::reconcile_idle(controller_id, key)), lift_state(post));
    assert forall |s, s_prime: ClusterState| post(s) && #[trigger] next(s, s_prime) implies post(s_prime) by {
        lemma_outer_status_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled);
        if s_prime.ongoing_reconciles(controller_id).contains_key(key) {
            if s.ongoing_reconciles(controller_id).contains_key(key) {
                assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.ongoing_reconciles(controller_id)[key].triggering_cr);
            } else {
                assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
                assert(s_prime.api_server == s.api_server);
            }
        }
    }
    leads_to_stable(spec, lift_action(next), true_pred(), lift_state(post));
}

// Phase III as a whole.
pub proof fn lemma_true_leads_to_always_r2_phase_iii(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(r2_phase_iii(k, b, controller_id, outer, settled))))),
{
    let spec_ii = r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    let a1 = lift_state(scheduled_generation_ok(controller_id, outer));
    let a2 = lift_state(ongoing_generation_ok(controller_id, outer));
    let c = lift_state(get_responses_are_settled(k, b, controller_id, outer, settled));
    let bw = lift_state(status_writes_are_desired(k, controller_id, outer, settled));
    let d1 = lift_state(scheduled_status_current(k, controller_id, outer, settled));
    let d2 = lift_state(ongoing_status_current(k, controller_id, outer, settled));
    r2_spec_with_phase_ii_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    assert(spec_ii.entails(spec_ii));

    // Layer 1: a1 and c directly.
    lemma_true_leads_to_always_scheduled_generation_ok(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id, outer, settled);
    lemma_true_leads_to_always_get_responses_are_settled(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id, outer, settled);
    leads_to_always_and(spec_ii, true_pred(), a1, c);
    // Layer 2: a2 under []a1 /\ []c.
    let l1 = always(a1.and(c));
    let spec_l1 = spec_ii.and(l1);
    always_p_is_stable(a1.and(c));
    stable_and_n!(spec_ii, l1);
    assert(spec_l1.entails(spec_l1));
    entails_and_split(spec_l1, spec_ii, l1);
    always_weaken(spec_l1, a1.and(c), a1);
    always_weaken(spec_l1, a1.and(c), c);
    lemma_true_leads_to_always_ongoing_generation_ok(k, b, spec_ok, spec_l1, cluster, controller_id, janitor_id, outer, settled);
    // Layer 3: bw under []a2 too.
    let l2 = always(a2);
    let spec_l2 = spec_l1.and(l2);
    always_p_is_stable(a2);
    stable_and_n!(spec_l1, l2);
    assert(spec_l2.entails(spec_l2));
    entails_and_split(spec_l2, spec_l1, l2);
    entails_and_split(spec_l2, spec_ii, l1);
    always_weaken(spec_l2, a1.and(c), a1);
    always_weaken(spec_l2, a1.and(c), c);
    lemma_true_leads_to_always_status_writes_are_desired(k, b, spec_ok, spec_l2, cluster, controller_id, janitor_id, outer, settled);
    // Layer 4: d1 under []bw too.
    let l3 = always(bw);
    let spec_l3 = spec_l2.and(l3);
    always_p_is_stable(bw);
    stable_and_n!(spec_l2, l3);
    assert(spec_l3.entails(spec_l3));
    entails_and_split(spec_l3, spec_l2, l3);
    entails_and_split(spec_l3, spec_l1, l2);
    entails_and_split(spec_l3, spec_ii, l1);
    lemma_true_leads_to_always_scheduled_status_current(k, b, spec_ok, spec_l3, cluster, controller_id, janitor_id, outer, settled);
    // Layer 5: d2 under []d1 too.
    let l4 = always(d1);
    let spec_l4 = spec_l3.and(l4);
    always_p_is_stable(d1);
    stable_and_n!(spec_l3, l4);
    assert(spec_l4.entails(spec_l4));
    entails_and_split(spec_l4, spec_l3, l4);
    entails_and_split(spec_l4, spec_l2, l3);
    entails_and_split(spec_l4, spec_l1, l2);
    entails_and_split(spec_l4, spec_ii, l1);
    lemma_true_leads_to_always_ongoing_status_current(k, b, spec_ok, spec_l4, cluster, controller_id, janitor_id, outer, settled);

    // Fold the layers back: each "true ~> []x" under a layer becomes "[]layer ~> []x" below it.
    let all = a1.and(c).and(a2).and(bw).and(d1).and(d2);
    // spec_l3 |= true ~> [](d1 /\ d2)
    unpack_conditions_from_spec(spec_l3, l4, true_pred(), always(d2));
    temp_pred_equality(true_pred().and(l4), l4);
    leads_to_trans(spec_l3, true_pred(), l4, always(d2));
    leads_to_always_and(spec_l3, true_pred(), d1, d2);
    // spec_l2 |= true ~> [](bw /\ d1 /\ d2)
    unpack_conditions_from_spec(spec_l2, l3, true_pred(), always(d1.and(d2)));
    temp_pred_equality(true_pred().and(l3), l3);
    leads_to_trans(spec_l2, true_pred(), l3, always(d1.and(d2)));
    leads_to_always_and(spec_l2, true_pred(), bw, d1.and(d2));
    // spec_l1 |= true ~> [](a2 /\ bw /\ d1 /\ d2)
    unpack_conditions_from_spec(spec_l1, l2, true_pred(), always(bw.and(d1.and(d2))));
    temp_pred_equality(true_pred().and(l2), l2);
    leads_to_trans(spec_l1, true_pred(), l2, always(bw.and(d1.and(d2))));
    leads_to_always_and(spec_l1, true_pred(), a2, bw.and(d1.and(d2)));
    // spec_ii |= true ~> [](a1 /\ c /\ a2 /\ bw /\ d1 /\ d2)
    unpack_conditions_from_spec(spec_ii, l1, true_pred(), always(a2.and(bw.and(d1.and(d2)))));
    temp_pred_equality(true_pred().and(l1), l1);
    leads_to_trans(spec_ii, true_pred(), l1, always(a2.and(bw.and(d1.and(d2)))));
    leads_to_always_and(spec_ii, true_pred(), a1.and(c), a2.and(bw.and(d1.and(d2))));
    temp_pred_equality(lift_state(r2_phase_iii(k, b, controller_id, outer, settled)), a1.and(c).and(a2.and(bw.and(d1.and(d2)))));
    entails_trans(spec, spec_ii, true_pred().leads_to(always(lift_state(r2_phase_iii(k, b, controller_id, outer, settled)))));
}

// ---------------------------------------------------------------------------
// The walk, under all layers.
// ---------------------------------------------------------------------------

pub proof fn lemma_unfold_r2_spec_with_phase_iii(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        spec.entails(r2_spec_with_phase_iii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
    ensures
        spec.entails(r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        spec.entails(always(lift_state(r2_phase_iii(k, b, controller_id, outer, settled)))),
        spec.entails(always(lift_state(scheduled_generation_ok(controller_id, outer)))),
        spec.entails(always(lift_state(ongoing_generation_ok(controller_id, outer)))),
        spec.entails(always(lift_state(get_responses_are_settled(k, b, controller_id, outer, settled)))),
        spec.entails(always(lift_state(status_writes_are_desired(k, controller_id, outer, settled)))),
        spec.entails(always(lift_state(scheduled_status_current(k, controller_id, outer, settled)))),
        spec.entails(always(lift_state(ongoing_status_current(k, controller_id, outer, settled)))),
{
    entails_and_split(spec, r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled), always(lift_state(r2_phase_iii(k, b, controller_id, outer, settled))));
    let p = lift_state(r2_phase_iii(k, b, controller_id, outer, settled));
    always_weaken(spec, p, lift_state(scheduled_generation_ok(controller_id, outer)));
    always_weaken(spec, p, lift_state(ongoing_generation_ok(controller_id, outer)));
    always_weaken(spec, p, lift_state(get_responses_are_settled(k, b, controller_id, outer, settled)));
    always_weaken(spec, p, lift_state(status_writes_are_desired(k, controller_id, outer, settled)));
    always_weaken(spec, p, lift_state(scheduled_status_current(k, controller_id, outer, settled)));
    always_weaken(spec, p, lift_state(ongoing_status_current(k, controller_id, outer, settled)));
}

pub open spec fn st_status_patch_msg_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView, settled: SyncedStatusView, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_sync_step(controller_id, outer.object_ref(), WidgetSyncStepView::AfterPatchOuterStatus)(s)
        &&& s.ongoing_reconciles(controller_id)[outer.object_ref()].pending_req_msg == Some(msg)
        &&& msg.src == HostId::Controller(controller_id, outer.object_ref())
        &&& msg.dst is APIServer
        &&& msg.content is APIRequest
        &&& msg.content.is_patch_status_request()
        &&& desired_status_patch(k, msg.content.get_patch_status_request(), outer, settled)
        &&& s.in_flight().contains(msg)
    }
}

pub open spec fn st_status_patch_in_flight(k: SyncKind, controller_id: int, outer: SyncedObjectView, settled: SyncedStatusView) -> StatePred<ClusterState> {
    |s: ClusterState| exists |msg: Message| #[trigger] st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg)(s)
}

// status_synced from its parts.
pub proof fn lemma_status_synced_from_parts(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, s: ClusterState, outer: SyncedObjectView, settled: SyncedStatusView)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_synced_object_in_etcd_is_well_formed(k.outer_kind)(s),
        outer_stable(k, b, outer)(s),
        stored_outer_status_desired(k, outer, settled)(s),
    ensures status_synced(k, outer, settled)(s),
{
    lemma_outer_object_facts(k, b, spec_ok, cluster, s, outer);
}

// The sync reconciler consumes the Get response, which shows the settled mirror: the
// desired status is already stored, or it sends the status patch that writes it.
proof fn lemma_r2_get_resp_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, settled: SyncedStatusView, resp: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime),
        Cluster::every_in_flight_msg_has_unique_id()(s),
        mirror_settled(k, b, outer)(s),
        get_responses_are_settled(k, b, controller_id, outer, settled)(s),
        ongoing_generation_ok(controller_id, outer)(s),
        ongoing_status_current(k, controller_id, outer, settled)(s),
        st_get_resp_msg_in_flight(k, b, controller_id, outer, resp)(s),
        cluster.controller_next().forward((controller_id, Some(resp), Some(outer.object_ref())))(s, s_prime),
    ensures st_status_patch_in_flight(k, controller_id, outer, settled)(s_prime) || status_synced(k, outer, settled)(s_prime),
{
    let key = outer.object_ref();
    let ikey = inner_key(k, outer);
    let input = (Some(resp), Some(key));
    
    unmarshal_of_marshal();
    marshal_status_preserves_integrity();
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let post = |s: ClusterState| {
        ||| st_status_patch_in_flight(k, controller_id, outer, settled)(s)
        ||| status_synced(k, outer, settled)(s)
    };
    lemma_current_reconcile_of_outer(k, b, spec_ok, cluster, controller_id, janitor_id, s, outer);
    lemma_outer_object_facts(k, b, spec_ok, cluster, s, outer);
    let reconcile = s.ongoing_reconciles(controller_id)[key];
    let cr = reconcile.triggering_cr;
    let cr_outer = unmarshal(k.outer_kind, cr)->Ok_0;
    let res = resp.content.get_get_response().res;
    assert(res is Ok);
    let obj = res->Ok_0;
    assert(settled_response_obj(k, b, obj, outer, settled));
    let inner = unmarshal(inner_kind(k, b), obj)->Ok_0;
    let resp_o = Some(ResponseView::<VoidERespView>::KResponse(resp.content->APIResponse_0));
    assert(is_some_k_get_resp_view(resp_o));
    assert(extract_some_k_get_resp_view(resp_o) == res);
    let (state_prime, req_o) = sync_reconciler::reconcile_core(k, cr_outer, resp_o, sync_reconciler::at_step(WidgetSyncStepView::AfterGetInner));
    assert(s_prime.ongoing_reconciles(controller_id)[key].local_state == state_prime.marshal());
    assert(s_prime.api_server == s.api_server);
    assert(is_mirror_of(inner, cr_outer));
    assert(inner.spec == cr_outer.spec);
    assert(inner_caught_up(inner));
    let status = outer_status_for(cr_outer.metadata.generation, inner.status->0, SyncOutcomeView::Synced);
    assert(cr_outer.metadata.generation == outer.metadata.generation);
    lemma_written_status_is_desired(k, b, outer, settled, inner.status->0);
    if cr_outer.status == Some(status) {
        // Done: the stored status is the snapshot's (which is desired) or desired anyway.
        assert(state_prime.reconcile_step is Done);
        
        assert(unmarshal_status(cr.status)->Ok_0 == Some(status));
        let stored = unmarshal(k.outer_kind, s.resources()[key])->Ok_0;
        if s.resources()[key].status == cr.status {
            assert(stored.status == unmarshal_status(s.resources()[key].status)->Ok_0);
            assert(stored.status == Some(status));
            assert(stored_outer_status_desired(k, outer, settled)(s));
        }
        assert(stored_outer_status_desired(k, outer, settled)(s_prime));
        lemma_status_synced_from_parts(k, b, spec_ok, cluster, s_prime, outer, settled);
    } else {
        assert(state_prime.reconcile_step is AfterPatchOuterStatus);
        let req = APIRequest::PatchStatusRequest(sync_reconciler::outer_status_patch(k, cr_outer, status));
        let msg = controller_req_msg(controller_id, key, s.rpc_id_allocator.allocate().1, req);
        assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(msg));
        assert(s_prime.in_flight().contains(msg));
        let preq = msg.content.get_patch_status_request();
        assert(preq.status == marshal_status(Some(status)));
        assert(desired_status_patch(k, preq, outer, settled));
        assert(st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg)(s_prime));
    }
}

// Any other step keeps the Get response in flight and reflecting the store.
proof fn lemma_r2_get_resp_stays_in_flight(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, settled: SyncedStatusView, resp: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime),
        Cluster::every_in_flight_msg_has_unique_id()(s),
        mirror_settled(k, b, outer)(s),
        get_responses_are_settled(k, b, controller_id, outer, settled)(s),
        ongoing_generation_ok(controller_id, outer)(s),
        ongoing_status_current(k, controller_id, outer, settled)(s),
        st_get_resp_msg_in_flight(k, b, controller_id, outer, resp)(s),
    ensures st_get_resp_msg_in_flight(k, b, controller_id, outer, resp)(s_prime) || st_status_patch_in_flight(k, controller_id, outer, settled)(s_prime) || status_synced(k, outer, settled)(s_prime),
{
    let key = outer.object_ref();
    let ikey = inner_key(k, outer);
    let input = (Some(resp), Some(key));
    
    unmarshal_of_marshal();
    marshal_status_preserves_integrity();
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    let pre = st_get_resp_msg_in_flight(k, b, controller_id, outer, resp);
    let post = |s: ClusterState| {
        ||| st_status_patch_in_flight(k, controller_id, outer, settled)(s)
        ||| status_synced(k, outer, settled)(s)
    };
    let pending = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::ControllerStep(i) => {
            if i.0 == controller_id && i.2 == Some(key) {
                assert(i.1 is Some);
                let other = i.1->0;
                assert(s.in_flight().contains(other) && resp_msg_matches_req_msg(other, pending));
                assert(other.rpc_id == resp.rpc_id);
                assert(other == resp);
                assert(cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime));
                lemma_r2_get_resp_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled, resp);
            } else {
                assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                if !s_prime.in_flight().contains(resp) {
                    assert(i.1 == Some(resp));
                    assert(resp.dst == HostId::Controller(controller_id, key));
                    assert(resp.dst == HostId::Controller(i.0, i.2->0));
                    assert(false);
                }
                lemma_get_resp_keeps_reflecting_store(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
                assert(pre(s_prime));
            }
        },
        Step::RestartControllerStep(id) => {
            assert(id != controller_id);
            assert(s_prime.api_server == s.api_server);
            assert(pre(s_prime));
        },
        Step::APIServerStep(i) => {
            assert(i->0 != resp);
            assert(s_prime.in_flight().contains(resp));
            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            lemma_get_resp_keeps_reflecting_store(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, resp);
            assert(pre(s_prime));
        },
        Step::DropReqStep(i) => {
            assert(i.0 != resp);
            assert(s_prime.in_flight().contains(resp));
            assert(s_prime.api_server == s.api_server);
            assert(pre(s_prime));
        },
        Step::ExternalStep(i) => {
            assert(i.1 != Some(resp));
            assert(s_prime.in_flight().contains(resp));
            assert(s_prime.api_server == s.api_server);
            assert(pre(s_prime));
        },
        _ => {
            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            assert(s_prime.in_flight().contains(resp));
            assert(s_prime.api_server == s.api_server);
            assert(pre(s_prime));
        },
    }
}

// The Get response in flight ~> the desired status is written or already there.
pub proof fn lemma_r2_get_resp_leads_to_decision(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_iii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
    ensures
        spec.entails(lift_state(st_get_resp_in_flight(k, b, controller_id, outer))
            .leads_to(lift_state(st_status_patch_in_flight(k, controller_id, outer, settled)).or(lift_state(status_synced(k, outer, settled))))),
{
    let key = outer.object_ref();
    lemma_unfold_r2_spec_with_phase_iii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r2_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    
    let post = |s: ClusterState| {
        ||| st_status_patch_in_flight(k, controller_id, outer, settled)(s)
        ||| status_synced(k, outer, settled)(s)
    };
    let pre_of = |resp: Message| lift_state(st_get_resp_msg_in_flight(k, b, controller_id, outer, resp));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& mirror_settled(k, b, outer)(s)
        &&& get_responses_are_settled(k, b, controller_id, outer, settled)(s)
        &&& ongoing_generation_ok(controller_id, outer)(s)
        &&& ongoing_status_current(k, controller_id, outer, settled)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(mirror_settled(k, b, outer)),
        lift_state(get_responses_are_settled(k, b, controller_id, outer, settled)),
        lift_state(ongoing_generation_ok(controller_id, outer)),
        lift_state(ongoing_status_current(k, controller_id, outer, settled))
    );
    assert forall |resp: Message| spec.entails(#[trigger] pre_of(resp).leads_to(lift_state(post))) by {
        let pre = st_get_resp_msg_in_flight(k, b, controller_id, outer, resp);
        let input = (Some(resp), Some(key));
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.controller_next().forward((controller_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
            lemma_r2_get_resp_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled, resp);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            lemma_r2_get_resp_stays_in_flight(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled, resp);
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::ContinueReconcile, (controller_id, input.0, input.1))(s) by {
            assert(key.kind == cluster.controller_models[controller_id].reconcile_model.kind);
            assert(resp.content is APIResponse);
        }
        cluster.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::ContinueReconcile, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_get_resp_in_flight(k, b, controller_id, outer)), {
        assert forall |ex| #[trigger] lift_state(st_get_resp_in_flight(k, b, controller_id, outer)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            let resp = choose |resp: Message| {
                &&& #[trigger] s.in_flight().contains(resp)
                &&& resp_msg_matches_req_msg(resp, msg)
                &&& get_resp_reflects_store(k, b, resp, outer)(s)
            };
            assert(pre_of(resp).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_get_resp_in_flight(k, b, controller_id, outer)));
    });
    temp_pred_equality(
        lift_state(post),
        lift_state(st_status_patch_in_flight(k, controller_id, outer, settled)).or(lift_state(status_synced(k, outer, settled)))
    );
}

// The API server handles the status patch: its tests pass on the stable outer copy,
// so the desired status is stored.
proof fn lemma_r2_status_patch_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, settled: SyncedStatusView, msg: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime),
        Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())(s),
        Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
        st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg)(s),
        cluster.api_server_next().forward(Some(msg))(s, s_prime),
    ensures status_synced(k, outer, settled)(s_prime),
{
    let key = outer.object_ref();
    let input = Some(msg);
    
    unmarshal_of_marshal();
    marshal_status_preserves_integrity();
    let post = status_synced(k, outer, settled);
    lemma_outer_object_facts(k, b, spec_ok, cluster, s, outer);
    lemma_weakly_well_formed_implies_kinds_match(s);
    let req = msg.content.get_patch_status_request();
    let old_obj = s.resources()[key];
    assert(req.key() == key);
    assert(req.tests.pass(old_obj));
    let update_req = UpdateStatusRequest { namespace: req.namespace, name: req.name, obj: old_obj.with_status(req.status) };
    assert(update_req.key() == key);
    assert(unmarshallable_object(update_req.obj, cluster.installed_types));
    assert(update_status_request_admission_check(cluster.installed_types, update_req, s.api_server) is None);
    let updated = status_updated_object(update_req, old_obj);
    let status = unmarshal_status(req.status)->Ok_0->0;
    if updated == old_obj {
        assert(old_obj.status == req.status);
        assert(s_prime.api_server == s.api_server);
        assert(stored_outer_status_desired(k, outer, settled)(s_prime));
    } else {
        let updated_rv = updated.with_resource_version(s.api_server.resource_version_counter);
        assert(metadata_validity_check(updated_rv) is None);
        assert(metadata_transition_validity_check(updated_rv, old_obj) is None);
        assert(unmarshal(k.outer_kind, updated_rv) is Ok);
        let updated_outer = unmarshal(k.outer_kind, updated_rv)->Ok_0;
        assert(updated_outer.spec == unmarshal(k.outer_kind, old_obj)->Ok_0.spec);
        assert(spec_ok(updated_outer.spec));
        assert(valid_object(updated_rv, cluster.installed_types));
        assert(valid_transition(updated_rv, old_obj, cluster.installed_types));
        assert(updated_object_validity_check(updated_rv, old_obj, cluster.installed_types) is None);
        assert(s_prime.resources()[key] == updated_rv);
        assert(updated_outer.status == Some(status));
        assert(stored_outer_status_desired(k, outer, settled)(s_prime));
    }
    lemma_status_synced_from_parts(k, b, spec_ok, cluster, s_prime, outer, settled);
}

// Any other step keeps the status patch in flight.
proof fn lemma_r2_status_patch_stays_in_flight(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    cluster: Cluster, controller_id: int, janitor_id: int, s: ClusterState, s_prime: ClusterState, outer: SyncedObjectView, settled: SyncedStatusView, msg: Message
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime),
        Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, outer.object_ref())(s),
        Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
        st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg)(s),
    ensures st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg)(s_prime) || status_synced(k, outer, settled)(s_prime),
{
    let key = outer.object_ref();
    let input = Some(msg);
    
    unmarshal_of_marshal();
    marshal_status_preserves_integrity();
    let pre = st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg);
    let post = status_synced(k, outer, settled);
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(i) => {
            if i->0 == msg {
                lemma_r2_status_patch_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled, msg);
            } else {
                assert(s_prime.in_flight().contains(msg));
                assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                assert(pre(s_prime));
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
                assert(pre(s_prime));
            }
        },
        Step::RestartControllerStep(id) => {
            assert(id != controller_id);
            assert(pre(s_prime));
        },
        _ => {
            assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
            assert(s_prime.in_flight().contains(msg));
            assert(pre(s_prime));
        },
    }
}

// The status patch in flight ~> the desired status is stored.
pub proof fn lemma_r2_status_patch_leads_to_synced(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_iii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
    ensures
        spec.entails(lift_state(st_status_patch_in_flight(k, controller_id, outer, settled)).leads_to(lift_state(status_synced(k, outer, settled)))),
{
    let key = outer.object_ref();
    lemma_unfold_r2_spec_with_phase_iii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r2_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    
    let post = status_synced(k, outer, settled);
    let pre_of = |msg: Message| lift_state(st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(controller_id, key)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())
    );
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_r2_status_patch_handled(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled, msg);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            lemma_r2_status_patch_stays_in_flight(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled, msg);
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {}
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_status_patch_in_flight(k, controller_id, outer, settled)), {
        assert forall |ex| #[trigger] lift_state(st_status_patch_in_flight(k, controller_id, outer, settled)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = choose |msg: Message| #[trigger] st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg)(s);
            assert(pre_of(msg).satisfied_by(ex));
        }
        assert forall |ex| #[trigger] tla_exists(pre_of).satisfied_by(ex)
        implies lift_state(st_status_patch_in_flight(k, controller_id, outer, settled)).satisfied_by(ex) by {
            let msg = choose |msg: Message| #[trigger] pre_of(msg).satisfied_by(ex);
            assert(st_status_patch_msg_in_flight(k, controller_id, outer, settled, msg)(ex.head()));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_status_patch_in_flight(k, controller_id, outer, settled)));
    });
}

// Under all layers: the desired status is eventually and forever stored.
pub proof fn lemma_true_leads_to_always_status_synced(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(r2_spec_with_phase_iii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(status_synced(k, outer, settled))))),
{
    let key = outer.object_ref();
    lemma_unfold_r2_spec_with_phase_iii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_r2_layers_imply_r1_layers(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_unfold_sync_spec_with_phase_ii(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    lemma_always_r2_step_next(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_sync_terminates(k, b, spec_ok, spec, cluster, controller_id, janitor_id, key);
    let idle = lift_state(Cluster::reconcile_idle(controller_id, key));
    let scheduled = lift_state(|s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(key)
        &&& s.scheduled_reconciles(controller_id).contains_key(key)
    });
    let init = lift_state(st_sync_init(controller_id, key));
    let get_req = lift_state(st_get_req_in_flight(k, controller_id, outer));
    let get_resp = lift_state(st_get_resp_in_flight(k, b, controller_id, outer));
    let status_req = lift_state(st_status_patch_in_flight(k, controller_id, outer, settled));
    let synced = lift_state(status_synced(k, outer, settled));
    lemma_sync_idle_leads_to_scheduled(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_scheduled_leads_to_init(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_init_leads_to_get_req_in_flight(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_sync_get_req_leads_to_get_resp(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer);
    lemma_r2_get_resp_leads_to_decision(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    lemma_r2_status_patch_leads_to_synced(k, b, spec_ok, spec, cluster, controller_id, janitor_id, outer, settled);
    entails_implies_leads_to(spec, synced, synced);
    or_leads_to(spec, status_req, synced, synced);
    leads_to_trans_n!(spec, true_pred(), idle, scheduled, init, get_req, get_resp, status_req.or(synced), synced);
    // Stability: the status changes only to the desired one, and the rest is fixed by the premise.
    let next = |s, s_prime: ClusterState| {
        &&& r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)(s, s_prime)
        &&& status_writes_are_desired(k, controller_id, outer, settled)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(r2_step_next(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled)),
        lift_state(status_writes_are_desired(k, controller_id, outer, settled))
    );
    assert forall |s, s_prime: ClusterState| status_synced(k, outer, settled)(s) && #[trigger] next(s, s_prime) implies status_synced(k, outer, settled)(s_prime) by {
        lemma_outer_status_after_step(k, b, spec_ok, cluster, controller_id, janitor_id, s, s_prime, outer, settled);
        lemma_outer_object_facts(k, b, spec_ok, cluster, s, outer);
        lemma_outer_object_facts(k, b, spec_ok, cluster, s_prime, outer);
        if s_prime.resources()[key].status == s.resources()[key].status {
            assert(unmarshal(k.outer_kind, s_prime.resources()[key])->Ok_0.status == unmarshal(k.outer_kind, s.resources()[key])->Ok_0.status);
            assert(stored_outer_status_desired(k, outer, settled)(s_prime));
        }
        lemma_status_synced_from_parts(k, b, spec_ok, cluster, s_prime, outer, settled);
    }
    leads_to_stable(spec, lift_action(next), true_pred(), synced);
}

// ---------------------------------------------------------------------------
// Assembly: R2 for one outer copy and status, then for all.
// ---------------------------------------------------------------------------

pub proof fn lemma_premise_leads_to_always_status_synced(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, 
    spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int, outer: SyncedObjectView, settled: SyncedStatusView
)
    requires
        k.bindings.contains(b),
        outer.kind == k.outer_kind,
        cluster_of(k.selector, outer) is Some,
        b == binding_of(k, outer),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id)),
    ensures spec.entails(r2_premise(k, b, outer, settled).leads_to(always(lift_state(status_synced(k, outer, settled))))),
{
    let target = always(lift_state(status_synced(k, outer, settled)));
    let stable_spec = sync_stable_spec(k, b, spec_ok, cluster, controller_id, janitor_id);
    let spec_p = r2_spec_with_premise(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    let spec_i = r2_spec_with_phase_i(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    let spec_ii = r2_spec_with_phase_ii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    let spec_iii = r2_spec_with_phase_iii(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    let phase_iii_temp = always(lift_state(r2_phase_iii(k, b, controller_id, outer, settled)));
    let phase_ii_temp = always(lift_state(sync_phase_ii(controller_id, outer)));
    let phase_i_temp = always(lift_state(phase_i(controller_id)));
    let premise_temp = r2_premise(k, b, outer, settled);

    assert(spec_iii.entails(spec_iii));
    lemma_true_leads_to_always_status_synced(k, b, spec_ok, spec_iii, cluster, controller_id, janitor_id, outer, settled);
    // Remove phase III.
    r2_spec_with_phase_ii_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    unpack_conditions_from_spec(spec_ii, phase_iii_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_iii_temp), phase_iii_temp);
    assert(spec_ii.entails(spec_ii));
    lemma_true_leads_to_always_r2_phase_iii(k, b, spec_ok, spec_ii, cluster, controller_id, janitor_id, outer, settled);
    leads_to_trans(spec_ii, true_pred(), phase_iii_temp, target);
    // Remove phase II: R1's phase II lemma applies since spec_i gives R1's phase-I layer.
    r2_spec_with_phase_i_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    unpack_conditions_from_spec(spec_i, phase_ii_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_ii_temp), phase_ii_temp);
    assert(spec_i.entails(spec_i));
    entails_and_split(spec_i, spec_p, phase_i_temp);
    entails_and_split(spec_i, stable_spec, premise_temp);
    always_weaken(spec_i, lift_state(outer_stable(k, b, outer)).and(lift_state(inner_settled(k, outer, settled))), lift_state(outer_stable(k, b, outer)));
    always_weaken(spec_i, lift_state(outer_stable(k, b, outer)), lift_state(outer_spec_stable(k, b, outer)));
    entails_and(spec_i, stable_spec, always(lift_state(outer_spec_stable(k, b, outer))));
    entails_and(spec_i, sync_spec_with_desired(k, b, spec_ok, cluster, controller_id, janitor_id, outer), phase_i_temp);
    lemma_true_leads_to_always_sync_phase_ii(k, b, spec_ok, spec_i, cluster, controller_id, janitor_id, outer);
    leads_to_trans(spec_i, true_pred(), phase_ii_temp, target);
    // Remove phase I.
    r2_spec_with_premise_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id, outer, settled);
    unpack_conditions_from_spec(spec_p, phase_i_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(phase_i_temp), phase_i_temp);
    assert(spec_p.entails(spec_p));
    entails_and_split(spec_p, stable_spec, premise_temp);
    lemma_sync_stable_spec_facts(k, b, spec_ok, spec_p, cluster, controller_id, janitor_id);
    lemma_true_leads_to_always_phase_i(k, b, spec_p, cluster, controller_id);
    leads_to_trans(spec_p, true_pred(), phase_i_temp, target);
    // Remove the premise.
    sync_stable_spec_is_stable(k, b, spec_ok, cluster, controller_id, janitor_id);
    unpack_conditions_from_spec(stable_spec, premise_temp, true_pred(), target);
    temp_pred_equality(true_pred().and(premise_temp), premise_temp);
    entails_trans(spec, stable_spec, premise_temp.leads_to(target));
}

// R2: once the outer copy is stable and the inner side has settled on a status for
// the mirror, the outer copy eventually and forever carries that status.
pub proof fn sync_eventually_mirrors_status(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, janitor_id: int)
    requires
        k.bindings.contains(b),
        spec.entails(lift_state(cluster.init())),
        spec.entails(sync_next_with_wf(cluster, controller_id)),
        sync_membership(k, b, spec_ok, cluster, controller_id, janitor_id),
        spec.entails(always(lift_state(sync_rely_with_janitor(k, b, cluster, controller_id, janitor_id)))),
        spec.entails(inner_releases_terminating_objects(k)),
        spec.entails(widget_janitor_esr(k, b, janitor_id)),
    ensures spec.entails(widget_status_eventually_mirrored(k, b)),
{
    entails_and_split(spec, widget_mirrors_eventually_collected(k, b), always(lift_state(janitor_deletes_are_sound(k, b, janitor_id))));
    assert(sync_next_with_wf(cluster, controller_id).entails(always(lift_action(cluster.next()))));
    entails_trans(spec, sync_next_with_wf(cluster, controller_id), always(lift_action(cluster.next())));
    sync_invariants_hold(k, b, spec_ok, spec, cluster, controller_id, janitor_id);
    entails_and_n!(
        spec,
        sync_next_with_wf(cluster, controller_id),
        always(lift_state(sync_rely_with_janitor(k, b, cluster, controller_id, janitor_id))),
        inner_releases_terminating_objects(k),
        widget_mirrors_eventually_collected(k, b),
        sync_invariants(k, b, spec_ok, cluster, controller_id, janitor_id)
    );
    let per_cr = |i: (SyncedObjectView, SyncedStatusView)| widget_status_eventually_mirrored_per_cr(k, b, i.0, i.1);
    assert forall |i: (SyncedObjectView, SyncedStatusView)| spec.entails(#[trigger] per_cr(i)) by {
        if i.0.kind == k.outer_kind && cluster_of(k.selector, i.0) is Some && b == binding_of(k, i.0) {
            lemma_premise_leads_to_always_status_synced(k, b, spec_ok, spec, cluster, controller_id, janitor_id, i.0, i.1);
        } else {
            let premise = |s: ClusterState| outer_stable(k, b, i.0)(s) && inner_settled(k, i.0, i.1)(s);
            temp_pred_equality(lift_state(outer_stable(k, b, i.0)).and(lift_state(inner_settled(k, i.0, i.1))), lift_state(premise));
            lemma_vacuous_always_leads_to(spec, premise, always(lift_state(status_synced(k, i.0, i.1))));
        }
    }
    spec_entails_tla_forall(spec, per_cr);
}

}
