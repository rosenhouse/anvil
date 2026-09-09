// The Widget sync reconciler of a kind as a Welder controller spec, its singleton
// core, and the composition of the sync reconciler with the janitors of its
// bindings.
//
// The sync reconciler depends on each janitor only through that janitor's
// ControllerSpec: on its guarantee (the partial rely for the janitor's id) and on
// its ESR (the liveness dependency: R3, and that the janitor's Deletes are
// sound). Its environment rely is D3 (the inner side releases terminating
// mirrors). compose_dep discharges the dependency with the janitors' proved ESRs.
use crate::composition::widget_janitor_reconciler::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::vstd_ext::string_view::*;
use crate::kubernetes_cluster::proof::composition::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::{api_server::types::*, cluster::*, message::*};
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::proof::{guarantee::*, liveness::cleanup_proof::*, liveness::spec::*, liveness::sync_spec_proof::*, liveness::sync_status_proof::*};
use crate::widget_sync_controller::trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*};
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

// R1, R2 and R3s, for every bound binding of the kind.
pub open spec fn widget_sync_esr(k: SyncKind) -> TempPred<ClusterState> {
    tla_forall(|b: Binding| if k.bindings.contains(b) {
        widget_spec_eventually_synced(k, b)
            .and(widget_status_eventually_mirrored(k, b))
            .and(widget_mirrors_stably_collected(k, b))
    } else {
        true_pred::<ClusterState>()
    })
}

// The conjunction over the bindings of the janitors' ESRs: what the sync
// reconciler's liveness depends on.
pub open spec fn janitors_esr(k: SyncKind, ids: Map<Binding, int>) -> TempPred<ClusterState> {
    tla_forall(|b: Binding| if k.bindings.contains(b) {
        widget_janitor_esr(k, b, ids[b])
    } else {
        true_pred::<ClusterState>()
    })
}

// The janitors have distinct ids, none of them the sync reconciler's.
pub open spec fn ids_ok(bs: Set<Binding>, ids: Map<Binding, int>, controller_id: int) -> bool {
    &&& forall |b: Binding| #[trigger] bs.contains(b) ==> ids[b] != controller_id
    &&& forall |x: Binding, y: Binding| #![trigger ids[x], ids[y]] bs.contains(x) && bs.contains(y) && ids[x] == ids[y] ==> x == y
}

pub open spec fn is_janitor_id(bs: Set<Binding>, ids: Map<Binding, int>, id: int) -> bool {
    exists |b: Binding| bs.contains(b) && #[trigger] ids[b] == id
}

pub open spec fn binding_at(bs: Set<Binding>, ids: Map<Binding, int>, id: int) -> Binding {
    choose |b: Binding| bs.contains(b) && #[trigger] ids[b] == id
}

// The sync reconciler relies on each of its janitors through that janitor's
// guarantee, and on everybody else through widget_sync_rely.
pub open spec fn widget_sync_partial_rely(k: SyncKind, ids: Map<Binding, int>) -> spec_fn(int) -> TempPred<ClusterState> {
    |other_id: int| if is_janitor_id(k.bindings, ids, other_id) {
        always(lift_state(widget_janitor_guarantee(k, binding_at(k.bindings, ids, other_id), other_id)))
    } else {
        always(lift_state(widget_sync_rely(k, other_id)))
    }
}

// The sync reconciler's cluster: it runs at `controller_id`, each bound binding's
// janitor at its own id, and the kind is installed for the outer copies and for
// every bound binding's mirrors with the same schema and selector.
pub open spec fn sync_membership_all(k: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, ids: Map<Binding, int>) -> bool {
    &&& ids_ok(k.bindings, ids, controller_id)
    &&& cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model(k))
    &&& cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector)
    &&& forall |b: Binding| #[trigger] k.bindings.contains(b) ==> sync_membership(k, b, spec_ok, cluster, controller_id, ids[b])
}

pub open spec fn widget_sync_controller_spec(k: SyncKind, spec_ok: spec_fn(Value) -> bool, id: int, ids: Map<Binding, int>) -> ControllerSpec {
    ControllerSpec {
        esr: widget_sync_esr(k),
        // The janitors' ESRs: R3 and sound deletes, per binding.
        liveness_dependency: janitors_esr(k, ids),
        safety_guarantee: always(lift_state(widget_sync_guarantee(k, id))),
        // D3: the inner side releases terminating mirrors.
        environment_rely: inner_releases_terminating_objects_all(k),
        safety_partial_rely: widget_sync_partial_rely(k, ids),
        fairness: |cluster: Cluster| sync_next_with_wf(cluster, id),
        membership: |cluster: Cluster, c_id: int| sync_membership_all(k, spec_ok, cluster, c_id, ids),
    }
}

pub open spec fn widget_sync_core_set(k: SyncKind, id: int, ids: Map<Binding, int>) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: janitors_esr(k, ids),
    }
}

// The per-controller rely facts, lifted into the one always-predicate the
// liveness proofs of the binding `b` take.
pub proof fn sync_rely_facts_imply_lifted_condition(k: SyncKind, b: Binding, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, ids: Map<Binding, int>)
    requires
        k.bindings.contains(b),
        ids_ok(k.bindings, ids, controller_id),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(#[trigger] widget_sync_partial_rely(k, ids)(other_id)),
    ensures spec.entails(always(lift_state(sync_rely_with_janitor(k, b, cluster, controller_id, ids[b])))),
{
    assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
        spec.satisfied_by(ex)
        && cluster.controller_models.remove(controller_id).contains_key(other_id)
        implies (if other_id == ids[b] { widget_janitor_guarantee(k, b, ids[b])(ex.suffix(n).head()) } else { widget_sync_rely(k, other_id)(ex.suffix(n).head()) }) by {
        let p = widget_sync_partial_rely(k, ids)(other_id);
        assert(valid(spec.implies(p)));
        assert(spec.implies(p).satisfied_by(ex));
        assert(p.satisfied_by(ex));
        if other_id == ids[b] {
            assert(is_janitor_id(k.bindings, ids, other_id));
            let b2 = binding_at(k.bindings, ids, other_id);
            assert(k.bindings.contains(b2) && ids[b2] == other_id);
            assert(b2 == b);
            assert(always(lift_state(widget_janitor_guarantee(k, b2, other_id))).satisfied_by(ex));
            assert(lift_state(widget_janitor_guarantee(k, b2, other_id)).satisfied_by(ex.suffix(n)));
        } else if is_janitor_id(k.bindings, ids, other_id) {
            // Another binding's janitor: its guarantee is stronger than the rely.
            let b2 = binding_at(k.bindings, ids, other_id);
            assert(k.bindings.contains(b2) && ids[b2] == other_id);
            assert(always(lift_state(widget_janitor_guarantee(k, b2, other_id))).satisfied_by(ex));
            assert(lift_state(widget_janitor_guarantee(k, b2, other_id)).satisfied_by(ex.suffix(n)));
            janitor_guarantee_implies_sync_rely(k, b2, other_id);
            assert(lift_state(widget_janitor_guarantee(k, b2, other_id)).entails(lift_state(widget_sync_rely(k, other_id))));
        } else {
            assert(always(lift_state(widget_sync_rely(k, other_id))).satisfied_by(ex));
            assert(lift_state(widget_sync_rely(k, other_id)).satisfied_by(ex.suffix(n)));
        }
    }
}

pub proof fn widget_sync_singleton_core_holds(k: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, id: int, ids: Map<Binding, int>)
    requires
        cluster.registry.contains_pair(id, widget_sync_controller_spec(k, spec_ok, id, ids)),
        well_formed(cluster, widget_sync_core_set(k, id, ids)),
    ensures
        core(cluster, widget_sync_core_set(k, id, ids)),
{
    let s = widget_sync_core_set(k, id, ids);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    assert(s.members.contains(id));
    assert((cluster.registry[id].membership)(inner, id));
    assert(sync_membership_all(k, spec_ok, inner, id, ids));

    let fairness_fn = |i: int| if cluster.registry.contains_key(i) {
        (cluster.registry[i].fairness)(inner)
    } else { true_pred::<ClusterState>() };
    assert(spec.entails(sync_next_with_wf(inner, id))) by {
        tla_forall_apply(fairness_fn, id);
    }
    assert(sync_next_with_wf(inner, id).entails(always(lift_action(inner.next()))));
    entails_trans(spec, sync_next_with_wf(inner, id), always(lift_action(inner.next())));

    // Guarantee.
    lemma_always_widget_sync_guarantee(spec, inner, k, spec_ok, id);

    let G_fn = |c: int| if s.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
    let R_fn = |pair: (int, int)| if s.members.contains(pair.0) && !s.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let ESR_fn = |c: int| if s.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
    let env_fn = |c: int| if s.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred::<ClusterState>() };

    assert forall |c: int| spec.entails(#[trigger] G_fn(c)) by {
        if s.members.contains(c) {
            tla_forall_apply(G_fn, c);
        }
    }
    spec_entails_tla_forall(spec, G_fn);

    // R, D (the janitors' ESRs) and the environment rely (D3) feed the liveness proofs.
    let assumption_rde = tla_forall(R_fn).and(s.liveness_dependency).and(tla_forall(env_fn));
    let spec_rde = spec.and(assumption_rde);

    assert forall |c: int| spec_rde.entails(#[trigger] ESR_fn(c)) by {
        if s.members.contains(c) {
            assert forall |other_id: int| #[trigger] inner.controller_models.remove(id).contains_key(other_id)
                implies spec_rde.entails(widget_sync_partial_rely(k, ids)(other_id)) by {
                tla_forall_apply(R_fn, (id, other_id));
                assert(R_fn((id, other_id)) == widget_sync_partial_rely(k, ids)(other_id));
                entails_trans(spec_rde, tla_forall(R_fn), R_fn((id, other_id)));
            }
            tla_forall_apply(env_fn, id);
            entails_trans(spec_rde, tla_forall(env_fn), env_fn(id));
            assert(env_fn(id) == inner_releases_terminating_objects_all(k));
            assert(s.liveness_dependency == janitors_esr(k, ids));
            entails_trans(spec_rde, spec, lift_state(inner.init()));
            entails_trans(spec_rde, spec, sync_next_with_wf(inner, id));

            let per_binding = |b: Binding| if k.bindings.contains(b) {
                widget_spec_eventually_synced(k, b)
                    .and(widget_status_eventually_mirrored(k, b))
                    .and(widget_mirrors_stably_collected(k, b))
            } else {
                true_pred::<ClusterState>()
            };
            let dep_fn = |b: Binding| if k.bindings.contains(b) { widget_janitor_esr(k, b, ids[b]) } else { true_pred::<ClusterState>() };
            // D3 is assumed per binding; the sync controller, which serves them
            // all, takes the conjunction and reads off the binding at hand.
            let d3_fn = |b: Binding| if k.bindings.contains(b) {
                inner_releases_terminating_objects(k, b)
            } else {
                true_pred::<ClusterState>()
            };
            assert(inner_releases_terminating_objects_all(k) == tla_forall(d3_fn));
            assert forall |b: Binding| spec_rde.entails(#[trigger] per_binding(b)) by {
                if k.bindings.contains(b) {
                    tla_forall_apply(d3_fn, b);
                    entails_trans(spec_rde, tla_forall(d3_fn), d3_fn(b));
                    assert(d3_fn(b) == inner_releases_terminating_objects(k, b));
                    tla_forall_apply(dep_fn, b);
                    entails_trans(spec_rde, s.liveness_dependency, dep_fn(b));
                    assert(dep_fn(b) == widget_janitor_esr(k, b, ids[b]));
                    sync_rely_facts_imply_lifted_condition(k, b, spec_rde, inner, id, ids);
                    sync_eventually_synced(k, b, spec_ok, spec_rde, inner, id, ids[b]);
                    sync_eventually_mirrors_status(k, b, spec_ok, spec_rde, inner, id, ids[b]);
                    sync_mirrors_stably_collected(k, b, spec_ok, spec_rde, inner, id, ids[b]);
                    entails_and(spec_rde, widget_spec_eventually_synced(k, b), widget_status_eventually_mirrored(k, b));
                    entails_and(spec_rde, widget_spec_eventually_synced(k, b).and(widget_status_eventually_mirrored(k, b)), widget_mirrors_stably_collected(k, b));
                }
            }
            spec_entails_tla_forall(spec_rde, per_binding);
            assert(ESR_fn(c) == widget_sync_esr(k));
        }
    }
    spec_entails_tla_forall(spec_rde, ESR_fn);
    entails_implies(spec, assumption_rde, tla_forall(ESR_fn));
    entails_and(spec, tla_forall(G_fn), assumption_rde.implies(tla_forall(ESR_fn)));
}

// ---------------------------------------------------------------------------
// Composing a janitor with the sync reconciler.
// ---------------------------------------------------------------------------

// The sync reconciler's guarantee implies every janitor's rely on it: the only
// mirror it creates is make_inner(outer) for an outer copy at the request's
// namespace and name, and it never sends Update or GetThenUpdate.
// A janitor sends only Lists of the outer kind and Deletes of its own mirrors, so
// its guarantee is stronger than what the sync reconciler relies on of any other
// controller: it creates nothing, and updates nothing.
pub proof fn janitor_guarantee_implies_sync_rely(k: SyncKind, b: Binding, id: int)
    ensures lift_state(widget_janitor_guarantee(k, b, id)).entails(lift_state(widget_sync_rely(k, id))),
{
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(k, b, id)(s) implies widget_sync_rely(k, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => !is_inner_kind(k, req.obj.kind),
                APIRequest::UpdateRequest(req) => mirror_update_req(k, req)(s),
                APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(k, req)(s),
                APIRequest::PatchRequest(_) => true,
                APIRequest::UpdateStatusRequest(req) => req.obj.kind != k.outer_kind,
                APIRequest::GetThenUpdateStatusRequest(req) => req.obj.kind != k.outer_kind,
                APIRequest::PatchStatusRequest(req) => req.kind != k.outer_kind,
                _ => true,
            }) by {
            match msg.content->APIRequest_0 {
                APIRequest::ListRequest(_) => {},
                APIRequest::DeleteRequest(_) => {},
                _ => { assert(false); },
            }
        }
    }
}

pub proof fn sync_guarantee_implies_janitor_rely(k: SyncKind, id: int)
    ensures lift_state(widget_sync_guarantee(k, id)).entails(lift_state(widget_janitor_rely(k, id))),
{
    assert forall |s: ClusterState| #[trigger] widget_sync_guarantee(k, id)(s) implies widget_janitor_rely(k, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
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
            }) by {
            let outer_key = msg.src->Controller_1;
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => {
                    assert(mirror_create_req(k, req, outer_key)(s));
                    let outer = choose |outer: SyncedObjectView| {
                        &&& outer.kind == k.outer_kind
                        &&& outer.object_ref() == outer_key
                        &&& outer.metadata.uid is Some
                        &&& cluster_of(k.selector, outer) is Some
                        &&& req.namespace == outer_key.namespace
                        &&& req.obj == #[trigger] marshal(make_inner(k, outer))
                        &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s)
                    };
                    marshal_preserves_metadata();
                    assert(req.obj.metadata == make_inner(k, outer).metadata);
                    assert(req.obj.metadata.name == Some(outer.metadata.name->0));
                    let key2 = ObjectRef { kind: k.outer_kind, namespace: req.namespace, name: req.obj.metadata.name->0 };
                    assert(key2 == outer_key);
                }
                _ => {}
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Composing the janitors of a finite set of bindings with the sync reconciler.
// ---------------------------------------------------------------------------

// A janitor's guarantee implies every other janitor's rely: the rely constrains
// Creates and Updates of mirrors, and a janitor sends neither.
pub proof fn janitor_guarantee_implies_janitor_rely(k: SyncKind, b: Binding, id: int)
    ensures lift_state(widget_janitor_guarantee(k, b, id)).entails(lift_state(widget_janitor_rely(k, id))),
{
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(k, b, id)(s) implies widget_janitor_rely(k, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
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
            }) by {
            match msg.content->APIRequest_0 {
                APIRequest::ListRequest(_) => {},
                APIRequest::DeleteRequest(_) => {},
                _ => { assert(false); },
            }
        }
    }
}

// The ids of the janitors of the bindings in `sub`, and the core set they form.
// Their liveness dependency is empty: a janitor's ESR rests on its rely alone.
pub open spec fn janitor_ids_of(sub: Set<Binding>, ids: Map<Binding, int>) -> Set<int> {
    sub.map(|b: Binding| ids[b])
}

pub open spec fn widget_janitors_core_set(sub: Set<Binding>, ids: Map<Binding, int>) -> CoreSet {
    CoreSet {
        members: janitor_ids_of(sub, ids),
        liveness_dependency: true_pred(),
    }
}

// Every bound binding's janitor is registered under its own id, with its own
// spec, and its membership holds of the cluster.
pub open spec fn janitors_registered(k: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, ids: Map<Binding, int>) -> bool {
    forall |b: Binding| #[trigger] k.bindings.contains(b) ==> {
        &&& cluster.registry.contains_pair(ids[b], widget_janitor_controller_spec(k, b, spec_ok, ids[b]))
        &&& (widget_janitor_controller_spec(k, b, spec_ok, ids[b]).membership)(cluster.cluster, ids[b])
    }
}

// An id of the janitor core set is the id of one bound binding, and ids_ok's
// injectivity names it.
pub proof fn lemma_janitor_id_is_a_binding(bs: Set<Binding>, sub: Set<Binding>, ids: Map<Binding, int>, controller_id: int, id: int)
    requires
        ids_ok(bs, ids, controller_id),
        sub.subset_of(bs),
        janitor_ids_of(sub, ids).contains(id),
    ensures
        sub.contains(binding_at(bs, ids, id)),
        ids[binding_at(bs, ids, id)] == id,
        is_janitor_id(bs, ids, id),
{
    broadcast use Set::lemma_map_contains;
    let f = |b: Binding| ids[b];
    assert(exists |b: Binding| sub.contains(b) && id == f(b));
    let b0 = choose |b: Binding| sub.contains(b) && id == f(b);
    assert(bs.contains(b0) && ids[b0] == id);
    assert(is_janitor_id(bs, ids, id));
    let b1 = binding_at(bs, ids, id);
    assert(bs.contains(b1) && ids[b1] == id);
    assert(b1 == b0);
}

// The id of a bound binding is in the core set of any subset that holds it.
pub proof fn lemma_binding_id_is_a_member(bs: Set<Binding>, sub: Set<Binding>, ids: Map<Binding, int>, controller_id: int, b: Binding)
    requires
        ids_ok(bs, ids, controller_id),
        sub.subset_of(bs),
        sub.contains(b),
    ensures
        janitor_ids_of(sub, ids).contains(ids[b]),
        is_janitor_id(bs, ids, ids[b]),
        binding_at(bs, ids, ids[b]) == b,
{
    broadcast use Set::lemma_map_contains;
    let f = |b2: Binding| ids[b2];
    assert(sub.contains(b) && ids[b] == f(b));
    assert(bs.contains(b) && ids[b] == ids[b]);
    let b1 = binding_at(bs, ids, ids[b]);
    assert(bs.contains(b1) && ids[b1] == ids[b]);
}

// The janitors of a set of bindings compose into one core set, one binding at a
// time: each janitor's guarantee is what every other janitor relies on, and none
// of them has a liveness dependency, so `compose` applies at every step.
pub proof fn widget_janitors_core_holds(k: SyncKind, sub: Set<Binding>, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, ids: Map<Binding, int>, controller_id: int)
    requires
        ids_ok(k.bindings, ids, controller_id),
        sub.subset_of(k.bindings),
        janitors_registered(k, spec_ok, cluster, ids),
    ensures
        well_formed(cluster, widget_janitors_core_set(sub, ids)),
        core(cluster, widget_janitors_core_set(sub, ids)),
    decreases sub.len(),
{
    broadcast use Set::lemma_map_contains;
    let s = widget_janitors_core_set(sub, ids);
    let spec = cluster_model(cluster);
    assert(well_formed(cluster, s)) by {
        assert forall |i: int| #[trigger] s.members.contains(i) implies cluster.registry.contains_key(i)
            && (cluster.registry[i].membership)(cluster.cluster, i) by {
            lemma_janitor_id_is_a_binding(k.bindings, sub, ids, controller_id, i);
            let b = binding_at(k.bindings, ids, i);
            assert(k.bindings.contains(b) && ids[b] == i);
        }
    }
    if sub.is_empty() {
        // No members: every conjunct of the ESR is true_pred.
        let g_fn = |c: int| if s.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r_fn = |pair: (int, int)| if s.members.contains(pair.0) && !s.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let env_fn = |c: int| if s.members.contains(c) { cluster.registry[c].environment_rely } else { true_pred::<ClusterState>() };
        let esr_fn = |c: int| if s.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
        assert(s.members =~= Set::<int>::empty());
        assert forall |c: int| spec.entails(#[trigger] g_fn(c)) by {
            assert(!s.members.contains(c));
            assert(g_fn(c) == true_pred::<ClusterState>());
        }
        spec_entails_tla_forall(spec, g_fn);
        assert forall |c: int| spec.entails(#[trigger] esr_fn(c)) by {
            assert(!s.members.contains(c));
            assert(esr_fn(c) == true_pred::<ClusterState>());
        }
        spec_entails_tla_forall(spec, esr_fn);
        let rest = tla_forall(r_fn).and(s.liveness_dependency).and(tla_forall(env_fn));
        entails_implies(spec, rest, tla_forall(esr_fn));
        entails_and(spec, tla_forall(g_fn), rest.implies(tla_forall(esr_fn)));
    } else {
        let b0 = sub.choose();
        assert(sub.contains(b0));
        let rest_bs = sub.remove(b0);
        vstd::set::lemma_set_remove_len(sub, b0);
        assert(rest_bs.len() < sub.len());
        assert(rest_bs.subset_of(k.bindings));
        widget_janitors_core_holds(k, rest_bs, spec_ok, cluster, ids, controller_id);
        let s1 = widget_janitors_core_set(rest_bs, ids);
        let s2 = widget_janitor_core_set(ids[b0]);
        assert(k.bindings.contains(b0));
        assert(cluster.registry.contains_pair(ids[b0], widget_janitor_controller_spec(k, b0, spec_ok, ids[b0])));
        assert(well_formed(cluster, s2));
        widget_janitor_singleton_core_holds(k, b0, spec_ok, cluster, ids[b0]);
        assert(compatible(cluster, s1, s2)) by {
            let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
            let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
            let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
            let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
            // What one janitor relies on of another is that other's guarantee.
            assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
                if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                    lemma_janitor_id_is_a_binding(k.bindings, rest_bs, ids, controller_id, pair.1);
                    let b2 = binding_at(k.bindings, ids, pair.1);
                    assert(pair.0 == ids[b0]);
                    assert(r21_fn(pair) == always(lift_state(widget_janitor_rely(k, pair.1))));
                    tla_forall_apply(g_fn_s1, pair.1);
                    assert(g_fn_s1(pair.1) == always(lift_state(widget_janitor_guarantee(k, b2, pair.1))));
                    janitor_guarantee_implies_janitor_rely(k, b2, pair.1);
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k, b2, pair.1)), lift_state(widget_janitor_rely(k, pair.1)));
                    entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(widget_janitor_guarantee(k, b2, pair.1))));
                    entails_trans(spec.and(tla_forall(g_fn_s1)), always(lift_state(widget_janitor_guarantee(k, b2, pair.1))), always(lift_state(widget_janitor_rely(k, pair.1))));
                }
            }
            spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
            entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));
            assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
                if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                    lemma_janitor_id_is_a_binding(k.bindings, rest_bs, ids, controller_id, pair.0);
                    assert(pair.1 == ids[b0]);
                    assert(r12_fn(pair) == always(lift_state(widget_janitor_rely(k, pair.1))));
                    tla_forall_apply(g_fn_s2, pair.1);
                    assert(g_fn_s2(pair.1) == always(lift_state(widget_janitor_guarantee(k, b0, ids[b0]))));
                    janitor_guarantee_implies_janitor_rely(k, b0, ids[b0]);
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k, b0, ids[b0])), lift_state(widget_janitor_rely(k, ids[b0])));
                    entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(widget_janitor_guarantee(k, b0, ids[b0]))));
                    entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(widget_janitor_guarantee(k, b0, ids[b0]))), always(lift_state(widget_janitor_rely(k, ids[b0]))));
                }
            }
            spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
            entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));
            entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
        }
        compose(cluster, s1, s2);
        assert(union_coreset(s1, s2, true_pred()).members =~= s.members) by {
            assert forall |i: int| s1.members.union(s2.members).contains(i) implies s.members.contains(i) by {
                if s1.members.contains(i) {
                    lemma_janitor_id_is_a_binding(k.bindings, rest_bs, ids, controller_id, i);
                    let b2 = binding_at(k.bindings, ids, i);
                    lemma_binding_id_is_a_member(k.bindings, sub, ids, controller_id, b2);
                } else {
                    assert(i == ids[b0]);
                    lemma_binding_id_is_a_member(k.bindings, sub, ids, controller_id, b0);
                }
            }
            assert forall |i: int| s.members.contains(i) implies s1.members.union(s2.members).contains(i) by {
                lemma_janitor_id_is_a_binding(k.bindings, sub, ids, controller_id, i);
                let b2 = binding_at(k.bindings, ids, i);
                if b2 == b0 {
                    assert(s2.members.contains(i));
                } else {
                    assert(rest_bs.contains(b2));
                    lemma_binding_id_is_a_member(k.bindings, rest_bs, ids, controller_id, b2);
                }
            }
        }
        assert(union_coreset(s1, s2, true_pred()) == s);
    }
}

// The whole pair for a configuration: the janitors of `k.bindings` composed
// together, then composed with the sync reconciler, whose liveness dependency
// (janitors_esr) their ESRs discharge. widget_pair_core_holds below is the
// singleton instance of this statement
// (doc/widget_sync_fanout_design.md, section 5.1).
pub proof fn widget_fanout_core_holds(k: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, ids: Map<Binding, int>, sync_id: int)
    requires
        ids_ok(k.bindings, ids, sync_id),
        janitors_registered(k, spec_ok, cluster, ids),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, ids)),
        (widget_sync_controller_spec(k, spec_ok, sync_id, ids).membership)(cluster.cluster, sync_id),
    ensures
        well_formed(cluster, union_coreset(widget_janitors_core_set(k.bindings, ids), widget_sync_core_set(k, sync_id, ids), true_pred())),
        core(cluster, union_coreset(widget_janitors_core_set(k.bindings, ids), widget_sync_core_set(k, sync_id, ids), true_pred())),
{
    broadcast use Set::lemma_map_contains;
    let s1 = widget_janitors_core_set(k.bindings, ids);
    let s2 = widget_sync_core_set(k, sync_id, ids);
    let spec = cluster_model(cluster);
    widget_janitors_core_holds(k, k.bindings, spec_ok, cluster, ids, sync_id);
    assert(well_formed(cluster, s2));
    widget_sync_singleton_core_holds(k, spec_ok, cluster, sync_id, ids);
    // The sync reconciler's dependency is the conjunction of the janitors' ESRs.
    assert(satisfies_dependency(cluster, s1, s2)) by {
        let esr_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
        let esr_s1 = tla_forall(esr_fn_s1);
        let dep_fn = |b2: Binding| if k.bindings.contains(b2) { widget_janitor_esr(k, b2, ids[b2]) } else { true_pred::<ClusterState>() };
        assert forall |b2: Binding| spec.and(esr_s1).entails(#[trigger] dep_fn(b2)) by {
            if k.bindings.contains(b2) {
                lemma_binding_id_is_a_member(k.bindings, k.bindings, ids, sync_id, b2);
                tla_forall_apply(esr_fn_s1, ids[b2]);
                assert(esr_fn_s1(ids[b2]) == widget_janitor_esr(k, b2, ids[b2]));
                entails_trans(spec.and(esr_s1), esr_s1, widget_janitor_esr(k, b2, ids[b2]));
            }
        }
        spec_entails_tla_forall(spec.and(esr_s1), dep_fn);
        assert(s2.liveness_dependency == janitors_esr(k, ids));
        entails_implies(spec, esr_s1, s2.liveness_dependency);
    }
    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        // The sync reconciler relies on each janitor through that janitor's guarantee.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                assert(pair.0 == sync_id);
                lemma_janitor_id_is_a_binding(k.bindings, k.bindings, ids, sync_id, pair.1);
                let b2 = binding_at(k.bindings, ids, pair.1);
                assert(r21_fn(pair) == always(lift_state(widget_janitor_guarantee(k, b2, pair.1))));
                tla_forall_apply(g_fn_s1, pair.1);
                assert(g_fn_s1(pair.1) == always(lift_state(widget_janitor_guarantee(k, b2, pair.1))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(widget_janitor_guarantee(k, b2, pair.1))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));
        // Each janitor's rely on the sync reconciler follows from its guarantee.
        sync_guarantee_implies_janitor_rely(k, sync_id);
        entails_preserved_by_always(lift_state(widget_sync_guarantee(k, sync_id)), lift_state(widget_janitor_rely(k, sync_id)));
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                assert(pair.1 == sync_id);
                lemma_janitor_id_is_a_binding(k.bindings, k.bindings, ids, sync_id, pair.0);
                let b2 = binding_at(k.bindings, ids, pair.0);
                assert(r12_fn(pair) == always(lift_state(widget_janitor_rely(k, sync_id))));
                tla_forall_apply(g_fn_s2, sync_id);
                assert(g_fn_s2(sync_id) == always(lift_state(widget_sync_guarantee(k, sync_id))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), tla_forall(g_fn_s2), always(lift_state(widget_sync_guarantee(k, sync_id))));
                entails_trans(spec.and(tla_forall(g_fn_s2)), always(lift_state(widget_sync_guarantee(k, sync_id))), always(lift_state(widget_janitor_rely(k, sync_id))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));
        entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }
    compose_dep(cluster, s1, s2);
}

// ---------------------------------------------------------------------------
// The singleton case, as an instance of the fan-out statement.
// ---------------------------------------------------------------------------

// The pair {janitor of `b`, sync of `k`} for a single binding: the janitor's ESR
// discharges the sync reconciler's liveness dependency, and the two guarantees
// discharge each other's relies. This is the case the deployed binary runs and
// the one compose_all puts beside the other four controllers. It is the singleton
// instance of widget_fanout_core_holds, not a second proof of it: the janitors'
// core set of a one-element binding set has the one janitor's id as its only
// member, so the two core sets are the same value by set extensionality.
pub proof fn widget_pair_core_holds(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, janitor_id: int, sync_id: int)
    requires
        // `b` is the whole configuration: the sync reconciler serves it alone,
        // which is what made the binding set of the old signature `{b}`.
        k.bindings == Set::<Binding>::empty().insert(b),
        cluster.registry.contains_pair(janitor_id, widget_janitor_controller_spec(k, b, spec_ok, janitor_id)),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, Map::empty().insert(b, janitor_id))),
        janitor_id != sync_id,
        well_formed(cluster, widget_janitor_core_set(janitor_id)),
        well_formed(cluster, widget_sync_core_set(k, sync_id, Map::empty().insert(b, janitor_id))),
    ensures
        well_formed(cluster, union_coreset(
            widget_janitor_core_set(janitor_id),
            widget_sync_core_set(k, sync_id, Map::empty().insert(b, janitor_id)), true_pred())),
        core(cluster, union_coreset(
            widget_janitor_core_set(janitor_id),
            widget_sync_core_set(k, sync_id, Map::empty().insert(b, janitor_id)), true_pred())),
{
    broadcast use Set::lemma_map_contains;
    let bs = k.bindings;
    let ids = Map::empty().insert(b, janitor_id);
    assert(bs.contains(b));
    assert(ids_ok(bs, ids, sync_id)) by {
        assert forall |x: Binding, y: Binding| #![trigger ids[x], ids[y]] bs.contains(x) && bs.contains(y) && ids[x] == ids[y] implies x == y by {
            assert(x == b && y == b);
        }
    }
    // well_formed of each singleton core set is what carries the memberships.
    assert(widget_janitor_core_set(janitor_id).members.contains(janitor_id));
    assert((cluster.registry[janitor_id].membership)(cluster.cluster, janitor_id));
    assert(widget_sync_core_set(k, sync_id, ids).members.contains(sync_id));
    assert((cluster.registry[sync_id].membership)(cluster.cluster, sync_id));
    assert(janitors_registered(k, spec_ok, cluster, ids)) by {
        assert forall |b2: Binding| #[trigger] bs.contains(b2) implies {
            &&& cluster.registry.contains_pair(ids[b2], widget_janitor_controller_spec(k, b2, spec_ok, ids[b2]))
            &&& (widget_janitor_controller_spec(k, b2, spec_ok, ids[b2]).membership)(cluster.cluster, ids[b2])
        } by {
            assert(b2 == b);
            assert(ids[b2] == janitor_id);
        }
    }
    widget_fanout_core_holds(k, spec_ok, cluster, ids, sync_id);
    // The janitors of a one-element binding set are the one janitor.
    assert(widget_janitors_core_set(bs, ids) == widget_janitor_core_set(janitor_id)) by {
        assert(janitor_ids_of(bs, ids) =~= Set::<int>::empty().insert(janitor_id)) by {
            assert forall |i: int| janitor_ids_of(bs, ids).contains(i) implies i == janitor_id by {
                let f = |b2: Binding| ids[b2];
                let b2 = choose |b2: Binding| bs.contains(b2) && i == f(b2);
                assert(b2 == b);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The cluster of a configuration, for any kind and any bindings.
// ---------------------------------------------------------------------------

// The names of the model kinds a configuration needs installed: the CRD name for
// the outer copies, and one mirror name per binding. Finitely many, because
// `k.bindings` is (doc/widget_sync_fanout_design.md, section 5.2).
pub open spec fn synced_kind_names(k: SyncKind) -> Set<StringView> {
    Set::empty().insert(k.name).union(k.bindings.map(|b: Binding| remote_kind_name(k.name, b)))
}

// Those names, each installed with the shape's type for the kind's schema and
// selector: the installed types of a cluster that serves `k`. Nothing else is
// installed, which is what makes every hypothesis about the installed types of
// the multi-store refinement one case.
pub open spec fn widget_installed_types(k: SyncKind, spec_ok: spec_fn(Value) -> bool) -> InstalledTypes {
    Map::new(
        synced_kind_names(k),
        |name: StringView| Cluster::synced_installed_type(spec_ok, k.selector))
}

// The kinds of the configuration are installed, and every installed name carries
// the same type. `sync_kind_ok` is what ties the outer kind to `k.name`; the
// mirror kinds are the model kinds of the bindings, and they are distinct from
// the outer kind and from each other by lemma_model_kind_distinct and
// lemma_inner_kind_injective, never by the length of a literal name.
pub proof fn lemma_widget_installed_types(k: SyncKind, spec_ok: spec_fn(Value) -> bool)
    requires sync_kind_ok(k),
    ensures
        k.outer_kind == Kind::CustomResourceKind(k.name),
        widget_installed_types(k, spec_ok).contains_key(k.name),
        forall |b: Binding| #[trigger] k.bindings.contains(b) ==> {
            &&& inner_kind(k, b) == Kind::CustomResourceKind(remote_kind_name(k.name, b))
            &&& widget_installed_types(k, spec_ok).contains_key(remote_kind_name(k.name, b))
        },
        forall |name: StringView| #[trigger] widget_installed_types(k, spec_ok).contains_key(name)
            ==> widget_installed_types(k, spec_ok)[name] == Cluster::synced_installed_type(spec_ok, k.selector),
{
    broadcast use Set::lemma_map_contains;
    assert(synced_kind_names(k).contains(k.name));
    assert forall |b: Binding| #[trigger] k.bindings.contains(b)
        implies widget_installed_types(k, spec_ok).contains_key(remote_kind_name(k.name, b)) by {
        let f = |b2: Binding| remote_kind_name(k.name, b2);
        assert(k.bindings.map(f).contains(f(b)));
        assert(synced_kind_names(k).contains(remote_kind_name(k.name, b)));
    }
}

// The same, read on a cluster whose installed types are exactly those.
pub proof fn lemma_widget_types_installed(k: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: Cluster)
    requires
        sync_kind_ok(k),
        cluster.installed_types == widget_installed_types(k, spec_ok),
    ensures
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        forall |b: Binding| #[trigger] k.bindings.contains(b)
            ==> cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector),
        forall |name: StringView| #[trigger] cluster.installed_types.contains_key(name)
            ==> cluster.installed_types[name] == Cluster::synced_installed_type(spec_ok, k.selector),
{
    lemma_widget_installed_types(k, spec_ok);
}

// The concrete cluster of a configuration: the sync controller of `k` at
// `sync_id`, the janitor of each of `k.bindings` at the id `ids` gives it, and
// the model kinds of `k` installed. Every part of it is a function of the
// configuration.
pub open spec fn widget_cluster_for(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>) -> Cluster {
    Cluster {
        installed_types: widget_installed_types(k, spec_ok),
        controller_models: Map::new(
            Set::empty().insert(sync_id).union(janitor_ids_of(k.bindings, ids)),
            |id: int| if id == sync_id {
                widget_sync_controller_model(k)
            } else {
                widget_janitor_controller_model(k, binding_at(k.bindings, ids, id))
            }),
    }
}

// What that cluster runs: the sync controller, each binding's janitor, nothing
// else. `ids_ok` is what lets a janitor's id name its binding back.
pub proof fn lemma_widget_cluster_for_models(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>)
    requires ids_ok(k.bindings, ids, sync_id),
    ensures
        widget_cluster_for(k, spec_ok, sync_id, ids).controller_models.contains_pair(sync_id, widget_sync_controller_model(k)),
        forall |b: Binding| #[trigger] k.bindings.contains(b)
            ==> widget_cluster_for(k, spec_ok, sync_id, ids).controller_models.contains_pair(ids[b], widget_janitor_controller_model(k, b)),
        widget_cluster_for(k, spec_ok, sync_id, ids).controller_models.dom()
            == Set::<int>::empty().insert(sync_id).union(janitor_ids_of(k.bindings, ids)),
{
    broadcast use Set::lemma_map_contains;
    let cluster = widget_cluster_for(k, spec_ok, sync_id, ids);
    assert(cluster.controller_models.dom() =~= Set::<int>::empty().insert(sync_id).union(janitor_ids_of(k.bindings, ids)));
    assert forall |b: Binding| #[trigger] k.bindings.contains(b)
        implies cluster.controller_models.contains_pair(ids[b], widget_janitor_controller_model(k, b)) by {
        lemma_binding_id_is_a_member(k.bindings, k.bindings, ids, sync_id, b);
        assert(ids[b] != sync_id);
    }
}

// The cluster of a configuration in which only one binding's janitor runs. The
// multi-store theorems are read one binding at a time
// (doc/widget_sync_fanout_design.md, section 5.2), and this is the cluster its
// closed statements are read on: the sync controller of `k`, the janitor of `b`,
// and the model kinds of the whole configuration installed, because the sync
// controller serves every binding of `k.bindings`.
pub open spec fn widget_pair_cluster_for(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int) -> Cluster {
    Cluster {
        installed_types: widget_installed_types(k, spec_ok),
        controller_models: Map::empty()
            .insert(sync_id, widget_sync_controller_model(k))
            .insert(janitor_id, widget_janitor_controller_model(k, b)),
    }
}

// When the configuration has the one binding, the two values are the same.
pub proof fn lemma_widget_cluster_for_is_pair(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int)
    requires
        k.bindings == Set::<Binding>::empty().insert(b),
        janitor_id != sync_id,
    ensures
        widget_cluster_for(k, spec_ok, sync_id, Map::<Binding, int>::empty().insert(b, janitor_id))
            == widget_pair_cluster_for(k, b, spec_ok, sync_id, janitor_id),
{
    broadcast use Set::lemma_map_contains;
    let ids = Map::<Binding, int>::empty().insert(b, janitor_id);
    let m1 = widget_cluster_for(k, spec_ok, sync_id, ids).controller_models;
    let m2 = widget_pair_cluster_for(k, b, spec_ok, sync_id, janitor_id).controller_models;
    assert(ids_ok(k.bindings, ids, sync_id)) by {
        assert forall |x: Binding, y: Binding| #![trigger ids[x], ids[y]] k.bindings.contains(x) && k.bindings.contains(y) && ids[x] == ids[y] implies x == y by {
            assert(x == b && y == b);
        }
    }
    assert(janitor_ids_of(k.bindings, ids) =~= Set::<int>::empty().insert(janitor_id)) by {
        assert forall |i: int| janitor_ids_of(k.bindings, ids).contains(i) implies i == janitor_id by {
            let f = |b2: Binding| ids[b2];
            let b2 = choose |b2: Binding| k.bindings.contains(b2) && i == f(b2);
            assert(b2 == b);
        }
        assert(k.bindings.contains(b) && ids[b] == janitor_id);
    }
    assert(binding_at(k.bindings, ids, janitor_id) == b) by {
        lemma_binding_id_is_a_member(k.bindings, k.bindings, ids, sync_id, b);
    }
    assert(m1 =~= m2);
}

// The Welder registry of that cluster: one ControllerSpec per controller.
pub open spec fn widget_core_cluster_for(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>) -> CoreCluster {
    CoreCluster {
        cluster: widget_cluster_for(k, spec_ok, sync_id, ids),
        registry: Map::new(
            Set::empty().insert(sync_id).union(janitor_ids_of(k.bindings, ids)),
            |id: int| if id == sync_id {
                widget_sync_controller_spec(k, spec_ok, sync_id, ids)
            } else {
                widget_janitor_controller_spec(k, binding_at(k.bindings, ids, id), spec_ok, id)
            }),
    }
}

pub open spec fn widget_core_set_for(k: SyncKind, sync_id: int, ids: Map<Binding, int>) -> CoreSet {
    union_coreset(
        widget_janitors_core_set(k.bindings, ids),
        widget_sync_core_set(k, sync_id, ids),
        true_pred())
}

// The closed statement, for ANY configuration: a cluster running the sync
// controller of `k` and one janitor per binding satisfies `core`. The
// distinctness of the model kinds is discharged inside, from `sync_kind_ok` and
// `binding_ok`, by the injectivity of model_kind -- never from the characters of
// a literal kind name.
pub proof fn widget_core_holds(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>)
    requires
        sync_kind_ok(k),
        forall |b: Binding| #[trigger] k.bindings.contains(b) ==> binding_ok(b),
        ids_ok(k.bindings, ids, sync_id),
    ensures
        well_formed(widget_core_cluster_for(k, spec_ok, sync_id, ids), widget_core_set_for(k, sync_id, ids)),
        core(widget_core_cluster_for(k, spec_ok, sync_id, ids), widget_core_set_for(k, sync_id, ids)),
{
    broadcast use Set::lemma_map_contains;
    let cluster = widget_core_cluster_for(k, spec_ok, sync_id, ids);
    let inner = cluster.cluster;
    lemma_widget_types_installed(k, spec_ok, inner);
    lemma_widget_cluster_for_models(k, spec_ok, sync_id, ids);
    lemma_outer_kind_is_not_any_inner(k);

    assert(cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, ids)));
    assert(janitors_registered(k, spec_ok, cluster, ids)) by {
        assert forall |b: Binding| #[trigger] k.bindings.contains(b) implies {
            &&& cluster.registry.contains_pair(ids[b], widget_janitor_controller_spec(k, b, spec_ok, ids[b]))
            &&& (widget_janitor_controller_spec(k, b, spec_ok, ids[b]).membership)(inner, ids[b])
        } by {
            lemma_binding_id_is_a_member(k.bindings, k.bindings, ids, sync_id, b);
            assert(ids[b] != sync_id);
            assert(binding_at(k.bindings, ids, ids[b]) == b);
        }
    }
    assert((widget_sync_controller_spec(k, spec_ok, sync_id, ids).membership)(inner, sync_id)) by {
        assert forall |b: Binding| #[trigger] k.bindings.contains(b)
            implies sync_membership(k, b, spec_ok, inner, sync_id, ids[b]) by {
            lemma_binding_id_is_a_member(k.bindings, k.bindings, ids, sync_id, b);
            assert(ids[b] != sync_id);
        }
    }
    widget_fanout_core_holds(k, spec_ok, cluster, ids, sync_id);
}

// ---------------------------------------------------------------------------
// The demo configuration: `widgets.anvil.dev` in `default/inner`.
// ---------------------------------------------------------------------------

pub open spec fn widget_kind_name() -> StringView { "widgets.anvil.dev"@ }

pub open spec fn widget_selector() -> ClusterSelector {
    ClusterSelector::Field(seq!["spec"@, "clusterName"@])
}

// The configured kind of the demo deployment: one kind, served for the one
// binding widget_bindings() holds. The binding set is part of the kind because
// the sync reconciler's model consults it (spec_types::serves); a deployment
// with more bindings is the same definition with a larger set.
pub open spec fn widget_kind() -> SyncKind {
    SyncKind {
        outer_kind: model_kind(widget_kind_name(), ClusterIdView::Primary),
        name: widget_kind_name(),
        selector: widget_selector(),
        bindings: widget_bindings(),
    }
}

pub open spec fn widget_binding() -> Binding {
    ClusterRefView { namespace: "default"@, name: "inner"@ }
}

pub open spec fn widget_bindings() -> Set<Binding> { Set::empty().insert(widget_binding()) }

// The CRD's schema, as far as the model is concerned: any spec.
pub open spec fn widget_spec_ok() -> spec_fn(Value) -> bool { |v: Value| true }

pub open spec fn widget_janitor_id() -> int { 1 }
pub open spec fn widget_sync_id() -> int { 2 }

pub open spec fn widget_janitor_ids() -> Map<Binding, int> {
    Map::empty().insert(widget_binding(), widget_janitor_id())
}

pub open spec fn widget_inner_kind() -> Kind { inner_kind(widget_kind(), widget_binding()) }

// The demo's literals meet the hypotheses of the generic statements: the CRD name
// carries no '@', the binding's namespace no '@' and no '/', its cluster name no
// '@'. This is all the literal strings are ever used for; the distinctness of the
// model kinds follows from these by lemma_model_kind_distinct.
pub proof fn widget_demo_config_ok()
    ensures
        sync_kind_ok(widget_kind()),
        forall |b: Binding| #[trigger] widget_kind().bindings.contains(b) ==> binding_ok(b),
        binding_ok(widget_binding()),
{
    reveal_strlit("widgets.anvil.dev");
    reveal_strlit("default");
    reveal_strlit("inner");
    assert forall |b: Binding| #[trigger] widget_kind().bindings.contains(b) implies binding_ok(b) by {
        assert(b == widget_binding());
    }
}

// The two model kinds of the demo differ: they are the model kinds of one CRD
// name in two different clusters.
pub proof fn widget_kinds_distinct()
    ensures widget_kind().outer_kind != widget_inner_kind(),
{
    widget_demo_config_ok();
    lemma_outer_kind_is_not_inner(widget_kind(), widget_binding());
}

// The demo's cluster as the multi-store statements read it: the sync controller and
// the one binding's janitor. lemma_widget_cluster_for_is_pair says it is the same
// value as widget_core_cluster().cluster.
pub open spec fn widget_cluster_instance() -> Cluster {
    widget_pair_cluster_for(widget_kind(), widget_binding(), widget_spec_ok(), widget_sync_id(), widget_janitor_id())
}

pub open spec fn widget_core_cluster() -> CoreCluster {
    widget_core_cluster_for(widget_kind(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids())
}

pub open spec fn widget_core_set() -> CoreSet {
    widget_core_set_for(widget_kind(), widget_sync_id(), widget_janitor_ids())
}

// The demo is one line of the generic statement.
pub proof fn widget_demo_core_holds()
    ensures
        well_formed(widget_core_cluster(), widget_core_set()),
        core(widget_core_cluster(), widget_core_set()),
{
    widget_demo_config_ok();
    assert(ids_ok(widget_bindings(), widget_janitor_ids(), widget_sync_id())) by {
        assert forall |x: Binding, y: Binding| #![trigger widget_janitor_ids()[x], widget_janitor_ids()[y]]
            widget_bindings().contains(x) && widget_bindings().contains(y) && widget_janitor_ids()[x] == widget_janitor_ids()[y]
            implies x == y by {
            assert(x == widget_binding() && y == widget_binding());
        }
    }
    widget_core_holds(widget_kind(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids());
}

// ---------------------------------------------------------------------------
// A second demo: the same kind served for two bindings.
// ---------------------------------------------------------------------------

// A second binding of the same namespace, so that the fan-out statement has a
// concrete instance with more than one janitor.
pub open spec fn widget_binding_two() -> Binding {
    ClusterRefView { namespace: "default"@, name: "second"@ }
}

pub open spec fn widget_fanout_bindings() -> Set<Binding> {
    Set::empty().insert(widget_binding()).insert(widget_binding_two())
}

// The same kind served for both bindings. It differs from widget_kind() only in
// its binding set, which is what the sync reconciler consults.
pub open spec fn widget_fanout_kind() -> SyncKind {
    SyncKind {
        outer_kind: model_kind(widget_kind_name(), ClusterIdView::Primary),
        name: widget_kind_name(),
        selector: widget_selector(),
        bindings: widget_fanout_bindings(),
    }
}

pub open spec fn widget_janitor_two_id() -> int { 4 }

pub open spec fn widget_fanout_janitor_ids() -> Map<Binding, int> {
    Map::empty().insert(widget_binding(), widget_janitor_id()).insert(widget_binding_two(), widget_janitor_two_id())
}

pub open spec fn widget_fanout_inner_kind(b: Binding) -> Kind { inner_kind(widget_fanout_kind(), b) }

pub proof fn widget_fanout_config_ok()
    ensures
        sync_kind_ok(widget_fanout_kind()),
        forall |b: Binding| #[trigger] widget_fanout_kind().bindings.contains(b) ==> binding_ok(b),
{
    reveal_strlit("widgets.anvil.dev");
    reveal_strlit("default");
    reveal_strlit("inner");
    reveal_strlit("second");
    assert forall |b: Binding| #[trigger] widget_fanout_kind().bindings.contains(b) implies binding_ok(b) by {
        assert(b == widget_binding() || b == widget_binding_two());
    }
}

// The two bindings differ, and so do their mirror kinds -- by the injectivity of
// inner_kind on well-formed bindings, not by the length of a cluster name.
pub proof fn widget_fanout_bindings_distinct()
    ensures
        widget_binding() != widget_binding_two(),
        widget_fanout_inner_kind(widget_binding()) != widget_fanout_inner_kind(widget_binding_two()),
{
    reveal_strlit("inner");
    reveal_strlit("second");
    assert("inner"@.len() != "second"@.len());
    widget_fanout_config_ok();
    assert(widget_fanout_kind().bindings.contains(widget_binding()));
    assert(widget_fanout_kind().bindings.contains(widget_binding_two()));
    if widget_fanout_inner_kind(widget_binding()) == widget_fanout_inner_kind(widget_binding_two()) {
        lemma_inner_kind_injective(widget_fanout_kind(), widget_binding(), widget_binding_two());
    }
}

pub open spec fn widget_fanout_core_cluster() -> CoreCluster {
    widget_core_cluster_for(widget_fanout_kind(), widget_spec_ok(), widget_sync_id(), widget_fanout_janitor_ids())
}

pub open spec fn widget_fanout_core_set() -> CoreSet {
    widget_core_set_for(widget_fanout_kind(), widget_sync_id(), widget_fanout_janitor_ids())
}

// The fan-out statement for a concrete cluster: one sync reconciler serving two
// bindings, one janitor for each, and the three kinds they need installed. This
// is the witness that widget_core_holds has instances with more than one binding.
pub proof fn widget_fanout_instance_core_holds()
    ensures
        well_formed(widget_fanout_core_cluster(), widget_fanout_core_set()),
        core(widget_fanout_core_cluster(), widget_fanout_core_set()),
{
    let ids = widget_fanout_janitor_ids();
    let bs = widget_fanout_bindings();
    widget_fanout_config_ok();
    widget_fanout_bindings_distinct();
    assert(ids_ok(bs, ids, widget_sync_id())) by {
        assert forall |b: Binding| #[trigger] bs.contains(b) implies ids[b] != widget_sync_id() by {
            assert(b == widget_binding() || b == widget_binding_two());
        }
        assert forall |x: Binding, y: Binding| #![trigger ids[x], ids[y]] bs.contains(x) && bs.contains(y) && ids[x] == ids[y] implies x == y by {
            assert((x == widget_binding() || x == widget_binding_two()) && (y == widget_binding() || y == widget_binding_two()));
        }
    }
    widget_core_holds(widget_fanout_kind(), widget_spec_ok(), widget_sync_id(), ids);
}

}
