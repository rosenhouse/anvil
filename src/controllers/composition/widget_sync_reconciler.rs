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
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::proof::{guarantee::*, liveness::cleanup_proof::*, liveness::spec::*, liveness::sync_spec_proof::*, liveness::sync_status_proof::*};
use crate::widget_sync_controller::trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*};
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use vstd::prelude::*;

verus! {

// R1, R2 and R3s, for every bound binding of the kind.
pub open spec fn widget_sync_esr(k: SyncKind, bs: Set<Binding>) -> TempPred<ClusterState> {
    tla_forall(|b: Binding| if bs.contains(b) {
        widget_spec_eventually_synced(k, b)
            .and(widget_status_eventually_mirrored(k, b))
            .and(widget_mirrors_stably_collected(k, b))
    } else {
        true_pred::<ClusterState>()
    })
}

// The conjunction over the bindings of the janitors' ESRs: what the sync
// reconciler's liveness depends on.
pub open spec fn janitors_esr(k: SyncKind, bs: Set<Binding>, ids: Map<Binding, int>) -> TempPred<ClusterState> {
    tla_forall(|b: Binding| if bs.contains(b) {
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
pub open spec fn widget_sync_partial_rely(k: SyncKind, bs: Set<Binding>, ids: Map<Binding, int>) -> spec_fn(int) -> TempPred<ClusterState> {
    |other_id: int| if is_janitor_id(bs, ids, other_id) {
        always(lift_state(widget_janitor_guarantee(k, binding_at(bs, ids, other_id), other_id)))
    } else {
        always(lift_state(widget_sync_rely(k, other_id)))
    }
}

// The sync reconciler's cluster: it runs at `controller_id`, each bound binding's
// janitor at its own id, and the kind is installed for the outer copies and for
// every bound binding's mirrors with the same schema and selector.
pub open spec fn sync_membership_all(k: SyncKind, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, controller_id: int, ids: Map<Binding, int>) -> bool {
    &&& ids_ok(bs, ids, controller_id)
    &&& cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model(k))
    &&& cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector)
    &&& forall |b: Binding| #[trigger] bs.contains(b) ==> sync_membership(k, b, bs, spec_ok, cluster, controller_id, ids[b])
}

pub open spec fn widget_sync_controller_spec(k: SyncKind, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, id: int, ids: Map<Binding, int>) -> ControllerSpec {
    ControllerSpec {
        esr: widget_sync_esr(k, bs),
        // The janitors' ESRs: R3 and sound deletes, per binding.
        liveness_dependency: janitors_esr(k, bs, ids),
        safety_guarantee: always(lift_state(widget_sync_guarantee(k, id))),
        // D3: the inner side releases terminating mirrors.
        environment_rely: inner_releases_terminating_objects(k, bs),
        safety_partial_rely: widget_sync_partial_rely(k, bs, ids),
        fairness: |cluster: Cluster| sync_next_with_wf(cluster, id),
        membership: |cluster: Cluster, c_id: int| sync_membership_all(k, bs, spec_ok, cluster, c_id, ids),
    }
}

pub open spec fn widget_sync_core_set(k: SyncKind, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, id: int, ids: Map<Binding, int>) -> CoreSet {
    CoreSet {
        members: Set::empty().insert(id),
        liveness_dependency: janitors_esr(k, bs, ids),
    }
}

// The per-controller rely facts, lifted into the one always-predicate the
// liveness proofs of the binding `b` take.
pub proof fn sync_rely_facts_imply_lifted_condition(k: SyncKind, b: Binding, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int, ids: Map<Binding, int>)
    requires
        bs.contains(b),
        ids_ok(bs, ids, controller_id),
        forall |other_id| cluster.controller_models.remove(controller_id).contains_key(other_id)
            ==> spec.entails(#[trigger] widget_sync_partial_rely(k, bs, ids)(other_id)),
    ensures spec.entails(always(lift_state(sync_rely_with_janitor(k, b, bs, spec_ok, cluster, controller_id, ids[b])))),
{
    assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
        spec.satisfied_by(ex)
        && cluster.controller_models.remove(controller_id).contains_key(other_id)
        implies (if other_id == ids[b] { widget_janitor_guarantee(k, b, ids[b])(ex.suffix(n).head()) } else { widget_sync_rely(k, other_id)(ex.suffix(n).head()) }) by {
        let p = widget_sync_partial_rely(k, bs, ids)(other_id);
        assert(valid(spec.implies(p)));
        assert(spec.implies(p).satisfied_by(ex));
        assert(p.satisfied_by(ex));
        if other_id == ids[b] {
            assert(is_janitor_id(bs, ids, other_id));
            let b2 = binding_at(bs, ids, other_id);
            assert(bs.contains(b2) && ids[b2] == other_id);
            assert(b2 == b);
            assert(always(lift_state(widget_janitor_guarantee(k, b2, other_id))).satisfied_by(ex));
            assert(lift_state(widget_janitor_guarantee(k, b2, other_id)).satisfied_by(ex.suffix(n)));
        } else if is_janitor_id(bs, ids, other_id) {
            // Another binding's janitor: its guarantee is stronger than the rely.
            let b2 = binding_at(bs, ids, other_id);
            assert(bs.contains(b2) && ids[b2] == other_id);
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

pub proof fn widget_sync_singleton_core_holds(k: SyncKind, bs: Set<Binding>, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, id: int, ids: Map<Binding, int>)
    requires
        cluster.registry.contains_pair(id, widget_sync_controller_spec(k, bs, spec_ok, id, ids)),
        well_formed(cluster, widget_sync_core_set(k, bs, spec_ok, id, ids)),
    ensures
        core(cluster, widget_sync_core_set(k, bs, spec_ok, id, ids)),
{
    let s = widget_sync_core_set(k, bs, spec_ok, id, ids);
    let spec = cluster_model(cluster);
    let inner = cluster.cluster;

    assert(s.members.contains(id));
    assert((cluster.registry[id].membership)(inner, id));
    assert(sync_membership_all(k, bs, spec_ok, inner, id, ids));

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
                implies spec_rde.entails(widget_sync_partial_rely(k, bs, ids)(other_id)) by {
                tla_forall_apply(R_fn, (id, other_id));
                assert(R_fn((id, other_id)) == widget_sync_partial_rely(k, bs, ids)(other_id));
                entails_trans(spec_rde, tla_forall(R_fn), R_fn((id, other_id)));
            }
            tla_forall_apply(env_fn, id);
            entails_trans(spec_rde, tla_forall(env_fn), env_fn(id));
            assert(env_fn(id) == inner_releases_terminating_objects(k, bs));
            assert(s.liveness_dependency == janitors_esr(k, bs, ids));
            entails_trans(spec_rde, spec, lift_state(inner.init()));
            entails_trans(spec_rde, spec, sync_next_with_wf(inner, id));

            let per_binding = |b: Binding| if bs.contains(b) {
                widget_spec_eventually_synced(k, b)
                    .and(widget_status_eventually_mirrored(k, b))
                    .and(widget_mirrors_stably_collected(k, b))
            } else {
                true_pred::<ClusterState>()
            };
            let dep_fn = |b: Binding| if bs.contains(b) { widget_janitor_esr(k, b, ids[b]) } else { true_pred::<ClusterState>() };
            assert forall |b: Binding| spec_rde.entails(#[trigger] per_binding(b)) by {
                if bs.contains(b) {
                    tla_forall_apply(dep_fn, b);
                    entails_trans(spec_rde, s.liveness_dependency, dep_fn(b));
                    assert(dep_fn(b) == widget_janitor_esr(k, b, ids[b]));
                    sync_rely_facts_imply_lifted_condition(k, b, bs, spec_ok, spec_rde, inner, id, ids);
                    sync_eventually_synced(k, b, bs, spec_ok, spec_rde, inner, id, ids[b]);
                    sync_eventually_mirrors_status(k, b, bs, spec_ok, spec_rde, inner, id, ids[b]);
                    sync_mirrors_stably_collected(k, b, bs, spec_ok, spec_rde, inner, id, ids[b]);
                    entails_and(spec_rde, widget_spec_eventually_synced(k, b), widget_status_eventually_mirrored(k, b));
                    entails_and(spec_rde, widget_spec_eventually_synced(k, b).and(widget_status_eventually_mirrored(k, b)), widget_mirrors_stably_collected(k, b));
                }
            }
            spec_entails_tla_forall(spec_rde, per_binding);
            assert(ESR_fn(c) == widget_sync_esr(k, bs));
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
// Composing one binding's janitor with the sync reconciler.
// ---------------------------------------------------------------------------

// The pair {janitor of `b`, sync of `k`} for a single binding: the janitor's ESR
// discharges the sync reconciler's liveness dependency, and the two guarantees
// discharge each other's relies.
//
// TODO (doc/widget_sync_fanout_design.md, section 5.1): the same statement for a
// finite set of bindings, composing the janitors one at a time. What is proved
// here is the one-binding case, which is what the deployed binary runs; the
// two-binding case is widget_two_binding_core_holds below.
pub proof fn widget_pair_core_holds(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, janitor_id: int, sync_id: int)
    requires
        cluster.registry.contains_pair(janitor_id, widget_janitor_controller_spec(k, b, Set::empty().insert(b), spec_ok, janitor_id)),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, Set::empty().insert(b), spec_ok, sync_id, Map::empty().insert(b, janitor_id))),
        janitor_id != sync_id,
        well_formed(cluster, widget_janitor_core_set(k, b, Set::empty().insert(b), spec_ok, janitor_id)),
        well_formed(cluster, widget_sync_core_set(k, Set::empty().insert(b), spec_ok, sync_id, Map::empty().insert(b, janitor_id))),
    ensures
        well_formed(cluster, union_coreset(
            widget_janitor_core_set(k, b, Set::empty().insert(b), spec_ok, janitor_id),
            widget_sync_core_set(k, Set::empty().insert(b), spec_ok, sync_id, Map::empty().insert(b, janitor_id)), true_pred())),
        core(cluster, union_coreset(
            widget_janitor_core_set(k, b, Set::empty().insert(b), spec_ok, janitor_id),
            widget_sync_core_set(k, Set::empty().insert(b), spec_ok, sync_id, Map::empty().insert(b, janitor_id)), true_pred())),
{
    let bs = Set::empty().insert(b);
    let ids = Map::empty().insert(b, janitor_id);
    let s1 = widget_janitor_core_set(k, b, bs, spec_ok, janitor_id);
    let s2 = widget_sync_core_set(k, bs, spec_ok, sync_id, ids);
    let spec = cluster_model(cluster);

    widget_janitor_singleton_core_holds(k, b, bs, spec_ok, cluster, janitor_id);
    widget_sync_singleton_core_holds(k, bs, spec_ok, cluster, sync_id, ids);

    assert(satisfies_dependency(cluster, s1, s2)) by {
        let esr_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].esr } else { true_pred::<ClusterState>() };
        let esr_s1 = tla_forall(esr_fn_s1);
        assert(s1.members.contains(janitor_id));
        tla_forall_apply(esr_fn_s1, janitor_id);
        assert(esr_fn_s1(janitor_id) == widget_janitor_esr(k, b, janitor_id));
        let dep_fn = |b2: Binding| if bs.contains(b2) { widget_janitor_esr(k, b2, ids[b2]) } else { true_pred::<ClusterState>() };
        assert forall |b2: Binding| spec.and(esr_s1).entails(#[trigger] dep_fn(b2)) by {
            if bs.contains(b2) {
                assert(b2 == b);
                assert(ids[b2] == janitor_id);
                entails_trans(spec.and(esr_s1), esr_s1, widget_janitor_esr(k, b, janitor_id));
            }
        }
        spec_entails_tla_forall(spec.and(esr_s1), dep_fn);
        assert(s2.liveness_dependency == janitors_esr(k, bs, ids));
        entails_implies(spec, esr_s1, s2.liveness_dependency);
    }

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        sync_guarantee_implies_janitor_rely(k, sync_id);
        entails_preserved_by_always(lift_state(widget_sync_guarantee(k, sync_id)), lift_state(widget_janitor_rely(k, sync_id)));

        // r_21: what the sync reconciler relies on from the janitor is the janitor's
        // guarantee itself.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                assert(pair == (sync_id, janitor_id));
                tla_forall_apply(g_fn_s1, janitor_id);
                assert(g_fn_s1(janitor_id) == always(lift_state(widget_janitor_guarantee(k, b, janitor_id))));
                assert(is_janitor_id(bs, ids, janitor_id));
                assert(binding_at(bs, ids, janitor_id) == b);
                assert(r21_fn(pair) == always(lift_state(widget_janitor_guarantee(k, b, janitor_id))));
                entails_trans(spec.and(tla_forall(g_fn_s1)), tla_forall(g_fn_s1), always(lift_state(widget_janitor_guarantee(k, b, janitor_id))));
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        // r_12: the janitor's rely on the sync reconciler follows from the sync
        // reconciler's guarantee.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                assert(pair == (janitor_id, sync_id));
                tla_forall_apply(g_fn_s2, sync_id);
                assert(g_fn_s2(sync_id) == always(lift_state(widget_sync_guarantee(k, sync_id))));
                assert(r12_fn(pair) == always(lift_state(widget_janitor_rely(k, sync_id))));
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
// A concrete configuration: one kind, one binding, two controllers.
// ---------------------------------------------------------------------------

pub open spec fn widget_kind_name() -> StringView { "widgets.anvil.dev"@ }

pub open spec fn widget_selector() -> ClusterSelector {
    ClusterSelector::Field(seq!["spec"@, "clusterName"@])
}

pub open spec fn widget_kind() -> SyncKind {
    SyncKind {
        outer_kind: model_kind(widget_kind_name(), ClusterIdView::Primary),
        name: widget_kind_name(),
        selector: widget_selector(),
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

// The two model kinds of the configuration differ, by length: a mirror kind name
// carries the binding after an '@'.
pub proof fn widget_kind_strings_distinct()
    ensures widget_kind().outer_kind != widget_inner_kind(),
{
    reveal_strlit("widgets.anvil.dev");
    reveal_strlit("@");
    reveal_strlit("/");
    reveal_strlit("default");
    reveal_strlit("inner");
    assert(widget_kind_name().len() == 17);
    assert(remote_kind_name(widget_kind_name(), widget_binding()).len()
        == widget_kind_name().len() + at_sign().len() + "default"@.len() + slash().len() + "inner"@.len());
}

pub open spec fn widget_cluster_instance() -> Cluster {
    Cluster {
        installed_types: Map::empty()
            .insert(widget_kind().outer_kind->CustomResourceKind_0, Cluster::synced_installed_type(widget_spec_ok(), widget_selector()))
            .insert(widget_inner_kind()->CustomResourceKind_0, Cluster::synced_installed_type(widget_spec_ok(), widget_selector())),
        controller_models: Map::empty()
            .insert(widget_janitor_id(), widget_janitor_controller_model(widget_kind(), widget_binding()))
            .insert(widget_sync_id(), widget_sync_controller_model(widget_kind())),
    }
}

pub open spec fn widget_core_cluster() -> CoreCluster {
    CoreCluster {
        cluster: widget_cluster_instance(),
        registry: Map::empty()
            .insert(widget_janitor_id(), widget_janitor_controller_spec(widget_kind(), widget_binding(), widget_bindings(), widget_spec_ok(), widget_janitor_id()))
            .insert(widget_sync_id(), widget_sync_controller_spec(widget_kind(), widget_bindings(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids())),
    }
}

pub open spec fn widget_core_set() -> CoreSet {
    union_coreset(
        widget_janitor_core_set(widget_kind(), widget_binding(), widget_bindings(), widget_spec_ok(), widget_janitor_id()),
        widget_sync_core_set(widget_kind(), widget_bindings(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids()),
        true_pred())
}

pub proof fn widget_core_holds()
    ensures
        well_formed(widget_core_cluster(), widget_core_set()),
        core(widget_core_cluster(), widget_core_set()),
{
    let cluster = widget_core_cluster();
    widget_kind_strings_distinct();
    assert(cluster.cluster.synced_type_is_installed(widget_kind().outer_kind, widget_spec_ok(), widget_selector()));
    assert(cluster.cluster.synced_type_is_installed(widget_inner_kind(), widget_spec_ok(), widget_selector()));
    assert(widget_bindings().contains(widget_binding()));
    assert(ids_ok(widget_bindings(), widget_janitor_ids(), widget_sync_id()));
    assert(well_formed(cluster, widget_janitor_core_set(widget_kind(), widget_binding(), widget_bindings(), widget_spec_ok(), widget_janitor_id())));
    assert(well_formed(cluster, widget_sync_core_set(widget_kind(), widget_bindings(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids())));
    widget_pair_core_holds(widget_kind(), widget_binding(), widget_spec_ok(), cluster, widget_janitor_id(), widget_sync_id());
}

}
