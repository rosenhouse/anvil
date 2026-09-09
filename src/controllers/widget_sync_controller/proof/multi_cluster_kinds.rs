// A whole deployment on the multi-store model: every configured kind's sync
// controller and janitors run in the primary cluster, each binding's inner
// cluster is one store, and R1, R2, R3, R3s and the janitor's delete soundness
// hold for every (kind, binding) of the configuration on executions of that
// (n+1)-store model (doc/widget_sync_fanout_design.md, section 5.3).
//
// The theorem is widget_multi_cluster_theorem applied once per (kind, binding).
// What it adds is the discharge of widget_cluster_with_others for the other
// controllers of the deployment: the sync controllers and janitors of every
// other kind, and the janitors of the other bindings of the same kind. Each is
// admitted by its model (which sends only requests the refinement handles and
// commutes with the relabeling) and by its guarantee, an invariant of the
// one-store model under init and next alone, which implies the pair's relies
// through the cross implications of composition::widget_two_kinds.
#![allow(unused_imports)]
use crate::composition::{widget_janitor_reconciler::*, widget_sync_reconciler::*, widget_two_kinds::*};
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::multi_cluster::{api_server::*, execution::*, fairness::*, relabel::*, steps::*};
use crate::kubernetes_cluster::proof::{composition::*, core::*, temporal_rules::*};
use crate::kubernetes_cluster::spec::{cluster::*, controller::types::*, message::*, multi_cluster::*};
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::{
    model::install::*,
    proof::{guarantee::*, liveness::spec::*, multi_cluster::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::{map_lib::*, prelude::*, set_lib::*};

verus! {

// ---------------------------------------------------------------------------
// A deployed configuration.
// ---------------------------------------------------------------------------

// A one-store cluster running exactly the controllers of a configuration: for
// every kind, its sync controller at the kind's id and one janitor per binding
// at that binding's id, with the kind installed for the outer copies and for
// every binding's mirrors. The kinds are well formed, name well-formed
// bindings, select by a spec field, are told apart by their outer kinds and
// occupy disjoint ids.
pub open spec fn kinds_deployed(setups: Map<SyncKind, KindSetup>, cluster: Cluster) -> bool {
    &&& forall |k: SyncKind| #[trigger] setups.contains_key(k) ==> {
        let c = setups[k];
        &&& sync_kind_ok(k)
        &&& bindings_ok(k)
        &&& k.selector is Field
        &&& ids_ok(k.bindings, c.janitor_ids, c.sync_id)
        &&& cluster.controller_models.contains_pair(c.sync_id, widget_sync_controller_model(k))
        &&& cluster.synced_type_is_installed(k.outer_kind, c.spec_ok, k.selector)
        &&& forall |b: Binding| #[trigger] k.bindings.contains(b) ==> {
            &&& cluster.controller_models.contains_pair(c.janitor_ids[b], widget_janitor_controller_model(k, b))
            &&& cluster.synced_type_is_installed(inner_kind(k, b), c.spec_ok, k.selector)
        }
    }
    &&& kinds_separate(setups)
    &&& cluster.controller_models.dom() == widget_kinds_core_set(setups).members
    &&& installed_types_ignore_metadata(cluster.installed_types)
    &&& installed_types_coherent(cluster.installed_types)
}

// Every binding of every configured kind is one of `bindings`, the sides of
// the multi-store cluster.
pub open spec fn bindings_cover(setups: Map<SyncKind, KindSetup>, bindings: Set<Binding>) -> bool {
    forall |k: SyncKind| #[trigger] setups.contains_key(k) ==> k.bindings.subset_of(bindings)
}

// What the theorem states for one (kind, binding): the properties of
// widget_multi_cluster_theorem, on the multi-store cluster of the deployment.
pub open spec fn kind_binding_esr(k: SyncKind, b: Binding, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int) -> bool {
    widget_multi_cluster_spec(k, b, tc, sync_id, janitor_id).entails(
        multi_cluster_spec_eventually_synced(k, b)
        .and(multi_cluster_status_eventually_mirrored(k, b))
        .and(multi_cluster_mirrors_stably_collected(k, b, tc))
        .and(multi_cluster_mirrors_eventually_collected(k, b, tc))
        .and(always(lift_state(multi_cluster_janitor_deletes_are_sound(k, b, tc, janitor_id))))
    )
}

// ---------------------------------------------------------------------------
// The other controllers of the deployment, admitted.
// ---------------------------------------------------------------------------

// The multi-store cluster of the deployment meets widget_kind_cluster_ok for
// every configured kind.
proof fn lemma_deployed_kind_cluster_ok(setups: Map<SyncKind, KindSetup>, cluster: Cluster, bindings: Set<Binding>, k: SyncKind)
    requires
        kinds_deployed(setups, cluster),
        bindings_cover(setups, bindings),
        setups.contains_key(k),
    ensures widget_kind_cluster_ok(k, widget_multi_cluster_for(cluster, bindings)),
{
    let tc = widget_multi_cluster_for(cluster, bindings);
    lemma_sides_of_bindings(bindings, k.bindings.choose());
    lemma_cluster_of_model_kind(k.name, ClusterIdView::Primary);
    assert forall |kind: Kind| tc.sides.contains(#[trigger] tc.side_of_kind(kind)) by {}
    assert forall |b: Binding| #[trigger] k.bindings.contains(b)
        implies tc.side_of_kind(inner_kind(k, b)) == ClusterIdView::Remote(b) && tc.sides.contains(ClusterIdView::Remote(b)) by {
        lemma_cluster_of_model_kind(k.name, ClusterIdView::Remote(b));
        lemma_sides_of_bindings(bindings, b);
    }
}

// The pair's one-store spec entails init and next.
proof fn lemma_pair_spec_init_next(sk: SyncKind, bnd: Binding, cluster: Cluster, sync_id: int, janitor_id: int)
    ensures ({
        let spec = widget_one_cluster_spec(sk, bnd, cluster, sync_id, janitor_id);
        &&& spec.entails(lift_state(cluster.init()))
        &&& spec.entails(always(lift_action(cluster.next())))
    }),
{
    let spec = widget_one_cluster_spec(sk, bnd, cluster, sync_id, janitor_id);
    assert(spec.entails(lift_state(cluster.init())));
    assert(spec.entails(sync_next_with_wf(cluster, sync_id)));
    assert(sync_next_with_wf(cluster, sync_id).entails(always(lift_action(cluster.next()))));
    entails_trans(spec, sync_next_with_wf(cluster, sync_id), always(lift_action(cluster.next())));
}

// The sync controller of another kind is admitted beside the pair of (sk, bnd).
proof fn lemma_other_sync_ok(setups: Map<SyncKind, KindSetup>, cluster: Cluster, bindings: Set<Binding>, sk: SyncKind, bnd: Binding, k2: SyncKind)
    requires
        kinds_deployed(setups, cluster),
        bindings_cover(setups, bindings),
        setups.contains_key(sk),
        setups.contains_key(k2),
        sk.bindings.contains(bnd),
        k2 != sk,
    ensures widget_other_controller_ok(sk, bnd, widget_multi_cluster_for(cluster, bindings), setups[sk].sync_id, setups[sk].janitor_ids[bnd], setups[k2].sync_id),
{
    let tc = widget_multi_cluster_for(cluster, bindings);
    let (sync_id, janitor_id) = (setups[sk].sync_id, setups[sk].janitor_ids[bnd]);
    let id = setups[k2].sync_id;
    let spec_ok2 = setups[k2].spec_ok;
    let m = tc.cluster.controller_models[id];
    assert(m == widget_sync_controller_model(k2));
    assert(k2.outer_kind != sk.outer_kind);
    // The model.
    assert(all_inner_kinds_installed(k2, spec_ok2, cluster));
    lemma_sync_model_ok(k2, spec_ok2, tc);
    lemma_deployed_kind_cluster_ok(setups, cluster, bindings, k2);
    lemma_widget_kinds_ok(k2, bnd);
    assert forall |r: Relabeling<ClusterIdView>| widget_relabeling(tc, r) implies #[trigger] other_model_commutes(tc, r, m) by {
        let rm = m.reconcile_model;
        let t = rm.transition;
        assert forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState|
            cr.kind == rm.kind && stored_object_ok(tc, cr)
            implies #[trigger] t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls)
                == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1)) by {
            lemma_sync_model_commutes(k2, bnd, spec_ok2, tc, r, cr, resp, ls);
        }
    }
    // The relies, from the guarantee under init and next.
    let spec = widget_one_cluster_spec(sk, bnd, cluster, sync_id, janitor_id);
    lemma_pair_spec_init_next(sk, bnd, cluster, sync_id, janitor_id);
    lemma_always_widget_sync_guarantee(spec, cluster, k2, spec_ok2, id);
    sync_guarantee_implies_other_sync_rely(k2, sk, id);
    sync_guarantee_implies_other_janitor_rely(k2, sk, id);
    always_weaken(spec, lift_state(widget_sync_guarantee(k2, id)), lift_state(widget_sync_rely(sk, id)));
    always_weaken(spec, lift_state(widget_sync_guarantee(k2, id)), lift_state(widget_janitor_rely(sk, id)));
}

// The janitor of another (kind, binding) is admitted beside the pair of (sk, bnd).
proof fn lemma_other_janitor_ok(setups: Map<SyncKind, KindSetup>, cluster: Cluster, bindings: Set<Binding>, sk: SyncKind, bnd: Binding, k2: SyncKind, b2: Binding)
    requires
        kinds_deployed(setups, cluster),
        bindings_cover(setups, bindings),
        setups.contains_key(sk),
        setups.contains_key(k2),
        sk.bindings.contains(bnd),
        k2.bindings.contains(b2),
        !(k2 == sk && b2 == bnd),
    ensures widget_other_controller_ok(sk, bnd, widget_multi_cluster_for(cluster, bindings), setups[sk].sync_id, setups[sk].janitor_ids[bnd], setups[k2].janitor_ids[b2]),
{
    let tc = widget_multi_cluster_for(cluster, bindings);
    let (sync_id, janitor_id) = (setups[sk].sync_id, setups[sk].janitor_ids[bnd]);
    let id = setups[k2].janitor_ids[b2];
    let spec_ok2 = setups[k2].spec_ok;
    let m = tc.cluster.controller_models[id];
    assert(m == widget_janitor_controller_model(k2, b2));
    // The model.
    lemma_janitor_model_ok(k2, b2, tc);
    lemma_deployed_kind_cluster_ok(setups, cluster, bindings, k2);
    lemma_widget_kinds_ok(k2, b2);
    assert(widget_multi_cluster_ok(k2, b2, tc));
    assert forall |r: Relabeling<ClusterIdView>| widget_relabeling(tc, r) implies #[trigger] other_model_commutes(tc, r, m) by {
        let rm = m.reconcile_model;
        let t = rm.transition;
        assert forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState|
            cr.kind == rm.kind && stored_object_ok(tc, cr)
            implies #[trigger] t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls)
                == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1)) by {
            lemma_janitor_model_commutes(k2, b2, spec_ok2, tc, r, cr, resp, ls);
        }
    }
    // The relies, from the guarantee under init and next.
    let spec = widget_one_cluster_spec(sk, bnd, cluster, sync_id, janitor_id);
    lemma_pair_spec_init_next(sk, bnd, cluster, sync_id, janitor_id);
    lemma_always_widget_janitor_guarantee(spec, cluster, k2, b2, spec_ok2, id);
    if k2 == sk {
        janitor_guarantee_implies_sync_rely(sk, b2, id);
        janitor_guarantee_implies_janitor_rely(sk, b2, id);
    } else {
        janitor_guarantee_implies_other_relies(k2, b2, sk, id);
    }
    always_weaken(spec, lift_state(widget_janitor_guarantee(k2, b2, id)), lift_state(widget_sync_rely(sk, id)));
    always_weaken(spec, lift_state(widget_janitor_guarantee(k2, b2, id)), lift_state(widget_janitor_rely(sk, id)));
}

// The deployment, read from the pair of (sk, bnd): a cluster running the pair
// beside controllers the pair's relies hold of.
proof fn lemma_deployed_is_cluster_with_others(setups: Map<SyncKind, KindSetup>, cluster: Cluster, bindings: Set<Binding>, sk: SyncKind, bnd: Binding)
    requires
        kinds_deployed(setups, cluster),
        bindings_cover(setups, bindings),
        setups.contains_key(sk),
        sk.bindings.contains(bnd),
    ensures widget_cluster_with_others(sk, bnd, setups[sk].spec_ok, widget_multi_cluster_for(cluster, bindings), setups[sk].sync_id, setups[sk].janitor_ids[bnd]),
{
    broadcast use Set::lemma_map_contains;
    let tc = widget_multi_cluster_for(cluster, bindings);
    let c = setups[sk];
    let (sync_id, janitor_id) = (c.sync_id, c.janitor_ids[bnd]);
    lemma_kinds_core_set_members(setups);
    assert(sync_membership(sk, bnd, c.spec_ok, cluster, sync_id, janitor_id));
    assert forall |id: int| #[trigger] cluster.controller_models.contains_key(id) && id != sync_id && id != janitor_id
        implies widget_other_controller_ok(sk, bnd, tc, sync_id, janitor_id, id) by {
        let k2 = choose |k2: SyncKind| setups.contains_key(k2) && #[trigger] widget_ids_of(k2, setups[k2].janitor_ids, setups[k2].sync_id).contains(id);
        let c2 = setups[k2];
        if id == c2.sync_id {
            assert(k2 != sk);
            lemma_other_sync_ok(setups, cluster, bindings, sk, bnd, k2);
        } else {
            lemma_janitor_id_is_a_binding(k2.bindings, k2.bindings, c2.janitor_ids, c2.sync_id, id);
            let b2 = binding_at(k2.bindings, c2.janitor_ids, id);
            assert(k2.bindings.contains(b2) && c2.janitor_ids[b2] == id);
            assert(!(k2 == sk && b2 == bnd));
            lemma_other_janitor_ok(setups, cluster, bindings, sk, bnd, k2, b2);
        }
    }
}

// ---------------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------------

// For ANY deployment: R1, R2, R3, R3s and the janitor's delete soundness hold
// for every (kind, binding), on executions of the multi-store model with one
// store per binding of the deployment. Each pair is read under its own spec, so
// this is a family of statements about one model, not one statement about one
// execution. Nothing here names a kind or a binding.
pub proof fn widget_kinds_multi_cluster_theorem(setups: Map<SyncKind, KindSetup>, cluster: Cluster, bindings: Set<Binding>)
    requires
        kinds_deployed(setups, cluster),
        bindings_cover(setups, bindings),
    ensures forall |k: SyncKind, b: Binding| setups.contains_key(k) && k.bindings.contains(b)
        ==> #[trigger] kind_binding_esr(k, b, widget_multi_cluster_for(cluster, bindings), setups[k].sync_id, setups[k].janitor_ids[b]),
{
    let tc = widget_multi_cluster_for(cluster, bindings);
    assert forall |k: SyncKind, b: Binding| setups.contains_key(k) && k.bindings.contains(b)
        implies #[trigger] kind_binding_esr(k, b, tc, setups[k].sync_id, setups[k].janitor_ids[b]) by {
        let c = setups[k];
        lemma_widget_multi_cluster_ok(k, b, cluster, bindings);
        lemma_deployed_is_cluster_with_others(setups, cluster, bindings, k, b);
        widget_multi_cluster_theorem(k, b, c.spec_ok, tc, c.sync_id, c.janitor_ids[b]);
    }
}

// ---------------------------------------------------------------------------
// The demo: one kind served for two bindings.
// ---------------------------------------------------------------------------

// The fan-out demo (composition::widget_sync_reconciler::widget_fanout_kind):
// one kind, two bindings, three controllers. There is no two-kind instance: the
// second kind of the demo deployment, Gadget, selects its cluster by
// `metadata.name`, which kinds_deployed's field selector rules out
// (doc/widget_sync_fanout_design.md, section 5.2).
pub open spec fn widget_fanout_setups() -> Map<SyncKind, KindSetup> {
    Map::<SyncKind, KindSetup>::empty().insert(widget_fanout_kind(), KindSetup {
        spec_ok: widget_spec_ok(),
        sync_id: widget_sync_id(),
        janitor_ids: widget_fanout_janitor_ids(),
    })
}

pub open spec fn widget_fanout_cluster_instance() -> Cluster {
    widget_cluster_for(widget_fanout_kind(), widget_spec_ok(), widget_sync_id(), widget_fanout_janitor_ids())
}

// A one-kind deployment from the cluster composition::widget_sync_reconciler builds for a kind.
proof fn lemma_one_kind_deployed(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>)
    requires
        sync_kind_ok(k),
        bindings_ok(k),
        k.selector is Field,
        ids_ok(k.bindings, ids, sync_id),
    ensures kinds_deployed(
        Map::<SyncKind, KindSetup>::empty().insert(k, KindSetup { spec_ok: spec_ok, sync_id: sync_id, janitor_ids: ids }),
        widget_cluster_for(k, spec_ok, sync_id, ids)),
{
    broadcast use Set::lemma_map_contains;
    let setups = Map::<SyncKind, KindSetup>::empty().insert(k, KindSetup { spec_ok: spec_ok, sync_id: sync_id, janitor_ids: ids });
    let cluster = widget_cluster_for(k, spec_ok, sync_id, ids);
    lemma_widget_cluster_for_models(k, spec_ok, sync_id, ids);
    lemma_widget_types(k, spec_ok, cluster);
    lemma_kinds_core_set_members(setups);
    lemma_widget_core_set_members(k, sync_id, ids);
    assert(setups.dom() =~= Set::<SyncKind>::empty().insert(k));
    assert forall |id: int| cluster.controller_models.dom().contains(id) <==> widget_kinds_core_set(setups).members.contains(id) by {
        if cluster.controller_models.dom().contains(id) {
            assert(widget_ids_of(k, ids, sync_id).contains(id));
        }
        if widget_kinds_core_set(setups).members.contains(id) {
            let k2 = choose |k2: SyncKind| setups.contains_key(k2) && #[trigger] widget_ids_of(k2, setups[k2].janitor_ids, setups[k2].sync_id).contains(id);
            assert(k2 == k);
        }
    }
    assert(cluster.controller_models.dom() =~= widget_kinds_core_set(setups).members);
    assert(kinds_separate(setups)) by {
        assert forall |k1: SyncKind, k2: SyncKind| #![trigger setups[k1], setups[k2]]
            setups.contains_key(k1) && setups.contains_key(k2) && k1 != k2 implies false by {}
    }
}

// The fan-out demo is one application of the theorem: R1 to R3s and delete
// soundness for both bindings of the kind, on the three-store model.
pub proof fn widget_fanout_demo_multi_cluster_theorem()
    ensures forall |b: Binding| #[trigger] widget_fanout_bindings().contains(b)
        ==> kind_binding_esr(widget_fanout_kind(), b, widget_multi_cluster_for(widget_fanout_cluster_instance(), widget_fanout_bindings()), widget_sync_id(), widget_fanout_janitor_ids()[b]),
{
    widget_fanout_config_ok();
    widget_fanout_bindings_distinct();
    let k = widget_fanout_kind();
    let setups = widget_fanout_setups();
    assert(k.bindings =~= widget_fanout_bindings());
    assert(ids_ok(k.bindings, widget_fanout_janitor_ids(), widget_sync_id())) by {
        let ids = widget_fanout_janitor_ids();
        assert forall |x: Binding, y: Binding| #![trigger ids[x], ids[y]]
            k.bindings.contains(x) && k.bindings.contains(y) && ids[x] == ids[y] implies x == y by {
            assert(x == widget_binding() || x == widget_binding_two());
            assert(y == widget_binding() || y == widget_binding_two());
        }
    }
    lemma_one_kind_deployed(k, widget_spec_ok(), widget_sync_id(), widget_fanout_janitor_ids());
    assert(bindings_cover(setups, widget_fanout_bindings()));
    widget_kinds_multi_cluster_theorem(setups, widget_fanout_cluster_instance(), widget_fanout_bindings());
    assert forall |b: Binding| #[trigger] widget_fanout_bindings().contains(b)
        implies kind_binding_esr(k, b, widget_multi_cluster_for(widget_fanout_cluster_instance(), widget_fanout_bindings()), widget_sync_id(), widget_fanout_janitor_ids()[b]) by {
        assert(setups.contains_key(k) && k.bindings.contains(b));
        assert(setups[k].sync_id == widget_sync_id() && setups[k].janitor_ids == widget_fanout_janitor_ids());
    }
}

}
