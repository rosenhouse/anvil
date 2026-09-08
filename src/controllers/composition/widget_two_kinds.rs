// Two configured kinds beside each other: the sync controller and janitors of
// `k1` composed with those of `k2` (doc/widget_sync_fanout_design.md,
// section 5.1).
//
// The whole argument is kind disjointness. A sync controller only ever touches
// its own outer kind (a status patch) and its own mirror kinds (a Get, a Create,
// a spec patch); a janitor only lists its own outer kind and deletes its own
// mirror. So each side's guarantee already says that it never writes an object of
// the other's kinds, which is what the other's relies ask of every other
// controller. lemma_kinds_of_distinct_configurations is where that disjointness
// comes from: from `k1.outer_kind != k2.outer_kind` and `sync_kind_ok` of both,
// through the injectivity of model_kind -- and it covers *every* binding, not
// only the configured ones, because the relies quantify over is_inner_kind.
use crate::composition::widget_janitor_reconciler::*;
use crate::composition::widget_sync_reconciler::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::core::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::model::install::*;
use crate::widget_sync_controller::proof::liveness::spec::*;
use crate::widget_sync_controller::trusted::{rely_guarantee::*, spec_types::*};
use verus_temporal_logic::defs::*;
use verus_temporal_logic::rules::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

// ---------------------------------------------------------------------------
// The four cross implications.
// ---------------------------------------------------------------------------

// The sync controller of `k1` meets the sync rely of `k2`: it creates only
// mirrors of `k1`, patches the status of `k1`'s outer copies only, and sends no
// Update at all.
pub proof fn sync_guarantee_implies_other_sync_rely(k1: SyncKind, k2: SyncKind, id: int)
    requires sync_kind_ok(k1), sync_kind_ok(k2), k1.outer_kind != k2.outer_kind,
    ensures lift_state(widget_sync_guarantee(k1, id)).entails(lift_state(widget_sync_rely(k2, id))),
{
    lemma_kinds_of_distinct_configurations(k1, k2);
    assert forall |s: ClusterState| #[trigger] widget_sync_guarantee(k1, id)(s) implies widget_sync_rely(k2, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => !is_inner_kind(k2, req.obj.kind),
                APIRequest::UpdateRequest(req) => mirror_update_req(k2, req)(s),
                APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(k2, req)(s),
                APIRequest::PatchRequest(_) => true,
                APIRequest::UpdateStatusRequest(req) => req.obj.kind != k2.outer_kind,
                APIRequest::GetThenUpdateStatusRequest(req) => req.obj.kind != k2.outer_kind,
                APIRequest::PatchStatusRequest(req) => req.kind != k2.outer_kind,
                _ => true,
            }) by {
            let outer_key = msg.src->Controller_1;
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => {
                    assert(mirror_create_req(k1, req, outer_key)(s));
                    let outer = choose |outer: SyncedObjectView| {
                        &&& outer.kind == k1.outer_kind
                        &&& outer.object_ref() == outer_key
                        &&& outer.metadata.uid is Some
                        &&& cluster_of(k1.selector, outer) is Some
                        &&& req.namespace == outer_key.namespace
                        &&& req.obj == #[trigger] marshal(make_inner(k1, outer))
                        &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s)
                    };
                    assert(req.obj.kind == inner_kind(k1, binding_of(k1, outer)));
                    assert(!is_inner_kind(k2, inner_kind(k1, binding_of(k1, outer))));
                }
                _ => {}
            }
        }
    }
}

// The sync controller of `k1` meets the janitor rely of `k2`: the only Creates it
// sends are of `k1`'s mirror kinds, which are none of `k2`'s.
pub proof fn sync_guarantee_implies_other_janitor_rely(k1: SyncKind, k2: SyncKind, id: int)
    requires sync_kind_ok(k1), sync_kind_ok(k2), k1.outer_kind != k2.outer_kind,
    ensures lift_state(widget_sync_guarantee(k1, id)).entails(lift_state(widget_janitor_rely(k2, id))),
{
    lemma_kinds_of_distinct_configurations(k1, k2);
    assert forall |s: ClusterState| #[trigger] widget_sync_guarantee(k1, id)(s) implies widget_janitor_rely(k2, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => is_inner_kind(k2, req.obj.kind) ==> {
                    &&& req.obj.metadata.name is Some
                    &&& mirror_create_req(k2, req, ObjectRef {
                        kind: k2.outer_kind,
                        namespace: req.namespace,
                        name: req.obj.metadata.name->0,
                    })(s)
                },
                APIRequest::UpdateRequest(req) => mirror_update_req(k2, req)(s),
                APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(k2, req)(s),
                _ => true,
            }) by {
            let outer_key = msg.src->Controller_1;
            match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => {
                    assert(mirror_create_req(k1, req, outer_key)(s));
                    let outer = choose |outer: SyncedObjectView| {
                        &&& outer.kind == k1.outer_kind
                        &&& outer.object_ref() == outer_key
                        &&& outer.metadata.uid is Some
                        &&& cluster_of(k1.selector, outer) is Some
                        &&& req.namespace == outer_key.namespace
                        &&& req.obj == #[trigger] marshal(make_inner(k1, outer))
                        &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, outer_key)(s)
                    };
                    assert(req.obj.kind == inner_kind(k1, binding_of(k1, outer)));
                    assert(!is_inner_kind(k2, inner_kind(k1, binding_of(k1, outer))));
                }
                _ => {}
            }
        }
    }
}

// A janitor of `k1` meets both relies of `k2`: it sends only Lists and Deletes,
// which neither rely constrains, whatever kind they name.
pub proof fn janitor_guarantee_implies_other_relies(k1: SyncKind, b: Binding, k2: SyncKind, id: int)
    ensures
        lift_state(widget_janitor_guarantee(k1, b, id)).entails(lift_state(widget_sync_rely(k2, id))),
        lift_state(widget_janitor_guarantee(k1, b, id)).entails(lift_state(widget_janitor_rely(k2, id))),
{
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(k1, b, id)(s) implies widget_sync_rely(k2, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => !is_inner_kind(k2, req.obj.kind),
                APIRequest::UpdateRequest(req) => mirror_update_req(k2, req)(s),
                APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(k2, req)(s),
                APIRequest::PatchRequest(_) => true,
                APIRequest::UpdateStatusRequest(req) => req.obj.kind != k2.outer_kind,
                APIRequest::GetThenUpdateStatusRequest(req) => req.obj.kind != k2.outer_kind,
                APIRequest::PatchStatusRequest(req) => req.kind != k2.outer_kind,
                _ => true,
            }) by {
            match msg.content->APIRequest_0 {
                APIRequest::ListRequest(_) => {},
                APIRequest::DeleteRequest(_) => {},
                _ => { assert(false); },
            }
        }
    }
    assert forall |s: ClusterState| #[trigger] widget_janitor_guarantee(k1, b, id)(s) implies widget_janitor_rely(k2, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies (match msg.content->APIRequest_0 {
                APIRequest::CreateRequest(req) => is_inner_kind(k2, req.obj.kind) ==> {
                    &&& req.obj.metadata.name is Some
                    &&& mirror_create_req(k2, req, ObjectRef {
                        kind: k2.outer_kind,
                        namespace: req.namespace,
                        name: req.obj.metadata.name->0,
                    })(s)
                },
                APIRequest::UpdateRequest(req) => mirror_update_req(k2, req)(s),
                APIRequest::GetThenUpdateRequest(req) => mirror_get_then_update_req(k2, req)(s),
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

// ---------------------------------------------------------------------------
// The two-kind composition.
// ---------------------------------------------------------------------------

// The ids one configuration occupies: its sync controller's and its janitors'.
pub open spec fn widget_ids_of(k: SyncKind, ids: Map<Binding, int>, sync_id: int) -> Set<int> {
    janitor_ids_of(k.bindings, ids).insert(sync_id)
}

// The guarantee registered at a member id of one configuration's core set, read
// off the registry: the sync controller's, or the janitor of the binding whose id
// it is.
proof fn lemma_member_guarantee(k: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, ids: Map<Binding, int>, sync_id: int, id: int)
    requires
        ids_ok(k.bindings, ids, sync_id),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, ids)),
        janitors_registered(k, spec_ok, cluster, ids),
        widget_core_set_for(k, spec_ok, sync_id, ids).members.contains(id),
    ensures
        id == sync_id ==> cluster.registry[id].safety_guarantee == always(lift_state(widget_sync_guarantee(k, id))),
        id != sync_id ==> {
            &&& k.bindings.contains(binding_at(k.bindings, ids, id))
            &&& ids[binding_at(k.bindings, ids, id)] == id
            &&& cluster.registry[id].safety_guarantee == always(lift_state(widget_janitor_guarantee(k, binding_at(k.bindings, ids, id), id)))
        },
{
    broadcast use Set::lemma_map_contains;
    if id != sync_id {
        lemma_janitor_id_is_a_binding(k.bindings, k.bindings, ids, sync_id, id);
    }
}

// The partial rely one configuration's member id places on an id outside the
// configuration: the sync controller's rely, or a janitor's.
proof fn lemma_member_rely(k: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, ids: Map<Binding, int>, sync_id: int, id: int, other: int)
    requires
        ids_ok(k.bindings, ids, sync_id),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, ids)),
        janitors_registered(k, spec_ok, cluster, ids),
        widget_core_set_for(k, spec_ok, sync_id, ids).members.contains(id),
        !widget_core_set_for(k, spec_ok, sync_id, ids).members.contains(other),
    ensures
        id == sync_id ==> (cluster.registry[id].safety_partial_rely)(other) == always(lift_state(widget_sync_rely(k, other))),
        id != sync_id ==> (cluster.registry[id].safety_partial_rely)(other) == always(lift_state(widget_janitor_rely(k, other))),
{
    broadcast use Set::lemma_map_contains;
    if id == sync_id {
        assert(!is_janitor_id(k.bindings, ids, other)) by {
            if is_janitor_id(k.bindings, ids, other) {
                let b = binding_at(k.bindings, ids, other);
                lemma_binding_id_is_a_member(k.bindings, k.bindings, ids, sync_id, b);
            }
        }
    } else {
        lemma_janitor_id_is_a_binding(k.bindings, k.bindings, ids, sync_id, id);
    }
}

// Two configured kinds compose: each side's core set stays a core set beside the
// other's. Neither side depends on the other for liveness -- widget_core_set_for
// has no liveness dependency left, the janitors' ESRs having discharged the sync
// controller's inside each side -- so this is plain `compose`, and all it needs is
// that the two guarantees imply each other's relies.
pub proof fn widget_two_kind_core_holds(
    k1: SyncKind, spec_ok1: spec_fn(Value) -> bool, sync1: int, ids1: Map<Binding, int>,
    k2: SyncKind, spec_ok2: spec_fn(Value) -> bool, sync2: int, ids2: Map<Binding, int>,
    cluster: CoreCluster)
    requires
        sync_kind_ok(k1),
        sync_kind_ok(k2),
        k1.outer_kind != k2.outer_kind,
        ids_ok(k1.bindings, ids1, sync1),
        ids_ok(k2.bindings, ids2, sync2),
        widget_ids_of(k1, ids1, sync1).disjoint(widget_ids_of(k2, ids2, sync2)),
        cluster.registry.contains_pair(sync1, widget_sync_controller_spec(k1, spec_ok1, sync1, ids1)),
        janitors_registered(k1, spec_ok1, cluster, ids1),
        (widget_sync_controller_spec(k1, spec_ok1, sync1, ids1).membership)(cluster.cluster, sync1),
        cluster.registry.contains_pair(sync2, widget_sync_controller_spec(k2, spec_ok2, sync2, ids2)),
        janitors_registered(k2, spec_ok2, cluster, ids2),
        (widget_sync_controller_spec(k2, spec_ok2, sync2, ids2).membership)(cluster.cluster, sync2),
    ensures
        well_formed(cluster, union_coreset(
            widget_core_set_for(k1, spec_ok1, sync1, ids1),
            widget_core_set_for(k2, spec_ok2, sync2, ids2), true_pred())),
        core(cluster, union_coreset(
            widget_core_set_for(k1, spec_ok1, sync1, ids1),
            widget_core_set_for(k2, spec_ok2, sync2, ids2), true_pred())),
{
    broadcast use Set::lemma_map_contains;
    let s1 = widget_core_set_for(k1, spec_ok1, sync1, ids1);
    let s2 = widget_core_set_for(k2, spec_ok2, sync2, ids2);
    let spec = cluster_model(cluster);

    widget_fanout_core_holds(k1, spec_ok1, cluster, ids1, sync1);
    widget_fanout_core_holds(k2, spec_ok2, cluster, ids2, sync2);
    assert(s1.members =~= widget_ids_of(k1, ids1, sync1));
    assert(s2.members =~= widget_ids_of(k2, ids2, sync2));

    assert(compatible(cluster, s1, s2)) by {
        let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
        let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
        let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

        // What `k2`'s controllers rely on of one of `k1`'s is what that one guarantees.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
            if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                let spec_g1 = spec.and(tla_forall(g_fn_s1));
                lemma_member_rely(k2, spec_ok2, cluster, ids2, sync2, pair.0, pair.1);
                lemma_member_guarantee(k1, spec_ok1, cluster, ids1, sync1, pair.1);
                tla_forall_apply(g_fn_s1, pair.1);
                if pair.1 == sync1 {
                    sync_guarantee_implies_other_sync_rely(k1, k2, pair.1);
                    sync_guarantee_implies_other_janitor_rely(k1, k2, pair.1);
                    entails_preserved_by_always(lift_state(widget_sync_guarantee(k1, pair.1)), lift_state(widget_sync_rely(k2, pair.1)));
                    entails_preserved_by_always(lift_state(widget_sync_guarantee(k1, pair.1)), lift_state(widget_janitor_rely(k2, pair.1)));
                    entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(widget_sync_guarantee(k1, pair.1))));
                    entails_trans(spec_g1, always(lift_state(widget_sync_guarantee(k1, pair.1))), always(lift_state(widget_sync_rely(k2, pair.1))));
                    entails_trans(spec_g1, always(lift_state(widget_sync_guarantee(k1, pair.1))), always(lift_state(widget_janitor_rely(k2, pair.1))));
                } else {
                    let b1 = binding_at(k1.bindings, ids1, pair.1);
                    janitor_guarantee_implies_other_relies(k1, b1, k2, pair.1);
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k1, b1, pair.1)), lift_state(widget_sync_rely(k2, pair.1)));
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k1, b1, pair.1)), lift_state(widget_janitor_rely(k2, pair.1)));
                    entails_trans(spec_g1, tla_forall(g_fn_s1), always(lift_state(widget_janitor_guarantee(k1, b1, pair.1))));
                    entails_trans(spec_g1, always(lift_state(widget_janitor_guarantee(k1, b1, pair.1))), always(lift_state(widget_sync_rely(k2, pair.1))));
                    entails_trans(spec_g1, always(lift_state(widget_janitor_guarantee(k1, b1, pair.1))), always(lift_state(widget_janitor_rely(k2, pair.1))));
                }
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
        entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

        // And the other way round.
        assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
            if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                let spec_g2 = spec.and(tla_forall(g_fn_s2));
                lemma_member_rely(k1, spec_ok1, cluster, ids1, sync1, pair.0, pair.1);
                lemma_member_guarantee(k2, spec_ok2, cluster, ids2, sync2, pair.1);
                tla_forall_apply(g_fn_s2, pair.1);
                if pair.1 == sync2 {
                    sync_guarantee_implies_other_sync_rely(k2, k1, pair.1);
                    sync_guarantee_implies_other_janitor_rely(k2, k1, pair.1);
                    entails_preserved_by_always(lift_state(widget_sync_guarantee(k2, pair.1)), lift_state(widget_sync_rely(k1, pair.1)));
                    entails_preserved_by_always(lift_state(widget_sync_guarantee(k2, pair.1)), lift_state(widget_janitor_rely(k1, pair.1)));
                    entails_trans(spec_g2, tla_forall(g_fn_s2), always(lift_state(widget_sync_guarantee(k2, pair.1))));
                    entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(k2, pair.1))), always(lift_state(widget_sync_rely(k1, pair.1))));
                    entails_trans(spec_g2, always(lift_state(widget_sync_guarantee(k2, pair.1))), always(lift_state(widget_janitor_rely(k1, pair.1))));
                } else {
                    let b2 = binding_at(k2.bindings, ids2, pair.1);
                    janitor_guarantee_implies_other_relies(k2, b2, k1, pair.1);
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k2, b2, pair.1)), lift_state(widget_sync_rely(k1, pair.1)));
                    entails_preserved_by_always(lift_state(widget_janitor_guarantee(k2, b2, pair.1)), lift_state(widget_janitor_rely(k1, pair.1)));
                    entails_trans(spec_g2, tla_forall(g_fn_s2), always(lift_state(widget_janitor_guarantee(k2, b2, pair.1))));
                    entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(k2, b2, pair.1))), always(lift_state(widget_sync_rely(k1, pair.1))));
                    entails_trans(spec_g2, always(lift_state(widget_janitor_guarantee(k2, b2, pair.1))), always(lift_state(widget_janitor_rely(k1, pair.1))));
                }
            }
        }
        spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
        entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));
        entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
    }

    compose(cluster, s1, s2);
}

// ---------------------------------------------------------------------------
// The demo: Widget beside Gadget.
// ---------------------------------------------------------------------------

// A second configured kind of the demo deployment: a different CRD, a different
// selector, the same binding (doc/widget_sync_fanout_design.md, section 4).
pub open spec fn gadget_kind_name() -> StringView { "gadgets.anvil.dev"@ }

pub open spec fn gadget_kind() -> SyncKind {
    SyncKind {
        outer_kind: model_kind(gadget_kind_name(), ClusterIdView::Primary),
        name: gadget_kind_name(),
        selector: ClusterSelector::Name,
        bindings: widget_bindings(),
    }
}

pub open spec fn gadget_janitor_id() -> int { 5 }
pub open spec fn gadget_sync_id() -> int { 6 }

pub open spec fn gadget_janitor_ids() -> Map<Binding, int> {
    Map::empty().insert(widget_binding(), gadget_janitor_id())
}

// The two configurations' literals meet the hypotheses, and the two outer kinds
// differ. This is the only place the demo's kind names are read.
pub proof fn two_kind_demo_config_ok()
    ensures
        sync_kind_ok(gadget_kind()),
        forall |b: Binding| #[trigger] gadget_kind().bindings.contains(b) ==> binding_ok(b),
        ids_ok(gadget_kind().bindings, gadget_janitor_ids(), gadget_sync_id()),
        widget_kind().outer_kind != gadget_kind().outer_kind,
{
    reveal_strlit("widgets.anvil.dev");
    reveal_strlit("gadgets.anvil.dev");
    reveal_strlit("default");
    reveal_strlit("inner");
    widget_demo_config_ok();
    assert(gadget_kind().bindings =~= widget_bindings());
    assert forall |b: Binding| #[trigger] gadget_kind().bindings.contains(b) implies binding_ok(b) by {
        assert(b == widget_binding());
    }
    assert(ids_ok(gadget_kind().bindings, gadget_janitor_ids(), gadget_sync_id())) by {
        let ids = gadget_janitor_ids();
        assert forall |x: Binding, y: Binding| #![trigger ids[x], ids[y]]
            gadget_kind().bindings.contains(x) && gadget_kind().bindings.contains(y) && ids[x] == ids[y]
            implies x == y by {
            assert(x == widget_binding() && y == widget_binding());
        }
    }
    assert(widget_kind_name()[0] != gadget_kind_name()[0]);
}

// The cluster of the two configurations: the union of the two clusters of
// composition::widget_sync_reconciler, which is well defined because the two
// occupy disjoint kinds and disjoint ids.
pub open spec fn two_kind_cluster_instance() -> Cluster {
    Cluster {
        installed_types: widget_installed_types(widget_kind(), widget_spec_ok())
            .union_prefer_right(widget_installed_types(gadget_kind(), widget_spec_ok())),
        controller_models: widget_cluster_for(widget_kind(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids()).controller_models
            .union_prefer_right(widget_cluster_for(gadget_kind(), widget_spec_ok(), gadget_sync_id(), gadget_janitor_ids()).controller_models),
    }
}

pub open spec fn two_kind_core_cluster() -> CoreCluster {
    CoreCluster {
        cluster: two_kind_cluster_instance(),
        registry: widget_core_cluster_for(widget_kind(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids()).registry
            .union_prefer_right(widget_core_cluster_for(gadget_kind(), widget_spec_ok(), gadget_sync_id(), gadget_janitor_ids()).registry),
    }
}

pub open spec fn two_kind_core_set() -> CoreSet {
    union_coreset(
        widget_core_set_for(widget_kind(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids()),
        widget_core_set_for(gadget_kind(), widget_spec_ok(), gadget_sync_id(), gadget_janitor_ids()),
        true_pred())
}

// Neither configuration's kinds or ids fall in the other's map, so each survives
// the union and every lookup resolves to the configuration it came from.
proof fn lemma_two_kind_cluster_lookups()
    ensures
        two_kind_cluster_instance().installed_types
            == widget_installed_types(widget_kind(), widget_spec_ok())
                .union_prefer_right(widget_installed_types(gadget_kind(), widget_spec_ok())),
        forall |name: StringView| #[trigger] widget_installed_types(widget_kind(), widget_spec_ok()).contains_key(name)
            ==> !widget_installed_types(gadget_kind(), widget_spec_ok()).contains_key(name),
        forall |id: int| #[trigger] widget_ids_of(widget_kind(), widget_janitor_ids(), widget_sync_id()).contains(id)
            ==> !widget_ids_of(gadget_kind(), gadget_janitor_ids(), gadget_sync_id()).contains(id),
{
    broadcast use Set::lemma_map_contains;
    two_kind_demo_config_ok();
    widget_demo_config_ok();
    lemma_kinds_of_distinct_configurations(widget_kind(), gadget_kind());
    lemma_widget_installed_types(widget_kind(), widget_spec_ok());
    lemma_widget_installed_types(gadget_kind(), widget_spec_ok());
    // The names: the CRD names differ, a mirror name is never a CRD name, and two
    // mirror names of different CRDs differ.
    assert forall |name: StringView| #[trigger] widget_installed_types(widget_kind(), widget_spec_ok()).contains_key(name)
        implies !widget_installed_types(gadget_kind(), widget_spec_ok()).contains_key(name) by {
        let f1 = |b: Binding| remote_kind_name(widget_kind_name(), b);
        let f2 = |b: Binding| remote_kind_name(gadget_kind_name(), b);
        if widget_installed_types(gadget_kind(), widget_spec_ok()).contains_key(name) {
            if name == widget_kind_name() {
                if name == gadget_kind_name() {
                    assert(false);
                } else {
                    let b2 = choose |b2: Binding| gadget_kind().bindings.contains(b2) && name == f2(b2);
                    lemma_remote_kind_name_is_not_primary(widget_kind_name(), gadget_kind_name(), b2);
                }
            } else {
                let b1 = choose |b1: Binding| widget_kind().bindings.contains(b1) && name == f1(b1);
                if name == gadget_kind_name() {
                    lemma_remote_kind_name_is_not_primary(gadget_kind_name(), widget_kind_name(), b1);
                } else {
                    let b2 = choose |b2: Binding| gadget_kind().bindings.contains(b2) && name == f2(b2);
                    lemma_remote_kind_names_of_distinct_kinds(widget_kind_name(), gadget_kind_name(), b1, b2);
                }
            }
        }
    }
    // The ids: {1, 2} and {5, 6}.
    assert(janitor_ids_of(widget_kind().bindings, widget_janitor_ids()) =~= Set::<int>::empty().insert(widget_janitor_id())) by {
        assert forall |i: int| janitor_ids_of(widget_kind().bindings, widget_janitor_ids()).contains(i) implies i == widget_janitor_id() by {
            let f = |b: Binding| widget_janitor_ids()[b];
            let b = choose |b: Binding| widget_kind().bindings.contains(b) && i == f(b);
            assert(b == widget_binding());
        }
        assert(widget_kind().bindings.contains(widget_binding()));
    }
    assert(janitor_ids_of(gadget_kind().bindings, gadget_janitor_ids()) =~= Set::<int>::empty().insert(gadget_janitor_id())) by {
        assert forall |i: int| janitor_ids_of(gadget_kind().bindings, gadget_janitor_ids()).contains(i) implies i == gadget_janitor_id() by {
            let f = |b: Binding| gadget_janitor_ids()[b];
            let b = choose |b: Binding| gadget_kind().bindings.contains(b) && i == f(b);
            assert(b == widget_binding());
        }
        assert(gadget_kind().bindings.contains(widget_binding()));
    }
}

// The registration facts of one configuration survive the union with the other.
proof fn lemma_two_kind_registered(k: SyncKind, spec_ok: spec_fn(Value) -> bool, sync_id: int, ids: Map<Binding, int>, other: CoreCluster, cluster: CoreCluster)
    requires
        sync_kind_ok(k),
        ids_ok(k.bindings, ids, sync_id),
        cluster.cluster.installed_types == widget_installed_types(k, spec_ok).union_prefer_right(other.cluster.installed_types),
        cluster.cluster.controller_models == widget_cluster_for(k, spec_ok, sync_id, ids).controller_models
            .union_prefer_right(other.cluster.controller_models),
        cluster.registry == widget_core_cluster_for(k, spec_ok, sync_id, ids).registry.union_prefer_right(other.registry),
        other.cluster.controller_models.dom() == other.registry.dom(),
        forall |name: StringView| #[trigger] widget_installed_types(k, spec_ok).contains_key(name)
            ==> !other.cluster.installed_types.contains_key(name),
        forall |id: int| #[trigger] widget_ids_of(k, ids, sync_id).contains(id) ==> !other.registry.contains_key(id),
    ensures
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, ids)),
        janitors_registered(k, spec_ok, cluster, ids),
        (widget_sync_controller_spec(k, spec_ok, sync_id, ids).membership)(cluster.cluster, sync_id),
{
    broadcast use Set::lemma_map_contains;
    let alone = widget_core_cluster_for(k, spec_ok, sync_id, ids);
    lemma_widget_installed_types(k, spec_ok);
    lemma_widget_types_installed(k, spec_ok, alone.cluster);
    lemma_widget_cluster_for_models(k, spec_ok, sync_id, ids);
    // The kinds of `k` keep their installed types.
    assert(cluster.cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector));
    assert forall |b: Binding| #[trigger] k.bindings.contains(b)
        implies cluster.cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector) by {
        assert(inner_kind(k, b) == Kind::CustomResourceKind(remote_kind_name(k.name, b)));
        assert(widget_installed_types(k, spec_ok).contains_key(remote_kind_name(k.name, b)));
    }
    // The ids of `k` keep their models and their specs.
    assert(widget_ids_of(k, ids, sync_id).contains(sync_id));
    assert forall |b: Binding| #[trigger] k.bindings.contains(b) implies {
        &&& widget_ids_of(k, ids, sync_id).contains(ids[b])
        &&& ids[b] != sync_id
        &&& binding_at(k.bindings, ids, ids[b]) == b
    } by {
        lemma_binding_id_is_a_member(k.bindings, k.bindings, ids, sync_id, b);
    }
    assert(janitors_registered(k, spec_ok, cluster, ids)) by {
        assert forall |b: Binding| #[trigger] k.bindings.contains(b) implies {
            &&& cluster.registry.contains_pair(ids[b], widget_janitor_controller_spec(k, b, spec_ok, ids[b]))
            &&& (widget_janitor_controller_spec(k, b, spec_ok, ids[b]).membership)(cluster.cluster, ids[b])
        } by {
            assert(alone.registry.contains_pair(ids[b], widget_janitor_controller_spec(k, b, spec_ok, ids[b])));
            assert(cluster.cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector));
        }
    }
    assert((widget_sync_controller_spec(k, spec_ok, sync_id, ids).membership)(cluster.cluster, sync_id)) by {
        assert forall |b: Binding| #[trigger] k.bindings.contains(b)
            implies sync_membership(k, b, spec_ok, cluster.cluster, sync_id, ids[b]) by {
            assert(cluster.cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector));
        }
    }
}

// Widget and Gadget in one cluster: the closed instance of
// widget_two_kind_core_holds, and the statement section 5.1 of
// doc/widget_sync_fanout_design.md refers to.
pub proof fn two_kind_demo_core_holds()
    ensures
        well_formed(two_kind_core_cluster(), two_kind_core_set()),
        core(two_kind_core_cluster(), two_kind_core_set()),
{
    broadcast use Set::lemma_map_contains;
    let cluster = two_kind_core_cluster();
    let w = widget_core_cluster_for(widget_kind(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids());
    let g = widget_core_cluster_for(gadget_kind(), widget_spec_ok(), gadget_sync_id(), gadget_janitor_ids());
    widget_demo_config_ok();
    two_kind_demo_config_ok();
    lemma_two_kind_cluster_lookups();
    lemma_widget_cluster_for_models(widget_kind(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids());
    lemma_widget_cluster_for_models(gadget_kind(), widget_spec_ok(), gadget_sync_id(), gadget_janitor_ids());
    assert(w.cluster.controller_models.dom() =~= w.registry.dom());
    assert(g.cluster.controller_models.dom() =~= g.registry.dom());
    assert(g.registry.dom() =~= widget_ids_of(gadget_kind(), gadget_janitor_ids(), gadget_sync_id()));
    assert(w.registry.dom() =~= widget_ids_of(widget_kind(), widget_janitor_ids(), widget_sync_id()));
    lemma_two_kind_registered(widget_kind(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids(), g, cluster);
    // The other direction of the union: Gadget's entries are the right-hand side,
    // so they win outright.
    assert(cluster.registry.contains_pair(gadget_sync_id(), widget_sync_controller_spec(gadget_kind(), widget_spec_ok(), gadget_sync_id(), gadget_janitor_ids())));
    lemma_widget_installed_types(gadget_kind(), widget_spec_ok());
    lemma_widget_types_installed(gadget_kind(), widget_spec_ok(), g.cluster);
    assert(cluster.cluster.synced_type_is_installed(gadget_kind().outer_kind, widget_spec_ok(), gadget_kind().selector));
    assert forall |b: Binding| #[trigger] gadget_kind().bindings.contains(b) implies {
        &&& cluster.cluster.synced_type_is_installed(inner_kind(gadget_kind(), b), widget_spec_ok(), gadget_kind().selector)
        &&& widget_ids_of(gadget_kind(), gadget_janitor_ids(), gadget_sync_id()).contains(gadget_janitor_ids()[b])
        &&& gadget_janitor_ids()[b] != gadget_sync_id()
        &&& binding_at(gadget_kind().bindings, gadget_janitor_ids(), gadget_janitor_ids()[b]) == b
    } by {
        assert(inner_kind(gadget_kind(), b) == Kind::CustomResourceKind(remote_kind_name(gadget_kind_name(), b)));
        assert(widget_installed_types(gadget_kind(), widget_spec_ok()).contains_key(remote_kind_name(gadget_kind_name(), b)));
        lemma_binding_id_is_a_member(gadget_kind().bindings, gadget_kind().bindings, gadget_janitor_ids(), gadget_sync_id(), b);
    }
    assert(janitors_registered(gadget_kind(), widget_spec_ok(), cluster, gadget_janitor_ids())) by {
        assert forall |b: Binding| #[trigger] gadget_kind().bindings.contains(b) implies {
            &&& cluster.registry.contains_pair(gadget_janitor_ids()[b], widget_janitor_controller_spec(gadget_kind(), b, widget_spec_ok(), gadget_janitor_ids()[b]))
            &&& (widget_janitor_controller_spec(gadget_kind(), b, widget_spec_ok(), gadget_janitor_ids()[b]).membership)(cluster.cluster, gadget_janitor_ids()[b])
        } by {
            assert(g.registry.contains_pair(gadget_janitor_ids()[b], widget_janitor_controller_spec(gadget_kind(), b, widget_spec_ok(), gadget_janitor_ids()[b])));
        }
    }
    assert((widget_sync_controller_spec(gadget_kind(), widget_spec_ok(), gadget_sync_id(), gadget_janitor_ids()).membership)(cluster.cluster, gadget_sync_id())) by {
        assert forall |b: Binding| #[trigger] gadget_kind().bindings.contains(b)
            implies sync_membership(gadget_kind(), b, widget_spec_ok(), cluster.cluster, gadget_sync_id(), gadget_janitor_ids()[b]) by {}
    }
    assert(widget_ids_of(widget_kind(), widget_janitor_ids(), widget_sync_id())
        .disjoint(widget_ids_of(gadget_kind(), gadget_janitor_ids(), gadget_sync_id())));
    widget_two_kind_core_holds(
        widget_kind(), widget_spec_ok(), widget_sync_id(), widget_janitor_ids(),
        gadget_kind(), widget_spec_ok(), gadget_sync_id(), gadget_janitor_ids(),
        cluster);
}

}
