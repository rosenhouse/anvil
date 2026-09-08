// Configured kinds beside each other: the sync controller and janitors of one
// kind composed with those of another, and, by induction over the kinds, of a
// whole deployment (doc/widget_sync_fanout_design.md, section 5.1).
// widget_two_kind_core_holds is the two-kind instance of widget_kinds_core_holds.
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
pub proof fn lemma_member_guarantee(k: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, ids: Map<Binding, int>, sync_id: int, id: int)
    requires
        ids_ok(k.bindings, ids, sync_id),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, ids)),
        janitors_registered(k, spec_ok, cluster, ids),
        widget_core_set_for(k, sync_id, ids).members.contains(id),
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
pub proof fn lemma_member_rely(k: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: CoreCluster, ids: Map<Binding, int>, sync_id: int, id: int, other: int)
    requires
        ids_ok(k.bindings, ids, sync_id),
        cluster.registry.contains_pair(sync_id, widget_sync_controller_spec(k, spec_ok, sync_id, ids)),
        janitors_registered(k, spec_ok, cluster, ids),
        widget_core_set_for(k, sync_id, ids).members.contains(id),
        !widget_core_set_for(k, sync_id, ids).members.contains(other),
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

// ---------------------------------------------------------------------------
// Any finite set of configured kinds.
// ---------------------------------------------------------------------------

// What a configuration adds to a kind: the schema its types are installed with,
// the id its sync controller runs at, and the ids of its janitors. A whole
// deployment is a finite map from kinds to these, which is what the binary's
// `--kind` flags amount to (doc/widget_sync_fanout_design.md, section 3.4).
pub struct KindSetup {
    pub spec_ok: spec_fn(Value) -> bool,
    pub sync_id: int,
    pub janitor_ids: Map<Binding, int>,
}

// The core set of a whole deployment: the kinds' core sets, one kind at a time.
// Like each kind's own core set it has no liveness dependency left -- the
// janitors' ESRs discharge their sync controller's inside each kind, and no kind
// depends on another for liveness -- so the union carries true_pred throughout.
//
// It is written as a fold rather than as a comprehension because a vstd `Set` is
// finite by construction -- `Set::new` of a predicate is an Option -- and the
// union of a finite family is not a set one can write down without the induction.
// That the deployment is finite therefore needs no hypothesis: a `Map`'s domain
// is a `Set`, and every `Set` is finite.
pub open spec fn widget_kinds_core_set(setups: Map<SyncKind, KindSetup>) -> CoreSet
    decreases setups.dom().len()
    via widget_kinds_core_set_decreases
{
    if setups.dom().is_empty() {
        CoreSet { members: Set::empty(), liveness_dependency: true_pred() }
    } else {
        let k = setups.dom().choose();
        union_coreset(
            widget_core_set_for(k, setups[k].sync_id, setups[k].janitor_ids),
            widget_kinds_core_set(setups.remove(k)),
            true_pred())
    }
}

#[via_fn]
proof fn widget_kinds_core_set_decreases(setups: Map<SyncKind, KindSetup>) {
    if !setups.dom().is_empty() {
        let k = setups.dom().choose();
        assert(setups.dom().contains(k));
        assert(setups.remove(k).dom() =~= setups.dom().remove(k));
        vstd::set::lemma_set_remove_len(setups.dom(), k);
    }
}

// The members of that core set are exactly the ids the kinds occupy.
pub proof fn lemma_kinds_core_set_members(setups: Map<SyncKind, KindSetup>)
    ensures
        widget_kinds_core_set(setups).liveness_dependency == true_pred::<ClusterState>(),
        forall |id: int| #[trigger] widget_kinds_core_set(setups).members.contains(id)
            ==> exists |k: SyncKind| setups.contains_key(k)
                && #[trigger] widget_ids_of(k, setups[k].janitor_ids, setups[k].sync_id).contains(id),
        forall |k: SyncKind, id: int| setups.contains_key(k)
            && #[trigger] widget_ids_of(k, setups[k].janitor_ids, setups[k].sync_id).contains(id)
            ==> widget_kinds_core_set(setups).members.contains(id),
    decreases setups.dom().len(),
{
    if !setups.dom().is_empty() {
        let k0 = setups.dom().choose();
        assert(setups.dom().contains(k0));
        let rest = setups.remove(k0);
        assert(rest.dom() =~= setups.dom().remove(k0));
        vstd::set::lemma_set_remove_len(setups.dom(), k0);
        lemma_kinds_core_set_members(rest);
        assert forall |id: int| #[trigger] widget_kinds_core_set(setups).members.contains(id)
            implies exists |k: SyncKind| setups.contains_key(k)
                && #[trigger] widget_ids_of(k, setups[k].janitor_ids, setups[k].sync_id).contains(id) by {
            if widget_kinds_core_set(rest).members.contains(id) {
                let k = choose |k: SyncKind| rest.contains_key(k)
                    && #[trigger] widget_ids_of(k, rest[k].janitor_ids, rest[k].sync_id).contains(id);
                assert(setups.contains_key(k) && setups[k] == rest[k]);
                assert(widget_ids_of(k, setups[k].janitor_ids, setups[k].sync_id).contains(id));
            } else {
                assert(widget_ids_of(k0, setups[k0].janitor_ids, setups[k0].sync_id).contains(id)) by {
                    lemma_widget_core_set_members(k0, setups[k0].sync_id, setups[k0].janitor_ids);
                }
            }
        }
        assert forall |k: SyncKind, id: int| setups.contains_key(k)
            && #[trigger] widget_ids_of(k, setups[k].janitor_ids, setups[k].sync_id).contains(id)
            implies widget_kinds_core_set(setups).members.contains(id) by {
            if k == k0 {
                lemma_widget_core_set_members(k0, setups[k0].sync_id, setups[k0].janitor_ids);
            } else {
                assert(rest.contains_key(k) && rest[k] == setups[k]);
            }
        }
    }
}

// The kind a member id belongs to. Well defined because distinct kinds occupy
// disjoint ids (kinds_separate).
pub open spec fn kind_at(setups: Map<SyncKind, KindSetup>, id: int) -> SyncKind {
    choose |k: SyncKind| setups.contains_key(k)
        && #[trigger] widget_ids_of(k, setups[k].janitor_ids, setups[k].sync_id).contains(id)
}

// Every configured kind is well formed, occupies ids of its own, and runs the
// sync controller and the janitors its spec names: what one kind's
// widget_fanout_core_holds asks for, of every kind of the deployment.
pub open spec fn kinds_registered(setups: Map<SyncKind, KindSetup>, cluster: CoreCluster) -> bool {
    forall |k: SyncKind| #[trigger] setups.contains_key(k) ==> {
        &&& sync_kind_ok(k)
        &&& ids_ok(k.bindings, setups[k].janitor_ids, setups[k].sync_id)
        &&& cluster.registry.contains_pair(setups[k].sync_id,
                widget_sync_controller_spec(k, setups[k].spec_ok, setups[k].sync_id, setups[k].janitor_ids))
        &&& janitors_registered(k, setups[k].spec_ok, cluster, setups[k].janitor_ids)
        &&& (widget_sync_controller_spec(k, setups[k].spec_ok, setups[k].sync_id, setups[k].janitor_ids).membership)(cluster.cluster, setups[k].sync_id)
    }
}

// Two configured kinds are told apart by their outer kinds -- from which
// lemma_kinds_of_distinct_configurations tells their mirror kinds apart, for
// every binding -- and they occupy disjoint ids.
pub open spec fn kinds_separate(setups: Map<SyncKind, KindSetup>) -> bool {
    forall |k1: SyncKind, k2: SyncKind| #![trigger setups[k1], setups[k2]]
        setups.contains_key(k1) && setups.contains_key(k2) && k1 != k2 ==> {
            &&& k1.outer_kind != k2.outer_kind
            &&& widget_ids_of(k1, setups[k1].janitor_ids, setups[k1].sync_id)
                    .disjoint(widget_ids_of(k2, setups[k2].janitor_ids, setups[k2].sync_id))
        }
}

// One kind's core set is exactly the ids it occupies.
pub proof fn lemma_widget_core_set_members(k: SyncKind, sync_id: int, ids: Map<Binding, int>)
    ensures widget_core_set_for(k, sync_id, ids).members == widget_ids_of(k, ids, sync_id),
{
    assert(widget_core_set_for(k, sync_id, ids).members =~= widget_ids_of(k, ids, sync_id));
}

// The one compatibility fact of the whole induction: what a controller of one
// configuration relies on of a controller of another is what that other one
// guarantees. Two cases, by the role of the other one, and each is one of the
// cross implications above.
proof fn lemma_cross_configuration_rely(k1: SyncKind, c1: KindSetup, k2: SyncKind, c2: KindSetup, cluster: CoreCluster, id: int, other: int)
    requires
        sync_kind_ok(k1),
        sync_kind_ok(k2),
        k1.outer_kind != k2.outer_kind,
        ids_ok(k1.bindings, c1.janitor_ids, c1.sync_id),
        ids_ok(k2.bindings, c2.janitor_ids, c2.sync_id),
        cluster.registry.contains_pair(c1.sync_id, widget_sync_controller_spec(k1, c1.spec_ok, c1.sync_id, c1.janitor_ids)),
        janitors_registered(k1, c1.spec_ok, cluster, c1.janitor_ids),
        cluster.registry.contains_pair(c2.sync_id, widget_sync_controller_spec(k2, c2.spec_ok, c2.sync_id, c2.janitor_ids)),
        janitors_registered(k2, c2.spec_ok, cluster, c2.janitor_ids),
        widget_ids_of(k1, c1.janitor_ids, c1.sync_id).contains(id),
        widget_ids_of(k2, c2.janitor_ids, c2.sync_id).contains(other),
        widget_ids_of(k1, c1.janitor_ids, c1.sync_id).disjoint(widget_ids_of(k2, c2.janitor_ids, c2.sync_id)),
    ensures
        cluster.registry[other].safety_guarantee.entails((cluster.registry[id].safety_partial_rely)(other)),
{
    broadcast use Set::lemma_map_contains;
    lemma_widget_core_set_members(k1, c1.sync_id, c1.janitor_ids);
    lemma_widget_core_set_members(k2, c2.sync_id, c2.janitor_ids);
    assert(!widget_ids_of(k1, c1.janitor_ids, c1.sync_id).contains(other));
    lemma_member_rely(k1, c1.spec_ok, cluster, c1.janitor_ids, c1.sync_id, id, other);
    lemma_member_guarantee(k2, c2.spec_ok, cluster, c2.janitor_ids, c2.sync_id, other);
    if other == c2.sync_id {
        sync_guarantee_implies_other_sync_rely(k2, k1, other);
        sync_guarantee_implies_other_janitor_rely(k2, k1, other);
        entails_preserved_by_always(lift_state(widget_sync_guarantee(k2, other)), lift_state(widget_sync_rely(k1, other)));
        entails_preserved_by_always(lift_state(widget_sync_guarantee(k2, other)), lift_state(widget_janitor_rely(k1, other)));
    } else {
        let b2 = binding_at(k2.bindings, c2.janitor_ids, other);
        janitor_guarantee_implies_other_relies(k2, b2, k1, other);
        entails_preserved_by_always(lift_state(widget_janitor_guarantee(k2, b2, other)), lift_state(widget_sync_rely(k1, other)));
        entails_preserved_by_always(lift_state(widget_janitor_guarantee(k2, b2, other)), lift_state(widget_janitor_rely(k1, other)));
    }
}

// Any finite set of configured kinds composes, one kind at a time, by induction
// on the number of kinds -- the same induction widget_janitors_core_holds runs
// over a kind's bindings. Every step is Welder's `compose`: neither side has a
// liveness dependency left, so all a step needs is that the two sides' guarantees
// imply each other's relies, which is lemma_cross_configuration_rely.
// widget_two_kind_core_holds below is the two-element instance.
pub proof fn widget_kinds_core_holds(setups: Map<SyncKind, KindSetup>, cluster: CoreCluster)
    requires
        kinds_registered(setups, cluster),
        kinds_separate(setups),
    ensures
        well_formed(cluster, widget_kinds_core_set(setups)),
        core(cluster, widget_kinds_core_set(setups)),
    decreases setups.dom().len(),
{
    broadcast use Set::lemma_map_contains;
    let spec = cluster_model(cluster);

    if setups.dom().is_empty() {
        // No members: every conjunct of the ESR is true_pred.
        let s = widget_kinds_core_set(setups);
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
        let k0 = setups.dom().choose();
        let c0 = setups[k0];
        let rest = setups.remove(k0);
        assert(setups.contains_key(k0));
        assert(rest.dom() =~= setups.dom().remove(k0));
        vstd::set::lemma_set_remove_len(setups.dom(), k0);
        assert(kinds_registered(rest, cluster));
        assert(kinds_separate(rest)) by {
            assert forall |k1: SyncKind, k2: SyncKind| #![trigger rest[k1], rest[k2]]
                rest.contains_key(k1) && rest.contains_key(k2) && k1 != k2 implies {
                    &&& k1.outer_kind != k2.outer_kind
                    &&& widget_ids_of(k1, rest[k1].janitor_ids, rest[k1].sync_id)
                            .disjoint(widget_ids_of(k2, rest[k2].janitor_ids, rest[k2].sync_id))
                } by {
                assert(setups.contains_key(k1) && setups.contains_key(k2));
                assert(rest[k1] == setups[k1] && rest[k2] == setups[k2]);
            }
        }
        widget_kinds_core_holds(rest, cluster);
        widget_fanout_core_holds(k0, c0.spec_ok, cluster, c0.janitor_ids, c0.sync_id);
        lemma_kinds_core_set_members(rest);
        let s1 = widget_core_set_for(k0, c0.sync_id, c0.janitor_ids);
        let s2 = widget_kinds_core_set(rest);
        lemma_widget_core_set_members(k0, c0.sync_id, c0.janitor_ids);

        assert(compatible(cluster, s1, s2)) by {
            let g_fn_s1 = |c: int| if s1.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
            let g_fn_s2 = |c: int| if s2.members.contains(c) { cluster.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
            let r12_fn = |pair: (int, int)| if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
            let r21_fn = |pair: (int, int)| if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) { (cluster.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };

            // What the other kinds' controllers rely on of the new kind's.
            assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s1)).entails(#[trigger] r21_fn(pair)) by {
                if s2.members.contains(pair.0) && !s2.members.contains(pair.1) && s1.members.contains(pair.1) {
                    let spec_g1 = spec.and(tla_forall(g_fn_s1));
                    let k1 = kind_at(rest, pair.0);
                    assert(rest.contains_key(k1) && widget_ids_of(k1, rest[k1].janitor_ids, rest[k1].sync_id).contains(pair.0));
                    assert(setups.contains_key(k1) && rest[k1] == setups[k1]);
                    assert(k1 != k0);
                    lemma_cross_configuration_rely(k1, setups[k1], k0, c0, cluster, pair.0, pair.1);
                    tla_forall_apply(g_fn_s1, pair.1);
                    entails_trans(spec_g1, tla_forall(g_fn_s1), cluster.registry[pair.1].safety_guarantee);
                    entails_trans(spec_g1, cluster.registry[pair.1].safety_guarantee, r21_fn(pair));
                }
            }
            spec_entails_tla_forall(spec.and(tla_forall(g_fn_s1)), r21_fn);
            entails_implies(spec, tla_forall(g_fn_s1), tla_forall(r21_fn));

            // And what the new kind's rely on of the other kinds'.
            assert forall |pair: (int, int)| spec.and(tla_forall(g_fn_s2)).entails(#[trigger] r12_fn(pair)) by {
                if s1.members.contains(pair.0) && !s1.members.contains(pair.1) && s2.members.contains(pair.1) {
                    let spec_g2 = spec.and(tla_forall(g_fn_s2));
                    let k1 = kind_at(rest, pair.1);
                    assert(rest.contains_key(k1) && widget_ids_of(k1, rest[k1].janitor_ids, rest[k1].sync_id).contains(pair.1));
                    assert(setups.contains_key(k1) && rest[k1] == setups[k1]);
                    assert(k1 != k0);
                    lemma_cross_configuration_rely(k0, c0, k1, setups[k1], cluster, pair.0, pair.1);
                    tla_forall_apply(g_fn_s2, pair.1);
                    entails_trans(spec_g2, tla_forall(g_fn_s2), cluster.registry[pair.1].safety_guarantee);
                    entails_trans(spec_g2, cluster.registry[pair.1].safety_guarantee, r12_fn(pair));
                }
            }
            spec_entails_tla_forall(spec.and(tla_forall(g_fn_s2)), r12_fn);
            entails_implies(spec, tla_forall(g_fn_s2), tla_forall(r12_fn));
            entails_and(spec, tla_forall(g_fn_s1).implies(tla_forall(r21_fn)), tla_forall(g_fn_s2).implies(tla_forall(r12_fn)));
        }
        compose(cluster, s1, s2);
        assert(widget_kinds_core_set(setups) == union_coreset(s1, s2, true_pred()));
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
            widget_core_set_for(k1, sync1, ids1),
            widget_core_set_for(k2, sync2, ids2), true_pred())),
        core(cluster, union_coreset(
            widget_core_set_for(k1, sync1, ids1),
            widget_core_set_for(k2, sync2, ids2), true_pred())),
{
    broadcast use Set::lemma_map_contains;
    let c1 = KindSetup { spec_ok: spec_ok1, sync_id: sync1, janitor_ids: ids1 };
    let c2 = KindSetup { spec_ok: spec_ok2, sync_id: sync2, janitor_ids: ids2 };
    let setups = Map::<SyncKind, KindSetup>::empty().insert(k1, c1).insert(k2, c2);
    assert(k1 != k2);
    assert(setups.dom() =~= Set::<SyncKind>::empty().insert(k1).insert(k2));
    assert(setups[k1] == c1 && setups[k2] == c2);
    assert(kinds_registered(setups, cluster)) by {
        assert forall |k: SyncKind| #[trigger] setups.contains_key(k) implies {
            &&& sync_kind_ok(k)
            &&& ids_ok(k.bindings, setups[k].janitor_ids, setups[k].sync_id)
            &&& cluster.registry.contains_pair(setups[k].sync_id,
                    widget_sync_controller_spec(k, setups[k].spec_ok, setups[k].sync_id, setups[k].janitor_ids))
            &&& janitors_registered(k, setups[k].spec_ok, cluster, setups[k].janitor_ids)
            &&& (widget_sync_controller_spec(k, setups[k].spec_ok, setups[k].sync_id, setups[k].janitor_ids).membership)(cluster.cluster, setups[k].sync_id)
        } by {
            assert(k == k1 || k == k2);
        }
    }
    assert(kinds_separate(setups)) by {
        assert(widget_ids_of(k2, ids2, sync2).disjoint(widget_ids_of(k1, ids1, sync1)));
        assert forall |x: SyncKind, y: SyncKind| #![trigger setups[x], setups[y]]
            setups.contains_key(x) && setups.contains_key(y) && x != y implies {
                &&& x.outer_kind != y.outer_kind
                &&& widget_ids_of(x, setups[x].janitor_ids, setups[x].sync_id)
                        .disjoint(widget_ids_of(y, setups[y].janitor_ids, setups[y].sync_id))
            } by {
            assert((x == k1 && y == k2) || (x == k2 && y == k1));
        }
    }
    widget_kinds_core_holds(setups, cluster);
    // The two-element fold is the union of the two kinds' core sets, whichever of
    // the two the fold picks first.
    lemma_kinds_core_set_members(setups);
    lemma_widget_core_set_members(k1, sync1, ids1);
    lemma_widget_core_set_members(k2, sync2, ids2);
    let target = union_coreset(widget_core_set_for(k1, sync1, ids1), widget_core_set_for(k2, sync2, ids2), true_pred());
    assert(widget_kinds_core_set(setups).members =~= target.members) by {
        assert forall |id: int| #[trigger] widget_kinds_core_set(setups).members.contains(id)
            implies target.members.contains(id) by {
            let k = choose |k: SyncKind| setups.contains_key(k)
                && #[trigger] widget_ids_of(k, setups[k].janitor_ids, setups[k].sync_id).contains(id);
            assert(k == k1 || k == k2);
        }
        assert forall |id: int| target.members.contains(id)
            implies #[trigger] widget_kinds_core_set(setups).members.contains(id) by {
            if widget_ids_of(k1, ids1, sync1).contains(id) {
                assert(widget_ids_of(k1, setups[k1].janitor_ids, setups[k1].sync_id).contains(id));
            } else {
                assert(widget_ids_of(k2, setups[k2].janitor_ids, setups[k2].sync_id).contains(id));
            }
        }
    }
    assert(widget_kinds_core_set(setups) == target);
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
        widget_core_set_for(widget_kind(), widget_sync_id(), widget_janitor_ids()),
        widget_core_set_for(gadget_kind(), gadget_sync_id(), gadget_janitor_ids()),
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
