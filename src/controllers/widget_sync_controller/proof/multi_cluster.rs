// The Widget controllers in the multi-store model: the outer copies live in the
// primary store, the mirrors of each binding in that binding's store. This module
// instantiates the refinement of kubernetes_cluster::proof::multi_cluster for
// them: the annotation hook that carries a parent uid across the relabeling, the
// proof that both reconcilers commute with the relabeling, and the reading of
// R1, R2 and R3s on multi-store executions, one (kind, binding) at a time.
//
// The statements here were vacuous between the fan-out port (commit 7eebc12) and
// the change that added SyncKind::bindings: all_inner_kinds_installed asked that
// the mirror kind of *every* binding be installed, and those kinds are infinitely
// many while InstalledTypes is a finite Map, so no Cluster satisfied it. The sync
// reconciler model now serves the finite set k.bindings and refuses every other
// binding before it sends a request, so the hypothesis is a finite conjunction;
// widget_instance_multi_cluster_theorem and widget_disturbed_multi_cluster_theorem at
// the end of this file close the statement for the cluster of any configuration,
// and are the witness that the hypotheses of the general theorem are satisfiable
// at all. Nothing there names a kind: the distinctness of the model kinds comes
// from sync_kind_ok and binding_ok through the injectivity of model_kind, and the
// demo configuration is one line applying them.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::{composition::*, core::*, temporal_rules::*};
use crate::kubernetes_cluster::proof::multi_cluster::{api_server::*, execution::*, fairness::*, relabel::*, steps::*};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, api_server::types::*, builtin_controllers::types::*, cluster::*, controller::state_machine::*,
    controller::types::*, message::*, multi_cluster::*,
};
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::action::*;
use crate::vstd_ext::string_view::*;
use crate::composition::{widget_disturber_reconciler::*, widget_janitor_reconciler::*, widget_sync_reconciler::*};
use crate::widget_sync_controller::{
    model::{disturber_reconciler, install::*, janitor_reconciler, sync_reconciler},
    proof::{disturber::*, guarantee::*, liveness::{janitor_proof::*, spec::*, sync_spec_proof::*, sync_status_proof::*, cleanup_proof::*}, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::{map_lib::*, multiset::*, prelude::*, seq_lib::*, set_lib::*, string::*};

verus! {

// ---------------------------------------------------------------------------
// The multi-store cluster and its hook.
// ---------------------------------------------------------------------------

// What the one-store reading needs of the configured kind and binding: the
// outer kind is not this binding's mirror kind (lemma_widget_kinds_ok discharges
// it from sync_kind_ok, by the injectivity of model_kind), and the selector
// reads the spec, not metadata, so that the API server's validation is
// metadata-blind as the refinement requires.
pub open spec fn widget_kinds_ok(sk: SyncKind, bnd: Binding) -> bool {
    &&& sk.outer_kind != inner_kind(sk, bnd)
    &&& sk.selector is Field
}

// What the multi-store instantiation needs of the cluster for one kind: the
// primary side is the home side, the outer kind lives there, the selector reads
// the spec, and the mirror kind of every binding the sync reconciler serves
// lives on that binding's side, which the cluster has. Nothing is said about
// the sides of other kinds: the mirrors of other configured kinds live wherever
// their own bindings say.
pub open spec fn widget_kind_cluster_ok(sk: SyncKind, tc: MultiCluster<ClusterIdView>) -> bool {
    &&& sk.selector is Field
    &&& tc.wf()
    &&& tc.home == ClusterIdView::Primary
    &&& tc.side_of_kind(sk.outer_kind) == ClusterIdView::Primary
    &&& forall |b: Binding| #[trigger] sk.bindings.contains(b)
        ==> tc.side_of_kind(inner_kind(sk, b)) == ClusterIdView::Remote(b) && tc.sides.contains(ClusterIdView::Remote(b))
}

// The same for one (kind, binding) pair: the binding is one the kind serves.
pub open spec fn widget_multi_cluster_ok(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>) -> bool {
    &&& widget_kind_cluster_ok(sk, tc)
    &&& widget_kinds_ok(sk, bnd)
    &&& sk.bindings.contains(bnd)
}

// The cluster holds the mirror kinds of every binding the sync controller of
// `sk` serves, not only of `bnd`: it serves all of `sk.bindings`, and its Create
// of a mirror for an outer copy of another one of them must still write a known
// kind (MultiCluster::request_ok). A binding outside `sk.bindings` is refused by
// the model before any request is sent (spec_types::serves), which is what keeps
// this set finite and so lets a concrete cluster satisfy the hypothesis.
pub open spec fn all_inner_kinds_installed(sk: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: Cluster) -> bool {
    forall |b2: Binding| sk.bindings.contains(b2) ==> cluster.synced_type_is_installed(#[trigger] inner_kind(sk, b2), spec_ok, sk.selector)
}

// The side of the outer kind, read off widget_kind_cluster_ok.
pub proof fn lemma_widget_outer_side(sk: SyncKind, tc: MultiCluster<ClusterIdView>)
    requires widget_kind_cluster_ok(sk, tc),
    ensures
        tc.side_of_kind(sk.outer_kind) == ClusterIdView::Primary,
        tc.sides.contains(ClusterIdView::Primary),
{
}

// The sides of the pair's kinds, read off widget_multi_cluster_ok.
pub proof fn lemma_widget_sides(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>)
    requires widget_multi_cluster_ok(sk, bnd, tc),
    ensures
        tc.side_of_kind(sk.outer_kind) == ClusterIdView::Primary,
        tc.side_of_kind(inner_kind(sk, bnd)) == ClusterIdView::Remote(bnd),
        tc.sides.contains(ClusterIdView::Primary),
        tc.sides.contains(ClusterIdView::Remote(bnd)),
{
}

// A uid written as a string follows the uid of the primary side; other strings
// are left alone.
pub open spec fn relabel_uid_string(u: spec_fn(ClusterIdView, Uid) -> Uid, v: StringView) -> StringView {
    if exists |i: int| v == #[trigger] int_to_string_view(i) {
        int_to_string_view(u(ClusterIdView::Primary, choose |i: int| v == #[trigger] int_to_string_view(i)))
    } else {
        v
    }
}

// Only the parent-uid annotation carries a uid.
pub open spec fn widget_hook() -> Hook<ClusterIdView> {
    |u: spec_fn(ClusterIdView, Uid) -> Uid, v: spec_fn(ClusterIdView, ResourceVersion) -> ResourceVersion|
        |kind: Kind, key: StringView, val: StringView| if key == parent_uid_key() { relabel_uid_string(u, val) } else { val }
}

pub proof fn lemma_uid_string_of(u: spec_fn(ClusterIdView, Uid) -> Uid, i: int)
    ensures relabel_uid_string(u, int_to_string_view(i)) == int_to_string_view(u(ClusterIdView::Primary, i)),
{
    int_to_string_view_injectivity();
    let j = choose |j: int| int_to_string_view(i) == #[trigger] int_to_string_view(j);
    assert(j == i);
}

// relabel_uid_string(u, a) names the relabeled uid i exactly when a names i.
pub proof fn lemma_uid_string_eq(sides: Set<ClusterIdView>, u: spec_fn(ClusterIdView, Uid) -> Uid, a: StringView, i: int)
    requires
        uid_map_injective(sides, u),
        sides.contains(ClusterIdView::Primary),
    ensures (relabel_uid_string(u, a) == int_to_string_view(u(ClusterIdView::Primary, i))) == (a == int_to_string_view(i)),
{
    int_to_string_view_injectivity();
    if exists |j: int| a == #[trigger] int_to_string_view(j) {
        let j = choose |j: int| a == #[trigger] int_to_string_view(j);
        lemma_uid_string_of(u, j);
        if u(ClusterIdView::Primary, j) == u(ClusterIdView::Primary, i) {
            assert(j == i);
        }
    }
}

pub proof fn lemma_widget_hook_injective(tc: MultiCluster<ClusterIdView>)
    requires tc.sides.contains(ClusterIdView::Primary),
    ensures hook_injective(tc, widget_hook()),
{
    let hook = widget_hook();
    assert forall |u: spec_fn(ClusterIdView, Uid) -> Uid, v: spec_fn(ClusterIdView, ResourceVersion) -> ResourceVersion|
        uid_map_injective(tc.sides, u) && rv_map_injective(tc.sides, v) implies annotation_injective(#[trigger] hook(u, v)) by {
        let h = hook(u, v);
        assert forall |kind: Kind, key: StringView, a: StringView, b: StringView| #[trigger] h(kind, key, a) == #[trigger] h(kind, key, b) implies a == b by {
            if key == parent_uid_key() {
                int_to_string_view_injectivity();
                if exists |i: int| a == #[trigger] int_to_string_view(i) {
                    let i = choose |i: int| a == #[trigger] int_to_string_view(i);
                    lemma_uid_string_of(u, i);
                    lemma_uid_string_eq(tc.sides, u, b, i);
                } else if exists |j: int| b == #[trigger] int_to_string_view(j) {
                    let j = choose |j: int| b == #[trigger] int_to_string_view(j);
                    lemma_uid_string_of(u, j);
                    lemma_uid_string_eq(tc.sides, u, a, j);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The relabeling on the Widget views.
// ---------------------------------------------------------------------------

// The relabeling on an object of the shape: its metadata is relabeled by the side
// its kind lives on, everything else is left alone. The same function serves the
// outer copies and the mirrors; which side an object is on is read off its kind.
pub open spec fn relabel_synced(tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, o: SyncedObjectView) -> SyncedObjectView {
    SyncedObjectView { metadata: relabel_meta(tc, r, o.kind, o.metadata), ..o }
}

pub proof fn lemma_unmarshal_outer_relabel(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, obj: DynamicObjectView)
    requires widget_kinds_ok(sk, bnd),
    ensures
        unmarshal(sk.outer_kind, relabel_obj(tc, r, obj)) is Ok == unmarshal(sk.outer_kind, obj) is Ok,
        unmarshal(sk.outer_kind, obj) is Ok ==> unmarshal(sk.outer_kind, relabel_obj(tc, r, obj))->Ok_0 == relabel_synced(tc, r, unmarshal(sk.outer_kind, obj)->Ok_0),
        !(unmarshal(sk.outer_kind, obj) is Ok) ==> unmarshal(sk.outer_kind, relabel_obj(tc, r, obj)) == unmarshal(sk.outer_kind, obj),
{
}

pub proof fn lemma_unmarshal_inner_relabel(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, obj: DynamicObjectView)
    requires widget_kinds_ok(sk, bnd),
    ensures
        unmarshal(inner_kind(sk, bnd), relabel_obj(tc, r, obj)) is Ok == unmarshal(inner_kind(sk, bnd), obj) is Ok,
        unmarshal(inner_kind(sk, bnd), obj) is Ok ==> unmarshal(inner_kind(sk, bnd), relabel_obj(tc, r, obj))->Ok_0 == relabel_synced(tc, r, unmarshal(inner_kind(sk, bnd), obj)->Ok_0),
        !(unmarshal(inner_kind(sk, bnd), obj) is Ok) ==> unmarshal(inner_kind(sk, bnd), relabel_obj(tc, r, obj)) == unmarshal(inner_kind(sk, bnd), obj),
{
}

// The same at any kind: relabel_synced is one function of the object's own kind,
// and the sync reconciler reads the mirror of whatever binding its outer copy
// selects, not only of `bnd`.
pub proof fn lemma_unmarshal_kind_relabel(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, kind: Kind, obj: DynamicObjectView)
    requires widget_kinds_ok(sk, bnd),
    ensures
        unmarshal(kind, relabel_obj(tc, r, obj)) is Ok == unmarshal(kind, obj) is Ok,
        unmarshal(kind, obj) is Ok ==> unmarshal(kind, relabel_obj(tc, r, obj))->Ok_0 == relabel_synced(tc, r, unmarshal(kind, obj)->Ok_0),
{
}

// The hypotheses the Widget instantiation works under.
pub open spec fn widget_relabeling(tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>) -> bool {
    &&& injective(tc, r)
    &&& r.annotation == widget_hook()(r.uid, r.rv)
}

// The parent-uid annotation of a relabeled mirror.
pub proof fn lemma_parent_annotation_relabel(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, inner: SyncedObjectView)
    requires widget_kind_cluster_ok(sk, tc), widget_kinds_ok(sk, bnd),
        widget_relabeling(tc, r),
        has_mirror_identity(inner),
    ensures
        has_mirror_identity(relabel_synced(tc, r, inner)),
        parent_uid_annotation(relabel_synced(tc, r, inner)) == relabel_uid_string(r.uid, parent_uid_annotation(inner)),
{
    let m = inner.metadata.annotations->0;
    let m1 = relabel_synced(tc, r, inner).metadata.annotations->0;
    assert(m1 == Map::new(m.dom(), |k: StringView| (r.annotation)(inner.kind, k, m[k])));
    assert(m1.contains_key(parent_uid_key()));
    assert(m1[parent_uid_key()] == (r.annotation)(inner_kind(sk, bnd), parent_uid_key(), m[parent_uid_key()]));
}

pub proof fn lemma_has_mirror_identity_relabel(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, inner: SyncedObjectView)
    requires widget_kind_cluster_ok(sk, tc), widget_kinds_ok(sk, bnd), widget_relabeling(tc, r),
    ensures has_mirror_identity(relabel_synced(tc, r, inner)) == has_mirror_identity(inner),
{
    match inner.metadata.annotations {
        Some(m) => {
            let m1 = relabel_synced(tc, r, inner).metadata.annotations->0;
            assert(m1 == Map::new(m.dom(), |k: StringView| (r.annotation)(inner.kind, k, m[k])));
            assert(m1.contains_key(parent_uid_key()) == m.contains_key(parent_uid_key()));
        },
        None => {},
    }
}

pub proof fn lemma_is_mirror_of_relabel(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, inner: SyncedObjectView, outer: SyncedObjectView)
    requires widget_kind_cluster_ok(sk, tc), widget_kinds_ok(sk, bnd),
        widget_relabeling(tc, r),
        outer.kind == sk.outer_kind,
        outer.metadata.uid is Some,
    ensures is_mirror_of(relabel_synced(tc, r, inner), relabel_synced(tc, r, outer)) == is_mirror_of(inner, outer),
{
    lemma_widget_outer_side(sk, tc);
    let inner1 = relabel_synced(tc, r, inner);
    let outer1 = relabel_synced(tc, r, outer);
    assert(outer1.metadata.uid == Some((r.uid)(ClusterIdView::Primary, outer.metadata.uid->0)));
    lemma_has_mirror_identity_relabel(sk, bnd, tc, r, inner);
    if has_mirror_identity(inner) {
        lemma_parent_annotation_relabel(sk, bnd, tc, r, inner);
        lemma_uid_string_eq(tc.sides, r.uid, parent_uid_annotation(inner), outer.metadata.uid->0);
    }
}

// The mirror the sync reconciler would create for the relabeled outer copy is
// the relabeled mirror.
pub proof fn lemma_make_inner_relabel(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, outer: SyncedObjectView)
    requires widget_kind_cluster_ok(sk, tc), widget_kinds_ok(sk, bnd),
        widget_relabeling(tc, r),
        outer.kind == sk.outer_kind,
        outer.metadata.uid is Some,
    ensures relabel_obj(tc, r, marshal(make_inner(sk, outer))) == marshal(make_inner(sk, relabel_synced(tc, r, outer))),
{
    lemma_widget_outer_side(sk, tc);
    let outer1 = relabel_synced(tc, r, outer);
    let lhs = relabel_obj(tc, r, marshal(make_inner(sk, outer)));
    let rhs = marshal(make_inner(sk, outer1));
    let m = make_inner(sk, outer).metadata.annotations->0;
    assert(m == Map::<StringView, StringView>::empty().insert(parent_uid_key(), parent_uid_of(outer)));
    let m_lhs = lhs.metadata.annotations->0;
    let m_rhs = rhs.metadata.annotations->0;
    assert(m_lhs == Map::new(m.dom(), |k: StringView| (r.annotation)(make_inner(sk, outer).kind, k, m[k])));
    lemma_uid_string_of(r.uid, outer.metadata.uid->0);
    assert(parent_uid_of(outer1) == int_to_string_view((r.uid)(ClusterIdView::Primary, outer.metadata.uid->0)));
    assert(m_lhs =~= m_rhs);
    assert(lhs.metadata =~= rhs.metadata);
    assert(lhs =~= rhs);
}

// ---------------------------------------------------------------------------
// The reconcilers commute with the relabeling.
// ---------------------------------------------------------------------------

pub open spec fn relabel_resp_view(tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, resp: Option<ResponseView<VoidERespView>>) -> Option<ResponseView<VoidERespView>> {
    match resp {
        Some(ResponseView::KResponse(x)) => Some(ResponseView::KResponse(relabel_resp(tc, r, x))),
        _ => resp,
    }
}

pub open spec fn relabel_req_view(tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, req: Option<RequestView<VoidEReqView>>) -> Option<RequestView<VoidEReqView>> {
    match req {
        Some(RequestView::KRequest(x)) => Some(RequestView::KRequest(relabel_req(tc, r, x))),
        _ => req,
    }
}

pub proof fn lemma_sync_core_commutes(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, outer: SyncedObjectView, resp: Option<ResponseView<VoidERespView>>, state: sync_reconciler::WidgetSyncReconcileState)
    requires widget_kind_cluster_ok(sk, tc), widget_kinds_ok(sk, bnd),
        widget_relabeling(tc, r),
        outer.kind == sk.outer_kind,
        outer.metadata.uid is Some,
    ensures ({
        let (state1, req1) = sync_reconciler::reconcile_core(sk, outer, resp, state);
        sync_reconciler::reconcile_core(sk, relabel_synced(tc, r, outer), relabel_resp_view(tc, r, resp), state) == (state1, relabel_req_view(tc, r, req1))
    }),
{
    lemma_widget_outer_side(sk, tc);
    let outer1 = relabel_synced(tc, r, outer);
    let resp1 = relabel_resp_view(tc, r, resp);
    match state.reconcile_step {
        WidgetSyncStepView::Init => {},
        WidgetSyncStepView::AfterGetInner => {
            if is_some_k_get_resp_view(resp) {
                let res = extract_some_k_get_resp_view(resp);
                match res {
                    Err(_) => {
                        if res->Err_0 is ObjectNotFound {
                            lemma_make_inner_relabel(sk, bnd, tc, r, outer);
                        }
                    },
                    Ok(obj) => {
                        // The mirror kind is the one the outer copy's own selector names,
                        // which need not be `bnd`: the sync reconciler of a kind serves
                        // every binding, and only the mirrors of `bnd` are remote.
                        let ik = inner_key(sk, outer).kind;
                        assert(inner_key(sk, outer1) == inner_key(sk, outer));
                        lemma_unmarshal_kind_relabel(sk, bnd, tc, r, ik, obj);
                        if unmarshal(ik, obj) is Ok {
                            let inner = unmarshal(ik, obj)->Ok_0;
                            let inner1 = relabel_synced(tc, r, inner);
                            assert(unmarshal(ik, relabel_obj(tc, r, obj))->Ok_0 == inner1);
                            lemma_is_mirror_of_relabel(sk, bnd, tc, r, inner, outer);
                            lemma_has_mirror_identity_relabel(sk, bnd, tc, r, inner);
                            if inner.metadata.deletion_timestamp is None && is_mirror_of(inner, outer) && inner.spec != outer.spec {
                                let p = sync_reconciler::inner_spec_patch(sk, inner, outer);
                                let p1 = sync_reconciler::inner_spec_patch(sk, inner1, outer1);
                                assert(inner.kind == ik);
                                assert(p1 == PatchRequest { tests: relabel_tests(r, tc.side_of_kind(ik), p.tests), ..p });
                            }
                        }
                    },
                }
            }
        },
        WidgetSyncStepView::AfterCreateInner => {},
        WidgetSyncStepView::AfterPatchInner => {},
        WidgetSyncStepView::AfterPatchOuterStatus => {},
        _ => {},
    }
}

pub proof fn lemma_parent_listed_relabel(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, objs: Seq<DynamicObjectView>, parent: StringView)
    requires widget_multi_cluster_ok(sk, bnd, tc), widget_relabeling(tc, r),
    ensures janitor_reconciler::parent_listed(sk, bnd, relabel_list(tc, r, objs), relabel_uid_string(r.uid, parent)) == janitor_reconciler::parent_listed(sk, bnd, objs, parent),
{
    lemma_widget_sides(sk, bnd, tc);
    let f = |o: DynamicObjectView| relabel_obj(tc, r, o);
    let image = objs.to_set().map(f);
    let objs1 = relabel_list(tc, r, objs);
    image.lemma_to_seq_to_set_id();
    assert(objs1.to_set() == image);
    let parent1 = relabel_uid_string(r.uid, parent);
    int_to_string_view_injectivity();
    if janitor_reconciler::parent_listed(sk, bnd, objs, parent) {
        let i = choose |i: int| 0 <= i < objs.len()
            && (#[trigger] objs[i]).kind == sk.outer_kind
            && objs[i].metadata.uid is Some
            && int_to_string_view(objs[i].metadata.uid->0) == parent
            && cluster_of_dynamic(sk.selector, objs[i]) == Some(bnd.name);
        let o = objs[i];
        let o1 = f(o);
        assert(objs.to_set().contains(o));
        objs.to_set().lemma_map_contains(f, o1);
        assert(image.contains(o1));
        assert(objs1.to_set().contains(o1));
        let j = choose |j: int| 0 <= j < objs1.len() && objs1[j] == o1;
        lemma_uid_string_of(r.uid, o.metadata.uid->0);
        assert(o1.metadata.uid == Some((r.uid)(ClusterIdView::Primary, o.metadata.uid->0)));
        assert((#[trigger] objs1[j]).kind == sk.outer_kind && objs1[j].metadata.uid is Some
            && int_to_string_view(objs1[j].metadata.uid->0) == parent1
            && cluster_of_dynamic(sk.selector, objs1[j]) == Some(bnd.name));
    }
    if janitor_reconciler::parent_listed(sk, bnd, objs1, parent1) {
        let j = choose |j: int| 0 <= j < objs1.len()
            && (#[trigger] objs1[j]).kind == sk.outer_kind
            && objs1[j].metadata.uid is Some
            && int_to_string_view(objs1[j].metadata.uid->0) == parent1
            && cluster_of_dynamic(sk.selector, objs1[j]) == Some(bnd.name);
        let o1 = objs1[j];
        assert(objs1.to_set().contains(o1));
        objs.to_set().lemma_map_contains(f, o1);
        let o = choose |o: DynamicObjectView| objs.to_set().contains(o) && o1 == f(o);
        let i = choose |i: int| 0 <= i < objs.len() && objs[i] == o;
        assert(o.metadata.uid is Some);
        let w = o.metadata.uid->0;
        assert(o1.metadata.uid == Some((r.uid)(ClusterIdView::Primary, w)));
        lemma_uid_string_eq(tc.sides, r.uid, parent, w);
        assert((#[trigger] objs[i]).kind == sk.outer_kind && objs[i].metadata.uid is Some
            && int_to_string_view(objs[i].metadata.uid->0) == parent
            && cluster_of_dynamic(sk.selector, objs[i]) == Some(bnd.name));
    }
}

pub proof fn lemma_janitor_core_commutes(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, inner: SyncedObjectView, resp: Option<ResponseView<VoidERespView>>, state: janitor_reconciler::WidgetJanitorReconcileState)
    requires widget_multi_cluster_ok(sk, bnd, tc), widget_relabeling(tc, r),
        inner.kind == inner_kind(sk, bnd),
    ensures ({
        let (state1, req1) = janitor_reconciler::reconcile_core(sk, bnd, inner, resp, state);
        janitor_reconciler::reconcile_core(sk, bnd, relabel_synced(tc, r, inner), relabel_resp_view(tc, r, resp), state) == (state1, relabel_req_view(tc, r, req1))
    }),
{
    lemma_widget_sides(sk, bnd, tc);
    let inner1 = relabel_synced(tc, r, inner);
    lemma_has_mirror_identity_relabel(sk, bnd, tc, r, inner);
    match state.reconcile_step {
        WidgetJanitorStepView::Init => {},
        WidgetJanitorStepView::AfterListOuter => {
            if has_mirror_identity(inner) && is_some_k_list_resp_view(resp) && extract_some_k_list_resp_view(resp) is Ok {
                let objs = extract_some_k_list_resp_view(resp)->Ok_0;
                lemma_parent_annotation_relabel(sk, bnd, tc, r, inner);
                lemma_parent_listed_relabel(sk, bnd, tc, r, objs, parent_uid_annotation(inner));
                if !janitor_reconciler::parent_listed(sk, bnd, objs, parent_uid_annotation(inner)) {
                    let d = DeleteRequest { key: inner.object_ref(), preconditions: Some(PreconditionsView::default().with_uid_from_object_meta(inner.metadata)) };
                    let d1 = DeleteRequest { key: inner1.object_ref(), preconditions: Some(PreconditionsView::default().with_uid_from_object_meta(inner1.metadata)) };
                    assert(d1 == DeleteRequest { preconditions: relabel_preconditions(r, ClusterIdView::Remote(bnd), d.preconditions), ..d });
                }
            }
        },
        WidgetJanitorStepView::AfterDeleteInner => {},
        _ => {},
    }
}

// A triggering object of the sync reconciler, as the simulation sees it: of the
// model's kind, with a uid, and unmarshallable (all three hold of objects taken
// from a store).
pub proof fn lemma_outer_unmarshals(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, cr: DynamicObjectView)
    requires widget_kinds_ok(sk, bnd),
        cluster.synced_type_is_installed(sk.outer_kind, spec_ok, sk.selector),
        cr.kind == sk.outer_kind,
        unmarshallable_object(cr, cluster.installed_types),
    ensures unmarshal(sk.outer_kind, cr) is Ok,
{
}

pub proof fn lemma_inner_unmarshals(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, cr: DynamicObjectView)
    requires widget_kinds_ok(sk, bnd),
        cluster.synced_type_is_installed(inner_kind(sk, bnd), spec_ok, sk.selector),
        cr.kind == inner_kind(sk, bnd),
        unmarshallable_object(cr, cluster.installed_types),
    ensures unmarshal(inner_kind(sk, bnd), cr) is Ok,
{
}

// The installed reconcile models commute: what models_commute asks of them.
pub proof fn lemma_sync_model_commutes(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState)
    requires widget_kind_cluster_ok(sk, tc), widget_kinds_ok(sk, bnd),
        widget_relabeling(tc, r),
        tc.cluster.synced_type_is_installed(sk.outer_kind, spec_ok, sk.selector),
        cr.kind == sk.outer_kind,
        cr.metadata.uid is Some,
        unmarshallable_object(cr, tc.cluster.installed_types),
    ensures ({
        let t = widget_sync_controller_model(sk).reconcile_model.transition;
        t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls) == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1))
    }),
{
    lemma_outer_unmarshals(sk, bnd, spec_ok, tc.cluster, cr);
    lemma_unmarshal_outer_relabel(sk, bnd, tc, r, cr);
    let outer = unmarshal(sk.outer_kind, cr)->Ok_0;
    let resp_um = match resp {
        None => None,
        Some(x) => Some(match x {
            ResponseContent::KubernetesResponse(api_resp) => ResponseView::<VoidERespView>::KResponse(api_resp),
            ResponseContent::ExternalResponse(ext_resp) => ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(ext_resp)->Ok_0),
        }),
    };
    let state = sync_reconciler::WidgetSyncReconcileState::unmarshal(ls)->Ok_0;
    assert(unmarshal(sk.outer_kind, relabel_obj(tc, r, cr))->Ok_0 == relabel_synced(tc, r, outer));
    lemma_sync_core_commutes(sk, bnd, tc, r, outer, resp_um, state);
}

pub proof fn lemma_janitor_model_commutes(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        tc.cluster.synced_type_is_installed(inner_kind(sk, bnd), spec_ok, sk.selector),
        cr.kind == inner_kind(sk, bnd),
        unmarshallable_object(cr, tc.cluster.installed_types),
    ensures ({
        let t = widget_janitor_controller_model(sk, bnd).reconcile_model.transition;
        t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls) == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1))
    }),
{
    lemma_inner_unmarshals(sk, bnd, spec_ok, tc.cluster, cr);
    lemma_unmarshal_inner_relabel(sk, bnd, tc, r, cr);
    let inner = unmarshal(inner_kind(sk, bnd), cr)->Ok_0;
    let resp_um = match resp {
        None => None,
        Some(x) => Some(match x {
            ResponseContent::KubernetesResponse(api_resp) => ResponseView::<VoidERespView>::KResponse(api_resp),
            ResponseContent::ExternalResponse(ext_resp) => ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(ext_resp)->Ok_0),
        }),
    };
    let state = janitor_reconciler::WidgetJanitorReconcileState::unmarshal(ls)->Ok_0;
    assert(unmarshal(inner_kind(sk, bnd), relabel_obj(tc, r, cr))->Ok_0 == relabel_synced(tc, r, inner));
    lemma_janitor_core_commutes(sk, bnd, tc, r, inner, resp_um, state);
}

// The disturber (model/disturber_reconciler.rs) reads only the namespace, name
// and spec of its object and tests nothing, so it commutes by computation.
pub proof fn lemma_disturber_core_commutes(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, inner: SyncedObjectView, resp: Option<ResponseView<VoidERespView>>, state: disturber_reconciler::WidgetDisturberReconcileState)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        inner.kind == inner_kind(sk, bnd),
    ensures ({
        let (state1, req1) = disturber_reconciler::reconcile_core(inner_kind(sk, bnd), inner, resp, state);
        disturber_reconciler::reconcile_core(inner_kind(sk, bnd), relabel_synced(tc, r, inner), relabel_resp_view(tc, r, resp), state) == (state1, relabel_req_view(tc, r, req1))
    }),
{
    lemma_widget_sides(sk, bnd, tc);
    let inner1 = relabel_synced(tc, r, inner);
    match state.reconcile_step {
        disturber_reconciler::WidgetDisturberStepView::Init => {
            let p = disturber_reconciler::disturbing_patch(inner_kind(sk, bnd), inner);
            let p1 = disturber_reconciler::disturbing_patch(inner_kind(sk, bnd), inner1);
            assert(p1 == PatchRequest { tests: relabel_tests(r, ClusterIdView::Remote(bnd), p.tests), ..p });
        },
        disturber_reconciler::WidgetDisturberStepView::AfterPatchInner => {
            let d = disturber_reconciler::disturbing_delete(inner);
            let d1 = disturber_reconciler::disturbing_delete(inner1);
            assert(d1 == DeleteRequest { preconditions: relabel_preconditions(r, ClusterIdView::Remote(bnd), d.preconditions), ..d });
        },
        _ => {},
    }
}

pub proof fn lemma_disturber_model_commutes(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        tc.cluster.synced_type_is_installed(inner_kind(sk, bnd), spec_ok, sk.selector),
        cr.kind == inner_kind(sk, bnd),
        unmarshallable_object(cr, tc.cluster.installed_types),
    ensures ({
        let t = widget_disturber_controller_model(inner_kind(sk, bnd)).reconcile_model.transition;
        t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls) == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1))
    }),
{
    lemma_inner_unmarshals(sk, bnd, spec_ok, tc.cluster, cr);
    lemma_unmarshal_inner_relabel(sk, bnd, tc, r, cr);
    let inner = unmarshal(inner_kind(sk, bnd), cr)->Ok_0;
    let resp_um = match resp {
        None => None,
        Some(x) => Some(match x {
            ResponseContent::KubernetesResponse(api_resp) => ResponseView::<VoidERespView>::KResponse(api_resp),
            ResponseContent::ExternalResponse(ext_resp) => ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(ext_resp)->Ok_0),
        }),
    };
    let state = disturber_reconciler::WidgetDisturberReconcileState::unmarshal(ls)->Ok_0;
    assert(unmarshal(inner_kind(sk, bnd), relabel_obj(tc, r, cr))->Ok_0 == relabel_synced(tc, r, inner));
    lemma_disturber_core_commutes(sk, bnd, tc, r, inner, resp_um, state);
}


// ---------------------------------------------------------------------------
// The hypotheses of the refinement, for the Widget pair and whoever runs
// beside it.
// ---------------------------------------------------------------------------

// The clause of models_ok for one controller model: no external system, and
// every request it sends is one the refinement handles.
pub open spec fn other_model_ok(tc: MultiCluster<ClusterIdView>, m: ControllerModel) -> bool {
    &&& m.external_model is None
    &&& forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState| {
        let req_o = (#[trigger] (m.reconcile_model.transition)(cr, resp, ls)).1;
        req_o is Some && req_o->0 is KubernetesRequest ==> tc.request_ok(req_o->0->KubernetesRequest_0)
    }
}

// The clause of models_commute for one controller model.
pub open spec fn other_model_commutes(tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, m: ControllerModel) -> bool {
    let rm = m.reconcile_model;
    let t = rm.transition;
    forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState|
        cr.kind == rm.kind && stored_object_ok(tc, cr)
        ==> #[trigger] t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls)
            == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1))
}

// The pair's relies on the controller at `id`, as invariants of the one-store
// model under the pair's own spec: init, next, the pair's fairness and D3
// (widget_one_cluster_spec, the one-store reading of the multi-store spec's
// conjuncts). Relies are safety, so init and next would do; the pair's
// fairness is admitted into the hypothesis only so that a Welder result, which
// is stated under cluster_model (init, next and every registered fairness),
// can be cited: lemma_relies_hold_of_from_welder. No fairness of the other
// controller is assumed anywhere.
pub open spec fn widget_relies_hold_of(sk: SyncKind, bnd: Binding, cluster: Cluster, sync_id: int, janitor_id: int, id: int) -> bool {
    let spec = widget_one_cluster_spec(sk, bnd, cluster, sync_id, janitor_id);
    &&& spec.entails(always(lift_state(widget_sync_rely(sk, id))))
    &&& spec.entails(always(lift_state(widget_janitor_rely(sk, id))))
}

// A Welder registry on this cluster whose model the pair's spec covers: every
// fairness it declares is entailed by the pair's spec (the pair's own, or
// true_pred for a controller that assumes none, like the disturber).
pub open spec fn pair_spec_covers(sk: SyncKind, bnd: Binding, cluster: Cluster, sync_id: int, janitor_id: int, cc: CoreCluster) -> bool {
    &&& cc.cluster == cluster
    &&& forall |i: int| #[trigger] cc.registry.contains_key(i)
        ==> widget_one_cluster_spec(sk, bnd, cluster, sync_id, janitor_id).entails((cc.registry[i].fairness)(cluster))
}

pub proof fn lemma_pair_spec_entails_cluster_model(sk: SyncKind, bnd: Binding, cluster: Cluster, sync_id: int, janitor_id: int, cc: CoreCluster)
    requires widget_kinds_ok(sk, bnd), pair_spec_covers(sk, bnd, cluster, sync_id, janitor_id, cc),
    ensures widget_one_cluster_spec(sk, bnd, cluster, sync_id, janitor_id).entails(cluster_model(cc)),
{
    let spec = widget_one_cluster_spec(sk, bnd, cluster, sync_id, janitor_id);
    let fairness_fn = |i: int| if cc.registry.contains_key(i) { (cc.registry[i].fairness)(cc.cluster) } else { true_pred::<ClusterState>() };
    assert(spec.entails(lift_state(cc.cluster.init())));
    assert(spec.entails(sync_next_with_wf(cluster, sync_id)));
    assert(sync_next_with_wf(cluster, sync_id).entails(always(lift_action(cc.cluster.next()))));
    entails_trans(spec, sync_next_with_wf(cluster, sync_id), always(lift_action(cc.cluster.next())));
    assert forall |i: int| spec.entails(#[trigger] fairness_fn(i)) by {
        if cc.registry.contains_key(i) {
            assert(fairness_fn(i) == (cc.registry[i].fairness)(cluster));
        } else {
            assert(fairness_fn(i) == true_pred::<ClusterState>());
        }
    }
    spec_entails_tla_forall(spec, fairness_fn);
    entails_and(spec, lift_state(cc.cluster.init()), always(lift_action(cc.cluster.next())));
    entails_and(spec, lift_state(cc.cluster.init()).and(always(lift_action(cc.cluster.next()))), tla_forall(fairness_fn));
}

// A member's guarantee under cluster_model, read off the core of a set it
// belongs to (a singleton core, or a composed one).
pub proof fn lemma_core_member_guarantee(sk: SyncKind, bnd: Binding, cc: CoreCluster, cs: CoreSet, id: int)
    requires widget_kinds_ok(sk, bnd),
        cs.members.contains(id),
        core(cc, cs),
    ensures cluster_model(cc).entails(cc.registry[id].safety_guarantee),
{
    let spec = cluster_model(cc);
    let g_fn = |c: int| if cs.members.contains(c) { cc.registry[c].safety_guarantee } else { true_pred::<ClusterState>() };
    let r_fn = |pair: (int, int)| if cs.members.contains(pair.0) && !cs.members.contains(pair.1) { (cc.registry[pair.0].safety_partial_rely)(pair.1) } else { true_pred::<ClusterState>() };
    let env_fn = |c: int| if cs.members.contains(c) { cc.registry[c].environment_rely } else { true_pred::<ClusterState>() };
    let esr_fn = |c: int| if cs.members.contains(c) { cc.registry[c].esr } else { true_pred::<ClusterState>() };
    let rest = tla_forall(r_fn).and(cs.liveness_dependency).and(tla_forall(env_fn)).implies(tla_forall(esr_fn));
    assert(spec.entails(tla_forall(g_fn).and(rest)));
    entails_and_split(spec, tla_forall(g_fn), rest);
    tla_forall_apply(g_fn, id);
    entails_trans(spec, tla_forall(g_fn), g_fn(id));
    assert(g_fn(id) == cc.registry[id].safety_guarantee);
}

// widget_relies_hold_of from a Welder fact about the controller at `id`: its
// guarantee holds as an invariant under cluster_model(cc), the form in which
// compatible and a singleton core state it (lemma_core_member_guarantee reads
// it off a core); the guarantee implies both relies pointwise (as
// disturber_guarantee_implies_relies does for the disturber); and the pair's
// spec covers cc's model. The last hypothesis is where the fairness gap
// between the two statements closes: a Welder fact is stated under every
// registered fairness, widget_relies_hold_of under the pair's alone.
pub proof fn lemma_relies_hold_of_from_welder(sk: SyncKind, bnd: Binding, cluster: Cluster, sync_id: int, janitor_id: int, id: int, cc: CoreCluster, guarantee: StatePred<ClusterState>)
    requires widget_kinds_ok(sk, bnd),
        pair_spec_covers(sk, bnd, cluster, sync_id, janitor_id, cc),
        cluster_model(cc).entails(always(lift_state(guarantee))),
        lift_state(guarantee).entails(lift_state(widget_sync_rely(sk, id))),
        lift_state(guarantee).entails(lift_state(widget_janitor_rely(sk, id))),
    ensures widget_relies_hold_of(sk, bnd, cluster, sync_id, janitor_id, id),
{
    let spec = widget_one_cluster_spec(sk, bnd, cluster, sync_id, janitor_id);
    lemma_pair_spec_entails_cluster_model(sk, bnd, cluster, sync_id, janitor_id, cc);
    entails_trans(spec, cluster_model(cc), always(lift_state(guarantee)));
    entails_preserved_by_always(lift_state(guarantee), lift_state(widget_sync_rely(sk, id)));
    entails_preserved_by_always(lift_state(guarantee), lift_state(widget_janitor_rely(sk, id)));
    entails_trans(spec, always(lift_state(guarantee)), always(lift_state(widget_sync_rely(sk, id))));
    entails_trans(spec, always(lift_state(guarantee)), always(lift_state(widget_janitor_rely(sk, id))));
}

// A controller other than the pair that the multi-store theorem admits: its model
// meets the per-controller hypotheses of the refinement (hypotheses 1 and 3 of
// doc/widget_sync_design.md section 2.2, under the Widget hook), and the pair's
// relies hold of it.
pub open spec fn widget_other_controller_ok(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int, id: int) -> bool {
    let m = tc.cluster.controller_models[id];
    &&& other_model_ok(tc, m)
    &&& forall |r: Relabeling<ClusterIdView>| widget_relabeling(tc, r) ==> #[trigger] other_model_commutes(tc, r, m)
    &&& widget_relies_hold_of(sk, bnd, tc.cluster, sync_id, janitor_id, id)
}

// A cluster running the sync reconciler and the janitor, with the two Widget
// types installed, installed types the refinement can follow, and any number of
// other controllers, each admitted by widget_other_controller_ok.
pub open spec fn widget_cluster_with_others(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int) -> bool {
    // The refinement is read one binding at a time: `bnd` is one of the bindings
    // the sync reconciler serves, the ESRs and D3 of this theorem are the ones of
    // `bnd`, and the janitors of the other bindings are other controllers
    // (widget_other_controller_ok), whose mirrors stay on the primary side.
    &&& sk.bindings.contains(bnd)
    &&& sync_membership(sk, bnd, spec_ok, tc.cluster, sync_id, janitor_id)
    &&& tc.cluster.controller_models.contains_pair(janitor_id, widget_janitor_controller_model(sk, bnd))
    &&& all_inner_kinds_installed(sk, spec_ok, tc.cluster)
    &&& installed_types_ignore_metadata(tc.cluster.installed_types)
    &&& installed_types_coherent(tc.cluster.installed_types)
    &&& forall |id: int| #[trigger] tc.cluster.controller_models.contains_key(id) && id != sync_id && id != janitor_id
        ==> widget_other_controller_ok(sk, bnd, tc, sync_id, janitor_id, id)
}

// A cluster running exactly the sync reconciler and the janitor: the special
// case with no other controller.
pub open spec fn widget_pair_cluster(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int) -> bool {
    &&& sk.bindings.contains(bnd)
    &&& sync_membership(sk, bnd, spec_ok, cluster, sync_id, janitor_id)
    &&& cluster.controller_models.contains_pair(janitor_id, widget_janitor_controller_model(sk, bnd))
    &&& cluster.controller_models.dom() == Set::<int>::empty().insert(sync_id).insert(janitor_id)
    &&& all_inner_kinds_installed(sk, spec_ok, cluster)
    &&& installed_types_ignore_metadata(cluster.installed_types)
    &&& installed_types_coherent(cluster.installed_types)
}

pub proof fn lemma_pair_cluster_is_cluster_with_others(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int)
    requires widget_multi_cluster_ok(sk, bnd, tc), widget_pair_cluster(sk, bnd, spec_ok, tc.cluster, sync_id, janitor_id),
    ensures widget_cluster_with_others(sk, bnd, spec_ok, tc, sync_id, janitor_id),
{
    assert forall |id: int| #[trigger] tc.cluster.controller_models.contains_key(id) && id != sync_id && id != janitor_id
        implies widget_other_controller_ok(sk, bnd, tc, sync_id, janitor_id, id) by {
        assert(tc.cluster.controller_models.dom().contains(id));
        assert(false);
    }
}

// The sync reconciler's model sends only requests the refinement handles: its
// one Create is of a named mirror without owner references, of the mirror kind
// of a binding it serves, which the cluster installs.
pub proof fn lemma_sync_model_ok(sk: SyncKind, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>)
    requires all_inner_kinds_installed(sk, spec_ok, tc.cluster),
    ensures other_model_ok(tc, widget_sync_controller_model(sk)),
{
    let m = widget_sync_controller_model(sk);
    assert forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState| {
        let req_o = (#[trigger] (m.reconcile_model.transition)(cr, resp, ls)).1;
        req_o is Some && req_o->0 is KubernetesRequest ==> tc.request_ok(req_o->0->KubernetesRequest_0)
    } by {
        let req_o = (m.reconcile_model.transition)(cr, resp, ls).1;
        if req_o is Some && req_o->0 is KubernetesRequest {
            let req = req_o->0->KubernetesRequest_0;
            let outer = unmarshal(sk.outer_kind, cr)->Ok_0;
            let state = sync_reconciler::WidgetSyncReconcileState::unmarshal(ls)->Ok_0;
            match state.reconcile_step {
                WidgetSyncStepView::AfterGetInner => {
                    if req is CreateRequest {
                        let obj = marshal(make_inner(sk, outer));
                        assert(req->CreateRequest_0.obj == obj);
                        assert(obj.metadata.owner_references is None);
                        assert(serves(sk, outer));
                        assert(obj.kind == inner_kind(sk, binding_of(sk, outer)));
                        assert(tc.cluster.synced_type_is_installed(inner_kind(sk, binding_of(sk, outer)), spec_ok, sk.selector));
                        assert(tc.kind_ok(obj.kind));
                    }
                },
                _ => {},
            }
        }
    }
}

// The janitor's model sends a List and a Delete, which the refinement handles as they are.
pub proof fn lemma_janitor_model_ok(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>)
    ensures other_model_ok(tc, widget_janitor_controller_model(sk, bnd)),
{
}

pub proof fn lemma_widget_models_ok(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int)
    requires widget_multi_cluster_ok(sk, bnd, tc), widget_cluster_with_others(sk, bnd, spec_ok, tc, sync_id, janitor_id),
    ensures models_ok(tc),
{
    assert forall |id: int| #[trigger] tc.cluster.controller_models.contains_key(id) implies {
        let m = tc.cluster.controller_models[id];
        &&& m.external_model is None
        &&& forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState| {
            let req_o = (#[trigger] (m.reconcile_model.transition)(cr, resp, ls)).1;
            req_o is Some && req_o->0 is KubernetesRequest ==> tc.request_ok(req_o->0->KubernetesRequest_0)
        }
    } by {
        let m = tc.cluster.controller_models[id];
        if id == sync_id {
            lemma_sync_model_ok(sk, spec_ok, tc);
        } else if id == janitor_id {
            lemma_janitor_model_ok(sk, bnd, tc);
        } else {
            assert(widget_other_controller_ok(sk, bnd, tc, sync_id, janitor_id, id));
        }
        assert(other_model_ok(tc, m));
    }
}

pub proof fn lemma_widget_models_commute(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int, r: Relabeling<ClusterIdView>)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_cluster_with_others(sk, bnd, spec_ok, tc, sync_id, janitor_id),
        widget_relabeling(tc, r),
    ensures models_commute(tc, r),
{
    assert forall |id: int| #[trigger] tc.cluster.controller_models.contains_key(id) implies {
        let m = tc.cluster.controller_models[id].reconcile_model;
        let t = m.transition;
        forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState|
            cr.kind == m.kind && stored_object_ok(tc, cr)
            ==> #[trigger] t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls)
                == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1))
    } by {
        let m = tc.cluster.controller_models[id].reconcile_model;
        let t = m.transition;
        if id == sync_id || id == janitor_id {
            assert forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState|
                cr.kind == m.kind && stored_object_ok(tc, cr)
                implies #[trigger] t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls)
                    == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1)) by {
                if id == sync_id {
                    lemma_sync_model_commutes(sk, bnd, spec_ok, tc, r, cr, resp, ls);
                } else {
                    lemma_janitor_model_commutes(sk, bnd, spec_ok, tc, r, cr, resp, ls);
                }
            }
        } else {
            assert(widget_other_controller_ok(sk, bnd, tc, sync_id, janitor_id, id));
            assert(other_model_commutes(tc, r, tc.cluster.controller_models[id]));
        }
    }
}

pub proof fn lemma_widget_refinement_hyps(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int)
    requires widget_multi_cluster_ok(sk, bnd, tc), widget_cluster_with_others(sk, bnd, spec_ok, tc, sync_id, janitor_id),
    ensures refinement_hyps(tc, widget_hook()),
{
    let hook = widget_hook();
    lemma_widget_models_ok(sk, bnd, spec_ok, tc, sync_id, janitor_id);
    lemma_widget_hook_injective(tc);
    assert forall |r: Relabeling<ClusterIdView>| injective(tc, r) && r.annotation == hook(r.uid, r.rv) implies #[trigger] models_commute(tc, r) by {
        lemma_widget_models_commute(sk, bnd, spec_ok, tc, sync_id, janitor_id, r);
    }
}

// ---------------------------------------------------------------------------
// Fairness of the multi-store model, and its transfer.
// ---------------------------------------------------------------------------

// A property asked only of the sides the cluster has.
pub open spec fn on_a_side(tc: MultiCluster<ClusterIdView>, side: ClusterIdView, p: TempPred<MultiClusterState<ClusterIdView>>) -> TempPred<MultiClusterState<ClusterIdView>> {
    if tc.sides.contains(side) { p } else { true_pred::<MultiClusterState<ClusterIdView>>() }
}

// Weak fairness of the multi-store actions, on the sides the cluster has.
pub open spec fn multi_cluster_next_with_wf(tc: MultiCluster<ClusterIdView>, id: int) -> TempPred<MultiClusterState<ClusterIdView>> {
    always(lift_action(tc.next()))
    .and(tla_forall(|input: (ClusterIdView, Option<Message>)| on_a_side(tc, input.0, tc.api_server_next(input.0).weak_fairness(input.1))))
    .and(tla_forall(|input: (ClusterIdView, (BuiltinControllerChoice, ObjectRef))| on_a_side(tc, input.0, tc.builtin_controllers_next(input.0).weak_fairness(input.1))))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| tc.controller_next().weak_fairness((id, input.0, input.1))))
    .and(tla_forall(|input: (ClusterIdView, ObjectRef)| on_a_side(tc, input.0, tc.schedule_controller_reconcile(input.0).weak_fairness((id, input.1)))))
    .and(tla_forall(|input: int| tc.disable_crash().weak_fairness(input)))
    .and(tc.disable_req_drop().weak_fairness(()))
    .and(tc.disable_pod_monkey().weak_fairness(()))
}

// The one-store fairness of a controller on the abstract execution.
pub proof fn lemma_next_with_wf_transfer(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, id: int)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        fair_sim(tc, r, ex),
        always(lift_action(tc.cluster.next())).satisfied_by(alpha(tc, r, ex)),
        multi_cluster_next_with_wf(tc, id).satisfied_by(ex),
    ensures
        sync_next_with_wf(tc.cluster, id).satisfied_by(alpha(tc, r, ex)),
        janitor_next_with_wf(tc.cluster, id).satisfied_by(alpha(tc, r, ex)),
{
    let ex1 = alpha(tc, r, ex);
    let f_api = |input: (ClusterIdView, Option<Message>)| on_a_side(tc, input.0, tc.api_server_next(input.0).weak_fairness(input.1));
    let f_gc = |input: (ClusterIdView, (BuiltinControllerChoice, ObjectRef))| on_a_side(tc, input.0, tc.builtin_controllers_next(input.0).weak_fairness(input.1));
    let f_ctrl = |input: (Option<Message>, Option<ObjectRef>)| tc.controller_next().weak_fairness((id, input.0, input.1));
    let f_sched = |input: (ClusterIdView, ObjectRef)| on_a_side(tc, input.0, tc.schedule_controller_reconcile(input.0).weak_fairness((id, input.1)));
    let f_crash = |input: int| tc.disable_crash().weak_fairness(input);
    assert(tla_forall(f_api).satisfied_by(ex));
    assert(tla_forall(f_gc).satisfied_by(ex));
    assert(tla_forall(f_ctrl).satisfied_by(ex));
    assert(tla_forall(f_sched).satisfied_by(ex));
    assert(tla_forall(f_crash).satisfied_by(ex));
    assert forall |side: ClusterIdView, input: Option<Message>| tc.sides.contains(side) implies #[trigger] tc.api_server_next(side).weak_fairness(input).satisfied_by(ex) by {
        let i = (side, input);
        assert(f_api(i).satisfied_by(ex));
    }
    assert forall |side: ClusterIdView, input: (BuiltinControllerChoice, ObjectRef)| tc.sides.contains(side) implies #[trigger] tc.builtin_controllers_next(side).weak_fairness(input).satisfied_by(ex) by {
        let i = (side, input);
        assert(f_gc(i).satisfied_by(ex));
    }
    assert forall |msg: Option<Message>, key: Option<ObjectRef>| #[trigger] tc.controller_next().weak_fairness((id, msg, key)).satisfied_by(ex) by {
        let i = (msg, key);
        assert(f_ctrl(i).satisfied_by(ex));
    }
    assert forall |side: ClusterIdView, key: ObjectRef| tc.sides.contains(side) implies #[trigger] tc.schedule_controller_reconcile(side).weak_fairness((id, key)).satisfied_by(ex) by {
        let i = (side, key);
        assert(f_sched(i).satisfied_by(ex));
    }
    assert forall |input: int| #[trigger] tc.disable_crash().weak_fairness(input).satisfied_by(ex) by {
        assert(f_crash(input).satisfied_by(ex));
    }
    assert forall |input: Option<Message>| #[trigger] tc.cluster.api_server_next().weak_fairness(input).satisfied_by(ex1) by {
        lemma_wf_api_server(tc, r, ex, input);
    }
    assert forall |input: (BuiltinControllerChoice, ObjectRef)| #[trigger] tc.cluster.builtin_controllers_next().weak_fairness(input).satisfied_by(ex1) by {
        lemma_wf_builtin(tc, r, ex, input);
    }
    assert forall |input: (Option<Message>, Option<ObjectRef>)| #[trigger] tc.cluster.controller_next().weak_fairness((id, input.0, input.1)).satisfied_by(ex1) by {
        lemma_wf_controller(tc, r, ex, id, input);
    }
    assert forall |input: ObjectRef| #[trigger] tc.cluster.schedule_controller_reconcile().weak_fairness((id, input)).satisfied_by(ex1) by {
        lemma_wf_schedule(tc, r, ex, id, input);
    }
    assert forall |input: int| #[trigger] tc.cluster.disable_crash().weak_fairness(input).satisfied_by(ex1) by {
        lemma_wf_disable_crash(tc, r, ex, input);
    }
    assert forall |input: Option<Message>| #[trigger] tc.cluster.external_next().weak_fairness((id, input)).satisfied_by(ex1) by {
        lemma_wf_external(tc, r, ex, id, input);
    }
    lemma_wf_disable_req_drop(tc, r, ex);
    lemma_wf_disable_pod_monkey(tc, r, ex);
    assert(tla_forall(|input| tc.cluster.api_server_next().weak_fairness(input)).satisfied_by(ex1));
    assert(tla_forall(|input| tc.cluster.builtin_controllers_next().weak_fairness(input)).satisfied_by(ex1));
    assert(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| tc.cluster.controller_next().weak_fairness((id, input.0, input.1))).satisfied_by(ex1));
    assert(tla_forall(|input| tc.cluster.schedule_controller_reconcile().weak_fairness((id, input))).satisfied_by(ex1));
    assert(tla_forall(|input| tc.cluster.disable_crash().weak_fairness(input)).satisfied_by(ex1));
    assert(tla_forall(|input| tc.cluster.external_next().weak_fairness((id, input))).satisfied_by(ex1));
}

// ---------------------------------------------------------------------------
// The properties, read on multi-store states.
// ---------------------------------------------------------------------------

// A one-store state predicate read on the store of one side.
pub open spec fn on_side(side: ClusterIdView, p: StatePred<ClusterState>) -> StatePred<MultiClusterState<ClusterIdView>> {
    |s: MultiClusterState<ClusterIdView>| p(s.project(side))
}

// The premises of R1 and R2 on many clusters: the outer copy and the in-flight
// writes are read on the primary side; the delete clause, which looks at the
// mirror, is read on the binding's side, where the mirror lives.
pub open spec fn multi_cluster_outer_spec_stable(sk: SyncKind, bnd: Binding, outer: SyncedObjectView) -> StatePred<MultiClusterState<ClusterIdView>> {
    |s: MultiClusterState<ClusterIdView>| {
        &&& outer_spec_stable(sk, bnd, outer)(s.project(ClusterIdView::Primary))
        &&& mirror_undeleted(sk, outer)(s.project(ClusterIdView::Remote(bnd)))
    }
}

pub open spec fn multi_cluster_outer_stable(sk: SyncKind, bnd: Binding, outer: SyncedObjectView) -> StatePred<MultiClusterState<ClusterIdView>> {
    |s: MultiClusterState<ClusterIdView>| {
        &&& outer_stable(sk, bnd, outer)(s.project(ClusterIdView::Primary))
        &&& mirror_undeleted(sk, outer)(s.project(ClusterIdView::Remote(bnd)))
    }
}

// R1 on many clusters: the outer copy is read in the primary store, the mirror in the binding's.
pub open spec fn multi_cluster_spec_eventually_synced(sk: SyncKind, bnd: Binding) -> TempPred<MultiClusterState<ClusterIdView>> {
    tla_forall(|outer: SyncedObjectView|
        always(lift_state(multi_cluster_outer_spec_stable(sk, bnd, outer)))
            .leads_to(always(lift_state(on_side(ClusterIdView::Remote(bnd), spec_synced(sk, outer))))))
}

// R2 on many clusters.
pub open spec fn multi_cluster_status_eventually_mirrored(sk: SyncKind, bnd: Binding) -> TempPred<MultiClusterState<ClusterIdView>> {
    tla_forall(|i: (SyncedObjectView, SyncedStatusView)|
        always(lift_state(multi_cluster_outer_stable(sk, bnd, i.0)).and(lift_state(on_side(ClusterIdView::Remote(bnd), inner_settled(sk, i.0, i.1)))))
            .leads_to(always(lift_state(on_side(ClusterIdView::Primary, status_synced(sk, i.0, i.1))))))
}

// R3s on many clusters: the parent is looked for in the primary store, the mirror
// at `key` in the store of the key's kind.
pub open spec fn multi_cluster_mirrors_stably_collected(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>) -> TempPred<MultiClusterState<ClusterIdView>> {
    tla_forall(|i: (ObjectRef, Uid)|
        always(lift_state(on_side(ClusterIdView::Primary, bound_parent_absent(sk, bnd, i.0, i.1))))
            .leads_to(always(lift_state(on_side(tc.side_of_kind(i.0.kind), mirror_collected(inner_kind(sk, bnd), i.0, i.1))))))
}

// R3 on many clusters.
pub open spec fn multi_cluster_mirrors_eventually_collected(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>) -> TempPred<MultiClusterState<ClusterIdView>> {
    tla_forall(|i: (ObjectRef, Uid, Uid)|
        always(lift_state(on_side(ClusterIdView::Primary, parent_absent(sk, i.0, i.1)))).and(lift_state(on_side(tc.side_of_kind(i.0.kind), mirror_object_is(inner_kind(sk, bnd), i.0, i.1, i.2))))
            .leads_to(lift_state(on_side(tc.side_of_kind(i.0.kind), object_is_gone(i.0, i.2)))))
}

// D3 on many clusters: the inner side releases terminating mirrors.
pub open spec fn multi_cluster_inner_releases_terminating_objects(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>) -> TempPred<MultiClusterState<ClusterIdView>> {
    tla_forall(|i: (ObjectRef, Uid)|
        lift_state(on_side(tc.side_of_kind(i.0.kind), inner_terminating_object(sk, bnd, i.0, i.1)))
            .leads_to(lift_state(on_side(tc.side_of_kind(i.0.kind), object_is_gone(i.0, i.1)))))
}

// The spec of the Widget pair on many clusters.
pub open spec fn widget_multi_cluster_spec(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int) -> TempPred<MultiClusterState<ClusterIdView>> {
    lift_state(tc.init())
    .and(multi_cluster_next_with_wf(tc, sync_id))
    .and(multi_cluster_next_with_wf(tc, janitor_id))
    .and(multi_cluster_inner_releases_terminating_objects(sk, bnd, tc))
}

// ---------------------------------------------------------------------------
// Per-state pull-backs.
// ---------------------------------------------------------------------------

// The object at a key of the primary side, in the abstraction and in the primary store.
proof fn lemma_abs_object(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, key: ObjectRef, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc), inv(tc, s),
    ensures ({
        let side = tc.side_of_kind(key.kind);
        let a = abs(tc, r, s, uid_next, rv_next);
        &&& a.resources().contains_key(key) == s.project(side).resources().contains_key(key)
        &&& s.project(side).resources().contains_key(key) ==> a.resources()[key] == relabel_obj(tc, r, s.project(side).resources()[key])
            && s.project(side).resources()[key].kind == key.kind
            && s.project(side).resources()[key].metadata.uid is Some
    }),
{
    reveal(inv);
    lemma_abs_store_index(tc, r, s, key);
}

proof fn lemma_desired_state_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, outer: SyncedObjectView, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
        outer.kind == sk.outer_kind,
    ensures ({
        Cluster::synced_desired_state_is(relabel_synced(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == Cluster::synced_desired_state_is(outer)(s.project(ClusterIdView::Primary))
    }),
{
    reveal(inv);
    lemma_widget_sides(sk, bnd, tc);
    let outer1 = relabel_synced(tc, r, outer);
    let key = outer.object_ref();
    assert(outer1.object_ref() == key);
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_next, rv_next);
    let a = abs(tc, r, s, uid_next, rv_next);
    let p = s.project(ClusterIdView::Primary);
    if p.resources().contains_key(key) {
        let obj = p.resources()[key];
        lemma_unmarshal_outer_relabel(sk, bnd, tc, r, obj);
        lemma_relabel_obj_keeps_identity(tc, r, obj);
        match (obj.metadata.uid, outer.metadata.uid) {
            (Some(x), Some(y)) => {
                if (r.uid)(ClusterIdView::Primary, x) == (r.uid)(ClusterIdView::Primary, y) { assert(x == y); }
            },
            _ => {},
        }
    }
}

// The premise of R1, pulled back.
proof fn lemma_outer_spec_stable_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, outer: SyncedObjectView, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
        outer.kind == sk.outer_kind,
        binding_of(sk, outer) == bnd,
        outer.metadata.uid is Some,
    ensures ({
        outer_spec_stable(sk, bnd, relabel_synced(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == multi_cluster_outer_spec_stable(sk, bnd, outer)(s)
    }),
{
    reveal(inv);
    lemma_widget_sides(sk, bnd, tc);
    let outer1 = relabel_synced(tc, r, outer);
    let a = abs(tc, r, s, uid_next, rv_next);
    let p = s.project(ClusterIdView::Primary);
    lemma_desired_state_pull_back(sk, bnd, tc, r, s, outer, uid_next, rv_next);
    // Writes of the mirror's spec in flight.
    let in_flight = s.network.in_flight;
    assert(mirror_spec_undisturbed(sk, outer1)(a) == mirror_spec_undisturbed(sk, outer)(p)) by {
        if mirror_spec_undisturbed(sk, outer)(p) {
            assert forall |msg: Message| #[trigger] a.in_flight().contains(msg) && msg.content is APIRequest implies match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => req.key() == inner_key(sk, outer1) ==> writes_outer_spec(req.obj.spec, outer1),
                APIRequest::GetThenUpdateRequest(req) => req.key() == inner_key(sk, outer1) ==> writes_outer_spec(req.obj.spec, outer1),
                APIRequest::PatchRequest(req) => req.key() == inner_key(sk, outer1) ==> writes_outer_spec(req.spec, outer1),
                _ => true,
            } by {
                lemma_relabel_msgs_contains(tc, r, in_flight, msg);
                let m2 = choose |m2: Message| in_flight.contains(m2) && relabel_msg(tc, r, m2) == msg;
                assert(p.in_flight().contains(m2));
            }
        }
        if mirror_spec_undisturbed(sk, outer1)(a) {
            assert forall |msg: Message| #[trigger] p.in_flight().contains(msg) && msg.content is APIRequest implies match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => req.key() == inner_key(sk, outer) ==> writes_outer_spec(req.obj.spec, outer),
                APIRequest::GetThenUpdateRequest(req) => req.key() == inner_key(sk, outer) ==> writes_outer_spec(req.obj.spec, outer),
                APIRequest::PatchRequest(req) => req.key() == inner_key(sk, outer) ==> writes_outer_spec(req.spec, outer),
                _ => true,
            } by {
                lemma_relabel_msgs_contains(tc, r, in_flight, msg);
                let msg1 = relabel_msg(tc, r, msg);
                assert(a.in_flight().contains(msg1));
            }
        }
    }
    // Deletes of the mirror key in flight, read on the binding's side.
    lemma_mirror_undeleted_pull_back(sk, bnd, tc, r, s, outer, uid_next, rv_next);
}

// The premise of R2, pulled back: R1's premise, and the generation of the outer
// copy, which relabeling keeps.
proof fn lemma_outer_stable_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, outer: SyncedObjectView, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
        outer.kind == sk.outer_kind,
        binding_of(sk, outer) == bnd,
        outer.metadata.uid is Some,
    ensures ({
        outer_stable(sk, bnd, relabel_synced(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == multi_cluster_outer_stable(sk, bnd, outer)(s)
    }),
{
    reveal(inv);
    lemma_widget_sides(sk, bnd, tc);
    let outer1 = relabel_synced(tc, r, outer);
    let a = abs(tc, r, s, uid_next, rv_next);
    let p = s.project(ClusterIdView::Primary);
    lemma_outer_spec_stable_pull_back(sk, bnd, tc, r, s, outer, uid_next, rv_next);
    lemma_desired_state_pull_back(sk, bnd, tc, r, s, outer, uid_next, rv_next);
    lemma_abs_object(sk, bnd, tc, r, s, outer.object_ref(), uid_next, rv_next);
    if p.resources().contains_key(outer.object_ref()) {
        lemma_relabel_obj_keeps_identity(tc, r, p.resources()[outer.object_ref()]);
    }
}

// The delete clause of the premise, pulled back: a Delete of the mirror key misses
// the relabeled mirror exactly when its preimage misses the mirror in the remote
// store, since uids of one side are relabeled injectively.
proof fn lemma_mirror_undeleted_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, outer: SyncedObjectView, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
        outer.kind == sk.outer_kind,
        binding_of(sk, outer) == bnd,
        outer.metadata.uid is Some,
    ensures ({
        mirror_undeleted(sk, relabel_synced(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == mirror_undeleted(sk, outer)(s.project(ClusterIdView::Remote(bnd)))
    }),
{
    reveal(inv);
    lemma_widget_sides(sk, bnd, tc);
    let outer1 = relabel_synced(tc, r, outer);
    let a = abs(tc, r, s, uid_next, rv_next);
    let q = s.project(ClusterIdView::Remote(bnd));
    let key = inner_key(sk, outer);
    assert(inner_key(sk, outer1) == key);
    let in_flight = s.network.in_flight;
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_next, rv_next);
    // The mirror at the key, on both sides of the abstraction.
    if q.resources().contains_key(key) {
        let obj = q.resources()[key];
        lemma_unmarshal_inner_relabel(sk, bnd, tc, r, obj);
        lemma_relabel_obj_keeps_identity(tc, r, obj);
        if unmarshal(inner_kind(sk, bnd), obj) is Ok {
            lemma_is_mirror_of_relabel(sk, bnd, tc, r, unmarshal(inner_kind(sk, bnd), obj)->Ok_0, outer);
        }
    }
    // A Delete of the mirror key and its relabeling miss the mirror together.
    assert forall |m2: Message| #[trigger] in_flight.contains(m2) && m2.content is APIRequest && m2.content->APIRequest_0 is DeleteRequest
        && m2.content->APIRequest_0->DeleteRequest_0.key == key
        implies delete_misses_mirror(sk, relabel_msg(tc, r, m2).content->APIRequest_0->DeleteRequest_0, outer1)(a)
            == delete_misses_mirror(sk, m2.content->APIRequest_0->DeleteRequest_0, outer)(q) by {
        let req2 = m2.content->APIRequest_0->DeleteRequest_0;
        let req1 = relabel_msg(tc, r, m2).content->APIRequest_0->DeleteRequest_0;
        assert(req1.preconditions == relabel_preconditions(r, ClusterIdView::Remote(bnd), req2.preconditions));
        if q.resources().contains_key(key) {
            let obj = q.resources()[key];
            assert(a.resources()[key].metadata.uid == relabel_opt_uid(r, ClusterIdView::Remote(bnd), obj.metadata.uid));
            match (req2.preconditions, obj.metadata.uid) {
                (Some(pre), Some(x)) => {
                    match pre.uid {
                        Some(y) => { if (r.uid)(ClusterIdView::Remote(bnd), y) == (r.uid)(ClusterIdView::Remote(bnd), x) { assert(y == x); } },
                        None => {},
                    }
                },
                _ => {},
            }
        }
    }
    if mirror_undeleted(sk, outer)(q) {
        assert forall |msg: Message| #[trigger] a.in_flight().contains(msg) && msg.content is APIRequest implies match msg.content->APIRequest_0 {
            APIRequest::DeleteRequest(req) => req.key == key ==> delete_misses_mirror(sk, req, outer1)(a),
            _ => true,
        } by {
            lemma_relabel_msgs_contains(tc, r, in_flight, msg);
            let m2 = choose |m2: Message| #[trigger] in_flight.contains(m2) && relabel_msg(tc, r, m2) == msg;
            assert(q.in_flight().contains(m2));
        }
    }
    if mirror_undeleted(sk, outer1)(a) {
        assert forall |msg: Message| #[trigger] q.in_flight().contains(msg) && msg.content is APIRequest implies match msg.content->APIRequest_0 {
            APIRequest::DeleteRequest(req) => req.key == key ==> delete_misses_mirror(sk, req, outer)(q),
            _ => true,
        } by {
            lemma_relabel_msgs_contains(tc, r, in_flight, msg);
            let msg1 = relabel_msg(tc, r, msg);
            assert(a.in_flight().contains(msg1));
        }
    }
}

proof fn lemma_spec_synced_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, outer: SyncedObjectView, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
        outer.kind == sk.outer_kind,
        binding_of(sk, outer) == bnd,
        outer.metadata.uid is Some,
    ensures ({
        spec_synced(sk, relabel_synced(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == spec_synced(sk, outer)(s.project(ClusterIdView::Remote(bnd)))
    }),
{
    reveal(inv);
    lemma_widget_sides(sk, bnd, tc);
    let outer1 = relabel_synced(tc, r, outer);
    let key = inner_key(sk, outer);
    assert(inner_key(sk, outer1) == key);
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_next, rv_next);
    let q = s.project(ClusterIdView::Remote(bnd));
    if q.resources().contains_key(key) {
        let obj = q.resources()[key];
        lemma_unmarshal_inner_relabel(sk, bnd, tc, r, obj);
        lemma_relabel_obj_keeps_identity(tc, r, obj);
        if unmarshal(inner_kind(sk, bnd), obj) is Ok {
            lemma_is_mirror_of_relabel(sk, bnd, tc, r, unmarshal(inner_kind(sk, bnd), obj)->Ok_0, outer);
        }
    }
}

proof fn lemma_inner_settled_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, outer: SyncedObjectView, mirrored: SyncedStatusView, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
        outer.kind == sk.outer_kind,
        binding_of(sk, outer) == bnd,
        outer.metadata.uid is Some,
    ensures ({
        inner_settled(sk, relabel_synced(tc, r, outer), mirrored)(abs(tc, r, s, uid_next, rv_next)) == inner_settled(sk, outer, mirrored)(s.project(ClusterIdView::Remote(bnd)))
    }),
{
    reveal(inv);
    lemma_widget_sides(sk, bnd, tc);
    lemma_spec_synced_pull_back(sk, bnd, tc, r, s, outer, uid_next, rv_next);
    let key = inner_key(sk, outer);
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_next, rv_next);
    let q = s.project(ClusterIdView::Remote(bnd));
    if q.resources().contains_key(key) {
        let obj = q.resources()[key];
        lemma_unmarshal_inner_relabel(sk, bnd, tc, r, obj);
    }
}

proof fn lemma_status_synced_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, outer: SyncedObjectView, mirrored: SyncedStatusView, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
        outer.kind == sk.outer_kind,
    ensures ({
        status_synced(sk, relabel_synced(tc, r, outer), mirrored)(abs(tc, r, s, uid_next, rv_next)) == status_synced(sk, outer, mirrored)(s.project(ClusterIdView::Primary))
    }),
{
    reveal(inv);
    lemma_widget_sides(sk, bnd, tc);
    let key = outer.object_ref();
    assert(relabel_synced(tc, r, outer).object_ref() == key);
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_next, rv_next);
    let p = s.project(ClusterIdView::Primary);
    if p.resources().contains_key(key) {
        let obj = p.resources()[key];
        lemma_unmarshal_outer_relabel(sk, bnd, tc, r, obj);
    }
}

proof fn lemma_parent_absent_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, key: ObjectRef, parent_uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
    ensures ({
        parent_absent(sk, key, (r.uid)(ClusterIdView::Primary, parent_uid))(abs(tc, r, s, uid_next, rv_next)) == parent_absent(sk, key, parent_uid)(s.project(ClusterIdView::Primary))
    }),
{
    reveal(inv);
    lemma_widget_sides(sk, bnd, tc);
    let okey = outer_key_of(sk, key);
    lemma_abs_object(sk, bnd, tc, r, s, okey, uid_next, rv_next);
    let p = s.project(ClusterIdView::Primary);
    if p.resources().contains_key(okey) {
        let obj = p.resources()[okey];
        match obj.metadata.uid {
            Some(x) => { if (r.uid)(ClusterIdView::Primary, x) == (r.uid)(ClusterIdView::Primary, parent_uid) { assert(x == parent_uid); } },
            None => {},
        }
    }
}

proof fn lemma_mirror_of_parent_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, obj: DynamicObjectView, parent_uid: Uid)
    requires widget_multi_cluster_ok(sk, bnd, tc), widget_relabeling(tc, r),
    ensures mirror_of_parent(inner_kind(sk, bnd), relabel_obj(tc, r, obj), (r.uid)(ClusterIdView::Primary, parent_uid)) == mirror_of_parent(inner_kind(sk, bnd), obj, parent_uid),
{
    lemma_unmarshal_inner_relabel(sk, bnd, tc, r, obj);
    if unmarshal(inner_kind(sk, bnd), obj) is Ok {
        let inner = unmarshal(inner_kind(sk, bnd), obj)->Ok_0;
        lemma_has_mirror_identity_relabel(sk, bnd, tc, r, inner);
        if has_mirror_identity(inner) {
            lemma_parent_annotation_relabel(sk, bnd, tc, r, inner);
            lemma_uid_string_eq(tc.sides, r.uid, parent_uid_annotation(inner), parent_uid);
        }
    }
}

proof fn lemma_mirror_collected_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, key: ObjectRef, parent_uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
    ensures ({
        mirror_collected(inner_kind(sk, bnd), key, (r.uid)(ClusterIdView::Primary, parent_uid))(abs(tc, r, s, uid_next, rv_next)) == mirror_collected(inner_kind(sk, bnd), key, parent_uid)(s.project(tc.side_of_kind(key.kind)))
    }),
{
    reveal(inv);
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_next, rv_next);
    let q = s.project(tc.side_of_kind(key.kind));
    if q.resources().contains_key(key) {
        lemma_mirror_of_parent_pull_back(sk, bnd, tc, r, q.resources()[key], parent_uid);
    }
}

// mirror_object_is and object_is_gone name the mirror's own uid, which lives on the key's side.
proof fn lemma_mirror_object_is_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, key: ObjectRef, parent_uid: Uid, uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
    ensures ({
        let side = tc.side_of_kind(key.kind);
        mirror_object_is(inner_kind(sk, bnd), key, (r.uid)(ClusterIdView::Primary, parent_uid), (r.uid)(side, uid))(abs(tc, r, s, uid_next, rv_next)) == mirror_object_is(inner_kind(sk, bnd), key, parent_uid, uid)(s.project(side))
    }),
{
    reveal(inv);
    let side = tc.side_of_kind(key.kind);
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_next, rv_next);
    let q = s.project(side);
    if q.resources().contains_key(key) {
        let obj = q.resources()[key];
        lemma_mirror_of_parent_pull_back(sk, bnd, tc, r, obj, parent_uid);
        let x = obj.metadata.uid->0;
        if (r.uid)(side, x) == (r.uid)(side, uid) { assert(x == uid); }
    }
}

proof fn lemma_object_is_gone_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, key: ObjectRef, uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
    ensures ({
        let side = tc.side_of_kind(key.kind);
        object_is_gone(key, (r.uid)(side, uid))(abs(tc, r, s, uid_next, rv_next)) == object_is_gone(key, uid)(s.project(side))
    }),
{
    reveal(inv);
    let side = tc.side_of_kind(key.kind);
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_next, rv_next);
    let q = s.project(side);
    if q.resources().contains_key(key) {
        let x = q.resources()[key].metadata.uid->0;
        if (r.uid)(side, x) == (r.uid)(side, uid) { assert(x == uid); }
    }
}

proof fn lemma_inner_terminating_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, key: ObjectRef, uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
    ensures ({
        let side = tc.side_of_kind(key.kind);
        inner_terminating_object(sk, bnd, key, (r.uid)(side, uid))(abs(tc, r, s, uid_next, rv_next)) == inner_terminating_object(sk, bnd, key, uid)(s.project(side))
    }),
{
    reveal(inv);
    let side = tc.side_of_kind(key.kind);
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_next, rv_next);
    let q = s.project(side);
    if q.resources().contains_key(key) {
        let obj = q.resources()[key];
        lemma_relabel_obj_keeps_identity(tc, r, obj);
        let x = obj.metadata.uid->0;
        if (r.uid)(side, x) == (r.uid)(side, uid) { assert(x == uid); }
    }
}


// ---------------------------------------------------------------------------
// Temporal pull-backs: a property of the abstract execution, read on the
// multi-store execution through per-state equivalences.
// ---------------------------------------------------------------------------

proof fn lemma_heads(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, t: nat, d: nat, k: nat)
    requires widget_kinds_ok(sk, bnd),
    ensures
        ex.suffix(t).suffix(k).head() == state_at(ex, t + k),
        alpha(tc, r, ex).suffix(t).suffix(k).head() == abs_at(tc, r, ex, t + k),
        ex.suffix(t).suffix(d).suffix(k).head() == state_at(ex, t + d + k),
        alpha(tc, r, ex).suffix(t).suffix(d).suffix(k).head() == abs_at(tc, r, ex, t + d + k),
{
}

// always p2 ~> always q2 on ex, from always p1 ~> always q1 on the abstract execution.
proof fn lemma_pull_back_always_leads_to_always(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, p1: StatePred<ClusterState>, q1: StatePred<ClusterState>, p2: StatePred<MultiClusterState<ClusterIdView>>, q2: StatePred<MultiClusterState<ClusterIdView>>)
    requires widget_kinds_ok(sk, bnd),
        forall |i: nat| p1(abs_at(tc, r, ex, i)) == p2(#[trigger] state_at(ex, i)),
        forall |i: nat| q1(abs_at(tc, r, ex, i)) == q2(#[trigger] state_at(ex, i)),
        always(lift_state(p1)).leads_to(always(lift_state(q1))).satisfied_by(alpha(tc, r, ex)),
    ensures always(lift_state(p2)).leads_to(always(lift_state(q2))).satisfied_by(ex),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |t: nat| #[trigger] always(lift_state(p2)).implies(eventually(always(lift_state(q2)))).satisfied_by(ex.suffix(t)) by {
        if always(lift_state(p2)).satisfied_by(ex.suffix(t)) {
            assert forall |k: nat| #[trigger] lift_state(p1).satisfied_by(ex1.suffix(t).suffix(k)) by {
                assert(lift_state(p2).satisfied_by(ex.suffix(t).suffix(k)));
                lemma_heads(sk, bnd, tc, r, ex, t, 0, k);
            }
            assert(always(lift_state(p1)).satisfied_by(ex1.suffix(t)));
            assert(always(lift_state(p1)).implies(eventually(always(lift_state(q1)))).satisfied_by(ex1.suffix(t)));
            let d = choose |d: nat| #[trigger] always(lift_state(q1)).satisfied_by(ex1.suffix(t).suffix(d));
            assert forall |k: nat| #[trigger] lift_state(q2).satisfied_by(ex.suffix(t).suffix(d).suffix(k)) by {
                assert(lift_state(q1).satisfied_by(ex1.suffix(t).suffix(d).suffix(k)));
                lemma_heads(sk, bnd, tc, r, ex, t, d, k);
            }
            assert(always(lift_state(q2)).satisfied_by(ex.suffix(t).suffix(d)));
        }
    }
}

// always (p2 and p2b) ~> always q2, the same with a two-part premise.
proof fn lemma_pull_back_always_and_leads_to_always(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, p1: StatePred<ClusterState>, p1b: StatePred<ClusterState>, q1: StatePred<ClusterState>, p2: StatePred<MultiClusterState<ClusterIdView>>, p2b: StatePred<MultiClusterState<ClusterIdView>>, q2: StatePred<MultiClusterState<ClusterIdView>>)
    requires widget_kinds_ok(sk, bnd),
        forall |i: nat| p1(abs_at(tc, r, ex, i)) == p2(#[trigger] state_at(ex, i)),
        forall |i: nat| p1b(abs_at(tc, r, ex, i)) == p2b(#[trigger] state_at(ex, i)),
        forall |i: nat| q1(abs_at(tc, r, ex, i)) == q2(#[trigger] state_at(ex, i)),
        always(lift_state(p1).and(lift_state(p1b))).leads_to(always(lift_state(q1))).satisfied_by(alpha(tc, r, ex)),
    ensures always(lift_state(p2).and(lift_state(p2b))).leads_to(always(lift_state(q2))).satisfied_by(ex),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |t: nat| #[trigger] always(lift_state(p2).and(lift_state(p2b))).implies(eventually(always(lift_state(q2)))).satisfied_by(ex.suffix(t)) by {
        if always(lift_state(p2).and(lift_state(p2b))).satisfied_by(ex.suffix(t)) {
            assert forall |k: nat| #[trigger] lift_state(p1).and(lift_state(p1b)).satisfied_by(ex1.suffix(t).suffix(k)) by {
                assert(lift_state(p2).and(lift_state(p2b)).satisfied_by(ex.suffix(t).suffix(k)));
                lemma_heads(sk, bnd, tc, r, ex, t, 0, k);
            }
            assert(always(lift_state(p1).and(lift_state(p1b))).satisfied_by(ex1.suffix(t)));
            assert(always(lift_state(p1).and(lift_state(p1b))).implies(eventually(always(lift_state(q1)))).satisfied_by(ex1.suffix(t)));
            let d = choose |d: nat| #[trigger] always(lift_state(q1)).satisfied_by(ex1.suffix(t).suffix(d));
            assert forall |k: nat| #[trigger] lift_state(q2).satisfied_by(ex.suffix(t).suffix(d).suffix(k)) by {
                assert(lift_state(q1).satisfied_by(ex1.suffix(t).suffix(d).suffix(k)));
                lemma_heads(sk, bnd, tc, r, ex, t, d, k);
            }
            assert(always(lift_state(q2)).satisfied_by(ex.suffix(t).suffix(d)));
        }
    }
}

// (always p2) and p2b ~> q2, the shape of R3.
proof fn lemma_pull_back_always_and_now_leads_to(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, p1: StatePred<ClusterState>, p1b: StatePred<ClusterState>, q1: StatePred<ClusterState>, p2: StatePred<MultiClusterState<ClusterIdView>>, p2b: StatePred<MultiClusterState<ClusterIdView>>, q2: StatePred<MultiClusterState<ClusterIdView>>)
    requires widget_kinds_ok(sk, bnd),
        forall |i: nat| p1(abs_at(tc, r, ex, i)) == p2(#[trigger] state_at(ex, i)),
        forall |i: nat| p1b(abs_at(tc, r, ex, i)) == p2b(#[trigger] state_at(ex, i)),
        forall |i: nat| q1(abs_at(tc, r, ex, i)) == q2(#[trigger] state_at(ex, i)),
        always(lift_state(p1)).and(lift_state(p1b)).leads_to(lift_state(q1)).satisfied_by(alpha(tc, r, ex)),
    ensures always(lift_state(p2)).and(lift_state(p2b)).leads_to(lift_state(q2)).satisfied_by(ex),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |t: nat| #[trigger] always(lift_state(p2)).and(lift_state(p2b)).implies(eventually(lift_state(q2))).satisfied_by(ex.suffix(t)) by {
        if always(lift_state(p2)).and(lift_state(p2b)).satisfied_by(ex.suffix(t)) {
            assert forall |k: nat| #[trigger] lift_state(p1).satisfied_by(ex1.suffix(t).suffix(k)) by {
                assert(lift_state(p2).satisfied_by(ex.suffix(t).suffix(k)));
                lemma_heads(sk, bnd, tc, r, ex, t, 0, k);
            }
            assert(always(lift_state(p1)).satisfied_by(ex1.suffix(t)));
            assert(lift_state(p1b).satisfied_by(ex1.suffix(t))) by {
                assert(ex.suffix(t).head() == state_at(ex, t));
                assert(ex1.suffix(t).head() == abs_at(tc, r, ex, t));
            }
            assert(always(lift_state(p1)).and(lift_state(p1b)).implies(eventually(lift_state(q1))).satisfied_by(ex1.suffix(t)));
            let d = choose |d: nat| #[trigger] lift_state(q1).satisfied_by(ex1.suffix(t).suffix(d));
            lemma_heads(sk, bnd, tc, r, ex, t, 0, d);
            assert(lift_state(q2).satisfied_by(ex.suffix(t).suffix(d)));
        }
    }
}

// p1 ~> q1 on the abstract execution from p2 ~> q2 on ex (the shape of D3).
proof fn lemma_push_forward_leads_to(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, p1: StatePred<ClusterState>, q1: StatePred<ClusterState>, p2: StatePred<MultiClusterState<ClusterIdView>>, q2: StatePred<MultiClusterState<ClusterIdView>>)
    requires widget_kinds_ok(sk, bnd),
        forall |i: nat| p1(abs_at(tc, r, ex, i)) == p2(#[trigger] state_at(ex, i)),
        forall |i: nat| q1(abs_at(tc, r, ex, i)) == q2(#[trigger] state_at(ex, i)),
        lift_state(p2).leads_to(lift_state(q2)).satisfied_by(ex),
    ensures lift_state(p1).leads_to(lift_state(q1)).satisfied_by(alpha(tc, r, ex)),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |t: nat| #[trigger] lift_state(p1).implies(eventually(lift_state(q1))).satisfied_by(ex1.suffix(t)) by {
        if lift_state(p1).satisfied_by(ex1.suffix(t)) {
            assert(ex1.suffix(t).head() == abs_at(tc, r, ex, t));
            assert(ex.suffix(t).head() == state_at(ex, t));
            assert(lift_state(p2).satisfied_by(ex.suffix(t)));
            assert(lift_state(p2).implies(eventually(lift_state(q2))).satisfied_by(ex.suffix(t)));
            let d = choose |d: nat| #[trigger] lift_state(q2).satisfied_by(ex.suffix(t).suffix(d));
            lemma_heads(sk, bnd, tc, r, ex, t, 0, d);
            assert(lift_state(q1).satisfied_by(ex1.suffix(t).suffix(d)));
        }
    }
}

// ---------------------------------------------------------------------------
// The properties on the multi-store execution.
// ---------------------------------------------------------------------------

// What the instantiation knows about an execution once it has been simulated.
pub open spec fn widget_sim(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>) -> bool {
    &&& simulation(tc, r, ex)
    &&& widget_relabeling(tc, r)
}

proof fn lemma_widget_sim_inv(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, i: nat)
    requires widget_multi_cluster_ok(sk, bnd, tc), widget_sim(sk, bnd, tc, r, ex),
    ensures
        inv(tc, state_at(ex, i)),
        abs_at(tc, r, ex, i) == abs(tc, r, state_at(ex, i), uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i))),
{
    reveal(inv);
}

// An outer copy without a uid is never the desired state: stored objects have uids.
proof fn lemma_outer_without_uid_not_stable_at(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, outer: SyncedObjectView, t: nat)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        outer.metadata.uid is None,
    ensures
        !multi_cluster_outer_spec_stable(sk, bnd, outer)(state_at(ex, t)),
        !multi_cluster_outer_stable(sk, bnd, outer)(state_at(ex, t)),
{
    lemma_widget_sim_inv(sk, bnd, tc, r, ex, t);
    lemma_inv_parts_at(tc, r, ex, t);
    let s = state_at(ex, t);
    let key = outer.object_ref();
    if s.store(ClusterIdView::Primary).resources.contains_key(key) {
        assert(stored_object_ok(tc, s.store(ClusterIdView::Primary).resources[key]));
    }
    assert(!Cluster::synced_desired_state_is(outer)(s.project(ClusterIdView::Primary)));
}

// A leads-to whose premise never holds is vacuous.
proof fn lemma_vacuous_from_never(sk: SyncKind, bnd: Binding, ex: Execution<MultiClusterState<ClusterIdView>>, sp: StatePred<MultiClusterState<ClusterIdView>>, extra: TempPred<MultiClusterState<ClusterIdView>>, q: TempPred<MultiClusterState<ClusterIdView>>)
    requires widget_kinds_ok(sk, bnd), forall |t: nat| !sp(#[trigger] state_at(ex, t)),
    ensures
        always(lift_state(sp)).leads_to(q).satisfied_by(ex),
        always(lift_state(sp).and(extra)).leads_to(q).satisfied_by(ex),
{
    assert forall |t: nat| #[trigger] always(lift_state(sp)).implies(eventually(q)).satisfied_by(ex.suffix(t)) by {
        assert(ex.suffix(t).suffix(0).head() == state_at(ex, t + 0));
        assert(!lift_state(sp).satisfied_by(ex.suffix(t).suffix(0)));
    }
    assert forall |t: nat| #[trigger] always(lift_state(sp).and(extra)).implies(eventually(q)).satisfied_by(ex.suffix(t)) by {
        assert(ex.suffix(t).suffix(0).head() == state_at(ex, t + 0));
        assert(!lift_state(sp).satisfied_by(ex.suffix(t).suffix(0)));
        assert(!lift_state(sp).and(extra).satisfied_by(ex.suffix(t).suffix(0)));
    }
}

proof fn lemma_outer_without_uid_never_stable(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, outer: SyncedObjectView)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        outer.metadata.uid is None,
    ensures always(lift_state(multi_cluster_outer_spec_stable(sk, bnd, outer))).leads_to(always(lift_state(on_side(ClusterIdView::Remote(bnd), spec_synced(sk, outer))))).satisfied_by(ex),
        forall |mirrored: SyncedStatusView| #[trigger] always(lift_state(multi_cluster_outer_stable(sk, bnd, outer)).and(lift_state(on_side(ClusterIdView::Remote(bnd), inner_settled(sk, outer, mirrored)))))
            .leads_to(always(lift_state(on_side(ClusterIdView::Primary, status_synced(sk, outer, mirrored))))).satisfied_by(ex),
{
    let sp1 = multi_cluster_outer_spec_stable(sk, bnd, outer);
    let sp = multi_cluster_outer_stable(sk, bnd, outer);
    assert forall |t: nat| !sp1(#[trigger] state_at(ex, t)) && !sp(state_at(ex, t)) by {
        lemma_outer_without_uid_not_stable_at(sk, bnd, tc, r, ex, outer, t);
    }
    lemma_vacuous_from_never(sk, bnd, ex, sp1, true_pred(), always(lift_state(on_side(ClusterIdView::Remote(bnd), spec_synced(sk, outer)))));
    assert forall |mirrored: SyncedStatusView| #[trigger] always(lift_state(multi_cluster_outer_stable(sk, bnd, outer)).and(lift_state(on_side(ClusterIdView::Remote(bnd), inner_settled(sk, outer, mirrored)))))
        .leads_to(always(lift_state(on_side(ClusterIdView::Primary, status_synced(sk, outer, mirrored))))).satisfied_by(ex) by {
        lemma_vacuous_from_never(sk, bnd, ex, sp, lift_state(on_side(ClusterIdView::Remote(bnd), inner_settled(sk, outer, mirrored))), always(lift_state(on_side(ClusterIdView::Primary, status_synced(sk, outer, mirrored)))));
    }
}

// An outer copy of another kind, or one that names no cluster or another
// binding, never satisfies the premise: outer_spec_stable carries those three
// facts, and they do not depend on the state.
proof fn lemma_off_binding_outer_never_stable(sk: SyncKind, bnd: Binding, ex: Execution<MultiClusterState<ClusterIdView>>, outer: SyncedObjectView)
    requires widget_kinds_ok(sk, bnd),
        !(outer.kind == sk.outer_kind && cluster_of(sk.selector, outer) is Some && binding_of(sk, outer) == bnd),
    ensures always(lift_state(multi_cluster_outer_spec_stable(sk, bnd, outer))).leads_to(always(lift_state(on_side(ClusterIdView::Remote(bnd), spec_synced(sk, outer))))).satisfied_by(ex),
        forall |mirrored: SyncedStatusView| #[trigger] always(lift_state(multi_cluster_outer_stable(sk, bnd, outer)).and(lift_state(on_side(ClusterIdView::Remote(bnd), inner_settled(sk, outer, mirrored)))))
            .leads_to(always(lift_state(on_side(ClusterIdView::Primary, status_synced(sk, outer, mirrored))))).satisfied_by(ex),
{
    let sp1 = multi_cluster_outer_spec_stable(sk, bnd, outer);
    let sp = multi_cluster_outer_stable(sk, bnd, outer);
    assert forall |t: nat| !sp1(#[trigger] state_at(ex, t)) && !sp(state_at(ex, t)) by {}
    lemma_vacuous_from_never(sk, bnd, ex, sp1, true_pred(), always(lift_state(on_side(ClusterIdView::Remote(bnd), spec_synced(sk, outer)))));
    assert forall |mirrored: SyncedStatusView| #[trigger] always(lift_state(multi_cluster_outer_stable(sk, bnd, outer)).and(lift_state(on_side(ClusterIdView::Remote(bnd), inner_settled(sk, outer, mirrored)))))
        .leads_to(always(lift_state(on_side(ClusterIdView::Primary, status_synced(sk, outer, mirrored))))).satisfied_by(ex) by {
        lemma_vacuous_from_never(sk, bnd, ex, sp, lift_state(on_side(ClusterIdView::Remote(bnd), inner_settled(sk, outer, mirrored))), always(lift_state(on_side(ClusterIdView::Primary, status_synced(sk, outer, mirrored)))));
    }
}

pub proof fn lemma_r1_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        widget_spec_eventually_synced(sk, bnd).satisfied_by(alpha(tc, r, ex)),
    ensures multi_cluster_spec_eventually_synced(sk, bnd).satisfied_by(ex),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |outer: SyncedObjectView| #[trigger] always(lift_state(multi_cluster_outer_spec_stable(sk, bnd, outer)))
        .leads_to(always(lift_state(on_side(ClusterIdView::Remote(bnd), spec_synced(sk, outer))))).satisfied_by(ex) by {
        if outer.metadata.uid is None {
            lemma_outer_without_uid_never_stable(sk, bnd, tc, r, ex, outer);
        } else if !(outer.kind == sk.outer_kind && cluster_of(sk.selector, outer) is Some && binding_of(sk, outer) == bnd) {
            lemma_off_binding_outer_never_stable(sk, bnd, ex, outer);
        } else {
            let outer1 = relabel_synced(tc, r, outer);
            let f = |outer: SyncedObjectView| widget_spec_eventually_synced_per_cr(sk, bnd, outer);
            assert(tla_forall(f).satisfied_by(ex1));
            assert(f(outer1).satisfied_by(ex1));
            let p1 = outer_spec_stable(sk, bnd, outer1);
            let q1 = spec_synced(sk, outer1);
            let p2 = multi_cluster_outer_spec_stable(sk, bnd, outer);
            let q2 = on_side(ClusterIdView::Remote(bnd), spec_synced(sk, outer));
            assert forall |i: nat| p1(abs_at(tc, r, ex, i)) == p2(#[trigger] state_at(ex, i)) by {
                lemma_widget_sim_inv(sk, bnd, tc, r, ex, i);
                lemma_outer_spec_stable_pull_back(sk, bnd, tc, r, state_at(ex, i), outer, uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i)));
            }
            assert forall |i: nat| q1(abs_at(tc, r, ex, i)) == q2(#[trigger] state_at(ex, i)) by {
                lemma_widget_sim_inv(sk, bnd, tc, r, ex, i);
                lemma_spec_synced_pull_back(sk, bnd, tc, r, state_at(ex, i), outer, uid_sum(tc, state_at(ex, i)), rv_sum(tc, state_at(ex, i)));
            }
            lemma_pull_back_always_leads_to_always(sk, bnd, tc, r, ex, p1, q1, p2, q2);
        }
    }
}

pub proof fn lemma_r2_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        widget_status_eventually_mirrored(sk, bnd).satisfied_by(alpha(tc, r, ex)),
    ensures multi_cluster_status_eventually_mirrored(sk, bnd).satisfied_by(ex),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |i: (SyncedObjectView, SyncedStatusView)| #[trigger] always(lift_state(multi_cluster_outer_stable(sk, bnd, i.0)).and(lift_state(on_side(ClusterIdView::Remote(bnd), inner_settled(sk, i.0, i.1)))))
        .leads_to(always(lift_state(on_side(ClusterIdView::Primary, status_synced(sk, i.0, i.1))))).satisfied_by(ex) by {
        let outer = i.0;
        let mirrored = i.1;
        if outer.metadata.uid is None {
            lemma_outer_without_uid_never_stable(sk, bnd, tc, r, ex, outer);
        } else if !(outer.kind == sk.outer_kind && cluster_of(sk.selector, outer) is Some && binding_of(sk, outer) == bnd) {
            lemma_off_binding_outer_never_stable(sk, bnd, ex, outer);
        } else {
            let outer1 = relabel_synced(tc, r, outer);
            let j = (outer1, mirrored);
            let f = |i: (SyncedObjectView, SyncedStatusView)| widget_status_eventually_mirrored_per_cr(sk, bnd, i.0, i.1);
            assert(tla_forall(f).satisfied_by(ex1));
            assert(f(j).satisfied_by(ex1));
            let p1 = outer_stable(sk, bnd, outer1);
            let p1b = inner_settled(sk, outer1, mirrored);
            let q1 = status_synced(sk, outer1, mirrored);
            let p2 = multi_cluster_outer_stable(sk, bnd, outer);
            let p2b = on_side(ClusterIdView::Remote(bnd), inner_settled(sk, outer, mirrored));
            let q2 = on_side(ClusterIdView::Primary, status_synced(sk, outer, mirrored));
            assert forall |k: nat| p1(abs_at(tc, r, ex, k)) == p2(#[trigger] state_at(ex, k)) by {
                lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
                lemma_outer_stable_pull_back(sk, bnd, tc, r, state_at(ex, k), outer, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
            }
            assert forall |k: nat| p1b(abs_at(tc, r, ex, k)) == p2b(#[trigger] state_at(ex, k)) by {
                lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
                lemma_inner_settled_pull_back(sk, bnd, tc, r, state_at(ex, k), outer, mirrored, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
            }
            assert forall |k: nat| q1(abs_at(tc, r, ex, k)) == q2(#[trigger] state_at(ex, k)) by {
                lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
                lemma_status_synced_pull_back(sk, bnd, tc, r, state_at(ex, k), outer, mirrored, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
            }
            lemma_pull_back_always_and_leads_to_always(sk, bnd, tc, r, ex, p1, p1b, q1, p2, p2b, q2);
        }
    }
}

pub proof fn lemma_r3s_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        widget_mirrors_stably_collected(sk, bnd).satisfied_by(alpha(tc, r, ex)),
    ensures multi_cluster_mirrors_stably_collected(sk, bnd, tc).satisfied_by(ex),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |i: (ObjectRef, Uid)| #[trigger] always(lift_state(on_side(ClusterIdView::Primary, bound_parent_absent(sk, bnd, i.0, i.1))))
        .leads_to(always(lift_state(on_side(tc.side_of_kind(i.0.kind), mirror_collected(inner_kind(sk, bnd), i.0, i.1))))).satisfied_by(ex) by {
        let key = i.0;
        let parent_uid = i.1;
        let parent1 = (r.uid)(ClusterIdView::Primary, parent_uid);
        let j = (key, parent1);
        let f = |i: (ObjectRef, Uid)| widget_mirror_stably_collected_per_key(sk, bnd, i.0, i.1);
        assert(tla_forall(f).satisfied_by(ex1));
        assert(f(j).satisfied_by(ex1));
        let p1 = bound_parent_absent(sk, bnd, key, parent1);
        let q1 = mirror_collected(inner_kind(sk, bnd), key, parent1);
        let p2 = on_side(ClusterIdView::Primary, bound_parent_absent(sk, bnd, key, parent_uid));
        let q2 = on_side(tc.side_of_kind(key.kind), mirror_collected(inner_kind(sk, bnd), key, parent_uid));
        assert forall |k: nat| p1(abs_at(tc, r, ex, k)) == p2(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
            lemma_parent_absent_pull_back(sk, bnd, tc, r, state_at(ex, k), key, parent_uid, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
        }
        assert forall |k: nat| q1(abs_at(tc, r, ex, k)) == q2(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
            lemma_mirror_collected_pull_back(sk, bnd, tc, r, state_at(ex, k), key, parent_uid, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
        }
        lemma_pull_back_always_leads_to_always(sk, bnd, tc, r, ex, p1, q1, p2, q2);
    }
}

pub proof fn lemma_r3_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        widget_mirrors_eventually_collected(sk, bnd).satisfied_by(alpha(tc, r, ex)),
    ensures multi_cluster_mirrors_eventually_collected(sk, bnd, tc).satisfied_by(ex),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |i: (ObjectRef, Uid, Uid)| #[trigger] always(lift_state(on_side(ClusterIdView::Primary, parent_absent(sk, i.0, i.1)))).and(lift_state(on_side(tc.side_of_kind(i.0.kind), mirror_object_is(inner_kind(sk, bnd), i.0, i.1, i.2))))
        .leads_to(lift_state(on_side(tc.side_of_kind(i.0.kind), object_is_gone(i.0, i.2)))).satisfied_by(ex) by {
        let key = i.0;
        let parent_uid = i.1;
        let uid = i.2;
        let side = tc.side_of_kind(key.kind);
        let parent1 = (r.uid)(ClusterIdView::Primary, parent_uid);
        let uid1 = (r.uid)(side, uid);
        let j = (key, parent1, uid1);
        let f = |i: (ObjectRef, Uid, Uid)| widget_mirror_eventually_collected_per_object(sk, bnd, i.0, i.1, i.2);
        assert(tla_forall(f).satisfied_by(ex1));
        assert(f(j).satisfied_by(ex1));
        let p1 = parent_absent(sk, key, parent1);
        let p1b = mirror_object_is(inner_kind(sk, bnd), key, parent1, uid1);
        let q1 = object_is_gone(key, uid1);
        let p2 = on_side(ClusterIdView::Primary, parent_absent(sk, key, parent_uid));
        let p2b = on_side(side, mirror_object_is(inner_kind(sk, bnd), key, parent_uid, uid));
        let q2 = on_side(side, object_is_gone(key, uid));
        assert forall |k: nat| p1(abs_at(tc, r, ex, k)) == p2(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
            lemma_parent_absent_pull_back(sk, bnd, tc, r, state_at(ex, k), key, parent_uid, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
        }
        assert forall |k: nat| p1b(abs_at(tc, r, ex, k)) == p2b(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
            lemma_mirror_object_is_pull_back(sk, bnd, tc, r, state_at(ex, k), key, parent_uid, uid, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
        }
        assert forall |k: nat| q1(abs_at(tc, r, ex, k)) == q2(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
            lemma_object_is_gone_pull_back(sk, bnd, tc, r, state_at(ex, k), key, uid, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
        }
        lemma_pull_back_always_and_now_leads_to(sk, bnd, tc, r, ex, p1, p1b, q1, p2, p2b, q2);
    }
}

// D3 for one mirror with uid w on the multi-store execution gives D3 for the
// relabeled uid on the abstract one.
proof fn lemma_d3_instance(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, key: ObjectRef, w: Uid)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        multi_cluster_inner_releases_terminating_objects(sk, bnd, tc).satisfied_by(ex),
    ensures ({
        let side = tc.side_of_kind(key.kind);
        lift_state(inner_terminating_object(sk, bnd, key, (r.uid)(side, w))).leads_to(lift_state(object_is_gone(key, (r.uid)(side, w)))).satisfied_by(alpha(tc, r, ex))
    }),
{
    let side = tc.side_of_kind(key.kind);
    let uid1 = (r.uid)(side, w);
    let p1 = inner_terminating_object(sk, bnd, key, uid1);
    let q1 = object_is_gone(key, uid1);
    let f = |i: (ObjectRef, Uid)| lift_state(on_side(tc.side_of_kind(i.0.kind), inner_terminating_object(sk, bnd, i.0, i.1))).leads_to(lift_state(on_side(tc.side_of_kind(i.0.kind), object_is_gone(i.0, i.1))));
    let j = (key, w);
    assert(tla_forall(f).satisfied_by(ex));
    assert(f(j).satisfied_by(ex));
    let p2 = on_side(side, inner_terminating_object(sk, bnd, key, w));
    let q2 = on_side(side, object_is_gone(key, w));
    assert forall |k: nat| p1(abs_at(tc, r, ex, k)) == p2(#[trigger] state_at(ex, k)) by {
        lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
        lemma_inner_terminating_pull_back(sk, bnd, tc, r, state_at(ex, k), key, w, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
    }
    assert forall |k: nat| q1(abs_at(tc, r, ex, k)) == q2(#[trigger] state_at(ex, k)) by {
        lemma_widget_sim_inv(sk, bnd, tc, r, ex, k);
        lemma_object_is_gone_pull_back(sk, bnd, tc, r, state_at(ex, k), key, w, uid_sum(tc, state_at(ex, k)), rv_sum(tc, state_at(ex, k)));
    }
    lemma_push_forward_leads_to(sk, bnd, tc, r, ex, p1, q1, p2, q2);
}

// A terminating object of the abstraction has, behind it, an object of the
// key's side whose uid relabels to the abstract one.
proof fn lemma_terminating_has_source(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, key: ObjectRef, uid1: Uid, t: nat)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        inner_terminating_object(sk, bnd, key, uid1)(abs_at(tc, r, ex, t)),
    ensures ({
        let side = tc.side_of_kind(key.kind);
        exists |w: Uid| uid1 == #[trigger] (r.uid)(side, w)
    }),
{
    let side = tc.side_of_kind(key.kind);
    lemma_widget_sim_inv(sk, bnd, tc, r, ex, t);
    let s = state_at(ex, t);
    lemma_abs_object(sk, bnd, tc, r, s, key, uid_sum(tc, s), rv_sum(tc, s));
    let q = s.project(side);
    assert(q.resources().contains_key(key));
    let w = q.resources()[key].metadata.uid->0;
    assert(uid1 == (r.uid)(side, w));
}

// D3 on the multi-store execution gives D3 on the abstract one.
pub proof fn lemma_d3_transfer(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        multi_cluster_inner_releases_terminating_objects(sk, bnd, tc).satisfied_by(ex),
    ensures inner_releases_terminating_objects(sk, bnd).satisfied_by(alpha(tc, r, ex)),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |i: (ObjectRef, Uid)| #[trigger] lift_state(inner_terminating_object(sk, bnd, i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1))).satisfied_by(ex1) by {
        let key = i.0;
        let uid1 = i.1;
        let side = tc.side_of_kind(key.kind);
        let p1 = inner_terminating_object(sk, bnd, key, uid1);
        let q1 = object_is_gone(key, uid1);
        assert forall |t: nat| #[trigger] lift_state(p1).implies(eventually(lift_state(q1))).satisfied_by(ex1.suffix(t)) by {
            if lift_state(p1).satisfied_by(ex1.suffix(t)) {
                assert(ex1.suffix(t).head() == abs_at(tc, r, ex, t));
                lemma_terminating_has_source(sk, bnd, tc, r, ex, key, uid1, t);
                let w = choose |w: Uid| uid1 == #[trigger] (r.uid)(side, w);
                lemma_d3_instance(sk, bnd, tc, r, ex, key, w);
                assert(lift_state(p1).leads_to(lift_state(q1)).satisfied_by(ex1));
                assert(lift_state(p1).implies(eventually(lift_state(q1))).satisfied_by(ex1.suffix(t)));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The one-store results for the pair, and the theorem.
// ---------------------------------------------------------------------------

pub open spec fn widget_one_cluster_spec(sk: SyncKind, bnd: Binding, cluster: Cluster, sync_id: int, janitor_id: int) -> TempPred<ClusterState> {
    lift_state(cluster.init())
    .and(sync_next_with_wf(cluster, sync_id))
    .and(janitor_next_with_wf(cluster, janitor_id))
    .and(inner_releases_terminating_objects(sk, bnd))
}

// The sync reconciler's rely, assembled from the facts widget_cluster_with_others
// gives: the janitor of `bnd` satisfies its own guarantee, and every other
// registered controller satisfies widget_sync_rely. It is the same statement
// widget_sync_reconciler::sync_rely_facts_imply_lifted_condition assembles from a
// map of janitor ids, proved here without one so that the theorem does not have
// to name an id for every binding of `sk.bindings`: the janitors of the other
// bindings are other controllers of this cluster, and their sync rely is what
// is used of them.
pub proof fn lemma_sync_rely_with_janitor_holds(sk: SyncKind, bnd: Binding, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int)
    requires
        spec.entails(always(lift_state(widget_janitor_guarantee(sk, bnd, janitor_id)))),
        forall |other_id: int| cluster.controller_models.contains_key(other_id) && other_id != sync_id && other_id != janitor_id
            ==> spec.entails(always(lift_state(#[trigger] widget_sync_rely(sk, other_id)))),
    ensures spec.entails(always(lift_state(sync_rely_with_janitor(sk, bnd, cluster, sync_id, janitor_id)))),
{
    assert forall |ex: Execution<ClusterState>, n: nat, other_id: int| #![auto]
        spec.satisfied_by(ex)
        && cluster.controller_models.remove(sync_id).contains_key(other_id)
        implies (if other_id == janitor_id { widget_janitor_guarantee(sk, bnd, janitor_id)(ex.suffix(n).head()) } else { widget_sync_rely(sk, other_id)(ex.suffix(n).head()) }) by {
        if other_id == janitor_id {
            assert(spec.implies(always(lift_state(widget_janitor_guarantee(sk, bnd, janitor_id)))).satisfied_by(ex));
            assert(lift_state(widget_janitor_guarantee(sk, bnd, janitor_id)).satisfied_by(ex.suffix(n)));
        } else {
            assert(cluster.controller_models.contains_key(other_id));
            assert(spec.implies(always(lift_state(widget_sync_rely(sk, other_id)))).satisfied_by(ex));
            assert(lift_state(widget_sync_rely(sk, other_id)).satisfied_by(ex.suffix(n)));
        }
    }
}

// R1, R2, R3s and the janitor's ESR, for a cluster running the pair beside
// controllers the pair's relies hold of. The relies on the pair's members are
// their guarantees; the relies on everyone else are the invariants
// widget_relies_hold_of provides, stated under this very spec.
pub proof fn lemma_one_cluster_esr(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int)
    requires widget_multi_cluster_ok(sk, bnd, tc), widget_cluster_with_others(sk, bnd, spec_ok, tc, sync_id, janitor_id),
    ensures ({
        let spec = widget_one_cluster_spec(sk, bnd, tc.cluster, sync_id, janitor_id);
        &&& spec.entails(widget_spec_eventually_synced(sk, bnd))
        &&& spec.entails(widget_status_eventually_mirrored(sk, bnd))
        &&& spec.entails(widget_mirrors_stably_collected(sk, bnd))
        &&& spec.entails(widget_janitor_esr(sk, bnd, janitor_id))
    }),
{
    let spec = widget_one_cluster_spec(sk, bnd, tc.cluster, sync_id, janitor_id);
    assert(spec.entails(lift_state(tc.cluster.init())));
    assert(spec.entails(sync_next_with_wf(tc.cluster, sync_id)));
    assert(spec.entails(janitor_next_with_wf(tc.cluster, janitor_id)));
    assert(spec.entails(inner_releases_terminating_objects(sk, bnd)));
    assert(sync_next_with_wf(tc.cluster, sync_id).entails(always(lift_action(tc.cluster.next()))));
    entails_trans(spec, sync_next_with_wf(tc.cluster, sync_id), always(lift_action(tc.cluster.next())));
    entails_and(spec, lift_state(tc.cluster.init()), always(lift_action(tc.cluster.next())));
    lemma_always_widget_sync_guarantee(spec, tc.cluster, sk, spec_ok, sync_id);
    lemma_always_widget_janitor_guarantee(spec, tc.cluster, sk, bnd, spec_ok, janitor_id);
    // The janitor's rely: the sync reconciler's guarantee, and the invariants of the others.
    assert forall |other_id: int| tc.cluster.controller_models.remove(janitor_id).contains_key(other_id)
        implies spec.entails(always(lift_state(#[trigger] widget_janitor_rely(sk, other_id)))) by {
        if other_id == sync_id {
            sync_guarantee_implies_janitor_rely(sk, sync_id);
            always_weaken(spec, lift_state(widget_sync_guarantee(sk, sync_id)), lift_state(widget_janitor_rely(sk, sync_id)));
        } else {
            assert(tc.cluster.controller_models.contains_key(other_id));
            assert(widget_other_controller_ok(sk, bnd, tc, sync_id, janitor_id, other_id));
        }
    }
    janitor_rely_facts_imply_lifted_condition(sk, spec, tc.cluster, janitor_id);
    janitor_satisfies_its_spec(sk, bnd, spec_ok, spec, tc.cluster, janitor_id);
    // The sync reconciler's rely: the janitor of `bnd` satisfies its guarantee,
    // and everyone else -- the janitors of the other bindings included, which
    // enter as other controllers -- satisfies widget_sync_rely.
    assert forall |other_id: int| tc.cluster.controller_models.contains_key(other_id) && other_id != sync_id && other_id != janitor_id
        implies spec.entails(always(lift_state(#[trigger] widget_sync_rely(sk, other_id)))) by {
        assert(widget_other_controller_ok(sk, bnd, tc, sync_id, janitor_id, other_id));
    }
    lemma_sync_rely_with_janitor_holds(sk, bnd, spec, tc.cluster, sync_id, janitor_id);
    sync_eventually_synced(sk, bnd, spec_ok, spec, tc.cluster, sync_id, janitor_id);
    sync_eventually_mirrors_status(sk, bnd, spec_ok, spec, tc.cluster, sync_id, janitor_id);
    sync_mirrors_stably_collected(sk, bnd, spec_ok, spec, tc.cluster, sync_id, janitor_id);
}

// R1, R2, R3s and R3 hold of every execution of the multi-store model that runs
// the pair, whatever else runs beside it under widget_cluster_with_others. The
// fairness assumed is the pair's alone.
pub proof fn widget_multi_cluster_theorem(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int)
    requires widget_multi_cluster_ok(sk, bnd, tc), widget_cluster_with_others(sk, bnd, spec_ok, tc, sync_id, janitor_id),
    ensures ({
        widget_multi_cluster_spec(sk, bnd, tc, sync_id, janitor_id).entails(
            multi_cluster_spec_eventually_synced(sk, bnd)
            .and(multi_cluster_status_eventually_mirrored(sk, bnd))
            .and(multi_cluster_mirrors_stably_collected(sk, bnd, tc))
            .and(multi_cluster_mirrors_eventually_collected(sk, bnd, tc))
            .and(always(lift_state(multi_cluster_janitor_deletes_are_sound(sk, bnd, tc, janitor_id))))
        )
    }),
{
    let hook = widget_hook();
    let spec2 = widget_multi_cluster_spec(sk, bnd, tc, sync_id, janitor_id);
    let spec1 = widget_one_cluster_spec(sk, bnd, tc.cluster, sync_id, janitor_id);
    lemma_widget_refinement_hyps(sk, bnd, spec_ok, tc, sync_id, janitor_id);
    lemma_one_cluster_esr(sk, bnd, spec_ok, tc, sync_id, janitor_id);
    assert forall |ex: Execution<MultiClusterState<ClusterIdView>>| #[trigger] spec2.satisfied_by(ex) implies
        multi_cluster_spec_eventually_synced(sk, bnd)
        .and(multi_cluster_status_eventually_mirrored(sk, bnd))
        .and(multi_cluster_mirrors_stably_collected(sk, bnd, tc))
        .and(multi_cluster_mirrors_eventually_collected(sk, bnd, tc))
        .and(always(lift_state(multi_cluster_janitor_deletes_are_sound(sk, bnd, tc, janitor_id)))).satisfied_by(ex) by {
        assert(lift_state(tc.init()).satisfied_by(ex));
        assert(multi_cluster_next_with_wf(tc, sync_id).satisfied_by(ex));
        assert(multi_cluster_next_with_wf(tc, janitor_id).satisfied_by(ex));
        assert(multi_cluster_inner_releases_terminating_objects(sk, bnd, tc).satisfied_by(ex));
        assert(always(lift_action(tc.next())).satisfied_by(ex));
        assert forall |i: nat| tc.next()(#[trigger] state_at(ex, i), state_at(ex, i + 1)) by {
            assert(lift_action(tc.next()).satisfied_by(ex.suffix(i)));
        }
        assert(tc.init()(state_at(ex, 0)));
        assert(multi_cluster_run(tc, ex));
        lemma_simulation(tc, hook, ex);
        let r = relabeling_of(tc, ex, hook);
        let ex1 = alpha(tc, r, ex);
        assert(widget_sim(sk, bnd, tc, r, ex));
        lemma_fair_sim(tc, r, ex);
        lemma_next_with_wf_transfer(sk, bnd, tc, r, ex, sync_id);
        lemma_next_with_wf_transfer(sk, bnd, tc, r, ex, janitor_id);
        lemma_d3_transfer(sk, bnd, tc, r, ex);
        assert(spec1.satisfied_by(ex1));
        assert(widget_spec_eventually_synced(sk, bnd).satisfied_by(ex1)) by {
            assert(spec1.implies(widget_spec_eventually_synced(sk, bnd)).satisfied_by(ex1));
        }
        assert(widget_status_eventually_mirrored(sk, bnd).satisfied_by(ex1)) by {
            assert(spec1.implies(widget_status_eventually_mirrored(sk, bnd)).satisfied_by(ex1));
        }
        assert(widget_mirrors_stably_collected(sk, bnd).satisfied_by(ex1)) by {
            assert(spec1.implies(widget_mirrors_stably_collected(sk, bnd)).satisfied_by(ex1));
        }
        assert(widget_janitor_esr(sk, bnd, janitor_id).satisfied_by(ex1)) by {
            assert(spec1.implies(widget_janitor_esr(sk, bnd, janitor_id)).satisfied_by(ex1));
        }
        assert(widget_mirrors_eventually_collected(sk, bnd).satisfied_by(ex1));
        lemma_r1_pull_back(sk, bnd, tc, r, ex);
        lemma_r2_pull_back(sk, bnd, tc, r, ex);
        lemma_r3s_pull_back(sk, bnd, tc, r, ex);
        lemma_r3_pull_back(sk, bnd, tc, r, ex);
        assert(always(lift_state(janitor_deletes_are_sound(sk, bnd, janitor_id))).satisfied_by(ex1));
        lemma_janitor_sound_transfer(sk, bnd, spec_ok, tc, r, ex, janitor_id);
    }
}


// ---------------------------------------------------------------------------
// The uids the janitor deletes by. A janitor Delete carries the uid of the
// stored mirror it was scheduled for, which the binding's store issued.
// This is an invariant of the multi-store model itself, proved by induction over
// its steps, not a pull-back: a uid a store's counter never reaches relabels to
// a negative value, about which the one-store facts say nothing.
// ---------------------------------------------------------------------------

// Every stored object carries a uid the store's counter has issued.
pub open spec fn store_uids_issued(st: APIServerState) -> bool {
    forall |k: ObjectRef| #[trigger] st.resources.contains_key(k)
        ==> st.resources[k].metadata.uid is Some && st.resources[k].metadata.uid->0 < st.uid_counter
}

// A janitor Delete names, by uid precondition, a mirror the binding's store has issued.
pub open spec fn janitor_delete_uid_issued(sk: SyncKind, bnd: Binding, msg: Message, s: MultiClusterState<ClusterIdView>) -> bool {
    let req = msg.content.get_delete_request();
    &&& req.key.kind == inner_kind(sk, bnd)
    &&& req.preconditions is Some
    &&& req.preconditions->0.uid is Some
    &&& req.preconditions->0.uid->0 < s.store(ClusterIdView::Remote(bnd)).uid_counter
}

// Both stores hold issued uids, and every object the janitor is scheduled for
// or reconciling, and every Delete it has in flight, carries a uid the remote
// store, where its kind lives, has issued.
pub open spec fn janitor_uids_issued(sk: SyncKind, bnd: Binding, janitor_id: int) -> StatePred<MultiClusterState<ClusterIdView>> {
    |s: MultiClusterState<ClusterIdView>| {
        let c = s.controller_and_externals[janitor_id].controller;
        &&& store_uids_issued(s.store(ClusterIdView::Primary))
        &&& store_uids_issued(s.store(ClusterIdView::Remote(bnd)))
        &&& forall |key: ObjectRef| #[trigger] c.scheduled_reconciles.contains_key(key)
            ==> c.scheduled_reconciles[key].metadata.uid is Some
                && c.scheduled_reconciles[key].metadata.uid->0 < s.store(ClusterIdView::Remote(bnd)).uid_counter
        &&& forall |key: ObjectRef| #[trigger] c.ongoing_reconciles.contains_key(key)
            ==> c.ongoing_reconciles[key].triggering_cr.metadata.uid is Some
                && c.ongoing_reconciles[key].triggering_cr.metadata.uid->0 < s.store(ClusterIdView::Remote(bnd)).uid_counter
        &&& forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_controller_id(janitor_id)
            &&& msg.content is APIRequest
            &&& msg.content.is_delete_request()
        } ==> janitor_delete_uid_issued(sk, bnd, msg, s)
    }
}

proof fn lemma_projection_roundtrip(sk: SyncKind, bnd: Binding, s: MultiClusterState<ClusterIdView>, side: ClusterIdView, c: ClusterState)
    ensures
        s.with_projection(side, c).project(side) == c,
        forall |other: ClusterIdView| other != side ==> #[trigger] s.with_projection(side, c).store(other) == s.store(other),
{
}

// The projection a step of the multi-store model is taken on.
pub open spec fn step_side(tc: MultiCluster<ClusterIdView>, side: ClusterIdView, step: Step) -> ClusterIdView {
    match step {
        Step::APIServerStep(_) => side,
        Step::BuiltinControllersStep(_) => side,
        Step::ScheduleControllerReconcileStep(_) => side,
        _ => tc.home,
    }
}

// Every step of the multi-store model is a step of the one-store model on the
// projection it is taken on, and leaves every other store alone.
proof fn lemma_step_projects(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, s: MultiClusterState<ClusterIdView>, s_prime: MultiClusterState<ClusterIdView>, side: ClusterIdView, step: Step)
    requires widget_multi_cluster_ok(sk, bnd, tc), tc.next_step(s, s_prime, side, step),
    ensures
        tc.cluster.next_step(s.project(step_side(tc, side, step)), s_prime.project(step_side(tc, side, step)), step),
        forall |other: ClusterIdView| other != step_side(tc, side, step) ==> #[trigger] s_prime.store(other) == s.store(other),
{
    let cluster = tc.cluster;
    let x = step_side(tc, side, step);
    let p = s.project(x);
    match step {
        Step::APIServerStep(input) => {
            let c = (cluster.api_server_next().transition)(input, p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::BuiltinControllersStep(input) => {
            let c = (cluster.builtin_controllers_next().transition)(input, p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::ControllerStep(input) => {
            let c = (cluster.controller_next().transition)(input, p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::ScheduleControllerReconcileStep(input) => {
            let c = (cluster.schedule_controller_reconcile().transition)(input, p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::RestartControllerStep(input) => {
            let c = (cluster.restart_controller().transition)(input, p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::DisableCrashStep(input) => {
            let c = (cluster.disable_crash().transition)(input, p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::DropReqStep(input) => {
            let c = (cluster.drop_req().transition)(input, p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::DisableReqDropStep => {
            let c = (cluster.disable_req_drop().transition)((), p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::PodMonkeyStep(input) => {
            let c = (cluster.pod_monkey_next().transition)(input, p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::DisablePodMonkeyStep => {
            let c = (cluster.disable_pod_monkey().transition)((), p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::ExternalStep(input) => {
            let c = (cluster.external_next().transition)(input, p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
        Step::StutterStep => {
            let c = (cluster.stutter().transition)((), p).0;
            assert(s_prime == s.with_projection(x, c));
            lemma_projection_roundtrip(sk, bnd, s, x, c);
        },
    }
}

// One request handled by any store never lowers its uid counter and is answered
// by a response.
proof fn lemma_etcd_step_answers(it: InstalledTypes, msg: Message, st: APIServerState)
    requires msg.content is APIRequest,
    ensures
        transition_by_etcd(it, msg, st).0.uid_counter >= st.uid_counter,
        transition_by_etcd(it, msg, st).1.content is APIResponse,
{
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(_) => {},
        APIRequest::ListRequest(_) => {},
        APIRequest::CreateRequest(_) => {},
        APIRequest::DeleteRequest(_) => {},
        APIRequest::UpdateRequest(_) => {},
        APIRequest::UpdateStatusRequest(_) => {},
        APIRequest::GetThenDeleteRequest(_) => {},
        APIRequest::GetThenUpdateRequest(_) => {},
        APIRequest::GetThenUpdateStatusRequest(_) => {},
        APIRequest::PatchRequest(_) => {},
        APIRequest::PatchStatusRequest(_) => {},
    }
}

// A request handled by a store whose uids are issued leaves them issued.
proof fn lemma_etcd_step_keeps_uids(sk: SyncKind, bnd: Binding, it: InstalledTypes, msg: Message, st: APIServerState)
    requires widget_kinds_ok(sk, bnd),
        msg.content is APIRequest,
        store_uids_issued(st),
    ensures store_uids_issued(transition_by_etcd(it, msg, st).0),
{
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(_) => {},
        APIRequest::ListRequest(_) => {},
        APIRequest::CreateRequest(_) => {},
        APIRequest::DeleteRequest(_) => {},
        APIRequest::UpdateRequest(_) => {},
        APIRequest::UpdateStatusRequest(_) => {},
        APIRequest::GetThenDeleteRequest(_) => {},
        APIRequest::GetThenUpdateRequest(_) => {},
        APIRequest::GetThenUpdateStatusRequest(_) => {},
        APIRequest::PatchRequest(_) => {},
        APIRequest::PatchStatusRequest(_) => {},
    }
}

proof fn lemma_janitor_uids_issued_init(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, janitor_id: int, s: MultiClusterState<ClusterIdView>)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        tc.cluster.controller_models.contains_key(janitor_id),
        tc.init()(s),
    ensures janitor_uids_issued(sk, bnd, janitor_id)(s),
{
    broadcast use group_multiset_axioms;
    lemma_widget_sides(sk, bnd, tc);
    let p = s.project(ClusterIdView::Primary);
    assert(tc.cluster.init()(p));
    let c = s.controller_and_externals[janitor_id].controller;
    assert((controller(tc.cluster.controller_models[janitor_id].reconcile_model, janitor_id).init)(c));
    assert(c.scheduled_reconciles == Map::<ObjectRef, DynamicObjectView>::empty());
    assert(c.ongoing_reconciles == Map::<ObjectRef, OngoingReconcile>::empty());
    assert(s.network.in_flight == Multiset::<Message>::empty());
    assert(s.store(ClusterIdView::Primary).resources == Map::<ObjectRef, DynamicObjectView>::empty());
    assert(s.store(ClusterIdView::Remote(bnd)).resources == Map::<ObjectRef, DynamicObjectView>::empty());
}

// The API server of `side` handles a request: that store keeps its uids issued
// and its counter does not go down; the answer is a response.
proof fn lemma_janitor_uids_issued_api_server_step(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, janitor_id: int, s: MultiClusterState<ClusterIdView>, s_prime: MultiClusterState<ClusterIdView>, side: ClusterIdView, input: Option<Message>)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        janitor_uids_issued(sk, bnd, janitor_id)(s),
        tc.api_server_next(side).forward(input)(s, s_prime),
    ensures janitor_uids_issued(sk, bnd, janitor_id)(s_prime),
{
    broadcast use group_multiset_axioms;
    lemma_step_projects(sk, bnd, tc, s, s_prime, side, Step::APIServerStep(input));
    let p = s.project(side);
    let p_prime = s_prime.project(side);
    let msg = input->0;
    let it = tc.cluster.installed_types;
    let (st1, resp) = transition_by_etcd(it, msg, p.api_server);
    assert(msg.content is APIRequest);
    assert(p_prime.api_server == st1);
    assert(p_prime.network.in_flight == p.network.in_flight.remove(msg).insert(resp));
    assert(p_prime.controller_and_externals == p.controller_and_externals);
    lemma_etcd_step_answers(it, msg, p.api_server);
    if side == ClusterIdView::Primary || side == ClusterIdView::Remote(bnd) {
        lemma_etcd_step_keeps_uids(sk, bnd, it, msg, p.api_server);
    }
    // The store of `side` is the handled one; the primary store and the
    // binding's store are each either it or untouched.
    assert(s_prime.store(side) == st1);
    if side != ClusterIdView::Primary { assert(s_prime.store(ClusterIdView::Primary) == s.store(ClusterIdView::Primary)); }
    if side != ClusterIdView::Remote(bnd) { assert(s_prime.store(ClusterIdView::Remote(bnd)) == s.store(ClusterIdView::Remote(bnd))); }
    assert(s_prime.store(ClusterIdView::Remote(bnd)).uid_counter >= s.store(ClusterIdView::Remote(bnd)).uid_counter);
    assert forall |m: Message| {
        &&& #[trigger] s_prime.in_flight().contains(m)
        &&& m.src.is_controller_id(janitor_id)
        &&& m.content is APIRequest
        &&& m.content.is_delete_request()
    } implies janitor_delete_uid_issued(sk, bnd, m, s_prime) by {
        assert(m != resp);
        assert(s.in_flight().contains(m));
    }
}

// A Delete the janitor sends while reconciling `key` names the uid of its
// triggering object, which the binding's store has issued.
proof fn lemma_janitor_sends_issued_uid(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, janitor_id: int, s: MultiClusterState<ClusterIdView>, key: ObjectRef, msg_o: Option<Message>, m: Message)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        tc.cluster.synced_type_is_installed(inner_kind(sk, bnd), spec_ok, sk.selector),
        tc.cluster.controller_models.contains_pair(janitor_id, widget_janitor_controller_model(sk, bnd)),
        inv(tc, s),
        janitor_uids_issued(sk, bnd, janitor_id)(s),
        ({
            let act = continue_reconcile(tc.cluster.controller_models[janitor_id].reconcile_model, janitor_id);
            let c = s.controller_and_externals[janitor_id].controller;
            let in2 = ControllerActionInput { recv: msg_o, scheduled_cr_key: Some(key), rpc_id_allocator: s.rpc_id_allocator };
            &&& (act.precondition)(in2, c)
            &&& (act.transition)(in2, c).1.send.contains(m)
        }),
        m.content is APIRequest,
        m.content.is_delete_request(),
    ensures janitor_delete_uid_issued(sk, bnd, m, s),
{
    reveal(inv);
    broadcast use group_multiset_axioms;
    let model = tc.cluster.controller_models[janitor_id].reconcile_model;
    let act = continue_reconcile(model, janitor_id);
    let c = s.controller_and_externals[janitor_id].controller;
    let in2 = ControllerActionInput { recv: msg_o, scheduled_cr_key: Some(key), rpc_id_allocator: s.rpc_id_allocator };
    let rs = c.ongoing_reconciles[key];
    assert(c.ongoing_reconciles.contains_key(key));
    assert(key.kind == model.kind);
    assert(model.kind == inner_kind(sk, bnd));
    assert(tc.cluster.controller_models.contains_key(janitor_id));
    assert(controller_crs_ok(tc, c));
    assert(rs.triggering_cr.kind == key.kind && stored_object_ok(tc, rs.triggering_cr));
    lemma_inner_unmarshals(sk, bnd, spec_ok, tc.cluster, rs.triggering_cr);
    let inner = unmarshal(inner_kind(sk, bnd), rs.triggering_cr)->Ok_0;
    assert(inner.metadata == rs.triggering_cr.metadata);
    let resp_c = if msg_o is Some {
        if msg_o->0.content is APIResponse {
            Some(ResponseContent::KubernetesResponse(msg_o->0.content->APIResponse_0))
        } else {
            Some(ResponseContent::ExternalResponse(msg_o->0.content->ExternalResponse_0))
        }
    } else {
        None
    };
    let (ls_prime, req_c) = (model.transition)(rs.triggering_cr, resp_c, rs.local_state);
    assert(req_c is Some);
    assert(req_c->0 is KubernetesRequest);
    let req = req_c->0->KubernetesRequest_0;
    assert(m == controller_req_msg(janitor_id, key, s.rpc_id_allocator.allocate().1, req));
    assert(m.content->APIRequest_0 == req);
    let resp_um = match resp_c {
        None => None,
        Some(x) => Some(match x {
            ResponseContent::KubernetesResponse(api_resp) => ResponseView::<VoidERespView>::KResponse(api_resp),
            ResponseContent::ExternalResponse(ext_resp) => ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(ext_resp)->Ok_0),
        }),
    };
    let state = janitor_reconciler::WidgetJanitorReconcileState::unmarshal(rs.local_state)->Ok_0;
    let (state_prime, req_um) = janitor_reconciler::reconcile_core(sk, bnd, inner, resp_um, state);
    assert(req_um is Some && req_um->0 is KRequest && req_um->0->KRequest_0 == req);
    match state.reconcile_step {
        WidgetJanitorStepView::AfterListOuter => {
            assert(req == APIRequest::DeleteRequest(DeleteRequest {
                key: inner.object_ref(),
                preconditions: Some(PreconditionsView::default().with_uid_from_object_meta(inner.metadata)),
            }));
        },
        _ => { assert(false); },
    }
}

// One controller step: the janitor's own state keeps issued uids, and the one
// request it may send, if a Delete, names one.
proof fn lemma_janitor_uids_issued_controller_step(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, janitor_id: int, s: MultiClusterState<ClusterIdView>, s_prime: MultiClusterState<ClusterIdView>, input: (int, Option<Message>, Option<ObjectRef>))
    requires widget_multi_cluster_ok(sk, bnd, tc),
        tc.cluster.synced_type_is_installed(inner_kind(sk, bnd), spec_ok, sk.selector),
        tc.cluster.controller_models.contains_pair(janitor_id, widget_janitor_controller_model(sk, bnd)),
        inv(tc, s),
        janitor_uids_issued(sk, bnd, janitor_id)(s),
        tc.controller_next().forward(input)(s, s_prime),
    ensures janitor_uids_issued(sk, bnd, janitor_id)(s_prime),
{
    reveal(inv);
    broadcast use group_multiset_axioms;
    lemma_step_projects(sk, bnd, tc, s, s_prime, ClusterIdView::Primary, Step::ControllerStep(input));
    let p = s.project(ClusterIdView::Primary);
    let p_prime = s_prime.project(ClusterIdView::Primary);
    let (id, msg_o, key_o) = input;
    let key = key_o->0;
    assert(key_o is Some);
    assert(p_prime.api_server == p.api_server);
    assert(s_prime.store(ClusterIdView::Primary) == s.store(ClusterIdView::Primary));
    assert(s_prime.store(ClusterIdView::Remote(bnd)) == s.store(ClusterIdView::Remote(bnd)));
    let model = tc.cluster.controller_models[id].reconcile_model;
    let sm = tc.cluster.controller(id);
    let c = s.controller_and_externals[id].controller;
    let in2 = ControllerActionInput { recv: msg_o, scheduled_cr_key: key_o, rpc_id_allocator: s.rpc_id_allocator };
    let st = choose |step: ControllerStep| (#[trigger] (sm.step_to_action)(step).precondition)((sm.action_input)(step, in2), c);
    let host = sm.next_result(in2, c);
    assert(host == ActionResult::Enabled(((sm.step_to_action)(st).transition)(in2, c).0, ((sm.step_to_action)(st).transition)(in2, c).1));
    let sent = host->Enabled_1.send;
    assert(s_prime.controller_and_externals == s.controller_and_externals.insert(id, ControllerAndExternalState { controller: host->Enabled_0, ..s.controller_and_externals[id] }));
    assert(s_prime.network.in_flight == (if msg_o is Some { s.network.in_flight.remove(msg_o->0) } else { s.network.in_flight }).add(sent));
    // Whatever is sent comes from this controller, at its key, out of ContinueReconcile.
    assert forall |m: Message| #[trigger] sent.contains(m) implies m.src == HostId::Controller(id, key) && st is ContinueReconcile by {
        match st {
            ControllerStep::RunScheduledReconcile => {},
            ControllerStep::ContinueReconcile => {},
            ControllerStep::EndReconcile => {},
        }
    }
    let cj = s.controller_and_externals[janitor_id].controller;
    let cj_prime = s_prime.controller_and_externals[janitor_id].controller;
    if id == janitor_id {
        assert(cj_prime == host->Enabled_0);
        match st {
            ControllerStep::RunScheduledReconcile => {
                assert(cj_prime.scheduled_reconciles == cj.scheduled_reconciles.remove(key));
                assert(cj_prime.ongoing_reconciles[key].triggering_cr == cj.scheduled_reconciles[key]);
                assert forall |k: ObjectRef| #[trigger] cj_prime.ongoing_reconciles.contains_key(k)
                    implies cj_prime.ongoing_reconciles[k].triggering_cr.metadata.uid is Some
                        && cj_prime.ongoing_reconciles[k].triggering_cr.metadata.uid->0 < s_prime.store(ClusterIdView::Remote(bnd)).uid_counter by {
                    if k != key { assert(cj_prime.ongoing_reconciles[k] == cj.ongoing_reconciles[k]); }
                }
            },
            ControllerStep::ContinueReconcile => {
                let rs = cj.ongoing_reconciles[key];
                assert(cj_prime.scheduled_reconciles == cj.scheduled_reconciles);
                assert forall |k: ObjectRef| #[trigger] cj_prime.ongoing_reconciles.contains_key(k)
                    implies cj_prime.ongoing_reconciles[k].triggering_cr.metadata.uid is Some
                        && cj_prime.ongoing_reconciles[k].triggering_cr.metadata.uid->0 < s_prime.store(ClusterIdView::Remote(bnd)).uid_counter by {
                    if k == key {
                        assert(cj_prime.ongoing_reconciles[k].triggering_cr == rs.triggering_cr);
                    } else {
                        assert(cj_prime.ongoing_reconciles[k] == cj.ongoing_reconciles[k]);
                    }
                }
            },
            ControllerStep::EndReconcile => {
                assert(cj_prime.scheduled_reconciles == cj.scheduled_reconciles);
                assert(cj_prime.ongoing_reconciles == cj.ongoing_reconciles.remove(key));
            },
        }
    } else {
        assert(s_prime.controller_and_externals[janitor_id] == s.controller_and_externals[janitor_id]);
    }
    assert forall |m: Message| {
        &&& #[trigger] s_prime.in_flight().contains(m)
        &&& m.src.is_controller_id(janitor_id)
        &&& m.content is APIRequest
        &&& m.content.is_delete_request()
    } implies janitor_delete_uid_issued(sk, bnd, m, s_prime) by {
        if s.in_flight().contains(m) {
            assert(janitor_delete_uid_issued(sk, bnd, m, s));
        } else {
            assert(sent.contains(m));
            assert(id == janitor_id);
            assert(st is ContinueReconcile);
            assert((sm.step_to_action)(st) == continue_reconcile(model, janitor_id));
            lemma_janitor_sends_issued_uid(sk, bnd, spec_ok, tc, janitor_id, s, key, msg_o, m);
        }
    }
}

// janitor_uids_issued is kept by every step of the multi-store model.
proof fn lemma_janitor_uids_issued_step(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, janitor_id: int, s: MultiClusterState<ClusterIdView>, s_prime: MultiClusterState<ClusterIdView>, side: ClusterIdView, step: Step)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        tc.cluster.synced_type_is_installed(inner_kind(sk, bnd), spec_ok, sk.selector),
        tc.cluster.controller_models.contains_pair(janitor_id, widget_janitor_controller_model(sk, bnd)),
        models_ok(tc),
        inv(tc, s),
        janitor_uids_issued(sk, bnd, janitor_id)(s),
        tc.next_step(s, s_prime, side, step),
    ensures janitor_uids_issued(sk, bnd, janitor_id)(s_prime),
{
    reveal(inv);
    broadcast use group_multiset_axioms;
    lemma_widget_sides(sk, bnd, tc);
    let x = step_side(tc, side, step);
    lemma_step_projects(sk, bnd, tc, s, s_prime, side, step);
    let p = s.project(x);
    let p_prime = s_prime.project(x);
    let c = s.controller_and_externals[janitor_id].controller;
    match step {
        Step::APIServerStep(input) => {
            lemma_janitor_uids_issued_api_server_step(sk, bnd, tc, janitor_id, s, s_prime, side, input);
        },
        Step::ControllerStep(input) => {
            lemma_janitor_uids_issued_controller_step(sk, bnd, spec_ok, tc, janitor_id, s, s_prime, input);
        },
        Step::ScheduleControllerReconcileStep(input) => {
            let (id, key) = input;
            assert(p_prime.api_server == p.api_server);
            assert(p_prime.network == p.network);
            assert(s_prime.store(ClusterIdView::Primary) == s.store(ClusterIdView::Primary));
            assert(s_prime.store(ClusterIdView::Remote(bnd)) == s.store(ClusterIdView::Remote(bnd)));
            if id == janitor_id {
                assert(key.kind == inner_kind(sk, bnd));
                assert(x == ClusterIdView::Remote(bnd));
                let c_prime = s_prime.controller_and_externals[janitor_id].controller;
                assert(c_prime.scheduled_reconciles == c.scheduled_reconciles.insert(key, s.store(ClusterIdView::Remote(bnd)).resources[key]));
                assert(c_prime.ongoing_reconciles == c.ongoing_reconciles);
                assert(s.store(ClusterIdView::Remote(bnd)).resources.contains_key(key));
            } else {
                assert(s_prime.controller_and_externals[janitor_id] == s.controller_and_externals[janitor_id]);
            }
        },
        Step::RestartControllerStep(input) => {
            assert(p_prime.api_server == p.api_server);
            assert(p_prime.network == p.network);
            if input == janitor_id {
                let c_prime = s_prime.controller_and_externals[janitor_id].controller;
                assert(c_prime.scheduled_reconciles == Map::<ObjectRef, DynamicObjectView>::empty());
                assert(c_prime.ongoing_reconciles == Map::<ObjectRef, OngoingReconcile>::empty());
            } else {
                assert(s_prime.controller_and_externals[janitor_id] == s.controller_and_externals[janitor_id]);
            }
        },
        Step::ExternalStep(input) => {
            assert(tc.cluster.controller_models.contains_key(input.0));
            assert(false);
        },
        _ => {
            // The garbage collector, the pod monkey, a dropped request and the
            // environment switches: no store and no controller state changes,
            // and what enters the network is a response or carries no
            // controller source.
            assert(p_prime.api_server == p.api_server);
            assert(s_prime.controller_and_externals[janitor_id].controller == c);
            assert forall |m: Message| {
                &&& #[trigger] s_prime.in_flight().contains(m)
                &&& m.src.is_controller_id(janitor_id)
                &&& m.content is APIRequest
                &&& m.content.is_delete_request()
            } implies janitor_delete_uid_issued(sk, bnd, m, s_prime) by {
                assert(s.in_flight().contains(m));
            }
        },
    }
}

// janitor_uids_issued holds along every simulated execution from an initial state.
proof fn lemma_janitor_uids_issued_at(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, janitor_id: int, i: nat)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        tc.init()(state_at(ex, 0)),
        tc.cluster.synced_type_is_installed(inner_kind(sk, bnd), spec_ok, sk.selector),
        tc.cluster.controller_models.contains_pair(janitor_id, widget_janitor_controller_model(sk, bnd)),
    ensures janitor_uids_issued(sk, bnd, janitor_id)(state_at(ex, i)),
    decreases i,
{
    if i == 0 {
        lemma_janitor_uids_issued_init(sk, bnd, tc, janitor_id, state_at(ex, 0));
    } else {
        let j = (i - 1) as nat;
        lemma_janitor_uids_issued_at(sk, bnd, spec_ok, tc, r, ex, janitor_id, j);
        lemma_widget_sim_inv(sk, bnd, tc, r, ex, j);
        let s = state_at(ex, j);
        let s_prime = state_at(ex, j + 1);
        assert(tc.next()(s, s_prime));
        let (side, step) = choose |side: ClusterIdView, step: Step| tc.next_step(s, s_prime, side, step);
        lemma_janitor_uids_issued_step(sk, bnd, spec_ok, tc, janitor_id, s, s_prime, side, step);
        assert(j + 1 == i);
    }
}

// ---------------------------------------------------------------------------
// The janitor's delete soundness, read on many clusters.
// ---------------------------------------------------------------------------

// A Delete the janitor has in flight names a uid the store of its kind has
// issued (below that store's uid counter), and if the object it would remove,
// in that store, is a mirror with that uid, no outer copy in the primary store
// carries the mirror's parent uid. Of the one-store fact, the object clause is
// pulled back through the relabeling and the counter clause is
// janitor_uids_issued, an invariant of the multi-store model. The remaining
// clause of parent_absent_forever, that no uid at or above the primary counter
// names the parent, is not stated: a primary uid the primary counter never
// reaches relabels to a negative value, which no one-store fact rules out of an
// annotation.
pub open spec fn multi_cluster_janitor_delete_is_sound(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, msg: Message, s: MultiClusterState<ClusterIdView>) -> bool {
    let req = msg.content.get_delete_request();
    let side = tc.side_of_kind(req.key.kind);
    let store = s.store(side).resources;
    let obj = store[req.key];
    &&& req.preconditions is Some
    &&& req.preconditions->0.uid is Some
    &&& req.preconditions->0.uid->0 < s.store(side).uid_counter
    &&& (store.contains_key(req.key) && obj.metadata.uid == req.preconditions->0.uid && snapshot_is_mirror(inner_kind(sk, bnd), obj))
        ==> forall |k: ObjectRef| #[trigger] s.store(ClusterIdView::Primary).resources.contains_key(k) && k.kind == sk.outer_kind
            && s.store(ClusterIdView::Primary).resources[k].metadata.uid is Some
            && cluster_of_dynamic(sk.selector, s.store(ClusterIdView::Primary).resources[k]) == Some(bnd.name)
            ==> int_to_string_view(s.store(ClusterIdView::Primary).resources[k].metadata.uid->0) != snapshot_parent(inner_kind(sk, bnd), obj)
}

pub open spec fn multi_cluster_janitor_deletes_are_sound(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, controller_id: int) -> StatePred<MultiClusterState<ClusterIdView>> {
    |s: MultiClusterState<ClusterIdView>| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.content is APIRequest
            &&& msg.content.is_delete_request()
        } ==> multi_cluster_janitor_delete_is_sound(sk, bnd, tc, msg, s)
    }
}

// The object clause comes from the abstract state, where janitor_delete_is_sound
// holds; the counter clause from janitor_uids_issued.
proof fn lemma_janitor_sound_pull_back(sk: SyncKind, bnd: Binding, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, s: MultiClusterState<ClusterIdView>, controller_id: int, uid_next: Uid, rv_next: ResourceVersion)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_relabeling(tc, r),
        inv(tc, s),
        janitor_uids_issued(sk, bnd, controller_id)(s),
        janitor_deletes_are_sound(sk, bnd, controller_id)(abs(tc, r, s, uid_next, rv_next)),
    ensures multi_cluster_janitor_deletes_are_sound(sk, bnd, tc, controller_id)(s),
{
    reveal(inv);
    lemma_widget_sides(sk, bnd, tc);
    let a = abs(tc, r, s, uid_next, rv_next);
    assert forall |msg: Message| {
        &&& #[trigger] s.in_flight().contains(msg)
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.content is APIRequest
        &&& msg.content.is_delete_request()
    } implies multi_cluster_janitor_delete_is_sound(sk, bnd, tc, msg, s) by {
        let m1 = relabel_msg(tc, r, msg);
        lemma_relabel_msgs_contains(tc, r, s.network.in_flight, msg);
        assert(a.in_flight().contains(m1));
        assert(janitor_delete_is_sound(sk, bnd, m1, a));
        let req = msg.content.get_delete_request();
        let side = tc.side_of_kind(req.key.kind);
        let store = s.store(side).resources;
        assert(janitor_delete_uid_issued(sk, bnd, msg, s));
        assert(side == ClusterIdView::Remote(bnd));
        assert(req.preconditions->0.uid->0 < s.store(side).uid_counter);
        lemma_abs_object(sk, bnd, tc, r, s, req.key, uid_next, rv_next);
        if store.contains_key(req.key) && store[req.key].metadata.uid == req.preconditions->0.uid && snapshot_is_mirror(inner_kind(sk, bnd), store[req.key]) {
            let obj = store[req.key];
            let obj1 = relabel_obj(tc, r, obj);
            lemma_unmarshal_inner_relabel(sk, bnd, tc, r, obj);
            let inner = unmarshal(inner_kind(sk, bnd), obj)->Ok_0;
            assert(unmarshal(inner_kind(sk, bnd), obj1)->Ok_0 == relabel_synced(tc, r, inner));
            lemma_parent_annotation_relabel(sk, bnd, tc, r, inner);
            assert(snapshot_is_mirror(inner_kind(sk, bnd), obj1));
            assert(snapshot_parent(inner_kind(sk, bnd), obj1) == relabel_uid_string(r.uid, snapshot_parent(inner_kind(sk, bnd), obj)));
            assert(a.resources()[req.key] == obj1);
            assert(obj1.metadata.uid == m1.content.get_delete_request().preconditions->0.uid);
            assert(parent_absent_forever(sk, bnd, snapshot_parent(inner_kind(sk, bnd), obj1))(a));
            assert forall |k: ObjectRef| #[trigger] s.store(ClusterIdView::Primary).resources.contains_key(k) && k.kind == sk.outer_kind
                && s.store(ClusterIdView::Primary).resources[k].metadata.uid is Some
                && cluster_of_dynamic(sk.selector, s.store(ClusterIdView::Primary).resources[k]) == Some(bnd.name)
                implies int_to_string_view(s.store(ClusterIdView::Primary).resources[k].metadata.uid->0) != snapshot_parent(inner_kind(sk, bnd), obj) by {
                lemma_abs_object(sk, bnd, tc, r, s, k, uid_next, rv_next);
                let w = s.store(ClusterIdView::Primary).resources[k].metadata.uid->0;
                assert(a.resources().contains_key(k));
                assert(a.resources()[k].metadata.uid == Some((r.uid)(ClusterIdView::Primary, w)));
                assert(int_to_string_view((r.uid)(ClusterIdView::Primary, w)) != snapshot_parent(inner_kind(sk, bnd), obj1));
                lemma_uid_string_eq(tc.sides, r.uid, snapshot_parent(inner_kind(sk, bnd), obj), w);
            }
        }
    }
}

pub proof fn lemma_janitor_sound_transfer(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, r: Relabeling<ClusterIdView>, ex: Execution<MultiClusterState<ClusterIdView>>, controller_id: int)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        widget_sim(sk, bnd, tc, r, ex),
        tc.init()(state_at(ex, 0)),
        tc.cluster.synced_type_is_installed(inner_kind(sk, bnd), spec_ok, sk.selector),
        tc.cluster.controller_models.contains_pair(controller_id, widget_janitor_controller_model(sk, bnd)),
        always(lift_state(janitor_deletes_are_sound(sk, bnd, controller_id))).satisfied_by(alpha(tc, r, ex)),
    ensures always(lift_state(multi_cluster_janitor_deletes_are_sound(sk, bnd, tc, controller_id))).satisfied_by(ex),
{
    let ex1 = alpha(tc, r, ex);
    assert forall |i: nat| #[trigger] lift_state(multi_cluster_janitor_deletes_are_sound(sk, bnd, tc, controller_id)).satisfied_by(ex.suffix(i)) by {
        assert(lift_state(janitor_deletes_are_sound(sk, bnd, controller_id)).satisfied_by(ex1.suffix(i)));
        assert(ex1.suffix(i).head() == abs_at(tc, r, ex, i));
        assert(ex.suffix(i).head() == state_at(ex, i));
        lemma_widget_sim_inv(sk, bnd, tc, r, ex, i);
        lemma_janitor_uids_issued_at(sk, bnd, spec_ok, tc, r, ex, controller_id, i);
        let s = state_at(ex, i);
        lemma_janitor_sound_pull_back(sk, bnd, tc, r, s, controller_id, uid_sum(tc, s), rv_sum(tc, s));
    }
}

// ---------------------------------------------------------------------------
// Closed statements, for any configuration.
// ---------------------------------------------------------------------------

// What the refinement needs of the kinds, for any configuration: the outer kind
// is not the binding's mirror kind, which is lemma_outer_kind_is_not_inner under
// sync_kind_ok -- the injectivity of model_kind, not the length of a name.
pub proof fn lemma_widget_kinds_ok(sk: SyncKind, bnd: Binding)
    requires sync_kind_ok(sk), sk.selector is Field,
    ensures widget_kinds_ok(sk, bnd),
{
    lemma_outer_kind_is_not_inner(sk, bnd);
}

// The sides of a configuration: the primary cluster and the inner cluster of
// every binding of every configured kind.
pub open spec fn sides_of_bindings(bindings: Set<Binding>) -> Set<ClusterIdView> {
    Set::<ClusterIdView>::empty().insert(ClusterIdView::Primary).union(bindings.map(|b: Binding| ClusterIdView::Remote(b)))
}

// The multi-store cluster of a one-store cluster and a set of bindings: one
// store per side, a kind routed to the cluster its model kind names when that is
// one of the sides, and to the primary cluster otherwise. A mirror kind of a
// binding nobody serves is never installed, so nothing writes it: request_ok
// refuses a write of an uninstalled custom kind, and store_sided keeps one out
// of the primary store. A read of such a kind is answered from the primary
// store, which holds none of them; no admitted model issues one.
pub open spec fn widget_multi_cluster_for(cluster: Cluster, bindings: Set<Binding>) -> MultiCluster<ClusterIdView> {
    MultiCluster {
        cluster: cluster,
        sides: sides_of_bindings(bindings),
        home: ClusterIdView::Primary,
        side_of: |kind: Kind| if sides_of_bindings(bindings).contains(cluster_of_kind(kind)) { cluster_of_kind(kind) } else { ClusterIdView::Primary },
    }
}

pub proof fn lemma_sides_of_bindings(bindings: Set<Binding>, b: Binding)
    ensures
        sides_of_bindings(bindings).contains(ClusterIdView::Primary),
        bindings.contains(b) ==> sides_of_bindings(bindings).contains(ClusterIdView::Remote(b)),
{
    if bindings.contains(b) {
        bindings.lemma_map_contains(|b: Binding| ClusterIdView::Remote(b), ClusterIdView::Remote(b));
    }
}

// The multi-store cluster of a configuration meets widget_multi_cluster_ok for
// every kind and binding it holds: the model kinds are routed by their names,
// which sync_kind_ok and bindings_ok make injective, and every binding's side
// is one of the sides.
pub proof fn lemma_widget_multi_cluster_ok(sk: SyncKind, bnd: Binding, cluster: Cluster, bindings: Set<Binding>)
    requires
        sync_kind_ok(sk),
        bindings_ok(sk),
        sk.selector is Field,
        sk.bindings.contains(bnd),
        sk.bindings.subset_of(bindings),
    ensures widget_multi_cluster_ok(sk, bnd, widget_multi_cluster_for(cluster, bindings)),
{
    let tc = widget_multi_cluster_for(cluster, bindings);
    lemma_widget_kinds_ok(sk, bnd);
    lemma_sides_of_bindings(bindings, bnd);
    lemma_cluster_of_model_kind(sk.name, ClusterIdView::Primary);
    assert forall |kind: Kind| tc.sides.contains(#[trigger] tc.side_of_kind(kind)) by {}
    assert forall |b: Binding| #[trigger] sk.bindings.contains(b)
        implies tc.side_of_kind(inner_kind(sk, b)) == ClusterIdView::Remote(b) && tc.sides.contains(ClusterIdView::Remote(b)) by {
        lemma_cluster_of_model_kind(sk.name, ClusterIdView::Remote(b));
        lemma_sides_of_bindings(bindings, b);
    }
}

// The installed types of a configuration are ones the refinement can follow.
// Every kind of the configuration carries the same synced_installed_type, whose
// schema check reads the spec and whose transition check reads the selector field
// of the spec, so neither reads metadata; and the default status it stamps on a
// created object unmarshals, by the round trip of marshal_status.
//
// This is also where the mirror kinds are counted: the sync reconciler serves
// `sk.bindings` and refuses every other binding before it sends a request
// (spec_types::serves), so the mirror kinds the folded store must install are the
// finitely many inner_kind(sk, b) for b in sk.bindings -- exactly the names
// widget_installed_types holds.
pub proof fn lemma_widget_types(sk: SyncKind, spec_ok: spec_fn(Value) -> bool, cluster: Cluster)
    requires
        sync_kind_ok(sk),
        // The refinement asks that the API server's validation not read metadata,
        // and a `name` selector's immutability rule reads metadata.name
        // (doc/widget_sync_fanout_design.md, section 5.2).
        sk.selector is Field,
        cluster.installed_types == widget_installed_types(sk, spec_ok),
    ensures
        cluster.synced_type_is_installed(sk.outer_kind, spec_ok, sk.selector),
        forall |b: Binding| #[trigger] sk.bindings.contains(b)
            ==> cluster.synced_type_is_installed(inner_kind(sk, b), spec_ok, sk.selector),
        all_inner_kinds_installed(sk, spec_ok, cluster),
        installed_types_ignore_metadata(cluster.installed_types),
        installed_types_coherent(cluster.installed_types),
{
    let it = cluster.installed_types;
    let ty = Cluster::synced_installed_type(spec_ok, sk.selector);
    lemma_widget_types_installed(sk, spec_ok, cluster);
    assert forall |b2: Binding| sk.bindings.contains(b2)
        implies cluster.synced_type_is_installed(#[trigger] inner_kind(sk, b2), spec_ok, sk.selector) by {}
    assert forall |name: StringView, o: DynamicObjectView, m: ObjectMetaView| it.contains_key(name) && o.kind == Kind::CustomResourceKind(name)
        implies (#[trigger] (it[name].valid_object)(DynamicObjectView { metadata: m, ..o })) == (it[name].valid_object)(o) by {
        assert(it[name] == ty);
    }
    assert forall |name: StringView, o: DynamicObjectView, old: DynamicObjectView, m: ObjectMetaView, m_old: ObjectMetaView|
        it.contains_key(name) && o.kind == Kind::CustomResourceKind(name)
        implies (#[trigger] (it[name].valid_transition)(DynamicObjectView { metadata: m, ..o }, DynamicObjectView { metadata: m_old, ..old }))
            == (it[name].valid_transition)(o, old) by {
        assert(it[name] == ty);
    }
    assert forall |name: StringView| #[trigger] it.contains_key(name) implies (it[name].unmarshallable_status)((it[name].marshalled_default_status)()) by {
        assert(it[name] == ty);
        marshal_status_preserves_integrity();
    }
}

// The cluster of composition::widget_sync_reconciler::widget_pair_cluster_for is
// the pair's cluster: the sync reconciler of `sk` at `sync_id`, the janitor of
// `bnd` at `janitor_id`, and nothing else.
pub proof fn lemma_widget_is_pair_cluster(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int)
    requires
        sync_kind_ok(sk),
        sk.selector is Field,
        sk.bindings.contains(bnd),
        sync_id != janitor_id,
    ensures widget_pair_cluster(sk, bnd, spec_ok, widget_pair_cluster_for(sk, bnd, spec_ok, sync_id, janitor_id), sync_id, janitor_id),
{
    let cluster = widget_pair_cluster_for(sk, bnd, spec_ok, sync_id, janitor_id);
    lemma_widget_types(sk, spec_ok, cluster);
    assert(cluster.controller_models.dom() =~= Set::<int>::empty().insert(sync_id).insert(janitor_id));
}

// The theorem for ANY configuration: R1, R2, R3, R3s and the janitor's delete
// soundness, read on multi-store executions of the pair, with the outer copies
// in the primary store and the mirrors of `bnd` in the binding's. Nothing here is
// specific to a kind name: `sync_kind_ok` and `bindings_ok` are what the
// distinctness of the model kinds is discharged from. `bindings_ok` asks it of
// every binding `sk` serves, not only of `bnd`, because every one of them has a
// store of its own to be routed to.
pub proof fn widget_instance_multi_cluster_theorem(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int)
    requires
        sync_kind_ok(sk),
        bindings_ok(sk),
        sk.selector is Field,
        sk.bindings.contains(bnd),
        sync_id != janitor_id,
    ensures ({
        let cluster = widget_pair_cluster_for(sk, bnd, spec_ok, sync_id, janitor_id);
        let tc = widget_multi_cluster_for(cluster, sk.bindings);
        widget_multi_cluster_spec(sk, bnd, tc, sync_id, janitor_id).entails(
            multi_cluster_spec_eventually_synced(sk, bnd)
            .and(multi_cluster_status_eventually_mirrored(sk, bnd))
            .and(multi_cluster_mirrors_stably_collected(sk, bnd, tc))
            .and(multi_cluster_mirrors_eventually_collected(sk, bnd, tc))
            .and(always(lift_state(multi_cluster_janitor_deletes_are_sound(sk, bnd, tc, janitor_id))))
        )
    }),
{
    let cluster = widget_pair_cluster_for(sk, bnd, spec_ok, sync_id, janitor_id);
    let tc = widget_multi_cluster_for(cluster, sk.bindings);
    lemma_widget_multi_cluster_ok(sk, bnd, cluster, sk.bindings);
    lemma_widget_is_pair_cluster(sk, bnd, spec_ok, sync_id, janitor_id);
    lemma_pair_cluster_is_cluster_with_others(sk, bnd, spec_ok, tc, sync_id, janitor_id);
    widget_multi_cluster_theorem(sk, bnd, spec_ok, tc, sync_id, janitor_id);
}

// The demo configuration is one application of it.
pub proof fn widget_demo_multi_cluster_theorem()
    ensures ({
        let cluster = widget_cluster_instance();
        let (k, b, bs, spec_ok) = (widget_kind(), widget_binding(), widget_bindings(), widget_spec_ok());
        let tc = widget_multi_cluster_for(cluster, bs);
        widget_multi_cluster_spec(k, b, tc, widget_sync_id(), widget_janitor_id()).entails(
            multi_cluster_spec_eventually_synced(k, b)
            .and(multi_cluster_status_eventually_mirrored(k, b))
            .and(multi_cluster_mirrors_stably_collected(k, b, tc))
            .and(multi_cluster_mirrors_eventually_collected(k, b, tc))
            .and(always(lift_state(multi_cluster_janitor_deletes_are_sound(k, b, tc, widget_janitor_id()))))
        )
    }),
{
    widget_demo_config_ok();
    assert(widget_kind().bindings =~= widget_bindings());
    widget_instance_multi_cluster_theorem(widget_kind(), widget_binding(), widget_spec_ok(), widget_sync_id(), widget_janitor_id());
}

// ---------------------------------------------------------------------------
// The pair with the disturber, on many stores.
// ---------------------------------------------------------------------------

// The disturber is admitted beside the pair: its model sends only Patches and
// Deletes (request_ok holds of both), commutes with the relabeling, and the
// pair's relies hold of it through Welder: the core of the disturber alone
// (composition/widget_disturber_reconciler.rs) gives its guarantee under the
// model of a registry holding only the disturber, which declares no fairness,
// and the guarantee implies both relies (proof/disturber.rs).
pub proof fn lemma_disturber_is_other_controller_ok(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, tc: MultiCluster<ClusterIdView>, sync_id: int, janitor_id: int, id: int)
    requires widget_multi_cluster_ok(sk, bnd, tc),
        tc.cluster.synced_type_is_installed(inner_kind(sk, bnd), spec_ok, sk.selector),
        tc.cluster.controller_models.contains_pair(id, widget_disturber_controller_model(inner_kind(sk, bnd))),
    ensures widget_other_controller_ok(sk, bnd, tc, sync_id, janitor_id, id),
{
    let m = tc.cluster.controller_models[id];
    assert(m == widget_disturber_controller_model(inner_kind(sk, bnd)));
    assert forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState| {
        let req_o = (#[trigger] (m.reconcile_model.transition)(cr, resp, ls)).1;
        req_o is Some && req_o->0 is KubernetesRequest ==> tc.request_ok(req_o->0->KubernetesRequest_0)
    } by {
        let req_o = (m.reconcile_model.transition)(cr, resp, ls).1;
        if req_o is Some && req_o->0 is KubernetesRequest {
            let state = disturber_reconciler::WidgetDisturberReconcileState::unmarshal(ls)->Ok_0;
            match state.reconcile_step {
                disturber_reconciler::WidgetDisturberStepView::Init => {},
                disturber_reconciler::WidgetDisturberStepView::AfterPatchInner => {},
                _ => {},
            }
        }
    }
    assert forall |r: Relabeling<ClusterIdView>| widget_relabeling(tc, r) implies #[trigger] other_model_commutes(tc, r, m) by {
        let rm = m.reconcile_model;
        let t = rm.transition;
        assert forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState|
            cr.kind == rm.kind && stored_object_ok(tc, cr)
            implies #[trigger] t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls)
                == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1)) by {
            lemma_disturber_model_commutes(sk, bnd, spec_ok, tc, r, cr, resp, ls);
        }
    }
    // The relies, through Welder.
    let cc = CoreCluster { cluster: tc.cluster, registry: Map::<int, ControllerSpec>::empty().insert(id, widget_disturber_controller_spec(sk, bnd, spec_ok, id)) };
    let cs = widget_disturber_core_set(id);
    assert(cs.members.contains(id));
    assert(well_formed(cc, cs)) by {
        assert forall |i: int| #[trigger] cs.members.contains(i) implies cc.registry.contains_key(i) && (cc.registry[i].membership)(cc.cluster, i) by {
            assert(i == id);
        }
    }
    widget_disturber_singleton_core_holds(sk, bnd, spec_ok, cc, id);
    lemma_core_member_guarantee(sk, bnd, cc, cs, id);
    assert(cc.registry[id].safety_guarantee == always(lift_state(widget_disturber_guarantee(id))));
    assert(pair_spec_covers(sk, bnd, tc.cluster, sync_id, janitor_id, cc)) by {
        let spec = widget_one_cluster_spec(sk, bnd, tc.cluster, sync_id, janitor_id);
        assert forall |i: int| #[trigger] cc.registry.contains_key(i) implies spec.entails((cc.registry[i].fairness)(tc.cluster)) by {
            assert(i == id);
            assert((cc.registry[i].fairness)(tc.cluster) == true_pred::<ClusterState>());
        }
    }
    disturber_guarantee_implies_relies(sk, id);
    lemma_relies_hold_of_from_welder(sk, bnd, tc.cluster, sync_id, janitor_id, id, cc, widget_disturber_guarantee(id));
}


// The three-controller cluster of composition/widget_disturber_reconciler.rs
// meets the same hypotheses, for ANY configuration, with the disturber as the one
// other controller.
pub proof fn lemma_widget_disturbed_is_cluster_with_others(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int, disturber_id: int)
    requires
        sync_kind_ok(sk),
        bindings_ok(sk),
        sk.selector is Field,
        sk.bindings.contains(bnd),
        sync_id != janitor_id,
        sync_id != disturber_id,
        janitor_id != disturber_id,
    ensures widget_cluster_with_others(sk, bnd, spec_ok,
        widget_multi_cluster_for(widget_disturbed_cluster_for(sk, bnd, spec_ok, sync_id, janitor_id, disturber_id), sk.bindings), sync_id, janitor_id),
{
    let cluster = widget_disturbed_cluster_for(sk, bnd, spec_ok, sync_id, janitor_id, disturber_id);
    let tc = widget_multi_cluster_for(cluster, sk.bindings);
    lemma_widget_multi_cluster_ok(sk, bnd, cluster, sk.bindings);
    lemma_widget_types(sk, spec_ok, cluster);
    assert forall |id: int| #[trigger] cluster.controller_models.contains_key(id) && id != sync_id && id != janitor_id
        implies widget_other_controller_ok(sk, bnd, tc, sync_id, janitor_id, id) by {
        assert(id == disturber_id);
        lemma_disturber_is_other_controller_ok(sk, bnd, spec_ok, tc, sync_id, janitor_id, id);
    }
}

// The same theorem with the disturber beside the pair, for ANY configuration: an
// out-of-band actor that patches and deletes mirrors in the binding's store,
// admitted by the pair's relies.
pub proof fn widget_disturbed_multi_cluster_theorem(sk: SyncKind, bnd: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int, disturber_id: int)
    requires
        sync_kind_ok(sk),
        bindings_ok(sk),
        sk.selector is Field,
        sk.bindings.contains(bnd),
        sync_id != janitor_id,
        sync_id != disturber_id,
        janitor_id != disturber_id,
    ensures ({
        let cluster = widget_disturbed_cluster_for(sk, bnd, spec_ok, sync_id, janitor_id, disturber_id);
        let tc = widget_multi_cluster_for(cluster, sk.bindings);
        widget_multi_cluster_spec(sk, bnd, tc, sync_id, janitor_id).entails(
            multi_cluster_spec_eventually_synced(sk, bnd)
            .and(multi_cluster_status_eventually_mirrored(sk, bnd))
            .and(multi_cluster_mirrors_stably_collected(sk, bnd, tc))
            .and(multi_cluster_mirrors_eventually_collected(sk, bnd, tc))
            .and(always(lift_state(multi_cluster_janitor_deletes_are_sound(sk, bnd, tc, janitor_id))))
        )
    }),
{
    let cluster = widget_disturbed_cluster_for(sk, bnd, spec_ok, sync_id, janitor_id, disturber_id);
    let tc = widget_multi_cluster_for(cluster, sk.bindings);
    lemma_widget_multi_cluster_ok(sk, bnd, cluster, sk.bindings);
    lemma_widget_disturbed_is_cluster_with_others(sk, bnd, spec_ok, sync_id, janitor_id, disturber_id);
    widget_multi_cluster_theorem(sk, bnd, spec_ok, tc, sync_id, janitor_id);
}

// The demo configuration with the disturber is one application of it.
pub proof fn widget_demo_disturbed_multi_cluster_theorem()
    ensures ({
        let cluster = widget_disturbed_cluster_instance();
        let (k, b, bs, spec_ok) = (widget_kind(), widget_binding(), widget_bindings(), widget_spec_ok());
        let tc = widget_multi_cluster_for(cluster, bs);
        widget_multi_cluster_spec(k, b, tc, widget_sync_id(), widget_janitor_id()).entails(
            multi_cluster_spec_eventually_synced(k, b)
            .and(multi_cluster_status_eventually_mirrored(k, b))
            .and(multi_cluster_mirrors_stably_collected(k, b, tc))
            .and(multi_cluster_mirrors_eventually_collected(k, b, tc))
            .and(always(lift_state(multi_cluster_janitor_deletes_are_sound(k, b, tc, widget_janitor_id()))))
        )
    }),
{
    widget_demo_config_ok();
    assert(widget_kind().bindings =~= widget_bindings());
    widget_disturbed_multi_cluster_theorem(widget_kind(), widget_binding(), widget_spec_ok(), widget_sync_id(), widget_janitor_id(), widget_disturber_id());
}

}
