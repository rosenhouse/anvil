// The Widget controllers in the two-store model: the outer copies live in the
// primary store, the mirrors in the remote one. This module instantiates the
// refinement of kubernetes_cluster::proof::two_cluster for them: the annotation
// hook that carries a parent uid across the relabeling, the proof that both
// reconcilers commute with the relabeling, and the reading of R1, R2 and R3s
// on two-store executions.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::proof::two_cluster::{api_server::*, execution::*, fairness::*, relabel::*, steps::*};
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, api_server::types::*, builtin_controllers::types::*, cluster::*, controller::types::*, message::*, two_cluster::*,
};
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::vstd_ext::string_view::*;
use crate::composition::{widget_janitor_reconciler::*, widget_sync_reconciler::*};
use crate::widget_sync_controller::{
    model::{install::*, janitor_reconciler, sync_reconciler},
    proof::{guarantee::*, liveness::{janitor_proof::*, spec::*, sync_spec_proof::*, sync_status_proof::*, cleanup_proof::*}, predicate::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::{map_lib::*, prelude::*, seq_lib::*, set_lib::*, string::*};

verus! {

// ---------------------------------------------------------------------------
// The two-store cluster and its hook.
// ---------------------------------------------------------------------------

pub open spec fn widget_two_cluster(cluster: Cluster) -> TwoCluster {
    TwoCluster { cluster: cluster, remote_kinds: Set::<Kind>::empty().insert(InnerWidgetView::kind()) }
}

pub proof fn lemma_widget_sides(cluster: Cluster)
    ensures
        widget_two_cluster(cluster).side_of_kind(OuterWidgetView::kind()) == Side::Primary,
        widget_two_cluster(cluster).side_of_kind(InnerWidgetView::kind()) == Side::Remote,
{
    reveal_strlit("widget");
    reveal_strlit("widget@inner");
    assert("widget"@.len() != "widget@inner"@.len());
}

// A uid written as a string follows the uid of the primary side; other strings
// are left alone.
pub open spec fn relabel_uid_string(u: spec_fn(Side, Uid) -> Uid, v: StringView) -> StringView {
    if exists |i: int| v == #[trigger] int_to_string_view(i) {
        int_to_string_view(u(Side::Primary, choose |i: int| v == #[trigger] int_to_string_view(i)))
    } else {
        v
    }
}

// Only the parent-uid annotation carries a uid.
pub open spec fn widget_hook() -> Hook {
    |u: spec_fn(Side, Uid) -> Uid, v: spec_fn(Side, ResourceVersion) -> ResourceVersion|
        |kind: Kind, key: StringView, val: StringView| if key == parent_uid_key() { relabel_uid_string(u, val) } else { val }
}

pub proof fn lemma_uid_string_of(u: spec_fn(Side, Uid) -> Uid, i: int)
    ensures relabel_uid_string(u, int_to_string_view(i)) == int_to_string_view(u(Side::Primary, i)),
{
    int_to_string_view_injectivity();
    let j = choose |j: int| int_to_string_view(i) == #[trigger] int_to_string_view(j);
    assert(j == i);
}

// relabel_uid_string(u, a) names the relabeled uid i exactly when a names i.
pub proof fn lemma_uid_string_eq(u: spec_fn(Side, Uid) -> Uid, a: StringView, i: int)
    requires uid_map_injective(u),
    ensures (relabel_uid_string(u, a) == int_to_string_view(u(Side::Primary, i))) == (a == int_to_string_view(i)),
{
    int_to_string_view_injectivity();
    if exists |j: int| a == #[trigger] int_to_string_view(j) {
        let j = choose |j: int| a == #[trigger] int_to_string_view(j);
        lemma_uid_string_of(u, j);
        if u(Side::Primary, j) == u(Side::Primary, i) {
            assert(j == i);
        }
    }
}

pub proof fn lemma_widget_hook_injective()
    ensures hook_injective(widget_hook()),
{
    let hook = widget_hook();
    assert forall |u: spec_fn(Side, Uid) -> Uid, v: spec_fn(Side, ResourceVersion) -> ResourceVersion|
        uid_map_injective(u) && rv_map_injective(v) implies annotation_injective(#[trigger] hook(u, v)) by {
        let h = hook(u, v);
        assert forall |kind: Kind, key: StringView, a: StringView, b: StringView| #[trigger] h(kind, key, a) == #[trigger] h(kind, key, b) implies a == b by {
            if key == parent_uid_key() {
                int_to_string_view_injectivity();
                if exists |i: int| a == #[trigger] int_to_string_view(i) {
                    let i = choose |i: int| a == #[trigger] int_to_string_view(i);
                    lemma_uid_string_of(u, i);
                    lemma_uid_string_eq(u, b, i);
                } else if exists |j: int| b == #[trigger] int_to_string_view(j) {
                    let j = choose |j: int| b == #[trigger] int_to_string_view(j);
                    lemma_uid_string_of(u, j);
                    lemma_uid_string_eq(u, a, j);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The relabeling on the Widget views.
// ---------------------------------------------------------------------------

pub open spec fn relabel_outer(tc: TwoCluster, r: Relabeling, o: OuterWidgetView) -> OuterWidgetView {
    OuterWidgetView { metadata: relabel_meta(tc, r, OuterWidgetView::kind(), o.metadata), ..o }
}

pub open spec fn relabel_inner(tc: TwoCluster, r: Relabeling, o: InnerWidgetView) -> InnerWidgetView {
    InnerWidgetView { metadata: relabel_meta(tc, r, InnerWidgetView::kind(), o.metadata), ..o }
}

pub proof fn lemma_unmarshal_outer_relabel(tc: TwoCluster, r: Relabeling, obj: DynamicObjectView)
    ensures
        OuterWidgetView::unmarshal(relabel_obj(tc, r, obj)) is Ok == OuterWidgetView::unmarshal(obj) is Ok,
        OuterWidgetView::unmarshal(obj) is Ok ==> OuterWidgetView::unmarshal(relabel_obj(tc, r, obj))->Ok_0 == relabel_outer(tc, r, OuterWidgetView::unmarshal(obj)->Ok_0),
        !(OuterWidgetView::unmarshal(obj) is Ok) ==> OuterWidgetView::unmarshal(relabel_obj(tc, r, obj)) == OuterWidgetView::unmarshal(obj),
{
}

pub proof fn lemma_unmarshal_inner_relabel(tc: TwoCluster, r: Relabeling, obj: DynamicObjectView)
    ensures
        InnerWidgetView::unmarshal(relabel_obj(tc, r, obj)) is Ok == InnerWidgetView::unmarshal(obj) is Ok,
        InnerWidgetView::unmarshal(obj) is Ok ==> InnerWidgetView::unmarshal(relabel_obj(tc, r, obj))->Ok_0 == relabel_inner(tc, r, InnerWidgetView::unmarshal(obj)->Ok_0),
        !(InnerWidgetView::unmarshal(obj) is Ok) ==> InnerWidgetView::unmarshal(relabel_obj(tc, r, obj)) == InnerWidgetView::unmarshal(obj),
{
}

// The hypotheses the Widget instantiation works under.
pub open spec fn widget_relabeling(cluster: Cluster, r: Relabeling) -> bool {
    &&& injective(r)
    &&& r.annotation == widget_hook()(r.uid, r.rv)
}

// The parent-uid annotation of a relabeled mirror.
pub proof fn lemma_parent_annotation_relabel(cluster: Cluster, r: Relabeling, inner: InnerWidgetView)
    requires
        widget_relabeling(cluster, r),
        has_mirror_identity(inner),
    ensures
        has_mirror_identity(relabel_inner(widget_two_cluster(cluster), r, inner)),
        parent_uid_annotation(relabel_inner(widget_two_cluster(cluster), r, inner)) == relabel_uid_string(r.uid, parent_uid_annotation(inner)),
{
    let tc = widget_two_cluster(cluster);
    let m = inner.metadata.annotations->0;
    let m1 = relabel_inner(tc, r, inner).metadata.annotations->0;
    assert(m1 == Map::new(m.dom(), |k: StringView| (r.annotation)(InnerWidgetView::kind(), k, m[k])));
    assert(m1.contains_key(parent_uid_key()));
    assert(m1[parent_uid_key()] == (r.annotation)(InnerWidgetView::kind(), parent_uid_key(), m[parent_uid_key()]));
}

pub proof fn lemma_has_mirror_identity_relabel(cluster: Cluster, r: Relabeling, inner: InnerWidgetView)
    requires widget_relabeling(cluster, r),
    ensures has_mirror_identity(relabel_inner(widget_two_cluster(cluster), r, inner)) == has_mirror_identity(inner),
{
    let tc = widget_two_cluster(cluster);
    match inner.metadata.annotations {
        Some(m) => {
            let m1 = relabel_inner(tc, r, inner).metadata.annotations->0;
            assert(m1 == Map::new(m.dom(), |k: StringView| (r.annotation)(InnerWidgetView::kind(), k, m[k])));
            assert(m1.contains_key(parent_uid_key()) == m.contains_key(parent_uid_key()));
        },
        None => {},
    }
}

pub proof fn lemma_is_mirror_of_relabel(cluster: Cluster, r: Relabeling, inner: InnerWidgetView, outer: OuterWidgetView)
    requires
        widget_relabeling(cluster, r),
        outer.metadata.uid is Some,
    ensures is_mirror_of(relabel_inner(widget_two_cluster(cluster), r, inner), relabel_outer(widget_two_cluster(cluster), r, outer)) == is_mirror_of(inner, outer),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let inner1 = relabel_inner(tc, r, inner);
    let outer1 = relabel_outer(tc, r, outer);
    assert(outer1.metadata.uid == Some((r.uid)(Side::Primary, outer.metadata.uid->0)));
    lemma_has_mirror_identity_relabel(cluster, r, inner);
    if has_mirror_identity(inner) {
        lemma_parent_annotation_relabel(cluster, r, inner);
        lemma_uid_string_eq(r.uid, parent_uid_annotation(inner), outer.metadata.uid->0);
    }
}

// The mirror the sync reconciler would create for the relabeled outer copy is
// the relabeled mirror.
pub proof fn lemma_make_inner_relabel(cluster: Cluster, r: Relabeling, outer: OuterWidgetView)
    requires
        widget_relabeling(cluster, r),
        outer.metadata.uid is Some,
    ensures relabel_obj(widget_two_cluster(cluster), r, make_inner(outer).marshal()) == make_inner(relabel_outer(widget_two_cluster(cluster), r, outer)).marshal(),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let outer1 = relabel_outer(tc, r, outer);
    let lhs = relabel_obj(tc, r, make_inner(outer).marshal());
    let rhs = make_inner(outer1).marshal();
    let m = make_inner(outer).metadata.annotations->0;
    assert(m == Map::<StringView, StringView>::empty().insert(parent_uid_key(), parent_uid_of(outer)));
    let m_lhs = lhs.metadata.annotations->0;
    let m_rhs = rhs.metadata.annotations->0;
    assert(m_lhs == Map::new(m.dom(), |k: StringView| (r.annotation)(InnerWidgetView::kind(), k, m[k])));
    lemma_uid_string_of(r.uid, outer.metadata.uid->0);
    assert(parent_uid_of(outer1) == int_to_string_view((r.uid)(Side::Primary, outer.metadata.uid->0)));
    assert(m_lhs =~= m_rhs);
    assert(lhs.metadata =~= rhs.metadata);
    assert(lhs =~= rhs);
}

// ---------------------------------------------------------------------------
// The reconcilers commute with the relabeling.
// ---------------------------------------------------------------------------

pub open spec fn relabel_resp_view(tc: TwoCluster, r: Relabeling, resp: Option<ResponseView<VoidERespView>>) -> Option<ResponseView<VoidERespView>> {
    match resp {
        Some(ResponseView::KResponse(x)) => Some(ResponseView::KResponse(relabel_resp(tc, r, x))),
        _ => resp,
    }
}

pub open spec fn relabel_req_view(tc: TwoCluster, r: Relabeling, req: Option<RequestView<VoidEReqView>>) -> Option<RequestView<VoidEReqView>> {
    match req {
        Some(RequestView::KRequest(x)) => Some(RequestView::KRequest(relabel_req(tc, r, x))),
        _ => req,
    }
}

pub proof fn lemma_sync_core_commutes(cluster: Cluster, r: Relabeling, outer: OuterWidgetView, resp: Option<ResponseView<VoidERespView>>, state: sync_reconciler::WidgetSyncReconcileState)
    requires
        widget_relabeling(cluster, r),
        outer.metadata.uid is Some,
    ensures ({
        let tc = widget_two_cluster(cluster);
        let (state1, req1) = sync_reconciler::reconcile_core(outer, resp, state);
        sync_reconciler::reconcile_core(relabel_outer(tc, r, outer), relabel_resp_view(tc, r, resp), state) == (state1, relabel_req_view(tc, r, req1))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let outer1 = relabel_outer(tc, r, outer);
    let resp1 = relabel_resp_view(tc, r, resp);
    match state.reconcile_step {
        WidgetSyncStepView::Init => {},
        WidgetSyncStepView::AfterGetInner => {
            if is_some_k_get_resp_view(resp) {
                let res = extract_some_k_get_resp_view(resp);
                match res {
                    Err(_) => {
                        if res->Err_0 is ObjectNotFound {
                            lemma_make_inner_relabel(cluster, r, outer);
                        }
                    },
                    Ok(obj) => {
                        lemma_unmarshal_inner_relabel(tc, r, obj);
                        if InnerWidgetView::unmarshal(obj) is Ok {
                            let inner = InnerWidgetView::unmarshal(obj)->Ok_0;
                            let inner1 = relabel_inner(tc, r, inner);
                            assert(InnerWidgetView::unmarshal(relabel_obj(tc, r, obj))->Ok_0 == inner1);
                            lemma_is_mirror_of_relabel(cluster, r, inner, outer);
                            if inner.metadata.deletion_timestamp is None && is_mirror_of(inner, outer) && inner.spec != outer.spec {
                                let p = sync_reconciler::inner_spec_patch(inner, outer);
                                let p1 = sync_reconciler::inner_spec_patch(inner1, outer1);
                                assert(p1 == PatchRequest { tests: relabel_tests(r, Side::Remote, p.tests), ..p });
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

pub proof fn lemma_parent_listed_relabel(cluster: Cluster, r: Relabeling, objs: Seq<DynamicObjectView>, parent: StringView)
    requires widget_relabeling(cluster, r),
    ensures janitor_reconciler::parent_listed(relabel_list(widget_two_cluster(cluster), r, objs), relabel_uid_string(r.uid, parent)) == janitor_reconciler::parent_listed(objs, parent),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let f = |o: DynamicObjectView| relabel_obj(tc, r, o);
    let image = objs.to_set().map(f);
    let objs1 = relabel_list(tc, r, objs);
    image.lemma_to_seq_to_set_id();
    assert(objs1.to_set() == image);
    let parent1 = relabel_uid_string(r.uid, parent);
    int_to_string_view_injectivity();
    if janitor_reconciler::parent_listed(objs, parent) {
        let i = choose |i: int| 0 <= i < objs.len()
            && (#[trigger] objs[i]).kind == OuterWidgetView::kind()
            && objs[i].metadata.uid is Some
            && int_to_string_view(objs[i].metadata.uid->0) == parent;
        let o = objs[i];
        let o1 = f(o);
        assert(objs.to_set().contains(o));
        objs.to_set().lemma_map_contains(f, o1);
        assert(image.contains(o1));
        assert(objs1.to_set().contains(o1));
        let j = choose |j: int| 0 <= j < objs1.len() && objs1[j] == o1;
        lemma_uid_string_of(r.uid, o.metadata.uid->0);
        assert(o1.metadata.uid == Some((r.uid)(Side::Primary, o.metadata.uid->0)));
        assert((#[trigger] objs1[j]).kind == OuterWidgetView::kind() && objs1[j].metadata.uid is Some
            && int_to_string_view(objs1[j].metadata.uid->0) == parent1);
    }
    if janitor_reconciler::parent_listed(objs1, parent1) {
        let j = choose |j: int| 0 <= j < objs1.len()
            && (#[trigger] objs1[j]).kind == OuterWidgetView::kind()
            && objs1[j].metadata.uid is Some
            && int_to_string_view(objs1[j].metadata.uid->0) == parent1;
        let o1 = objs1[j];
        assert(objs1.to_set().contains(o1));
        objs.to_set().lemma_map_contains(f, o1);
        let o = choose |o: DynamicObjectView| objs.to_set().contains(o) && o1 == f(o);
        let i = choose |i: int| 0 <= i < objs.len() && objs[i] == o;
        assert(o.metadata.uid is Some);
        let w = o.metadata.uid->0;
        assert(o1.metadata.uid == Some((r.uid)(Side::Primary, w)));
        lemma_uid_string_eq(r.uid, parent, w);
        assert((#[trigger] objs[i]).kind == OuterWidgetView::kind() && objs[i].metadata.uid is Some
            && int_to_string_view(objs[i].metadata.uid->0) == parent);
    }
}

pub proof fn lemma_janitor_core_commutes(cluster: Cluster, r: Relabeling, inner: InnerWidgetView, resp: Option<ResponseView<VoidERespView>>, state: janitor_reconciler::WidgetJanitorReconcileState)
    requires widget_relabeling(cluster, r),
    ensures ({
        let tc = widget_two_cluster(cluster);
        let (state1, req1) = janitor_reconciler::reconcile_core(inner, resp, state);
        janitor_reconciler::reconcile_core(relabel_inner(tc, r, inner), relabel_resp_view(tc, r, resp), state) == (state1, relabel_req_view(tc, r, req1))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let inner1 = relabel_inner(tc, r, inner);
    lemma_has_mirror_identity_relabel(cluster, r, inner);
    match state.reconcile_step {
        WidgetJanitorStepView::Init => {},
        WidgetJanitorStepView::AfterListOuter => {
            if has_mirror_identity(inner) && is_some_k_list_resp_view(resp) && extract_some_k_list_resp_view(resp) is Ok {
                let objs = extract_some_k_list_resp_view(resp)->Ok_0;
                lemma_parent_annotation_relabel(cluster, r, inner);
                lemma_parent_listed_relabel(cluster, r, objs, parent_uid_annotation(inner));
                if !janitor_reconciler::parent_listed(objs, parent_uid_annotation(inner)) {
                    let d = DeleteRequest { key: inner.object_ref(), preconditions: Some(PreconditionsView::default().with_uid_from_object_meta(inner.metadata)) };
                    let d1 = DeleteRequest { key: inner1.object_ref(), preconditions: Some(PreconditionsView::default().with_uid_from_object_meta(inner1.metadata)) };
                    assert(d1 == DeleteRequest { preconditions: relabel_preconditions(r, Side::Remote, d.preconditions), ..d });
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
pub proof fn lemma_outer_unmarshals(cluster: Cluster, cr: DynamicObjectView)
    requires
        cluster.type_is_installed_in_cluster::<OuterWidgetView>(),
        cr.kind == OuterWidgetView::kind(),
        unmarshallable_object(cr, cluster.installed_types),
    ensures OuterWidgetView::unmarshal(cr) is Ok,
{
    OuterWidgetView::unmarshal_result_determined_by_unmarshal_spec_and_status();
}

pub proof fn lemma_inner_unmarshals(cluster: Cluster, cr: DynamicObjectView)
    requires
        cluster.type_is_installed_in_cluster::<InnerWidgetView>(),
        cr.kind == InnerWidgetView::kind(),
        unmarshallable_object(cr, cluster.installed_types),
    ensures InnerWidgetView::unmarshal(cr) is Ok,
{
    InnerWidgetView::unmarshal_result_determined_by_unmarshal_spec_and_status();
}

// The installed reconcile models commute: what models_commute asks of them.
pub proof fn lemma_sync_model_commutes(cluster: Cluster, r: Relabeling, cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState)
    requires
        widget_relabeling(cluster, r),
        cluster.type_is_installed_in_cluster::<OuterWidgetView>(),
        cr.kind == OuterWidgetView::kind(),
        cr.metadata.uid is Some,
        unmarshallable_object(cr, cluster.installed_types),
    ensures ({
        let tc = widget_two_cluster(cluster);
        let t = widget_sync_controller_model().reconcile_model.transition;
        t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls) == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_outer_unmarshals(cluster, cr);
    lemma_unmarshal_outer_relabel(tc, r, cr);
    let outer = OuterWidgetView::unmarshal(cr)->Ok_0;
    let resp_um = match resp {
        None => None,
        Some(x) => Some(match x {
            ResponseContent::KubernetesResponse(api_resp) => ResponseView::<VoidERespView>::KResponse(api_resp),
            ResponseContent::ExternalResponse(ext_resp) => ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(ext_resp)->Ok_0),
        }),
    };
    let state = sync_reconciler::WidgetSyncReconcileState::unmarshal(ls)->Ok_0;
    assert(OuterWidgetView::unmarshal(relabel_obj(tc, r, cr))->Ok_0 == relabel_outer(tc, r, outer));
    lemma_sync_core_commutes(cluster, r, outer, resp_um, state);
}

pub proof fn lemma_janitor_model_commutes(cluster: Cluster, r: Relabeling, cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState)
    requires
        widget_relabeling(cluster, r),
        cluster.type_is_installed_in_cluster::<InnerWidgetView>(),
        cr.kind == InnerWidgetView::kind(),
        unmarshallable_object(cr, cluster.installed_types),
    ensures ({
        let tc = widget_two_cluster(cluster);
        let t = widget_janitor_controller_model().reconcile_model.transition;
        t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls) == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_inner_unmarshals(cluster, cr);
    lemma_unmarshal_inner_relabel(tc, r, cr);
    let inner = InnerWidgetView::unmarshal(cr)->Ok_0;
    let resp_um = match resp {
        None => None,
        Some(x) => Some(match x {
            ResponseContent::KubernetesResponse(api_resp) => ResponseView::<VoidERespView>::KResponse(api_resp),
            ResponseContent::ExternalResponse(ext_resp) => ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(ext_resp)->Ok_0),
        }),
    };
    let state = janitor_reconciler::WidgetJanitorReconcileState::unmarshal(ls)->Ok_0;
    assert(InnerWidgetView::unmarshal(relabel_obj(tc, r, cr))->Ok_0 == relabel_inner(tc, r, inner));
    lemma_janitor_core_commutes(cluster, r, inner, resp_um, state);
}


// ---------------------------------------------------------------------------
// The hypotheses of the refinement, for the Widget pair.
// ---------------------------------------------------------------------------

// A cluster running exactly the sync reconciler and the janitor, with the two
// Widget types installed, and with installed types the refinement can follow.
pub open spec fn widget_pair_cluster(cluster: Cluster, sync_id: int, janitor_id: int) -> bool {
    &&& sync_membership(cluster, sync_id, janitor_id)
    &&& cluster.controller_models.contains_pair(janitor_id, widget_janitor_controller_model())
    &&& cluster.controller_models.dom() == Set::<int>::empty().insert(sync_id).insert(janitor_id)
    &&& installed_types_ignore_metadata(cluster.installed_types)
    &&& installed_types_coherent(cluster.installed_types)
}

pub proof fn lemma_widget_models_ok(cluster: Cluster, sync_id: int, janitor_id: int)
    requires widget_pair_cluster(cluster, sync_id, janitor_id),
    ensures models_ok(widget_two_cluster(cluster)),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    assert forall |id: int| #[trigger] tc.cluster.controller_models.contains_key(id) implies {
        let m = tc.cluster.controller_models[id];
        &&& m.external_model is None
        &&& forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState| {
            let req_o = (#[trigger] (m.reconcile_model.transition)(cr, resp, ls)).1;
            req_o is Some && req_o->0 is KubernetesRequest ==> tc.request_ok(req_o->0->KubernetesRequest_0)
        }
    } by {
        assert(id == sync_id || id == janitor_id);
        let m = tc.cluster.controller_models[id];
        assert forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState| {
            let req_o = (#[trigger] (m.reconcile_model.transition)(cr, resp, ls)).1;
            req_o is Some && req_o->0 is KubernetesRequest ==> tc.request_ok(req_o->0->KubernetesRequest_0)
        } by {
            let req_o = (m.reconcile_model.transition)(cr, resp, ls).1;
            if req_o is Some && req_o->0 is KubernetesRequest {
                let req = req_o->0->KubernetesRequest_0;
                if id == sync_id {
                    let outer = OuterWidgetView::unmarshal(cr)->Ok_0;
                    let state = sync_reconciler::WidgetSyncReconcileState::unmarshal(ls)->Ok_0;
                    match state.reconcile_step {
                        WidgetSyncStepView::AfterGetInner => {
                            // A Create of the mirror: named, of the inner kind, without owner references.
                            if req is CreateRequest {
                                let obj = make_inner(outer).marshal();
                                assert(req->CreateRequest_0.obj == obj);
                                assert(obj.metadata.owner_references is None);
                                assert(obj.kind == InnerWidgetView::kind());
                            }
                        },
                        _ => {},
                    }
                }
            }
        }
    }
}

pub proof fn lemma_widget_models_commute(cluster: Cluster, sync_id: int, janitor_id: int, r: Relabeling)
    requires
        widget_pair_cluster(cluster, sync_id, janitor_id),
        widget_relabeling(cluster, r),
    ensures models_commute(widget_two_cluster(cluster), r),
{
    let tc = widget_two_cluster(cluster);
    assert forall |id: int| #[trigger] tc.cluster.controller_models.contains_key(id) implies {
        let m = tc.cluster.controller_models[id].reconcile_model;
        let t = m.transition;
        forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState|
            cr.kind == m.kind && stored_object_ok(tc, cr)
            ==> #[trigger] t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls)
                == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1))
    } by {
        assert(id == sync_id || id == janitor_id);
        let m = tc.cluster.controller_models[id].reconcile_model;
        let t = m.transition;
        assert forall |cr: DynamicObjectView, resp: Option<ResponseContent>, ls: ReconcileLocalState|
            cr.kind == m.kind && stored_object_ok(tc, cr)
            implies #[trigger] t(relabel_obj(tc, r, cr), relabel_resp_content(tc, r, resp), ls)
                == (t(cr, resp, ls).0, relabel_req_content(tc, r, t(cr, resp, ls).1)) by {
            if id == sync_id {
                lemma_sync_model_commutes(cluster, r, cr, resp, ls);
            } else {
                lemma_janitor_model_commutes(cluster, r, cr, resp, ls);
            }
        }
    }
}

pub proof fn lemma_widget_refinement_hyps(cluster: Cluster, sync_id: int, janitor_id: int)
    requires widget_pair_cluster(cluster, sync_id, janitor_id),
    ensures refinement_hyps(widget_two_cluster(cluster), widget_hook()),
{
    let tc = widget_two_cluster(cluster);
    let hook = widget_hook();
    lemma_widget_models_ok(cluster, sync_id, janitor_id);
    lemma_widget_hook_injective();
    assert forall |r: Relabeling| injective(r) && r.annotation == hook(r.uid, r.rv) implies #[trigger] models_commute(tc, r) by {
        lemma_widget_models_commute(cluster, sync_id, janitor_id, r);
    }
}

// ---------------------------------------------------------------------------
// Fairness of the two-store model, and its transfer.
// ---------------------------------------------------------------------------

pub open spec fn two_cluster_next_with_wf(tc: TwoCluster, id: int) -> TempPred<TwoClusterState> {
    always(lift_action(tc.next()))
    .and(tla_forall(|input: (Side, Option<Message>)| tc.api_server_next(input.0).weak_fairness(input.1)))
    .and(tla_forall(|input: (Side, (BuiltinControllerChoice, ObjectRef))| tc.builtin_controllers_next(input.0).weak_fairness(input.1)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| tc.controller_next().weak_fairness((id, input.0, input.1))))
    .and(tla_forall(|input: (Side, ObjectRef)| tc.schedule_controller_reconcile(input.0).weak_fairness((id, input.1))))
    .and(tla_forall(|input: int| tc.disable_crash().weak_fairness(input)))
    .and(tc.disable_req_drop().weak_fairness(()))
    .and(tc.disable_pod_monkey().weak_fairness(()))
}

// The one-store fairness of a controller on the abstract execution.
pub proof fn lemma_next_with_wf_transfer(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>, id: int)
    requires
        fair_sim(widget_two_cluster(cluster), r, ex),
        always(lift_action(cluster.next())).satisfied_by(alpha(widget_two_cluster(cluster), r, ex)),
        two_cluster_next_with_wf(widget_two_cluster(cluster), id).satisfied_by(ex),
    ensures
        sync_next_with_wf(cluster, id).satisfied_by(alpha(widget_two_cluster(cluster), r, ex)),
        janitor_next_with_wf(cluster, id).satisfied_by(alpha(widget_two_cluster(cluster), r, ex)),
{
    let tc = widget_two_cluster(cluster);
    let ex1 = alpha(tc, r, ex);
    let f_api = |input: (Side, Option<Message>)| tc.api_server_next(input.0).weak_fairness(input.1);
    let f_gc = |input: (Side, (BuiltinControllerChoice, ObjectRef))| tc.builtin_controllers_next(input.0).weak_fairness(input.1);
    let f_ctrl = |input: (Option<Message>, Option<ObjectRef>)| tc.controller_next().weak_fairness((id, input.0, input.1));
    let f_sched = |input: (Side, ObjectRef)| tc.schedule_controller_reconcile(input.0).weak_fairness((id, input.1));
    let f_crash = |input: int| tc.disable_crash().weak_fairness(input);
    assert(tla_forall(f_api).satisfied_by(ex));
    assert(tla_forall(f_gc).satisfied_by(ex));
    assert(tla_forall(f_ctrl).satisfied_by(ex));
    assert(tla_forall(f_sched).satisfied_by(ex));
    assert(tla_forall(f_crash).satisfied_by(ex));
    assert forall |side: Side, input: Option<Message>| #[trigger] tc.api_server_next(side).weak_fairness(input).satisfied_by(ex) by {
        let i = (side, input);
        assert(f_api(i).satisfied_by(ex));
    }
    assert forall |side: Side, input: (BuiltinControllerChoice, ObjectRef)| #[trigger] tc.builtin_controllers_next(side).weak_fairness(input).satisfied_by(ex) by {
        let i = (side, input);
        assert(f_gc(i).satisfied_by(ex));
    }
    assert forall |msg: Option<Message>, key: Option<ObjectRef>| #[trigger] tc.controller_next().weak_fairness((id, msg, key)).satisfied_by(ex) by {
        let i = (msg, key);
        assert(f_ctrl(i).satisfied_by(ex));
    }
    assert forall |side: Side, key: ObjectRef| #[trigger] tc.schedule_controller_reconcile(side).weak_fairness((id, key)).satisfied_by(ex) by {
        let i = (side, key);
        assert(f_sched(i).satisfied_by(ex));
    }
    assert forall |input: int| #[trigger] tc.disable_crash().weak_fairness(input).satisfied_by(ex) by {
        assert(f_crash(input).satisfied_by(ex));
    }
    assert forall |input: Option<Message>| #[trigger] cluster.api_server_next().weak_fairness(input).satisfied_by(ex1) by {
        lemma_wf_api_server(tc, r, ex, input);
    }
    assert forall |input: (BuiltinControllerChoice, ObjectRef)| #[trigger] cluster.builtin_controllers_next().weak_fairness(input).satisfied_by(ex1) by {
        lemma_wf_builtin(tc, r, ex, input);
    }
    assert forall |input: (Option<Message>, Option<ObjectRef>)| #[trigger] cluster.controller_next().weak_fairness((id, input.0, input.1)).satisfied_by(ex1) by {
        lemma_wf_controller(tc, r, ex, id, input);
    }
    assert forall |input: ObjectRef| #[trigger] cluster.schedule_controller_reconcile().weak_fairness((id, input)).satisfied_by(ex1) by {
        lemma_wf_schedule(tc, r, ex, id, input);
    }
    assert forall |input: int| #[trigger] cluster.disable_crash().weak_fairness(input).satisfied_by(ex1) by {
        lemma_wf_disable_crash(tc, r, ex, input);
    }
    assert forall |input: Option<Message>| #[trigger] cluster.external_next().weak_fairness((id, input)).satisfied_by(ex1) by {
        lemma_wf_external(tc, r, ex, id, input);
    }
    lemma_wf_disable_req_drop(tc, r, ex);
    lemma_wf_disable_pod_monkey(tc, r, ex);
    assert(tla_forall(|input| cluster.api_server_next().weak_fairness(input)).satisfied_by(ex1));
    assert(tla_forall(|input| cluster.builtin_controllers_next().weak_fairness(input)).satisfied_by(ex1));
    assert(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((id, input.0, input.1))).satisfied_by(ex1));
    assert(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((id, input))).satisfied_by(ex1));
    assert(tla_forall(|input| cluster.disable_crash().weak_fairness(input)).satisfied_by(ex1));
    assert(tla_forall(|input| cluster.external_next().weak_fairness((id, input))).satisfied_by(ex1));
}

// ---------------------------------------------------------------------------
// The properties, read on two-store states.
// ---------------------------------------------------------------------------

// A one-store state predicate read on the store of one side.
pub open spec fn on_side(side: Side, p: StatePred<ClusterState>) -> StatePred<TwoClusterState> {
    |s: TwoClusterState| p(s.project(side))
}

// The premises of R1 and R2 on two clusters: the outer copy and the in-flight
// writes are read on the primary side; the delete clause, which looks at the
// mirror, is read on the remote side, where the mirror lives.
pub open spec fn two_cluster_outer_spec_stable(outer: OuterWidgetView) -> StatePred<TwoClusterState> {
    |s: TwoClusterState| {
        &&& outer_spec_stable(outer)(s.project(Side::Primary))
        &&& mirror_undeleted(outer)(s.project(Side::Remote))
    }
}

pub open spec fn two_cluster_outer_stable(outer: OuterWidgetView) -> StatePred<TwoClusterState> {
    |s: TwoClusterState| {
        &&& outer_stable(outer)(s.project(Side::Primary))
        &&& mirror_undeleted(outer)(s.project(Side::Remote))
    }
}

// R1 on two clusters: the outer copy is read in the primary store, the mirror in the remote one.
pub open spec fn two_cluster_spec_eventually_synced() -> TempPred<TwoClusterState> {
    tla_forall(|outer: OuterWidgetView|
        always(lift_state(two_cluster_outer_spec_stable(outer)))
            .leads_to(always(lift_state(on_side(Side::Remote, spec_synced(outer))))))
}

// R2 on two clusters.
pub open spec fn two_cluster_status_eventually_mirrored() -> TempPred<TwoClusterState> {
    tla_forall(|i: (OuterWidgetView, WidgetStatusView)|
        always(lift_state(two_cluster_outer_stable(i.0)).and(lift_state(on_side(Side::Remote, inner_settled(i.0, i.1)))))
            .leads_to(always(lift_state(on_side(Side::Primary, status_synced(i.0, i.1))))))
}

// R3s on two clusters: the parent is looked for in the primary store, the mirror
// at `key` in the store of the key's kind.
pub open spec fn two_cluster_mirrors_stably_collected(tc: TwoCluster) -> TempPred<TwoClusterState> {
    tla_forall(|i: (ObjectRef, Uid)|
        always(lift_state(on_side(Side::Primary, parent_absent(i.0, i.1))))
            .leads_to(always(lift_state(on_side(tc.side_of_kind(i.0.kind), mirror_collected(i.0, i.1))))))
}

// R3 on two clusters.
pub open spec fn two_cluster_mirrors_eventually_collected(tc: TwoCluster) -> TempPred<TwoClusterState> {
    tla_forall(|i: (ObjectRef, Uid, Uid)|
        always(lift_state(on_side(Side::Primary, parent_absent(i.0, i.1)))).and(lift_state(on_side(tc.side_of_kind(i.0.kind), mirror_object_is(i.0, i.1, i.2))))
            .leads_to(lift_state(on_side(tc.side_of_kind(i.0.kind), object_is_gone(i.0, i.2)))))
}

// D3 on two clusters: the inner side releases terminating mirrors.
pub open spec fn two_cluster_inner_releases_terminating_objects(tc: TwoCluster) -> TempPred<TwoClusterState> {
    tla_forall(|i: (ObjectRef, Uid)|
        lift_state(on_side(tc.side_of_kind(i.0.kind), inner_terminating_object(i.0, i.1)))
            .leads_to(lift_state(on_side(tc.side_of_kind(i.0.kind), object_is_gone(i.0, i.1)))))
}

// The spec of the Widget pair on two clusters.
pub open spec fn widget_two_cluster_spec(cluster: Cluster, sync_id: int, janitor_id: int) -> TempPred<TwoClusterState> {
    let tc = widget_two_cluster(cluster);
    lift_state(tc.init())
    .and(two_cluster_next_with_wf(tc, sync_id))
    .and(two_cluster_next_with_wf(tc, janitor_id))
    .and(two_cluster_inner_releases_terminating_objects(tc))
}

// ---------------------------------------------------------------------------
// Per-state pull-backs.
// ---------------------------------------------------------------------------

// The object at a key of the primary side, in the abstraction and in the primary store.
proof fn lemma_abs_object(cluster: Cluster, r: Relabeling, s: TwoClusterState, key: ObjectRef, uid_next: Uid, rv_next: ResourceVersion)
    requires inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        let side = tc.side_of_kind(key.kind);
        let a = abs(tc, r, s, uid_next, rv_next);
        &&& a.resources().contains_key(key) == s.project(side).resources().contains_key(key)
        &&& s.project(side).resources().contains_key(key) ==> a.resources()[key] == relabel_obj(tc, r, s.project(side).resources()[key])
            && s.project(side).resources()[key].kind == key.kind
            && s.project(side).resources()[key].metadata.uid is Some
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_abs_store_index(tc, r, s, key);
}

proof fn lemma_desired_state_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, outer: OuterWidgetView, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        Cluster::desired_state_is(relabel_outer(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == Cluster::desired_state_is(outer)(s.project(Side::Primary))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let outer1 = relabel_outer(tc, r, outer);
    let key = outer.object_ref();
    assert(outer1.object_ref() == key);
    lemma_abs_object(cluster, r, s, key, uid_next, rv_next);
    let a = abs(tc, r, s, uid_next, rv_next);
    let p = s.project(Side::Primary);
    if p.resources().contains_key(key) {
        let obj = p.resources()[key];
        lemma_unmarshal_outer_relabel(tc, r, obj);
        lemma_relabel_obj_keeps_identity(tc, r, obj);
        match (obj.metadata.uid, outer.metadata.uid) {
            (Some(x), Some(y)) => {
                if (r.uid)(Side::Primary, x) == (r.uid)(Side::Primary, y) { assert(x == y); }
            },
            _ => {},
        }
    }
}

// The premise of R1, pulled back.
proof fn lemma_outer_spec_stable_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, outer: OuterWidgetView, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        outer_spec_stable(relabel_outer(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == two_cluster_outer_spec_stable(outer)(s)
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let outer1 = relabel_outer(tc, r, outer);
    let a = abs(tc, r, s, uid_next, rv_next);
    let p = s.project(Side::Primary);
    lemma_desired_state_pull_back(cluster, r, s, outer, uid_next, rv_next);
    // Writes of the mirror's spec in flight.
    let in_flight = s.network.in_flight;
    assert(mirror_spec_undisturbed(outer1)(a) == mirror_spec_undisturbed(outer)(p)) by {
        if mirror_spec_undisturbed(outer)(p) {
            assert forall |msg: Message| #[trigger] a.in_flight().contains(msg) && msg.content is APIRequest implies match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => req.key() == inner_key(outer1) ==> writes_outer_spec(req.obj.spec, outer1),
                APIRequest::GetThenUpdateRequest(req) => req.key() == inner_key(outer1) ==> writes_outer_spec(req.obj.spec, outer1),
                APIRequest::PatchRequest(req) => req.key() == inner_key(outer1) ==> writes_outer_spec(req.spec, outer1),
                _ => true,
            } by {
                lemma_relabel_msgs_contains(tc, r, in_flight, msg);
                let m2 = choose |m2: Message| in_flight.contains(m2) && relabel_msg(tc, r, m2) == msg;
                assert(p.in_flight().contains(m2));
            }
        }
        if mirror_spec_undisturbed(outer1)(a) {
            assert forall |msg: Message| #[trigger] p.in_flight().contains(msg) && msg.content is APIRequest implies match msg.content->APIRequest_0 {
                APIRequest::UpdateRequest(req) => req.key() == inner_key(outer) ==> writes_outer_spec(req.obj.spec, outer),
                APIRequest::GetThenUpdateRequest(req) => req.key() == inner_key(outer) ==> writes_outer_spec(req.obj.spec, outer),
                APIRequest::PatchRequest(req) => req.key() == inner_key(outer) ==> writes_outer_spec(req.spec, outer),
                _ => true,
            } by {
                lemma_relabel_msgs_contains(tc, r, in_flight, msg);
                let msg1 = relabel_msg(tc, r, msg);
                assert(a.in_flight().contains(msg1));
            }
        }
    }
    // Deletes of the mirror key in flight, read on the remote side. Only needed when
    // the outer copy exists, which fixes its uid; otherwise both sides of the
    // equality are false already.
    if Cluster::desired_state_is(outer)(p) {
        lemma_mirror_undeleted_pull_back(cluster, r, s, outer, uid_next, rv_next);
    }
}

// The premise of R2, pulled back: R1's premise, and the generation of the outer
// copy, which relabeling keeps.
proof fn lemma_outer_stable_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, outer: OuterWidgetView, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        outer_stable(relabel_outer(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == two_cluster_outer_stable(outer)(s)
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let outer1 = relabel_outer(tc, r, outer);
    let a = abs(tc, r, s, uid_next, rv_next);
    let p = s.project(Side::Primary);
    lemma_outer_spec_stable_pull_back(cluster, r, s, outer, uid_next, rv_next);
    lemma_desired_state_pull_back(cluster, r, s, outer, uid_next, rv_next);
    lemma_abs_object(cluster, r, s, outer.object_ref(), uid_next, rv_next);
    if p.resources().contains_key(outer.object_ref()) {
        lemma_relabel_obj_keeps_identity(tc, r, p.resources()[outer.object_ref()]);
    }
}

// The delete clause of the premise, pulled back: a Delete of the mirror key misses
// the relabeled mirror exactly when its preimage misses the mirror in the remote
// store, since uids of one side are relabeled injectively.
#[verifier(rlimit(200))]
#[verifier(spinoff_prover)]
proof fn lemma_mirror_undeleted_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, outer: OuterWidgetView, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
        outer.metadata.uid is Some,
    ensures ({
        let tc = widget_two_cluster(cluster);
        mirror_undeleted(relabel_outer(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == mirror_undeleted(outer)(s.project(Side::Remote))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let outer1 = relabel_outer(tc, r, outer);
    let a = abs(tc, r, s, uid_next, rv_next);
    let q = s.project(Side::Remote);
    let key = inner_key(outer);
    assert(inner_key(outer1) == key);
    let in_flight = s.network.in_flight;
    lemma_abs_object(cluster, r, s, key, uid_next, rv_next);
    // The mirror at the key, on both sides of the abstraction.
    if q.resources().contains_key(key) {
        let obj = q.resources()[key];
        lemma_unmarshal_inner_relabel(tc, r, obj);
        lemma_relabel_obj_keeps_identity(tc, r, obj);
        if InnerWidgetView::unmarshal(obj) is Ok {
            lemma_is_mirror_of_relabel(cluster, r, InnerWidgetView::unmarshal(obj)->Ok_0, outer);
        }
    }
    // A Delete of the mirror key and its relabeling miss the mirror together.
    assert forall |m2: Message| #[trigger] in_flight.contains(m2) && m2.content is APIRequest && m2.content->APIRequest_0 is DeleteRequest
        && m2.content->APIRequest_0->DeleteRequest_0.key == key
        implies delete_misses_mirror(relabel_msg(tc, r, m2).content->APIRequest_0->DeleteRequest_0, outer1)(a)
            == delete_misses_mirror(m2.content->APIRequest_0->DeleteRequest_0, outer)(q) by {
        let req2 = m2.content->APIRequest_0->DeleteRequest_0;
        let req1 = relabel_msg(tc, r, m2).content->APIRequest_0->DeleteRequest_0;
        assert(req1.preconditions == relabel_preconditions(r, Side::Remote, req2.preconditions));
        if q.resources().contains_key(key) {
            let obj = q.resources()[key];
            assert(a.resources()[key].metadata.uid == relabel_opt_uid(r, Side::Remote, obj.metadata.uid));
            match (req2.preconditions, obj.metadata.uid) {
                (Some(pre), Some(x)) => {
                    match pre.uid {
                        Some(y) => { if (r.uid)(Side::Remote, y) == (r.uid)(Side::Remote, x) { assert(y == x); } },
                        None => {},
                    }
                },
                _ => {},
            }
        }
    }
    if mirror_undeleted(outer)(q) {
        assert forall |msg: Message| #[trigger] a.in_flight().contains(msg) && msg.content is APIRequest implies match msg.content->APIRequest_0 {
            APIRequest::DeleteRequest(req) => req.key == key ==> delete_misses_mirror(req, outer1)(a),
            _ => true,
        } by {
            lemma_relabel_msgs_contains(tc, r, in_flight, msg);
            let m2 = choose |m2: Message| #[trigger] in_flight.contains(m2) && relabel_msg(tc, r, m2) == msg;
            assert(q.in_flight().contains(m2));
        }
    }
    if mirror_undeleted(outer1)(a) {
        assert forall |msg: Message| #[trigger] q.in_flight().contains(msg) && msg.content is APIRequest implies match msg.content->APIRequest_0 {
            APIRequest::DeleteRequest(req) => req.key == key ==> delete_misses_mirror(req, outer)(q),
            _ => true,
        } by {
            lemma_relabel_msgs_contains(tc, r, in_flight, msg);
            let msg1 = relabel_msg(tc, r, msg);
            assert(a.in_flight().contains(msg1));
        }
    }
}

proof fn lemma_spec_synced_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, outer: OuterWidgetView, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
        outer.metadata.uid is Some,
    ensures ({
        let tc = widget_two_cluster(cluster);
        spec_synced(relabel_outer(tc, r, outer))(abs(tc, r, s, uid_next, rv_next)) == spec_synced(outer)(s.project(Side::Remote))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let outer1 = relabel_outer(tc, r, outer);
    let key = inner_key(outer);
    assert(inner_key(outer1) == key);
    lemma_abs_object(cluster, r, s, key, uid_next, rv_next);
    let q = s.project(Side::Remote);
    if q.resources().contains_key(key) {
        let obj = q.resources()[key];
        lemma_unmarshal_inner_relabel(tc, r, obj);
        lemma_relabel_obj_keeps_identity(tc, r, obj);
        if InnerWidgetView::unmarshal(obj) is Ok {
            lemma_is_mirror_of_relabel(cluster, r, InnerWidgetView::unmarshal(obj)->Ok_0, outer);
        }
    }
}

proof fn lemma_inner_settled_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, outer: OuterWidgetView, mirrored: WidgetStatusView, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
        outer.metadata.uid is Some,
    ensures ({
        let tc = widget_two_cluster(cluster);
        inner_settled(relabel_outer(tc, r, outer), mirrored)(abs(tc, r, s, uid_next, rv_next)) == inner_settled(outer, mirrored)(s.project(Side::Remote))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    lemma_spec_synced_pull_back(cluster, r, s, outer, uid_next, rv_next);
    let key = inner_key(outer);
    lemma_abs_object(cluster, r, s, key, uid_next, rv_next);
    let q = s.project(Side::Remote);
    if q.resources().contains_key(key) {
        let obj = q.resources()[key];
        lemma_unmarshal_inner_relabel(tc, r, obj);
    }
}

proof fn lemma_status_synced_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, outer: OuterWidgetView, mirrored: WidgetStatusView, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        status_synced(relabel_outer(tc, r, outer), mirrored)(abs(tc, r, s, uid_next, rv_next)) == status_synced(outer, mirrored)(s.project(Side::Primary))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let key = outer.object_ref();
    assert(relabel_outer(tc, r, outer).object_ref() == key);
    lemma_abs_object(cluster, r, s, key, uid_next, rv_next);
    let p = s.project(Side::Primary);
    if p.resources().contains_key(key) {
        let obj = p.resources()[key];
        lemma_unmarshal_outer_relabel(tc, r, obj);
    }
}

proof fn lemma_parent_absent_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, key: ObjectRef, parent_uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        parent_absent(key, (r.uid)(Side::Primary, parent_uid))(abs(tc, r, s, uid_next, rv_next)) == parent_absent(key, parent_uid)(s.project(Side::Primary))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let okey = outer_key_of(key);
    lemma_abs_object(cluster, r, s, okey, uid_next, rv_next);
    let p = s.project(Side::Primary);
    if p.resources().contains_key(okey) {
        let obj = p.resources()[okey];
        match obj.metadata.uid {
            Some(x) => { if (r.uid)(Side::Primary, x) == (r.uid)(Side::Primary, parent_uid) { assert(x == parent_uid); } },
            None => {},
        }
    }
}

proof fn lemma_mirror_of_parent_pull_back(cluster: Cluster, r: Relabeling, obj: DynamicObjectView, parent_uid: Uid)
    requires widget_relabeling(cluster, r),
    ensures mirror_of_parent(relabel_obj(widget_two_cluster(cluster), r, obj), (r.uid)(Side::Primary, parent_uid)) == mirror_of_parent(obj, parent_uid),
{
    let tc = widget_two_cluster(cluster);
    lemma_unmarshal_inner_relabel(tc, r, obj);
    if InnerWidgetView::unmarshal(obj) is Ok {
        let inner = InnerWidgetView::unmarshal(obj)->Ok_0;
        lemma_has_mirror_identity_relabel(cluster, r, inner);
        if has_mirror_identity(inner) {
            lemma_parent_annotation_relabel(cluster, r, inner);
            lemma_uid_string_eq(r.uid, parent_uid_annotation(inner), parent_uid);
        }
    }
}

proof fn lemma_mirror_collected_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, key: ObjectRef, parent_uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        mirror_collected(key, (r.uid)(Side::Primary, parent_uid))(abs(tc, r, s, uid_next, rv_next)) == mirror_collected(key, parent_uid)(s.project(tc.side_of_kind(key.kind)))
    }),
{
    let tc = widget_two_cluster(cluster);
    lemma_abs_object(cluster, r, s, key, uid_next, rv_next);
    let q = s.project(tc.side_of_kind(key.kind));
    if q.resources().contains_key(key) {
        lemma_mirror_of_parent_pull_back(cluster, r, q.resources()[key], parent_uid);
    }
}

// mirror_object_is and object_is_gone name the mirror's own uid, which lives on the key's side.
proof fn lemma_mirror_object_is_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, key: ObjectRef, parent_uid: Uid, uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        let side = tc.side_of_kind(key.kind);
        mirror_object_is(key, (r.uid)(Side::Primary, parent_uid), (r.uid)(side, uid))(abs(tc, r, s, uid_next, rv_next)) == mirror_object_is(key, parent_uid, uid)(s.project(side))
    }),
{
    let tc = widget_two_cluster(cluster);
    let side = tc.side_of_kind(key.kind);
    lemma_abs_object(cluster, r, s, key, uid_next, rv_next);
    let q = s.project(side);
    if q.resources().contains_key(key) {
        let obj = q.resources()[key];
        lemma_mirror_of_parent_pull_back(cluster, r, obj, parent_uid);
        let x = obj.metadata.uid->0;
        if (r.uid)(side, x) == (r.uid)(side, uid) { assert(x == uid); }
    }
}

proof fn lemma_object_is_gone_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, key: ObjectRef, uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        let side = tc.side_of_kind(key.kind);
        object_is_gone(key, (r.uid)(side, uid))(abs(tc, r, s, uid_next, rv_next)) == object_is_gone(key, uid)(s.project(side))
    }),
{
    let tc = widget_two_cluster(cluster);
    let side = tc.side_of_kind(key.kind);
    lemma_abs_object(cluster, r, s, key, uid_next, rv_next);
    let q = s.project(side);
    if q.resources().contains_key(key) {
        let x = q.resources()[key].metadata.uid->0;
        if (r.uid)(side, x) == (r.uid)(side, uid) { assert(x == uid); }
    }
}

proof fn lemma_inner_terminating_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, key: ObjectRef, uid: Uid, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
    ensures ({
        let tc = widget_two_cluster(cluster);
        let side = tc.side_of_kind(key.kind);
        inner_terminating_object(key, (r.uid)(side, uid))(abs(tc, r, s, uid_next, rv_next)) == inner_terminating_object(key, uid)(s.project(side))
    }),
{
    let tc = widget_two_cluster(cluster);
    let side = tc.side_of_kind(key.kind);
    lemma_abs_object(cluster, r, s, key, uid_next, rv_next);
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
// two-store execution through per-state equivalences.
// ---------------------------------------------------------------------------

proof fn lemma_heads(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>, t: nat, d: nat, k: nat)
    ensures
        ex.suffix(t).suffix(k).head() == state_at(ex, t + k),
        alpha(tc, r, ex).suffix(t).suffix(k).head() == abs_at(tc, r, ex, t + k),
        ex.suffix(t).suffix(d).suffix(k).head() == state_at(ex, t + d + k),
        alpha(tc, r, ex).suffix(t).suffix(d).suffix(k).head() == abs_at(tc, r, ex, t + d + k),
{
}

// always p2 ~> always q2 on ex, from always p1 ~> always q1 on the abstract execution.
proof fn lemma_pull_back_always_leads_to_always(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>, p1: StatePred<ClusterState>, q1: StatePred<ClusterState>, p2: StatePred<TwoClusterState>, q2: StatePred<TwoClusterState>)
    requires
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
                lemma_heads(tc, r, ex, t, 0, k);
            }
            assert(always(lift_state(p1)).satisfied_by(ex1.suffix(t)));
            assert(always(lift_state(p1)).implies(eventually(always(lift_state(q1)))).satisfied_by(ex1.suffix(t)));
            let d = choose |d: nat| #[trigger] always(lift_state(q1)).satisfied_by(ex1.suffix(t).suffix(d));
            assert forall |k: nat| #[trigger] lift_state(q2).satisfied_by(ex.suffix(t).suffix(d).suffix(k)) by {
                assert(lift_state(q1).satisfied_by(ex1.suffix(t).suffix(d).suffix(k)));
                lemma_heads(tc, r, ex, t, d, k);
            }
            assert(always(lift_state(q2)).satisfied_by(ex.suffix(t).suffix(d)));
        }
    }
}

// always (p2 and p2b) ~> always q2, the same with a two-part premise.
proof fn lemma_pull_back_always_and_leads_to_always(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>, p1: StatePred<ClusterState>, p1b: StatePred<ClusterState>, q1: StatePred<ClusterState>, p2: StatePred<TwoClusterState>, p2b: StatePred<TwoClusterState>, q2: StatePred<TwoClusterState>)
    requires
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
                lemma_heads(tc, r, ex, t, 0, k);
            }
            assert(always(lift_state(p1).and(lift_state(p1b))).satisfied_by(ex1.suffix(t)));
            assert(always(lift_state(p1).and(lift_state(p1b))).implies(eventually(always(lift_state(q1)))).satisfied_by(ex1.suffix(t)));
            let d = choose |d: nat| #[trigger] always(lift_state(q1)).satisfied_by(ex1.suffix(t).suffix(d));
            assert forall |k: nat| #[trigger] lift_state(q2).satisfied_by(ex.suffix(t).suffix(d).suffix(k)) by {
                assert(lift_state(q1).satisfied_by(ex1.suffix(t).suffix(d).suffix(k)));
                lemma_heads(tc, r, ex, t, d, k);
            }
            assert(always(lift_state(q2)).satisfied_by(ex.suffix(t).suffix(d)));
        }
    }
}

// (always p2) and p2b ~> q2, the shape of R3.
proof fn lemma_pull_back_always_and_now_leads_to(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>, p1: StatePred<ClusterState>, p1b: StatePred<ClusterState>, q1: StatePred<ClusterState>, p2: StatePred<TwoClusterState>, p2b: StatePred<TwoClusterState>, q2: StatePred<TwoClusterState>)
    requires
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
                lemma_heads(tc, r, ex, t, 0, k);
            }
            assert(always(lift_state(p1)).satisfied_by(ex1.suffix(t)));
            assert(lift_state(p1b).satisfied_by(ex1.suffix(t))) by {
                assert(ex.suffix(t).head() == state_at(ex, t));
                assert(ex1.suffix(t).head() == abs_at(tc, r, ex, t));
            }
            assert(always(lift_state(p1)).and(lift_state(p1b)).implies(eventually(lift_state(q1))).satisfied_by(ex1.suffix(t)));
            let d = choose |d: nat| #[trigger] lift_state(q1).satisfied_by(ex1.suffix(t).suffix(d));
            lemma_heads(tc, r, ex, t, 0, d);
            assert(lift_state(q2).satisfied_by(ex.suffix(t).suffix(d)));
        }
    }
}

// p1 ~> q1 on the abstract execution from p2 ~> q2 on ex (the shape of D3).
proof fn lemma_push_forward_leads_to(tc: TwoCluster, r: Relabeling, ex: Execution<TwoClusterState>, p1: StatePred<ClusterState>, q1: StatePred<ClusterState>, p2: StatePred<TwoClusterState>, q2: StatePred<TwoClusterState>)
    requires
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
            lemma_heads(tc, r, ex, t, 0, d);
            assert(lift_state(q1).satisfied_by(ex1.suffix(t).suffix(d)));
        }
    }
}

// ---------------------------------------------------------------------------
// The properties on the two-store execution.
// ---------------------------------------------------------------------------

// What the instantiation knows about an execution once it has been simulated.
pub open spec fn widget_sim(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>) -> bool {
    &&& simulation(widget_two_cluster(cluster), r, ex)
    &&& widget_relabeling(cluster, r)
}

proof fn lemma_widget_sim_inv(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>, i: nat)
    requires widget_sim(cluster, r, ex),
    ensures
        inv(widget_two_cluster(cluster), state_at(ex, i)),
        abs_at(widget_two_cluster(cluster), r, ex, i) == abs(widget_two_cluster(cluster), r, state_at(ex, i), uid_sum(state_at(ex, i)), rv_sum(state_at(ex, i))),
{
}

// An outer copy without a uid is never the desired state: stored objects have uids.
proof fn lemma_outer_without_uid_not_stable_at(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>, outer: OuterWidgetView, t: nat)
    requires
        widget_sim(cluster, r, ex),
        outer.metadata.uid is None,
    ensures
        !two_cluster_outer_spec_stable(outer)(state_at(ex, t)),
        !two_cluster_outer_stable(outer)(state_at(ex, t)),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sim_inv(cluster, r, ex, t);
    let s = state_at(ex, t);
    let key = outer.object_ref();
    if s.primary.resources.contains_key(key) {
        assert(stored_object_ok(tc, s.primary.resources[key]));
    }
    assert(!Cluster::desired_state_is(outer)(s.project(Side::Primary)));
}

// A leads-to whose premise never holds is vacuous.
proof fn lemma_vacuous_from_never(ex: Execution<TwoClusterState>, sp: StatePred<TwoClusterState>, extra: TempPred<TwoClusterState>, q: TempPred<TwoClusterState>)
    requires forall |t: nat| !sp(#[trigger] state_at(ex, t)),
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

proof fn lemma_outer_without_uid_never_stable(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>, outer: OuterWidgetView)
    requires
        widget_sim(cluster, r, ex),
        outer.metadata.uid is None,
    ensures always(lift_state(two_cluster_outer_spec_stable(outer))).leads_to(always(lift_state(on_side(Side::Remote, spec_synced(outer))))).satisfied_by(ex),
        forall |mirrored: WidgetStatusView| #[trigger] always(lift_state(two_cluster_outer_stable(outer)).and(lift_state(on_side(Side::Remote, inner_settled(outer, mirrored)))))
            .leads_to(always(lift_state(on_side(Side::Primary, status_synced(outer, mirrored))))).satisfied_by(ex),
{
    let sp1 = two_cluster_outer_spec_stable(outer);
    let sp = two_cluster_outer_stable(outer);
    assert forall |t: nat| !sp1(#[trigger] state_at(ex, t)) && !sp(state_at(ex, t)) by {
        lemma_outer_without_uid_not_stable_at(cluster, r, ex, outer, t);
    }
    lemma_vacuous_from_never(ex, sp1, true_pred(), always(lift_state(on_side(Side::Remote, spec_synced(outer)))));
    assert forall |mirrored: WidgetStatusView| #[trigger] always(lift_state(two_cluster_outer_stable(outer)).and(lift_state(on_side(Side::Remote, inner_settled(outer, mirrored)))))
        .leads_to(always(lift_state(on_side(Side::Primary, status_synced(outer, mirrored))))).satisfied_by(ex) by {
        lemma_vacuous_from_never(ex, sp, lift_state(on_side(Side::Remote, inner_settled(outer, mirrored))), always(lift_state(on_side(Side::Primary, status_synced(outer, mirrored)))));
    }
}

pub proof fn lemma_r1_pull_back(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>)
    requires
        widget_sim(cluster, r, ex),
        widget_spec_eventually_synced().satisfied_by(alpha(widget_two_cluster(cluster), r, ex)),
    ensures two_cluster_spec_eventually_synced().satisfied_by(ex),
{
    let tc = widget_two_cluster(cluster);
    let ex1 = alpha(tc, r, ex);
    assert forall |outer: OuterWidgetView| #[trigger] always(lift_state(two_cluster_outer_spec_stable(outer)))
        .leads_to(always(lift_state(on_side(Side::Remote, spec_synced(outer))))).satisfied_by(ex) by {
        if outer.metadata.uid is None {
            lemma_outer_without_uid_never_stable(cluster, r, ex, outer);
        } else {
            let outer1 = relabel_outer(tc, r, outer);
            let f = |outer: OuterWidgetView| widget_spec_eventually_synced_per_cr(outer);
            assert(tla_forall(f).satisfied_by(ex1));
            assert(f(outer1).satisfied_by(ex1));
            let p1 = outer_spec_stable(outer1);
            let q1 = spec_synced(outer1);
            let p2 = two_cluster_outer_spec_stable(outer);
            let q2 = on_side(Side::Remote, spec_synced(outer));
            assert forall |i: nat| p1(abs_at(tc, r, ex, i)) == p2(#[trigger] state_at(ex, i)) by {
                lemma_widget_sim_inv(cluster, r, ex, i);
                lemma_outer_spec_stable_pull_back(cluster, r, state_at(ex, i), outer, uid_sum(state_at(ex, i)), rv_sum(state_at(ex, i)));
            }
            assert forall |i: nat| q1(abs_at(tc, r, ex, i)) == q2(#[trigger] state_at(ex, i)) by {
                lemma_widget_sim_inv(cluster, r, ex, i);
                lemma_spec_synced_pull_back(cluster, r, state_at(ex, i), outer, uid_sum(state_at(ex, i)), rv_sum(state_at(ex, i)));
            }
            lemma_pull_back_always_leads_to_always(tc, r, ex, p1, q1, p2, q2);
        }
    }
}

pub proof fn lemma_r2_pull_back(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>)
    requires
        widget_sim(cluster, r, ex),
        widget_status_eventually_mirrored().satisfied_by(alpha(widget_two_cluster(cluster), r, ex)),
    ensures two_cluster_status_eventually_mirrored().satisfied_by(ex),
{
    let tc = widget_two_cluster(cluster);
    let ex1 = alpha(tc, r, ex);
    assert forall |i: (OuterWidgetView, WidgetStatusView)| #[trigger] always(lift_state(two_cluster_outer_stable(i.0)).and(lift_state(on_side(Side::Remote, inner_settled(i.0, i.1)))))
        .leads_to(always(lift_state(on_side(Side::Primary, status_synced(i.0, i.1))))).satisfied_by(ex) by {
        let outer = i.0;
        let mirrored = i.1;
        if outer.metadata.uid is None {
            lemma_outer_without_uid_never_stable(cluster, r, ex, outer);
        } else {
            let outer1 = relabel_outer(tc, r, outer);
            let j = (outer1, mirrored);
            let f = |i: (OuterWidgetView, WidgetStatusView)| widget_status_eventually_mirrored_per_cr(i.0, i.1);
            assert(tla_forall(f).satisfied_by(ex1));
            assert(f(j).satisfied_by(ex1));
            let p1 = outer_stable(outer1);
            let p1b = inner_settled(outer1, mirrored);
            let q1 = status_synced(outer1, mirrored);
            let p2 = two_cluster_outer_stable(outer);
            let p2b = on_side(Side::Remote, inner_settled(outer, mirrored));
            let q2 = on_side(Side::Primary, status_synced(outer, mirrored));
            assert forall |k: nat| p1(abs_at(tc, r, ex, k)) == p2(#[trigger] state_at(ex, k)) by {
                lemma_widget_sim_inv(cluster, r, ex, k);
                lemma_outer_stable_pull_back(cluster, r, state_at(ex, k), outer, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
            }
            assert forall |k: nat| p1b(abs_at(tc, r, ex, k)) == p2b(#[trigger] state_at(ex, k)) by {
                lemma_widget_sim_inv(cluster, r, ex, k);
                lemma_inner_settled_pull_back(cluster, r, state_at(ex, k), outer, mirrored, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
            }
            assert forall |k: nat| q1(abs_at(tc, r, ex, k)) == q2(#[trigger] state_at(ex, k)) by {
                lemma_widget_sim_inv(cluster, r, ex, k);
                lemma_status_synced_pull_back(cluster, r, state_at(ex, k), outer, mirrored, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
            }
            lemma_pull_back_always_and_leads_to_always(tc, r, ex, p1, p1b, q1, p2, p2b, q2);
        }
    }
}

pub proof fn lemma_r3s_pull_back(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>)
    requires
        widget_sim(cluster, r, ex),
        widget_mirrors_stably_collected().satisfied_by(alpha(widget_two_cluster(cluster), r, ex)),
    ensures two_cluster_mirrors_stably_collected(widget_two_cluster(cluster)).satisfied_by(ex),
{
    let tc = widget_two_cluster(cluster);
    let ex1 = alpha(tc, r, ex);
    assert forall |i: (ObjectRef, Uid)| #[trigger] always(lift_state(on_side(Side::Primary, parent_absent(i.0, i.1))))
        .leads_to(always(lift_state(on_side(tc.side_of_kind(i.0.kind), mirror_collected(i.0, i.1))))).satisfied_by(ex) by {
        let key = i.0;
        let parent_uid = i.1;
        let parent1 = (r.uid)(Side::Primary, parent_uid);
        let j = (key, parent1);
        let f = |i: (ObjectRef, Uid)| widget_mirror_stably_collected_per_key(i.0, i.1);
        assert(tla_forall(f).satisfied_by(ex1));
        assert(f(j).satisfied_by(ex1));
        let p1 = parent_absent(key, parent1);
        let q1 = mirror_collected(key, parent1);
        let p2 = on_side(Side::Primary, parent_absent(key, parent_uid));
        let q2 = on_side(tc.side_of_kind(key.kind), mirror_collected(key, parent_uid));
        assert forall |k: nat| p1(abs_at(tc, r, ex, k)) == p2(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(cluster, r, ex, k);
            lemma_parent_absent_pull_back(cluster, r, state_at(ex, k), key, parent_uid, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
        }
        assert forall |k: nat| q1(abs_at(tc, r, ex, k)) == q2(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(cluster, r, ex, k);
            lemma_mirror_collected_pull_back(cluster, r, state_at(ex, k), key, parent_uid, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
        }
        lemma_pull_back_always_leads_to_always(tc, r, ex, p1, q1, p2, q2);
    }
}

pub proof fn lemma_r3_pull_back(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>)
    requires
        widget_sim(cluster, r, ex),
        widget_mirrors_eventually_collected().satisfied_by(alpha(widget_two_cluster(cluster), r, ex)),
    ensures two_cluster_mirrors_eventually_collected(widget_two_cluster(cluster)).satisfied_by(ex),
{
    let tc = widget_two_cluster(cluster);
    let ex1 = alpha(tc, r, ex);
    assert forall |i: (ObjectRef, Uid, Uid)| #[trigger] always(lift_state(on_side(Side::Primary, parent_absent(i.0, i.1)))).and(lift_state(on_side(tc.side_of_kind(i.0.kind), mirror_object_is(i.0, i.1, i.2))))
        .leads_to(lift_state(on_side(tc.side_of_kind(i.0.kind), object_is_gone(i.0, i.2)))).satisfied_by(ex) by {
        let key = i.0;
        let parent_uid = i.1;
        let uid = i.2;
        let side = tc.side_of_kind(key.kind);
        let parent1 = (r.uid)(Side::Primary, parent_uid);
        let uid1 = (r.uid)(side, uid);
        let j = (key, parent1, uid1);
        let f = |i: (ObjectRef, Uid, Uid)| widget_mirror_eventually_collected_per_object(i.0, i.1, i.2);
        assert(tla_forall(f).satisfied_by(ex1));
        assert(f(j).satisfied_by(ex1));
        let p1 = parent_absent(key, parent1);
        let p1b = mirror_object_is(key, parent1, uid1);
        let q1 = object_is_gone(key, uid1);
        let p2 = on_side(Side::Primary, parent_absent(key, parent_uid));
        let p2b = on_side(side, mirror_object_is(key, parent_uid, uid));
        let q2 = on_side(side, object_is_gone(key, uid));
        assert forall |k: nat| p1(abs_at(tc, r, ex, k)) == p2(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(cluster, r, ex, k);
            lemma_parent_absent_pull_back(cluster, r, state_at(ex, k), key, parent_uid, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
        }
        assert forall |k: nat| p1b(abs_at(tc, r, ex, k)) == p2b(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(cluster, r, ex, k);
            lemma_mirror_object_is_pull_back(cluster, r, state_at(ex, k), key, parent_uid, uid, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
        }
        assert forall |k: nat| q1(abs_at(tc, r, ex, k)) == q2(#[trigger] state_at(ex, k)) by {
            lemma_widget_sim_inv(cluster, r, ex, k);
            lemma_object_is_gone_pull_back(cluster, r, state_at(ex, k), key, uid, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
        }
        lemma_pull_back_always_and_now_leads_to(tc, r, ex, p1, p1b, q1, p2, p2b, q2);
    }
}

// D3 for one mirror with uid w on the two-store execution gives D3 for the
// relabeled uid on the abstract one.
proof fn lemma_d3_instance(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>, key: ObjectRef, w: Uid)
    requires
        widget_sim(cluster, r, ex),
        two_cluster_inner_releases_terminating_objects(widget_two_cluster(cluster)).satisfied_by(ex),
    ensures ({
        let tc = widget_two_cluster(cluster);
        let side = tc.side_of_kind(key.kind);
        lift_state(inner_terminating_object(key, (r.uid)(side, w))).leads_to(lift_state(object_is_gone(key, (r.uid)(side, w)))).satisfied_by(alpha(tc, r, ex))
    }),
{
    let tc = widget_two_cluster(cluster);
    let side = tc.side_of_kind(key.kind);
    let uid1 = (r.uid)(side, w);
    let p1 = inner_terminating_object(key, uid1);
    let q1 = object_is_gone(key, uid1);
    let f = |i: (ObjectRef, Uid)| lift_state(on_side(tc.side_of_kind(i.0.kind), inner_terminating_object(i.0, i.1))).leads_to(lift_state(on_side(tc.side_of_kind(i.0.kind), object_is_gone(i.0, i.1))));
    let j = (key, w);
    assert(tla_forall(f).satisfied_by(ex));
    assert(f(j).satisfied_by(ex));
    let p2 = on_side(side, inner_terminating_object(key, w));
    let q2 = on_side(side, object_is_gone(key, w));
    assert forall |k: nat| p1(abs_at(tc, r, ex, k)) == p2(#[trigger] state_at(ex, k)) by {
        lemma_widget_sim_inv(cluster, r, ex, k);
        lemma_inner_terminating_pull_back(cluster, r, state_at(ex, k), key, w, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
    }
    assert forall |k: nat| q1(abs_at(tc, r, ex, k)) == q2(#[trigger] state_at(ex, k)) by {
        lemma_widget_sim_inv(cluster, r, ex, k);
        lemma_object_is_gone_pull_back(cluster, r, state_at(ex, k), key, w, uid_sum(state_at(ex, k)), rv_sum(state_at(ex, k)));
    }
    lemma_push_forward_leads_to(tc, r, ex, p1, q1, p2, q2);
}

// A terminating object of the abstraction has, behind it, an object of the
// key's side whose uid relabels to the abstract one.
proof fn lemma_terminating_has_source(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>, key: ObjectRef, uid1: Uid, t: nat)
    requires
        widget_sim(cluster, r, ex),
        inner_terminating_object(key, uid1)(abs_at(widget_two_cluster(cluster), r, ex, t)),
    ensures ({
        let tc = widget_two_cluster(cluster);
        let side = tc.side_of_kind(key.kind);
        exists |w: Uid| uid1 == #[trigger] (r.uid)(side, w)
    }),
{
    let tc = widget_two_cluster(cluster);
    let side = tc.side_of_kind(key.kind);
    lemma_widget_sim_inv(cluster, r, ex, t);
    let s = state_at(ex, t);
    lemma_abs_object(cluster, r, s, key, uid_sum(s), rv_sum(s));
    let q = s.project(side);
    assert(q.resources().contains_key(key));
    let w = q.resources()[key].metadata.uid->0;
    assert(uid1 == (r.uid)(side, w));
}

// D3 on the two-store execution gives D3 on the abstract one.
pub proof fn lemma_d3_transfer(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>)
    requires
        widget_sim(cluster, r, ex),
        two_cluster_inner_releases_terminating_objects(widget_two_cluster(cluster)).satisfied_by(ex),
    ensures inner_releases_terminating_objects().satisfied_by(alpha(widget_two_cluster(cluster), r, ex)),
{
    let tc = widget_two_cluster(cluster);
    let ex1 = alpha(tc, r, ex);
    assert forall |i: (ObjectRef, Uid)| #[trigger] lift_state(inner_terminating_object(i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1))).satisfied_by(ex1) by {
        let key = i.0;
        let uid1 = i.1;
        let side = tc.side_of_kind(key.kind);
        let p1 = inner_terminating_object(key, uid1);
        let q1 = object_is_gone(key, uid1);
        assert forall |t: nat| #[trigger] lift_state(p1).implies(eventually(lift_state(q1))).satisfied_by(ex1.suffix(t)) by {
            if lift_state(p1).satisfied_by(ex1.suffix(t)) {
                assert(ex1.suffix(t).head() == abs_at(tc, r, ex, t));
                lemma_terminating_has_source(cluster, r, ex, key, uid1, t);
                let w = choose |w: Uid| uid1 == #[trigger] (r.uid)(side, w);
                lemma_d3_instance(cluster, r, ex, key, w);
                assert(lift_state(p1).leads_to(lift_state(q1)).satisfied_by(ex1));
                assert(lift_state(p1).implies(eventually(lift_state(q1))).satisfied_by(ex1.suffix(t)));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The one-store results for the pair, and the theorem.
// ---------------------------------------------------------------------------

pub open spec fn widget_one_cluster_spec(cluster: Cluster, sync_id: int, janitor_id: int) -> TempPred<ClusterState> {
    lift_state(cluster.init())
    .and(sync_next_with_wf(cluster, sync_id))
    .and(janitor_next_with_wf(cluster, janitor_id))
    .and(inner_releases_terminating_objects())
}

// R1, R2, R3s and the janitor's ESR, for a cluster running exactly the pair.
pub proof fn lemma_one_cluster_esr(cluster: Cluster, sync_id: int, janitor_id: int)
    requires widget_pair_cluster(cluster, sync_id, janitor_id),
    ensures ({
        let spec = widget_one_cluster_spec(cluster, sync_id, janitor_id);
        &&& spec.entails(widget_spec_eventually_synced())
        &&& spec.entails(widget_status_eventually_mirrored())
        &&& spec.entails(widget_mirrors_stably_collected())
        &&& spec.entails(widget_janitor_esr(janitor_id))
    }),
{
    let spec = widget_one_cluster_spec(cluster, sync_id, janitor_id);
    assert(spec.entails(lift_state(cluster.init())));
    assert(spec.entails(sync_next_with_wf(cluster, sync_id)));
    assert(spec.entails(janitor_next_with_wf(cluster, janitor_id)));
    assert(spec.entails(inner_releases_terminating_objects()));
    assert(sync_next_with_wf(cluster, sync_id).entails(always(lift_action(cluster.next()))));
    entails_trans(spec, sync_next_with_wf(cluster, sync_id), always(lift_action(cluster.next())));
    lemma_always_widget_sync_guarantee(spec, cluster, sync_id);
    lemma_always_widget_janitor_guarantee(spec, cluster, janitor_id);
    // The janitor's rely: the sync reconciler's guarantee.
    assert forall |other_id: int| cluster.controller_models.remove(janitor_id).contains_key(other_id)
        implies spec.entails(always(lift_state(#[trigger] widget_janitor_rely(other_id)))) by {
        assert(other_id == sync_id);
        sync_guarantee_implies_janitor_rely(sync_id);
        always_weaken(spec, lift_state(widget_sync_guarantee(sync_id)), lift_state(widget_janitor_rely(sync_id)));
    }
    janitor_rely_facts_imply_lifted_condition(spec, cluster, janitor_id);
    janitor_satisfies_its_spec(spec, cluster, janitor_id);
    // The sync reconciler's rely: the janitor's guarantee.
    assert forall |other_id: int| cluster.controller_models.remove(sync_id).contains_key(other_id)
        implies spec.entails(#[trigger] widget_sync_partial_rely(janitor_id)(other_id)) by {
        assert(other_id == janitor_id);
    }
    sync_rely_facts_imply_lifted_condition(spec, cluster, sync_id, janitor_id);
    sync_eventually_synced(spec, cluster, sync_id, janitor_id);
    sync_eventually_mirrors_status(spec, cluster, sync_id, janitor_id);
    sync_mirrors_stably_collected(spec, cluster, sync_id, janitor_id);
}

// R1, R2, R3s and R3 hold of every execution of the two-store model that runs the pair.
pub proof fn widget_two_cluster_theorem(cluster: Cluster, sync_id: int, janitor_id: int)
    requires widget_pair_cluster(cluster, sync_id, janitor_id),
    ensures ({
        let tc = widget_two_cluster(cluster);
        widget_two_cluster_spec(cluster, sync_id, janitor_id).entails(
            two_cluster_spec_eventually_synced()
            .and(two_cluster_status_eventually_mirrored())
            .and(two_cluster_mirrors_stably_collected(tc))
            .and(two_cluster_mirrors_eventually_collected(tc))
            .and(always(lift_state(two_cluster_janitor_deletes_are_sound(tc, janitor_id))))
        )
    }),
{
    let tc = widget_two_cluster(cluster);
    let hook = widget_hook();
    let spec2 = widget_two_cluster_spec(cluster, sync_id, janitor_id);
    let spec1 = widget_one_cluster_spec(cluster, sync_id, janitor_id);
    lemma_widget_refinement_hyps(cluster, sync_id, janitor_id);
    lemma_one_cluster_esr(cluster, sync_id, janitor_id);
    assert forall |ex: Execution<TwoClusterState>| #[trigger] spec2.satisfied_by(ex) implies
        two_cluster_spec_eventually_synced()
        .and(two_cluster_status_eventually_mirrored())
        .and(two_cluster_mirrors_stably_collected(tc))
        .and(two_cluster_mirrors_eventually_collected(tc))
        .and(always(lift_state(two_cluster_janitor_deletes_are_sound(tc, janitor_id)))).satisfied_by(ex) by {
        assert(lift_state(tc.init()).satisfied_by(ex));
        assert(two_cluster_next_with_wf(tc, sync_id).satisfied_by(ex));
        assert(two_cluster_next_with_wf(tc, janitor_id).satisfied_by(ex));
        assert(two_cluster_inner_releases_terminating_objects(tc).satisfied_by(ex));
        assert(always(lift_action(tc.next())).satisfied_by(ex));
        assert forall |i: nat| tc.next()(#[trigger] state_at(ex, i), state_at(ex, i + 1)) by {
            assert(lift_action(tc.next()).satisfied_by(ex.suffix(i)));
        }
        assert(tc.init()(state_at(ex, 0)));
        assert(two_cluster_run(tc, ex));
        lemma_simulation(tc, hook, ex);
        let r = relabeling_of(ex, hook);
        let ex1 = alpha(tc, r, ex);
        assert(widget_sim(cluster, r, ex));
        lemma_fair_sim(tc, r, ex);
        lemma_next_with_wf_transfer(cluster, r, ex, sync_id);
        lemma_next_with_wf_transfer(cluster, r, ex, janitor_id);
        lemma_d3_transfer(cluster, r, ex);
        assert(spec1.satisfied_by(ex1));
        assert(widget_spec_eventually_synced().satisfied_by(ex1)) by {
            assert(spec1.implies(widget_spec_eventually_synced()).satisfied_by(ex1));
        }
        assert(widget_status_eventually_mirrored().satisfied_by(ex1)) by {
            assert(spec1.implies(widget_status_eventually_mirrored()).satisfied_by(ex1));
        }
        assert(widget_mirrors_stably_collected().satisfied_by(ex1)) by {
            assert(spec1.implies(widget_mirrors_stably_collected()).satisfied_by(ex1));
        }
        assert(widget_janitor_esr(janitor_id).satisfied_by(ex1)) by {
            assert(spec1.implies(widget_janitor_esr(janitor_id)).satisfied_by(ex1));
        }
        assert(widget_mirrors_eventually_collected().satisfied_by(ex1));
        lemma_r1_pull_back(cluster, r, ex);
        lemma_r2_pull_back(cluster, r, ex);
        lemma_r3s_pull_back(cluster, r, ex);
        lemma_r3_pull_back(cluster, r, ex);
        assert(always(lift_state(janitor_deletes_are_sound(janitor_id))).satisfied_by(ex1));
        lemma_janitor_sound_transfer(cluster, r, ex, janitor_id);
    }
}


// ---------------------------------------------------------------------------
// The janitor's delete soundness, read on two clusters.
// ---------------------------------------------------------------------------

// A Delete the janitor has in flight names a uid, and if the object it would
// remove, in the store of its kind, is a mirror with that uid, no outer copy in
// the primary store carries the mirror's parent uid.
pub open spec fn two_cluster_janitor_delete_is_sound(tc: TwoCluster, msg: Message, s: TwoClusterState) -> bool {
    let req = msg.content.get_delete_request();
    let store = s.store(tc.side_of_kind(req.key.kind)).resources;
    let obj = store[req.key];
    &&& req.preconditions is Some
    &&& req.preconditions->0.uid is Some
    &&& (store.contains_key(req.key) && obj.metadata.uid == req.preconditions->0.uid && snapshot_is_mirror(obj))
        ==> forall |k: ObjectRef| #[trigger] s.primary.resources.contains_key(k) && s.primary.resources[k].metadata.uid is Some
            ==> int_to_string_view(s.primary.resources[k].metadata.uid->0) != snapshot_parent(obj)
}

pub open spec fn two_cluster_janitor_deletes_are_sound(tc: TwoCluster, controller_id: int) -> StatePred<TwoClusterState> {
    |s: TwoClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.content is APIRequest
            &&& msg.content.is_delete_request()
        } ==> two_cluster_janitor_delete_is_sound(tc, msg, s)
    }
}

proof fn lemma_janitor_sound_pull_back(cluster: Cluster, r: Relabeling, s: TwoClusterState, controller_id: int, uid_next: Uid, rv_next: ResourceVersion)
    requires
        widget_relabeling(cluster, r),
        inv(widget_two_cluster(cluster), s),
        janitor_deletes_are_sound(controller_id)(abs(widget_two_cluster(cluster), r, s, uid_next, rv_next)),
    ensures two_cluster_janitor_deletes_are_sound(widget_two_cluster(cluster), controller_id)(s),
{
    let tc = widget_two_cluster(cluster);
    lemma_widget_sides(cluster);
    let a = abs(tc, r, s, uid_next, rv_next);
    assert forall |msg: Message| {
        &&& #[trigger] s.in_flight().contains(msg)
        &&& msg.src.is_controller_id(controller_id)
        &&& msg.content is APIRequest
        &&& msg.content.is_delete_request()
    } implies two_cluster_janitor_delete_is_sound(tc, msg, s) by {
        let m1 = relabel_msg(tc, r, msg);
        lemma_relabel_msgs_contains(tc, r, s.network.in_flight, msg);
        assert(a.in_flight().contains(m1));
        assert(janitor_delete_is_sound(m1, a));
        let req = msg.content.get_delete_request();
        let side = tc.side_of_kind(req.key.kind);
        let store = s.store(side).resources;
        lemma_abs_object(cluster, r, s, req.key, uid_next, rv_next);
        if store.contains_key(req.key) && store[req.key].metadata.uid == req.preconditions->0.uid && snapshot_is_mirror(store[req.key]) {
            let obj = store[req.key];
            let obj1 = relabel_obj(tc, r, obj);
            lemma_unmarshal_inner_relabel(tc, r, obj);
            let inner = InnerWidgetView::unmarshal(obj)->Ok_0;
            assert(InnerWidgetView::unmarshal(obj1)->Ok_0 == relabel_inner(tc, r, inner));
            lemma_parent_annotation_relabel(cluster, r, inner);
            assert(snapshot_is_mirror(obj1));
            assert(snapshot_parent(obj1) == relabel_uid_string(r.uid, snapshot_parent(obj)));
            assert(a.resources()[req.key] == obj1);
            assert(obj1.metadata.uid == m1.content.get_delete_request().preconditions->0.uid);
            assert(parent_absent_forever(snapshot_parent(obj1))(a));
            assert forall |k: ObjectRef| #[trigger] s.primary.resources.contains_key(k) && s.primary.resources[k].metadata.uid is Some
                implies int_to_string_view(s.primary.resources[k].metadata.uid->0) != snapshot_parent(obj) by {
                lemma_abs_object(cluster, r, s, k, uid_next, rv_next);
                let w = s.primary.resources[k].metadata.uid->0;
                assert(a.resources().contains_key(k));
                assert(a.resources()[k].metadata.uid == Some((r.uid)(Side::Primary, w)));
                assert(int_to_string_view((r.uid)(Side::Primary, w)) != snapshot_parent(obj1));
                lemma_uid_string_eq(r.uid, snapshot_parent(obj), w);
            }
        }
    }
}

pub proof fn lemma_janitor_sound_transfer(cluster: Cluster, r: Relabeling, ex: Execution<TwoClusterState>, controller_id: int)
    requires
        widget_sim(cluster, r, ex),
        always(lift_state(janitor_deletes_are_sound(controller_id))).satisfied_by(alpha(widget_two_cluster(cluster), r, ex)),
    ensures always(lift_state(two_cluster_janitor_deletes_are_sound(widget_two_cluster(cluster), controller_id))).satisfied_by(ex),
{
    let tc = widget_two_cluster(cluster);
    let ex1 = alpha(tc, r, ex);
    assert forall |i: nat| #[trigger] lift_state(two_cluster_janitor_deletes_are_sound(tc, controller_id)).satisfied_by(ex.suffix(i)) by {
        assert(lift_state(janitor_deletes_are_sound(controller_id)).satisfied_by(ex1.suffix(i)));
        assert(ex1.suffix(i).head() == abs_at(tc, r, ex, i));
        assert(ex.suffix(i).head() == state_at(ex, i));
        lemma_widget_sim_inv(cluster, r, ex, i);
        let s = state_at(ex, i);
        lemma_janitor_sound_pull_back(cluster, r, s, controller_id, uid_sum(s), rv_sum(s));
    }
}

// ---------------------------------------------------------------------------
// The concrete cluster of the pair satisfies the hypotheses.
// ---------------------------------------------------------------------------

pub proof fn lemma_widget_instance_is_pair_cluster()
    ensures widget_pair_cluster(widget_cluster_instance(), widget_sync_id(), widget_janitor_id()),
{
    let cluster = widget_cluster_instance();
    let it = cluster.installed_types;
    let outer_name = OuterWidgetView::kind()->CustomResourceKind_0;
    let inner_name = InnerWidgetView::kind()->CustomResourceKind_0;
    reveal_strlit("widget");
    reveal_strlit("widget@inner");
    assert(outer_name != inner_name) by { assert(outer_name.len() != inner_name.len()); }
    assert(cluster.controller_models.dom() =~= Set::<int>::empty().insert(widget_sync_id()).insert(widget_janitor_id()));
    assert(it.contains_key(outer_name) && it[outer_name] == Cluster::installed_type::<OuterWidgetView>());
    assert(it.contains_key(inner_name) && it[inner_name] == Cluster::installed_type::<InnerWidgetView>());
    // Validation reads the spec only; transition validation is trivial.
    assert forall |name: StringView, o: DynamicObjectView, m: ObjectMetaView| it.contains_key(name) && o.kind == Kind::CustomResourceKind(name)
        implies (#[trigger] (it[name].valid_object)(DynamicObjectView { metadata: m, ..o })) == (it[name].valid_object)(o) by {
        let o1 = DynamicObjectView { metadata: m, ..o };
        if name == outer_name {
            assert(OuterWidgetView::unmarshal(o1) is Ok == OuterWidgetView::unmarshal(o) is Ok);
            if OuterWidgetView::unmarshal(o) is Ok {
                assert(OuterWidgetView::unmarshal(o1)->Ok_0.spec == OuterWidgetView::unmarshal(o)->Ok_0.spec);
            }
        } else {
            assert(name == inner_name);
            assert(InnerWidgetView::unmarshal(o1) is Ok == InnerWidgetView::unmarshal(o) is Ok);
            if InnerWidgetView::unmarshal(o) is Ok {
                assert(InnerWidgetView::unmarshal(o1)->Ok_0.spec == InnerWidgetView::unmarshal(o)->Ok_0.spec);
            }
        }
    }
    assert forall |name: StringView, o: DynamicObjectView, old: DynamicObjectView, m: ObjectMetaView, m_old: ObjectMetaView|
        it.contains_key(name) && o.kind == Kind::CustomResourceKind(name)
        implies (#[trigger] (it[name].valid_transition)(DynamicObjectView { metadata: m, ..o }, DynamicObjectView { metadata: m_old, ..old }))
            == (it[name].valid_transition)(o, old) by {
        if name == outer_name {} else { assert(name == inner_name); }
    }
    assert forall |name: StringView| #[trigger] it.contains_key(name) implies (it[name].unmarshallable_status)((it[name].marshalled_default_status)()) by {
        if name == outer_name {
            OuterWidgetView::marshal_status_preserves_integrity();
        } else {
            assert(name == inner_name);
            InnerWidgetView::marshal_status_preserves_integrity();
        }
    }
}

// The theorem for the concrete cluster: the sync reconciler at widget_sync_id()
// and the janitor at widget_janitor_id(), with both Widget types installed.
pub proof fn widget_instance_two_cluster_theorem()
    ensures ({
        let cluster = widget_cluster_instance();
        let tc = widget_two_cluster(cluster);
        widget_two_cluster_spec(cluster, widget_sync_id(), widget_janitor_id()).entails(
            two_cluster_spec_eventually_synced()
            .and(two_cluster_status_eventually_mirrored())
            .and(two_cluster_mirrors_stably_collected(tc))
            .and(two_cluster_mirrors_eventually_collected(tc))
            .and(always(lift_state(two_cluster_janitor_deletes_are_sound(tc, widget_janitor_id()))))
        )
    }),
{
    lemma_widget_instance_is_pair_cluster();
    widget_two_cluster_theorem(widget_cluster_instance(), widget_sync_id(), widget_janitor_id());
}

}
