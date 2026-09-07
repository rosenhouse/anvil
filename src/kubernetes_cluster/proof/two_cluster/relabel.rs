// The abstraction from a two-cluster state to a one-store state.
//
// The two API servers of TwoCluster count uids and resource versions
// independently. The one-store model counts them once. The abstraction unions
// the two stores and relabels every counter value by an injective map per side,
// chosen (by the refinement proof) so that the k-th allocation overall gets the
// value k. Counter values sit in object metadata (uid, resourceVersion, owner
// references), in request preconditions and patch tests, and, for a controller
// that copies a uid into an annotation, in annotation values; the last is
// covered by a per-kind annotation hook that the controller's own commutation
// lemma instantiates.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, api_server::types::*, builtin_controllers::types::*,
    cluster::*, controller::types::*, message::*, network::types::*, two_cluster::*,
};
use crate::vstd_ext::string_view::*;
use vstd::{map_lib::*, multiset::*, prelude::*, seq_lib::*, set_lib::*};

verus! {

pub struct Relabeling {
    pub uid: spec_fn(Side, Uid) -> Uid,
    pub rv: spec_fn(Side, ResourceVersion) -> ResourceVersion,
    // (kind of the object, annotation key, annotation value) -> relabeled value.
    pub annotation: spec_fn(Kind, StringView, StringView) -> StringView,
}

// Injective per side, with disjoint images across sides; the annotation hook is
// injective per kind and key.
pub open spec fn injective(r: Relabeling) -> bool {
    &&& forall |side: Side, a: Uid, b: Uid| #[trigger] (r.uid)(side, a) == #[trigger] (r.uid)(side, b) ==> a == b
    &&& forall |a: Uid, b: Uid| #[trigger] (r.uid)(Side::Primary, a) != #[trigger] (r.uid)(Side::Remote, b)
    &&& forall |side: Side, a: ResourceVersion, b: ResourceVersion| #[trigger] (r.rv)(side, a) == #[trigger] (r.rv)(side, b) ==> a == b
    &&& forall |a: ResourceVersion, b: ResourceVersion| #[trigger] (r.rv)(Side::Primary, a) != #[trigger] (r.rv)(Side::Remote, b)
    &&& forall |kind: Kind, key: StringView, a: StringView, b: StringView|
        #[trigger] (r.annotation)(kind, key, a) == #[trigger] (r.annotation)(kind, key, b) ==> a == b
}

// ---------------------------------------------------------------------------
// Relabeling of objects.
// ---------------------------------------------------------------------------

pub open spec fn relabel_opt_uid(r: Relabeling, side: Side, u: Option<Uid>) -> Option<Uid> {
    match u {
        Some(x) => Some((r.uid)(side, x)),
        None => None,
    }
}

pub open spec fn relabel_opt_rv(r: Relabeling, side: Side, v: Option<ResourceVersion>) -> Option<ResourceVersion> {
    match v {
        Some(x) => Some((r.rv)(side, x)),
        None => None,
    }
}

pub open spec fn relabel_owner_ref(tc: TwoCluster, r: Relabeling, o: OwnerReferenceView) -> OwnerReferenceView {
    OwnerReferenceView { uid: (r.uid)(tc.side_of_kind(o.kind), o.uid), ..o }
}

pub open spec fn relabel_owner_refs(tc: TwoCluster, r: Relabeling, o: Option<Seq<OwnerReferenceView>>) -> Option<Seq<OwnerReferenceView>> {
    match o {
        Some(refs) => Some(refs.map_values(|x: OwnerReferenceView| relabel_owner_ref(tc, r, x))),
        None => None,
    }
}

pub open spec fn relabel_annotations(r: Relabeling, kind: Kind, a: Option<Map<StringView, StringView>>) -> Option<Map<StringView, StringView>> {
    match a {
        Some(m) => Some(Map::new(m.dom(), |k: StringView| (r.annotation)(kind, k, m[k]))),
        None => None,
    }
}

pub open spec fn relabel_meta(tc: TwoCluster, r: Relabeling, kind: Kind, m: ObjectMetaView) -> ObjectMetaView {
    let side = tc.side_of_kind(kind);
    ObjectMetaView {
        resource_version: relabel_opt_rv(r, side, m.resource_version),
        uid: relabel_opt_uid(r, side, m.uid),
        annotations: relabel_annotations(r, kind, m.annotations),
        owner_references: relabel_owner_refs(tc, r, m.owner_references),
        ..m
    }
}

pub open spec fn relabel_obj(tc: TwoCluster, r: Relabeling, o: DynamicObjectView) -> DynamicObjectView {
    DynamicObjectView {
        kind: o.kind,
        metadata: relabel_meta(tc, r, o.kind, o.metadata),
        spec: o.spec,
        status: o.status,
    }
}

pub open spec fn relabel_preconditions(r: Relabeling, side: Side, p: Option<PreconditionsView>) -> Option<PreconditionsView> {
    match p {
        Some(pre) => Some(PreconditionsView {
            uid: relabel_opt_uid(r, side, pre.uid),
            resource_version: relabel_opt_rv(r, side, pre.resource_version),
        }),
        None => None,
    }
}

pub open spec fn relabel_tests(r: Relabeling, side: Side, t: PatchTestsView) -> PatchTestsView {
    PatchTestsView { uid: relabel_opt_uid(r, side, t.uid), ..t }
}

// A list response is relabeled as a set: the one-store List orders its result by
// Set::to_seq of the relabeled set, so the abstraction takes the same order.
pub open spec fn relabel_list(tc: TwoCluster, r: Relabeling, objs: Seq<DynamicObjectView>) -> Seq<DynamicObjectView> {
    objs.to_set().map(|o: DynamicObjectView| relabel_obj(tc, r, o)).to_seq()
}

pub open spec fn relabel_obj_result(tc: TwoCluster, r: Relabeling, res: Result<DynamicObjectView, APIError>) -> Result<DynamicObjectView, APIError> {
    match res {
        Ok(o) => Ok(relabel_obj(tc, r, o)),
        Err(e) => Err(e),
    }
}

// ---------------------------------------------------------------------------
// Relabeling of messages.
// ---------------------------------------------------------------------------

pub open spec fn relabel_req(tc: TwoCluster, r: Relabeling, req: APIRequest) -> APIRequest {
    match req {
        APIRequest::GetRequest(x) => APIRequest::GetRequest(x),
        APIRequest::ListRequest(x) => APIRequest::ListRequest(x),
        APIRequest::CreateRequest(x) => APIRequest::CreateRequest(CreateRequest { obj: relabel_obj(tc, r, x.obj), ..x }),
        APIRequest::DeleteRequest(x) => APIRequest::DeleteRequest(DeleteRequest {
            preconditions: relabel_preconditions(r, tc.side_of_kind(x.key.kind), x.preconditions), ..x
        }),
        APIRequest::UpdateRequest(x) => APIRequest::UpdateRequest(UpdateRequest { obj: relabel_obj(tc, r, x.obj), ..x }),
        APIRequest::UpdateStatusRequest(x) => APIRequest::UpdateStatusRequest(UpdateStatusRequest { obj: relabel_obj(tc, r, x.obj), ..x }),
        APIRequest::GetThenDeleteRequest(x) => APIRequest::GetThenDeleteRequest(GetThenDeleteRequest {
            owner_ref: relabel_owner_ref(tc, r, x.owner_ref), ..x
        }),
        APIRequest::GetThenUpdateRequest(x) => APIRequest::GetThenUpdateRequest(GetThenUpdateRequest {
            owner_ref: relabel_owner_ref(tc, r, x.owner_ref), obj: relabel_obj(tc, r, x.obj), ..x
        }),
        APIRequest::GetThenUpdateStatusRequest(x) => APIRequest::GetThenUpdateStatusRequest(GetThenUpdateStatusRequest {
            owner_ref: relabel_owner_ref(tc, r, x.owner_ref), obj: relabel_obj(tc, r, x.obj), ..x
        }),
        APIRequest::PatchRequest(x) => APIRequest::PatchRequest(PatchRequest {
            tests: relabel_tests(r, tc.side_of_kind(x.kind), x.tests), ..x
        }),
        APIRequest::PatchStatusRequest(x) => APIRequest::PatchStatusRequest(PatchStatusRequest {
            tests: relabel_tests(r, tc.side_of_kind(x.kind), x.tests), ..x
        }),
    }
}

pub open spec fn relabel_resp(tc: TwoCluster, r: Relabeling, resp: APIResponse) -> APIResponse {
    match resp {
        APIResponse::GetResponse(x) => APIResponse::GetResponse(GetResponse { res: relabel_obj_result(tc, r, x.res) }),
        APIResponse::ListResponse(x) => APIResponse::ListResponse(ListResponse {
            res: match x.res { Ok(objs) => Ok(relabel_list(tc, r, objs)), Err(e) => Err(e) }
        }),
        APIResponse::CreateResponse(x) => APIResponse::CreateResponse(CreateResponse { res: relabel_obj_result(tc, r, x.res) }),
        APIResponse::DeleteResponse(x) => APIResponse::DeleteResponse(x),
        APIResponse::UpdateResponse(x) => APIResponse::UpdateResponse(UpdateResponse { res: relabel_obj_result(tc, r, x.res) }),
        APIResponse::UpdateStatusResponse(x) => APIResponse::UpdateStatusResponse(UpdateStatusResponse { res: relabel_obj_result(tc, r, x.res) }),
        APIResponse::GetThenDeleteResponse(x) => APIResponse::GetThenDeleteResponse(x),
        APIResponse::GetThenUpdateResponse(x) => APIResponse::GetThenUpdateResponse(GetThenUpdateResponse { res: relabel_obj_result(tc, r, x.res) }),
        APIResponse::GetThenUpdateStatusResponse(x) => APIResponse::GetThenUpdateStatusResponse(GetThenUpdateStatusResponse { res: relabel_obj_result(tc, r, x.res) }),
        APIResponse::PatchResponse(x) => APIResponse::PatchResponse(PatchResponse { res: relabel_obj_result(tc, r, x.res) }),
        APIResponse::PatchStatusResponse(x) => APIResponse::PatchStatusResponse(PatchStatusResponse { res: relabel_obj_result(tc, r, x.res) }),
    }
}

pub open spec fn relabel_content(tc: TwoCluster, r: Relabeling, c: MessageContent) -> MessageContent {
    match c {
        MessageContent::APIRequest(req) => MessageContent::APIRequest(relabel_req(tc, r, req)),
        MessageContent::APIResponse(resp) => MessageContent::APIResponse(relabel_resp(tc, r, resp)),
        MessageContent::ExternalRequest(x) => MessageContent::ExternalRequest(x),
        MessageContent::ExternalResponse(x) => MessageContent::ExternalResponse(x),
    }
}

pub open spec fn relabel_msg(tc: TwoCluster, r: Relabeling, m: Message) -> Message {
    Message { content: relabel_content(tc, r, m.content), ..m }
}

pub open spec fn relabel_opt_msg(tc: TwoCluster, r: Relabeling, m: Option<Message>) -> Option<Message> {
    match m {
        Some(x) => Some(relabel_msg(tc, r, x)),
        None => None,
    }
}

// The multiset of relabeled messages: the count of relabel(m) is the count of m.
// (Well defined as a multiset because relabel_msg is injective, see below.)
pub open spec fn relabel_preimage(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>, m1: Message) -> Message {
    choose |m2: Message| #[trigger] ms.contains(m2) && relabel_msg(tc, r, m2) == m1
}

pub open spec fn relabel_image(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>) -> Set<Message> {
    ms.dom().map(|m2: Message| relabel_msg(tc, r, m2))
}

pub open spec fn relabel_msgs(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>) -> Multiset<Message> {
    let dom = relabel_image(tc, r, ms);
    Multiset::from_map(Map::new(dom, |m1: Message| ms.count(relabel_preimage(tc, r, ms, m1))))
}

// ---------------------------------------------------------------------------
// Relabeling of controller and cluster state.
// ---------------------------------------------------------------------------

pub open spec fn relabel_ongoing(tc: TwoCluster, r: Relabeling, o: OngoingReconcile) -> OngoingReconcile {
    OngoingReconcile {
        triggering_cr: relabel_obj(tc, r, o.triggering_cr),
        pending_req_msg: relabel_opt_msg(tc, r, o.pending_req_msg),
        ..o
    }
}

pub open spec fn relabel_controller(tc: TwoCluster, r: Relabeling, c: ControllerState) -> ControllerState {
    ControllerState {
        ongoing_reconciles: c.ongoing_reconciles.map_values(|o: OngoingReconcile| relabel_ongoing(tc, r, o)),
        scheduled_reconciles: c.scheduled_reconciles.map_values(|o: DynamicObjectView| relabel_obj(tc, r, o)),
        ..c
    }
}

pub open spec fn relabel_cae(tc: TwoCluster, r: Relabeling, c: ControllerAndExternalState) -> ControllerAndExternalState {
    ControllerAndExternalState { controller: relabel_controller(tc, r, c.controller), ..c }
}

pub open spec fn relabel_store(tc: TwoCluster, r: Relabeling, store: StoredState) -> StoredState {
    store.map_values(|o: DynamicObjectView| relabel_obj(tc, r, o))
}

// The one-store state: the union of the relabeled stores, with the global counters.
pub open spec fn abs(tc: TwoCluster, r: Relabeling, s: TwoClusterState, uid_next: Uid, rv_next: ResourceVersion) -> ClusterState {
    ClusterState {
        api_server: APIServerState {
            resources: relabel_store(tc, r, s.primary.resources).union_prefer_right(relabel_store(tc, r, s.remote.resources)),
            uid_counter: uid_next,
            resource_version_counter: rv_next,
        },
        controller_and_externals: s.controller_and_externals.map_values(|c: ControllerAndExternalState| relabel_cae(tc, r, c)),
        network: NetworkState { in_flight: relabel_msgs(tc, r, s.network.in_flight) },
        rpc_id_allocator: s.rpc_id_allocator,
        req_drop_enabled: s.req_drop_enabled,
        pod_monkey_enabled: s.pod_monkey_enabled,
    }
}

// ---------------------------------------------------------------------------
// What relabeling keeps.
// ---------------------------------------------------------------------------

pub proof fn lemma_relabel_obj_keeps_identity(tc: TwoCluster, r: Relabeling, o: DynamicObjectView)
    ensures
        relabel_obj(tc, r, o).kind == o.kind,
        relabel_obj(tc, r, o).object_ref() == o.object_ref(),
        relabel_obj(tc, r, o).metadata.name == o.metadata.name,
        relabel_obj(tc, r, o).metadata.namespace == o.metadata.namespace,
        relabel_obj(tc, r, o).metadata.generate_name == o.metadata.generate_name,
        relabel_obj(tc, r, o).metadata.generation == o.metadata.generation,
        relabel_obj(tc, r, o).metadata.labels == o.metadata.labels,
        relabel_obj(tc, r, o).metadata.finalizers == o.metadata.finalizers,
        relabel_obj(tc, r, o).metadata.deletion_timestamp == o.metadata.deletion_timestamp,
        relabel_obj(tc, r, o).spec == o.spec,
        relabel_obj(tc, r, o).status == o.status,
        relabel_obj(tc, r, o).metadata.uid is Some == o.metadata.uid is Some,
        relabel_obj(tc, r, o).metadata.resource_version is Some == o.metadata.resource_version is Some,
        relabel_obj(tc, r, o).metadata.owner_references is Some == o.metadata.owner_references is Some,
        relabel_obj(tc, r, o).metadata.annotations is Some == o.metadata.annotations is Some,
{
}

pub proof fn lemma_relabel_meta_injective(tc: TwoCluster, r: Relabeling, kind: Kind, a: ObjectMetaView, b: ObjectMetaView)
    requires
        injective(r),
        relabel_meta(tc, r, kind, a) == relabel_meta(tc, r, kind, b),
    ensures a == b,
{
    let side = tc.side_of_kind(kind);
    assert(a.uid == b.uid) by {
        match (a.uid, b.uid) {
            (Some(x), Some(y)) => { assert((r.uid)(side, x) == (r.uid)(side, y)); },
            _ => {},
        }
    }
    assert(a.resource_version == b.resource_version) by {
        match (a.resource_version, b.resource_version) {
            (Some(x), Some(y)) => { assert((r.rv)(side, x) == (r.rv)(side, y)); },
            _ => {},
        }
    }
    assert(a.annotations == b.annotations) by {
        match (a.annotations, b.annotations) {
            (Some(ma), Some(mb)) => {
                let ra = Map::new(ma.dom(), |k: StringView| (r.annotation)(kind, k, ma[k]));
                let rb = Map::new(mb.dom(), |k: StringView| (r.annotation)(kind, k, mb[k]));
                assert(ra == rb);
                assert forall |k: StringView| ma.contains_key(k) <==> mb.contains_key(k) by {
                    assert(ra.contains_key(k) <==> rb.contains_key(k));
                }
                assert forall |k: StringView| #[trigger] ma.contains_key(k) implies ma[k] == mb[k] by {
                    assert(ra[k] == rb[k]);
                    assert((r.annotation)(kind, k, ma[k]) == (r.annotation)(kind, k, mb[k]));
                }
                assert(ma =~= mb);
            },
            _ => {},
        }
    }
    assert(a.owner_references == b.owner_references) by {
        match (a.owner_references, b.owner_references) {
            (Some(sa), Some(sb)) => {
                let ra = sa.map_values(|x: OwnerReferenceView| relabel_owner_ref(tc, r, x));
                let rb = sb.map_values(|x: OwnerReferenceView| relabel_owner_ref(tc, r, x));
                assert(ra == rb);
                assert(sa.len() == sb.len());
                assert forall |i: int| 0 <= i < sa.len() implies sa[i] == sb[i] by {
                    assert(ra[i] == rb[i]);
                    let x = sa[i];
                    let y = sb[i];
                    assert(relabel_owner_ref(tc, r, x) == relabel_owner_ref(tc, r, y));
                    assert(x.kind == y.kind);
                    assert((r.uid)(tc.side_of_kind(x.kind), x.uid) == (r.uid)(tc.side_of_kind(y.kind), y.uid));
                }
                assert(sa =~= sb);
            },
            _ => {},
        }
    }
}

pub proof fn lemma_relabel_obj_injective(tc: TwoCluster, r: Relabeling, a: DynamicObjectView, b: DynamicObjectView)
    requires
        injective(r),
        relabel_obj(tc, r, a) == relabel_obj(tc, r, b),
    ensures a == b,
{
    lemma_relabel_meta_injective(tc, r, a.kind, a.metadata, b.metadata);
}

pub proof fn lemma_relabel_owner_ref_injective(tc: TwoCluster, r: Relabeling, a: OwnerReferenceView, b: OwnerReferenceView)
    requires
        injective(r),
        relabel_owner_ref(tc, r, a) == relabel_owner_ref(tc, r, b),
    ensures a == b,
{
    assert((r.uid)(tc.side_of_kind(a.kind), a.uid) == (r.uid)(tc.side_of_kind(b.kind), b.uid));
}

// Membership of an owner reference in a relabeled sequence.
pub proof fn lemma_relabel_owner_refs_contains(tc: TwoCluster, r: Relabeling, refs: Seq<OwnerReferenceView>, o: OwnerReferenceView)
    requires injective(r),
    ensures
        refs.map_values(|x: OwnerReferenceView| relabel_owner_ref(tc, r, x)).contains(relabel_owner_ref(tc, r, o)) == refs.contains(o),
{
    let mapped = refs.map_values(|x: OwnerReferenceView| relabel_owner_ref(tc, r, x));
    if refs.contains(o) {
        let i = choose |i: int| 0 <= i < refs.len() && refs[i] == o;
        assert(mapped[i] == relabel_owner_ref(tc, r, o));
    }
    if mapped.contains(relabel_owner_ref(tc, r, o)) {
        let i = choose |i: int| 0 <= i < mapped.len() && mapped[i] == relabel_owner_ref(tc, r, o);
        lemma_relabel_owner_ref_injective(tc, r, refs[i], o);
    }
}

// ---------------------------------------------------------------------------
// Messages and multisets of messages.
// ---------------------------------------------------------------------------

pub proof fn lemma_relabel_req_injective(tc: TwoCluster, r: Relabeling, a: APIRequest, b: APIRequest)
    requires
        injective(r),
        relabel_req(tc, r, a) == relabel_req(tc, r, b),
    ensures a == b,
{
    match (a, b) {
        (APIRequest::CreateRequest(x), APIRequest::CreateRequest(y)) => { lemma_relabel_obj_injective(tc, r, x.obj, y.obj); },
        (APIRequest::DeleteRequest(x), APIRequest::DeleteRequest(y)) => {
            let side = tc.side_of_kind(x.key.kind);
            match (x.preconditions, y.preconditions) {
                (Some(px), Some(py)) => {
                    match (px.uid, py.uid) { (Some(u), Some(v)) => { assert((r.uid)(side, u) == (r.uid)(side, v)); }, _ => {} }
                    match (px.resource_version, py.resource_version) { (Some(u), Some(v)) => { assert((r.rv)(side, u) == (r.rv)(side, v)); }, _ => {} }
                },
                _ => {},
            }
        },
        (APIRequest::UpdateRequest(x), APIRequest::UpdateRequest(y)) => { lemma_relabel_obj_injective(tc, r, x.obj, y.obj); },
        (APIRequest::UpdateStatusRequest(x), APIRequest::UpdateStatusRequest(y)) => { lemma_relabel_obj_injective(tc, r, x.obj, y.obj); },
        (APIRequest::GetThenDeleteRequest(x), APIRequest::GetThenDeleteRequest(y)) => { lemma_relabel_owner_ref_injective(tc, r, x.owner_ref, y.owner_ref); },
        (APIRequest::GetThenUpdateRequest(x), APIRequest::GetThenUpdateRequest(y)) => {
            lemma_relabel_owner_ref_injective(tc, r, x.owner_ref, y.owner_ref);
            lemma_relabel_obj_injective(tc, r, x.obj, y.obj);
        },
        (APIRequest::GetThenUpdateStatusRequest(x), APIRequest::GetThenUpdateStatusRequest(y)) => {
            lemma_relabel_owner_ref_injective(tc, r, x.owner_ref, y.owner_ref);
            lemma_relabel_obj_injective(tc, r, x.obj, y.obj);
        },
        (APIRequest::PatchRequest(x), APIRequest::PatchRequest(y)) => {
            let side = tc.side_of_kind(x.kind);
            match (x.tests.uid, y.tests.uid) { (Some(u), Some(v)) => { assert((r.uid)(side, u) == (r.uid)(side, v)); }, _ => {} }
        },
        (APIRequest::PatchStatusRequest(x), APIRequest::PatchStatusRequest(y)) => {
            let side = tc.side_of_kind(x.kind);
            match (x.tests.uid, y.tests.uid) { (Some(u), Some(v)) => { assert((r.uid)(side, u) == (r.uid)(side, v)); }, _ => {} }
        },
        _ => {},
    }
}

pub proof fn lemma_relabel_list_injective(tc: TwoCluster, r: Relabeling, a: Seq<DynamicObjectView>, b: Seq<DynamicObjectView>)
    requires
        injective(r),
        relabel_list(tc, r, a) == relabel_list(tc, r, b),
    ensures a.to_set() == b.to_set(),
{
    let f = |o: DynamicObjectView| relabel_obj(tc, r, o);
    let sa = a.to_set().map(f);
    let sb = b.to_set().map(f);
    sa.lemma_to_seq_to_set_id();
    sb.lemma_to_seq_to_set_id();
    assert(sa =~= sb);
    assert forall |o: DynamicObjectView| a.to_set().contains(o) <==> b.to_set().contains(o) by {
        a.to_set().lemma_map_contains(f, f(o));
        b.to_set().lemma_map_contains(f, f(o));
        if a.to_set().contains(o) {
            assert(sa.contains(f(o)));
            assert(sb.contains(f(o)));
            let o2 = choose |o2: DynamicObjectView| b.to_set().contains(o2) && f(o) == f(o2);
            lemma_relabel_obj_injective(tc, r, o, o2);
        }
        if b.to_set().contains(o) {
            assert(sb.contains(f(o)));
            assert(sa.contains(f(o)));
            let o2 = choose |o2: DynamicObjectView| a.to_set().contains(o2) && f(o) == f(o2);
            lemma_relabel_obj_injective(tc, r, o, o2);
        }
    }
    assert(a.to_set() =~= b.to_set());
}

pub proof fn lemma_relabel_obj_result_injective(tc: TwoCluster, r: Relabeling, a: Result<DynamicObjectView, APIError>, b: Result<DynamicObjectView, APIError>)
    requires
        injective(r),
        relabel_obj_result(tc, r, a) == relabel_obj_result(tc, r, b),
    ensures a == b,
{
    match (a, b) {
        (Ok(x), Ok(y)) => { lemma_relabel_obj_injective(tc, r, x, y); },
        _ => {},
    }
}

// Relabeled responses are injective except for the order of a list, which the
// abstraction forgets. Two messages with the same relabeling therefore carry the
// same list as a set. The multiset of in-flight messages is treated up to that
// equivalence: see relabel_msgs_count below, which only needs the forward
// direction.
pub proof fn lemma_relabel_msg_of_eq(tc: TwoCluster, r: Relabeling, a: Message, b: Message)
    requires
        injective(r),
        relabel_msg(tc, r, a) == relabel_msg(tc, r, b),
        !(a.content is APIResponse && a.content->APIResponse_0 is ListResponse),
    ensures a == b,
{
    match (a.content, b.content) {
        (MessageContent::APIRequest(x), MessageContent::APIRequest(y)) => { lemma_relabel_req_injective(tc, r, x, y); },
        (MessageContent::APIResponse(x), MessageContent::APIResponse(y)) => {
            match (x, y) {
                (APIResponse::GetResponse(p), APIResponse::GetResponse(q)) => { lemma_relabel_obj_result_injective(tc, r, p.res, q.res); },
                (APIResponse::CreateResponse(p), APIResponse::CreateResponse(q)) => { lemma_relabel_obj_result_injective(tc, r, p.res, q.res); },
                (APIResponse::UpdateResponse(p), APIResponse::UpdateResponse(q)) => { lemma_relabel_obj_result_injective(tc, r, p.res, q.res); },
                (APIResponse::UpdateStatusResponse(p), APIResponse::UpdateStatusResponse(q)) => { lemma_relabel_obj_result_injective(tc, r, p.res, q.res); },
                (APIResponse::GetThenUpdateResponse(p), APIResponse::GetThenUpdateResponse(q)) => { lemma_relabel_obj_result_injective(tc, r, p.res, q.res); },
                (APIResponse::GetThenUpdateStatusResponse(p), APIResponse::GetThenUpdateStatusResponse(q)) => { lemma_relabel_obj_result_injective(tc, r, p.res, q.res); },
                (APIResponse::PatchResponse(p), APIResponse::PatchResponse(q)) => { lemma_relabel_obj_result_injective(tc, r, p.res, q.res); },
                (APIResponse::PatchStatusResponse(p), APIResponse::PatchStatusResponse(q)) => { lemma_relabel_obj_result_injective(tc, r, p.res, q.res); },
                _ => {},
            }
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Stores.
// ---------------------------------------------------------------------------

pub proof fn lemma_relabel_store_index(tc: TwoCluster, r: Relabeling, store: StoredState, k: ObjectRef)
    ensures
        relabel_store(tc, r, store).contains_key(k) == store.contains_key(k),
        store.contains_key(k) ==> relabel_store(tc, r, store)[k] == relabel_obj(tc, r, store[k]),
        relabel_store(tc, r, store).dom() == store.dom(),
{
    assert(relabel_store(tc, r, store).dom() =~= store.dom());
}

pub proof fn lemma_relabel_store_insert(tc: TwoCluster, r: Relabeling, store: StoredState, k: ObjectRef, o: DynamicObjectView)
    ensures relabel_store(tc, r, store.insert(k, o)) == relabel_store(tc, r, store).insert(k, relabel_obj(tc, r, o)),
{
    let lhs = relabel_store(tc, r, store.insert(k, o));
    let rhs = relabel_store(tc, r, store).insert(k, relabel_obj(tc, r, o));
    assert forall |j: ObjectRef| lhs.contains_key(j) <==> rhs.contains_key(j) by {
        lemma_relabel_store_index(tc, r, store.insert(k, o), j);
        lemma_relabel_store_index(tc, r, store, j);
    }
    assert forall |j: ObjectRef| #[trigger] lhs.contains_key(j) implies lhs[j] == rhs[j] by {
        lemma_relabel_store_index(tc, r, store.insert(k, o), j);
        lemma_relabel_store_index(tc, r, store, j);
    }
    assert(lhs =~= rhs);
}

pub proof fn lemma_relabel_store_remove(tc: TwoCluster, r: Relabeling, store: StoredState, k: ObjectRef)
    ensures relabel_store(tc, r, store.remove(k)) == relabel_store(tc, r, store).remove(k),
{
    let lhs = relabel_store(tc, r, store.remove(k));
    let rhs = relabel_store(tc, r, store).remove(k);
    assert forall |j: ObjectRef| lhs.contains_key(j) <==> rhs.contains_key(j) by {
        lemma_relabel_store_index(tc, r, store.remove(k), j);
        lemma_relabel_store_index(tc, r, store, j);
    }
    assert forall |j: ObjectRef| #[trigger] lhs.contains_key(j) implies lhs[j] == rhs[j] by {
        lemma_relabel_store_index(tc, r, store.remove(k), j);
        lemma_relabel_store_index(tc, r, store, j);
    }
    assert(lhs =~= rhs);
}

}
