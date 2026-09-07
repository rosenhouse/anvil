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

// Injective per side, with disjoint images across sides.
pub open spec fn uid_map_injective(u: spec_fn(Side, Uid) -> Uid) -> bool {
    &&& forall |side: Side, a: Uid, b: Uid| #[trigger] u(side, a) == #[trigger] u(side, b) ==> a == b
    &&& forall |a: Uid, b: Uid| #[trigger] u(Side::Primary, a) != #[trigger] u(Side::Remote, b)
}

pub open spec fn rv_map_injective(v: spec_fn(Side, ResourceVersion) -> ResourceVersion) -> bool {
    &&& forall |side: Side, a: ResourceVersion, b: ResourceVersion| #[trigger] v(side, a) == #[trigger] v(side, b) ==> a == b
    &&& forall |a: ResourceVersion, b: ResourceVersion| #[trigger] v(Side::Primary, a) != #[trigger] v(Side::Remote, b)
}

// Injective per kind and key.
pub open spec fn annotation_injective(h: spec_fn(Kind, StringView, StringView) -> StringView) -> bool {
    forall |kind: Kind, key: StringView, a: StringView, b: StringView| #[trigger] h(kind, key, a) == #[trigger] h(kind, key, b) ==> a == b
}

pub open spec fn injective(r: Relabeling) -> bool {
    &&& uid_map_injective(r.uid)
    &&& rv_map_injective(r.rv)
    &&& annotation_injective(r.annotation)
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

// The multiset of relabeled messages: the count of m1 is the number of messages
// of ms that relabel to m1, with multiplicity. (Only the order of a list response
// is forgotten by relabeling, so this is the count of the preimage in practice.)
pub open spec fn relabel_image(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>) -> Set<Message> {
    ms.dom().map(|m2: Message| relabel_msg(tc, r, m2))
}

pub open spec fn relabel_preimages(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>, m1: Message) -> Multiset<Message> {
    ms.filter(|m2: Message| relabel_msg(tc, r, m2) == m1)
}

pub open spec fn relabel_msgs(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>) -> Multiset<Message> {
    Multiset::from_map(Map::new(relabel_image(tc, r, ms), |m1: Message| relabel_preimages(tc, r, ms, m1).len()))
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

// The union of the two relabeled stores. Under stores_sided the two have disjoint keys.
pub open spec fn abs_store(tc: TwoCluster, r: Relabeling, s: TwoClusterState) -> StoredState {
    relabel_store(tc, r, s.primary.resources).union_prefer_right(relabel_store(tc, r, s.remote.resources))
}

pub open spec fn abs_api_server(tc: TwoCluster, r: Relabeling, s: TwoClusterState, uid_next: Uid, rv_next: ResourceVersion) -> APIServerState {
    APIServerState {
        resources: abs_store(tc, r, s),
        uid_counter: uid_next,
        resource_version_counter: rv_next,
    }
}

// The one-store state: the union of the relabeled stores, with the global counters.
pub open spec fn abs(tc: TwoCluster, r: Relabeling, s: TwoClusterState, uid_next: Uid, rv_next: ResourceVersion) -> ClusterState {
    ClusterState {
        api_server: abs_api_server(tc, r, s, uid_next, rv_next),
        controller_and_externals: s.controller_and_externals.map_values(|c: ControllerAndExternalState| relabel_cae(tc, r, c)),
        network: NetworkState { in_flight: relabel_msgs(tc, r, s.network.in_flight) },
        rpc_id_allocator: s.rpc_id_allocator,
        req_drop_enabled: s.req_drop_enabled,
        pod_monkey_enabled: s.pod_monkey_enabled,
    }
}

// An object a store may hold or a reconcile may be scheduled with: object_ok
// (of a known kind, with owner references to kinds of its own side), with a
// uid, and unmarshallable.
pub open spec fn stored_object_ok(tc: TwoCluster, o: DynamicObjectView) -> bool {
    &&& tc.object_ok(o)
    &&& o.metadata.uid is Some
    &&& unmarshallable_object(o, tc.cluster.installed_types)
}

// Every object of a store is under a key of its own kind, of a kind of that
// store's side, and stored_object_ok.
pub open spec fn store_sided(tc: TwoCluster, side: Side, store: StoredState) -> bool {
    forall |k: ObjectRef| #[trigger] store.contains_key(k) ==> tc.side_of_kind(k.kind) == side && store[k].kind == k.kind && stored_object_ok(tc, store[k])
}

// The default status of every installed type unmarshals. (Every type installed
// through Cluster::installed_type satisfies this.)
pub open spec fn installed_types_coherent(it: InstalledTypes) -> bool {
    forall |name: StringView| #[trigger] it.contains_key(name) ==> (it[name].unmarshallable_status)((it[name].marshalled_default_status)())
}

// A freshly created object, whose status is the default one, unmarshals if its
// spec does.
pub proof fn lemma_created_object_unmarshallable(tc: TwoCluster, o: DynamicObjectView)
    requires
        installed_types_coherent(tc.cluster.installed_types),
        tc.kind_ok(o.kind),
        unmarshallable_spec(o, tc.cluster.installed_types),
        o.status == marshalled_default_status(o.kind, tc.cluster.installed_types),
    ensures unmarshallable_object(o, tc.cluster.installed_types),
{
    match o.kind {
        Kind::ConfigMapKind => { ConfigMapView::marshal_status_preserves_integrity(); },
        Kind::DaemonSetKind => { DaemonSetView::marshal_status_preserves_integrity(); },
        Kind::PersistentVolumeClaimKind => { PersistentVolumeClaimView::marshal_status_preserves_integrity(); },
        Kind::PodKind => { PodView::marshal_status_preserves_integrity(); },
        Kind::RoleBindingKind => { RoleBindingView::marshal_status_preserves_integrity(); },
        Kind::RoleKind => { RoleView::marshal_status_preserves_integrity(); },
        Kind::SecretKind => { SecretView::marshal_status_preserves_integrity(); },
        Kind::ServiceKind => { ServiceView::marshal_status_preserves_integrity(); },
        Kind::StatefulSetKind => { StatefulSetView::marshal_status_preserves_integrity(); },
        Kind::ServiceAccountKind => { ServiceAccountView::marshal_status_preserves_integrity(); },
        Kind::CustomResourceKind(name) => {},
    }
}

pub open spec fn stores_sided(tc: TwoCluster, s: TwoClusterState) -> bool {
    &&& store_sided(tc, Side::Primary, s.primary.resources)
    &&& store_sided(tc, Side::Remote, s.remote.resources)
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


pub proof fn lemma_relabel_store_contains_key(tc: TwoCluster, r: Relabeling, store: StoredState, k: ObjectRef)
    ensures relabel_store(tc, r, store).contains_key(k) == store.contains_key(k),
{
}

pub proof fn lemma_abs_store_index(tc: TwoCluster, r: Relabeling, s: TwoClusterState, k: ObjectRef)
    requires stores_sided(tc, s),
    ensures
        abs_store(tc, r, s).contains_key(k) == s.store(tc.side_of_kind(k.kind)).resources.contains_key(k),
        s.store(tc.side_of_kind(k.kind)).resources.contains_key(k)
            ==> abs_store(tc, r, s)[k] == relabel_obj(tc, r, s.store(tc.side_of_kind(k.kind)).resources[k]),
        abs_store(tc, r, s).contains_key(k) ==> tc.side_of_kind(abs_store(tc, r, s)[k].kind) == tc.side_of_kind(k.kind)
            && abs_store(tc, r, s)[k].kind == k.kind,
{
    lemma_relabel_store_index(tc, r, s.primary.resources, k);
    lemma_relabel_store_index(tc, r, s.remote.resources, k);
}

pub proof fn lemma_abs_store_unchanged(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState)
    requires
        s_prime.primary.resources == s.primary.resources,
        s_prime.remote.resources == s.remote.resources,
    ensures abs_store(tc, r, s_prime) == abs_store(tc, r, s),
{
}

pub proof fn lemma_abs_store_insert(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, side: Side, k: ObjectRef, o: DynamicObjectView)
    requires
        stores_sided(tc, s),
        tc.side_of_kind(k.kind) == side,
        s_prime.store(side).resources == s.store(side).resources.insert(k, o),
        s_prime.store(side.other()).resources == s.store(side.other()).resources,
    ensures abs_store(tc, r, s_prime) == abs_store(tc, r, s).insert(k, relabel_obj(tc, r, o)),
{
    let lhs = abs_store(tc, r, s_prime);
    let rhs = abs_store(tc, r, s).insert(k, relabel_obj(tc, r, o));
    lemma_relabel_store_insert(tc, r, s.store(side).resources, k, o);
    assert forall |j: ObjectRef| lhs.contains_key(j) <==> rhs.contains_key(j) by {
        lemma_relabel_store_index(tc, r, s.primary.resources, j);
        lemma_relabel_store_index(tc, r, s.remote.resources, j);
        lemma_relabel_store_index(tc, r, s_prime.primary.resources, j);
        lemma_relabel_store_index(tc, r, s_prime.remote.resources, j);
    }
    assert forall |j: ObjectRef| #[trigger] lhs.contains_key(j) implies lhs[j] == rhs[j] by {
        lemma_relabel_store_index(tc, r, s.primary.resources, j);
        lemma_relabel_store_index(tc, r, s.remote.resources, j);
        lemma_relabel_store_index(tc, r, s_prime.primary.resources, j);
        lemma_relabel_store_index(tc, r, s_prime.remote.resources, j);
    }
    assert(lhs =~= rhs);
}

pub proof fn lemma_abs_store_remove(tc: TwoCluster, r: Relabeling, s: TwoClusterState, s_prime: TwoClusterState, side: Side, k: ObjectRef)
    requires
        stores_sided(tc, s),
        tc.side_of_kind(k.kind) == side,
        s_prime.store(side).resources == s.store(side).resources.remove(k),
        s_prime.store(side.other()).resources == s.store(side.other()).resources,
    ensures abs_store(tc, r, s_prime) == abs_store(tc, r, s).remove(k),
{
    let lhs = abs_store(tc, r, s_prime);
    let rhs = abs_store(tc, r, s).remove(k);
    lemma_relabel_store_remove(tc, r, s.store(side).resources, k);
    assert forall |j: ObjectRef| lhs.contains_key(j) <==> rhs.contains_key(j) by {
        lemma_relabel_store_index(tc, r, s.primary.resources, j);
        lemma_relabel_store_index(tc, r, s.remote.resources, j);
        lemma_relabel_store_index(tc, r, s_prime.primary.resources, j);
        lemma_relabel_store_index(tc, r, s_prime.remote.resources, j);
    }
    assert forall |j: ObjectRef| #[trigger] lhs.contains_key(j) implies lhs[j] == rhs[j] by {
        lemma_relabel_store_index(tc, r, s.primary.resources, j);
        lemma_relabel_store_index(tc, r, s.remote.resources, j);
        lemma_relabel_store_index(tc, r, s_prime.primary.resources, j);
        lemma_relabel_store_index(tc, r, s_prime.remote.resources, j);
    }
    assert(lhs =~= rhs);
}

// The objects of one namespace and kind in the union are the relabeled objects of
// that namespace and kind in the store of the kind's side.
pub proof fn lemma_abs_store_list(tc: TwoCluster, r: Relabeling, s: TwoClusterState, namespace: StringView, kind: Kind)
    requires stores_sided(tc, s),
    ensures ({
        let sel = |o: DynamicObjectView| {
            &&& o.object_ref().namespace == namespace
            &&& o.object_ref().kind == kind
        };
        let f = |o: DynamicObjectView| relabel_obj(tc, r, o);
        abs_store(tc, r, s).values().filter(sel) == s.store(tc.side_of_kind(kind)).resources.values().filter(sel).map(f)
    }),
{
    let sel = |o: DynamicObjectView| {
        &&& o.object_ref().namespace == namespace
        &&& o.object_ref().kind == kind
    };
    let f = |o: DynamicObjectView| relabel_obj(tc, r, o);
    let side = tc.side_of_kind(kind);
    let a = abs_store(tc, r, s);
    let store = s.store(side).resources;
    let lhs = a.values().filter(sel);
    let rhs = store.values().filter(sel).map(f);
    assert forall |o1: DynamicObjectView| lhs.contains(o1) implies rhs.contains(o1) by {
        a.dom().lemma_map_contains(|k: ObjectRef| a[k], o1);
        let k = choose |k: ObjectRef| a.dom().contains(k) && a[k] == o1;
        lemma_abs_store_index(tc, r, s, k);
        assert(tc.side_of_kind(k.kind) == side);
        let o = store[k];
        assert(o1 == f(o));
        assert(store.values().contains(o)) by {
            store.dom().lemma_map_contains(|k: ObjectRef| store[k], o);
            assert(store.dom().contains(k) && store[k] == o);
        }
        assert(store.values().filter(sel).contains(o));
        store.values().filter(sel).lemma_map_contains(f, o1);
    }
    assert forall |o1: DynamicObjectView| rhs.contains(o1) implies lhs.contains(o1) by {
        store.values().filter(sel).lemma_map_contains(f, o1);
        let o = choose |o: DynamicObjectView| store.values().filter(sel).contains(o) && o1 == f(o);
        store.dom().lemma_map_contains(|k: ObjectRef| store[k], o);
        let k = choose |k: ObjectRef| store.dom().contains(k) && store[k] == o;
        lemma_abs_store_index(tc, r, s, k);
        assert(a.dom().contains(k) && a[k] == o1);
        a.dom().lemma_map_contains(|k: ObjectRef| a[k], o1);
        assert(a.values().contains(o1));
    }
    assert(lhs =~= rhs);
}

// ---------------------------------------------------------------------------
// Multisets of messages.
// ---------------------------------------------------------------------------

pub proof fn lemma_relabel_msgs_count(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>, m1: Message)
    ensures relabel_msgs(tc, r, ms).count(m1) == relabel_preimages(tc, r, ms, m1).len(),
{
    broadcast use group_multiset_axioms, Multiset::dom_ensures;
    let image = relabel_image(tc, r, ms);
    let m = Map::new(image, |m1: Message| relabel_preimages(tc, r, ms, m1).len());
    let g = |m2: Message| relabel_msg(tc, r, m2);
    let pre = relabel_preimages(tc, r, ms, m1);
    if image.contains(m1) {
        assert(relabel_msgs(tc, r, ms).count(m1) == m[m1]);
    } else {
        assert(relabel_msgs(tc, r, ms).count(m1) == 0);
        assert forall |m2: Message| pre.count(m2) == 0 by {
            if relabel_msg(tc, r, m2) == m1 && ms.count(m2) > 0 {
                ms.dom().lemma_map_contains(g, m1);
                assert(ms.dom().contains(m2));
                assert(image.contains(m1));
            }
        }
        assert(pre =~= Multiset::<Message>::empty());
    }
}

pub proof fn lemma_relabel_msgs_empty(tc: TwoCluster, r: Relabeling)
    ensures relabel_msgs(tc, r, Multiset::<Message>::empty()) == Multiset::<Message>::empty(),
{
    broadcast use group_multiset_axioms;
    let lhs = relabel_msgs(tc, r, Multiset::<Message>::empty());
    assert forall |m1: Message| lhs.count(m1) == 0 by {
        lemma_relabel_msgs_count(tc, r, Multiset::<Message>::empty(), m1);
        let pre = relabel_preimages(tc, r, Multiset::<Message>::empty(), m1);
        assert forall |m2: Message| pre.count(m2) == 0 by {}
        assert(pre =~= Multiset::<Message>::empty());
    }
    assert(lhs =~= Multiset::<Message>::empty());
}

pub proof fn lemma_relabel_msgs_contains(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>, m: Message)
    ensures
        ms.contains(m) ==> relabel_msgs(tc, r, ms).contains(relabel_msg(tc, r, m)),
        relabel_msgs(tc, r, ms).contains(m) ==> exists |m2: Message| ms.contains(m2) && relabel_msg(tc, r, m2) == m,
{
    broadcast use group_multiset_axioms, group_multiset_properties;
    if ms.contains(m) {
        lemma_relabel_msgs_count(tc, r, ms, relabel_msg(tc, r, m));
        let pre = relabel_preimages(tc, r, ms, relabel_msg(tc, r, m));
        assert(pre.count(m) == ms.count(m));
    }
    if relabel_msgs(tc, r, ms).contains(m) {
        lemma_relabel_msgs_count(tc, r, ms, m);
        let pre = relabel_preimages(tc, r, ms, m);
        assert(pre.len() > 0);
        let m2 = choose |m2: Message| 0 < pre.count(m2);
        assert(ms.contains(m2) && relabel_msg(tc, r, m2) == m);
    }
}

pub proof fn lemma_relabel_msgs_insert(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>, m: Message)
    ensures relabel_msgs(tc, r, ms.insert(m)) == relabel_msgs(tc, r, ms).insert(relabel_msg(tc, r, m)),
{
    broadcast use group_multiset_axioms, group_multiset_properties;
    let lhs = relabel_msgs(tc, r, ms.insert(m));
    let rhs = relabel_msgs(tc, r, ms).insert(relabel_msg(tc, r, m));
    assert forall |m1: Message| lhs.count(m1) == rhs.count(m1) by {
        lemma_relabel_msgs_count(tc, r, ms.insert(m), m1);
        lemma_relabel_msgs_count(tc, r, ms, m1);
        let pre = relabel_preimages(tc, r, ms, m1);
        let pre_prime = relabel_preimages(tc, r, ms.insert(m), m1);
        if relabel_msg(tc, r, m) == m1 {
            assert(pre_prime =~= pre.insert(m));
        } else {
            assert(pre_prime =~= pre);
        }
    }
    assert(lhs =~= rhs);
}

pub proof fn lemma_relabel_msgs_remove(tc: TwoCluster, r: Relabeling, ms: Multiset<Message>, m: Message)
    requires ms.contains(m),
    ensures relabel_msgs(tc, r, ms.remove(m)) == relabel_msgs(tc, r, ms).remove(relabel_msg(tc, r, m)),
{
    broadcast use group_multiset_axioms, group_multiset_properties;
    let lhs = relabel_msgs(tc, r, ms.remove(m));
    let rhs = relabel_msgs(tc, r, ms).remove(relabel_msg(tc, r, m));
    assert forall |m1: Message| lhs.count(m1) == rhs.count(m1) by {
        lemma_relabel_msgs_count(tc, r, ms.remove(m), m1);
        lemma_relabel_msgs_count(tc, r, ms, m1);
        let pre = relabel_preimages(tc, r, ms, m1);
        let pre_prime = relabel_preimages(tc, r, ms.remove(m), m1);
        if relabel_msg(tc, r, m) == m1 {
            assert(pre_prime =~= pre.remove(m));
            assert(pre.count(m) == ms.count(m));
            assert(Multiset::singleton(m).subset_of(pre));
            assert(pre.remove(m).len() == pre.len() - 1);
        } else {
            assert(pre_prime =~= pre);
        }
    }
    assert(lhs =~= rhs);
}

pub proof fn lemma_add_empty<V>(ms: Multiset<V>)
    ensures ms.add(Multiset::<V>::empty()) == ms,
{
    broadcast use group_multiset_axioms;
    assert(ms.add(Multiset::<V>::empty()) =~= ms);
}

// ---------------------------------------------------------------------------
// Validity checks are relabel-invariant.
// ---------------------------------------------------------------------------

// The installed custom types validate objects and transitions without looking at
// the metadata. (CustomResourceView promises this for state validation; a type
// whose transition validation read a uid would violate it.)
pub open spec fn installed_types_ignore_metadata(it: InstalledTypes) -> bool {
    &&& forall |name: StringView, o: DynamicObjectView, m: ObjectMetaView| it.contains_key(name) && o.kind == Kind::CustomResourceKind(name)
        ==> (#[trigger] (it[name].valid_object)(DynamicObjectView { metadata: m, ..o })) == (it[name].valid_object)(o)
    &&& forall |name: StringView, o: DynamicObjectView, old: DynamicObjectView, m: ObjectMetaView, m_old: ObjectMetaView|
        it.contains_key(name) && o.kind == Kind::CustomResourceKind(name)
        ==> (#[trigger] (it[name].valid_transition)(DynamicObjectView { metadata: m, ..o }, DynamicObjectView { metadata: m_old, ..old }))
            == (it[name].valid_transition)(o, old)
}

pub proof fn lemma_owner_refs_filter_relabel(tc: TwoCluster, r: Relabeling, refs: Seq<OwnerReferenceView>)
    ensures ({
        let p = |o: OwnerReferenceView| o.controller is Some && o.controller->0;
        let g = |x: OwnerReferenceView| relabel_owner_ref(tc, r, x);
        refs.map_values(g).filter(p).len() == refs.filter(p).len()
    }),
    decreases refs.len(),
{
    let p = |o: OwnerReferenceView| o.controller is Some && o.controller->0;
    let g = |x: OwnerReferenceView| relabel_owner_ref(tc, r, x);
    reveal_with_fuel(Seq::filter, 2);
    if refs.len() == 0 {
        assert(refs.map_values(g).len() == 0);
    } else {
        let rest = refs.drop_last();
        lemma_owner_refs_filter_relabel(tc, r, rest);
        assert(refs.map_values(g).drop_last() =~= rest.map_values(g));
        assert(refs.map_values(g).last() == g(refs.last()));
        assert(p(g(refs.last())) == p(refs.last()));
    }
}

pub proof fn lemma_metadata_validity_check_relabel(tc: TwoCluster, r: Relabeling, o: DynamicObjectView)
    ensures metadata_validity_check(relabel_obj(tc, r, o)) == metadata_validity_check(o),
{
    match o.metadata.owner_references {
        Some(refs) => { lemma_owner_refs_filter_relabel(tc, r, refs); },
        None => {},
    }
}

pub proof fn lemma_metadata_transition_validity_check_relabel(tc: TwoCluster, r: Relabeling, o: DynamicObjectView, old: DynamicObjectView)
    ensures metadata_transition_validity_check(relabel_obj(tc, r, o), relabel_obj(tc, r, old)) == metadata_transition_validity_check(o, old),
{
}

pub proof fn lemma_unmarshallable_object_relabel(tc: TwoCluster, r: Relabeling, o: DynamicObjectView)
    ensures unmarshallable_object(relabel_obj(tc, r, o), tc.cluster.installed_types) == unmarshallable_object(o, tc.cluster.installed_types),
{
}

pub proof fn lemma_valid_object_ignores_metadata(tc: TwoCluster, o: DynamicObjectView, m: ObjectMetaView)
    requires
        installed_types_ignore_metadata(tc.cluster.installed_types),
        tc.kind_ok(o.kind),
    ensures valid_object(DynamicObjectView { metadata: m, ..o }, tc.cluster.installed_types) == valid_object(o, tc.cluster.installed_types),
{
    let it = tc.cluster.installed_types;
    let o1 = DynamicObjectView { metadata: m, ..o };
    match o.kind {
        Kind::CustomResourceKind(name) => {
            assert((it[name].valid_object)(o1) == (it[name].valid_object)(o));
        },
        _ => {},
    }
}

pub proof fn lemma_valid_transition_ignores_metadata(tc: TwoCluster, o: DynamicObjectView, old: DynamicObjectView, m: ObjectMetaView, m_old: ObjectMetaView)
    requires
        installed_types_ignore_metadata(tc.cluster.installed_types),
        tc.kind_ok(o.kind),
    ensures valid_transition(DynamicObjectView { metadata: m, ..o }, DynamicObjectView { metadata: m_old, ..old }, tc.cluster.installed_types)
        == valid_transition(o, old, tc.cluster.installed_types),
{
    let it = tc.cluster.installed_types;
    match o.kind {
        Kind::CustomResourceKind(name) => {
            assert((it[name].valid_transition)(DynamicObjectView { metadata: m, ..o }, DynamicObjectView { metadata: m_old, ..old })
                == (it[name].valid_transition)(o, old));
        },
        _ => {},
    }
}

pub proof fn lemma_valid_object_relabel(tc: TwoCluster, r: Relabeling, o: DynamicObjectView)
    requires
        installed_types_ignore_metadata(tc.cluster.installed_types),
        tc.kind_ok(o.kind),
    ensures valid_object(relabel_obj(tc, r, o), tc.cluster.installed_types) == valid_object(o, tc.cluster.installed_types),
{
    lemma_valid_object_ignores_metadata(tc, o, relabel_obj(tc, r, o).metadata);
}

pub proof fn lemma_valid_transition_relabel(tc: TwoCluster, r: Relabeling, o: DynamicObjectView, old: DynamicObjectView)
    requires
        installed_types_ignore_metadata(tc.cluster.installed_types),
        tc.kind_ok(o.kind),
    ensures valid_transition(relabel_obj(tc, r, o), relabel_obj(tc, r, old), tc.cluster.installed_types) == valid_transition(o, old, tc.cluster.installed_types),
{
    lemma_valid_transition_ignores_metadata(tc, o, old, relabel_obj(tc, r, o).metadata, relabel_obj(tc, r, old).metadata);
}

}
