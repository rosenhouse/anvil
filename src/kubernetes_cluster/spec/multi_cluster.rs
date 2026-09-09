// A cluster model with one API server per side.
//
// The one-store model (Cluster) keeps every object of every kind in one store
// with one uid counter and one resource-version counter. MultiCluster splits
// the kinds between a family of API servers indexed by a side `S`, each with
// its own store and counters. Everything else (controllers, network, failures)
// is shared, as it is for a controller that runs in one cluster and talks to
// the others.
//
// Every step of MultiCluster is a step of Cluster taken on one of its
// projections (the shared state plus one store), with every other store
// unchanged. A request is handled by the API server of its kind; the garbage
// collector of a side looks only at that side's store; a reconcile is scheduled
// from the store of the controller's kind. Steps that touch no store are taken
// on the home projection.
//
// The refinement of MultiCluster into Cluster (kubernetes_cluster::proof::multi_cluster)
// is what lets a property proved on Cluster be read as a property of many
// clusters. It needs every object written to a store to be of a kind the cluster
// knows and to refer, through its owner references, only to kinds of its own
// side (object_ok below); controllers are held to that by a hypothesis of the
// refinement, the pod monkey by its precondition here.
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::*, api_server::types::*, builtin_controllers::types::*,
    cluster::*, controller::types::*, message::*, network::types::*,
};
use crate::state_machine::action::*;
use verus_temporal_logic::defs::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct MultiClusterState<S> {
    pub stores: Map<S, APIServerState>,
    pub controller_and_externals: Map<int, ControllerAndExternalState>,
    pub network: NetworkState,
    pub rpc_id_allocator: RPCIdAllocator,
    pub req_drop_enabled: bool,
    pub pod_monkey_enabled: bool,
}

impl<S> MultiClusterState<S> {
    pub open spec fn store(self, side: S) -> APIServerState {
        self.stores[side]
    }

    // The one-store view of this state that sees the store of `side`.
    pub open spec fn project(self, side: S) -> ClusterState {
        ClusterState {
            api_server: self.store(side),
            controller_and_externals: self.controller_and_externals,
            network: self.network,
            rpc_id_allocator: self.rpc_id_allocator,
            req_drop_enabled: self.req_drop_enabled,
            pod_monkey_enabled: self.pod_monkey_enabled,
        }
    }

    // This state with the projection on `side` replaced by `c`; every other store is kept.
    pub open spec fn with_projection(self, side: S, c: ClusterState) -> MultiClusterState<S> {
        MultiClusterState {
            stores: self.stores.insert(side, c.api_server),
            controller_and_externals: c.controller_and_externals,
            network: c.network,
            rpc_id_allocator: c.rpc_id_allocator,
            req_drop_enabled: c.req_drop_enabled,
            pod_monkey_enabled: c.pod_monkey_enabled,
        }
    }

    #[verifier(inline)]
    pub open spec fn in_flight(self) -> Multiset<Message> {
        self.network.in_flight
    }

    #[verifier(inline)]
    pub open spec fn resources_of(self, side: S) -> StoredState {
        self.store(side).resources
    }

    #[verifier(inline)]
    pub open spec fn ongoing_reconciles(self, controller_id: int) -> Map<ObjectRef, OngoingReconcile> {
        self.controller_and_externals[controller_id].controller.ongoing_reconciles
    }

    #[verifier(inline)]
    pub open spec fn scheduled_reconciles(self, controller_id: int) -> Map<ObjectRef, DynamicObjectView> {
        self.controller_and_externals[controller_id].controller.scheduled_reconciles
    }
}

// A one-store cluster whose kinds are split between the API servers of `sides`:
// a kind lives on the side `side_of` names. Steps that touch no store, and the
// pod monkey, act on the `home` side.
#[verifier::reject_recursive_types(S)]
pub struct MultiCluster<S> {
    pub cluster: Cluster,
    pub sides: Set<S>,
    pub home: S,
    pub side_of: spec_fn(Kind) -> S,
}

impl<S> MultiCluster<S> {
    pub open spec fn side_of_kind(self, kind: Kind) -> S {
        (self.side_of)(kind)
    }

    // The home side is one of the sides, and every kind lives on one of them:
    // the routing is total, so every request has an API server to handle it.
    pub open spec fn wf(self) -> bool {
        &&& self.sides.contains(self.home)
        &&& forall |kind: Kind| self.sides.contains(#[trigger] self.side_of_kind(kind))
    }

    // The API server a request is for.
    pub open spec fn side_of_request(self, req: APIRequest) -> S {
        self.side_of_kind(request_kind(req))
    }

    pub open spec fn side_of_msg(self, msg: Message) -> S {
        if msg.content is APIRequest { self.side_of_request(msg.content->APIRequest_0) } else { self.home }
    }

    // A one-store action, taken on the projection of `side`.
    pub open spec fn on_side<I>(self, side: S, action: Action<ClusterState, I, ()>) -> Action<MultiClusterState<S>, I, ()> {
        Action {
            precondition: |input: I, s: MultiClusterState<S>| (action.precondition)(input, s.project(side)),
            transition: |input: I, s: MultiClusterState<S>| {
                (s.with_projection(side, (action.transition)(input, s.project(side)).0), ())
            },
        }
    }

    // The API server of `side` handles one request for one of its kinds.
    pub open spec fn api_server_next(self, side: S) -> Action<MultiClusterState<S>, Option<Message>, ()> {
        let base = self.on_side(side, self.cluster.api_server_next());
        Action {
            precondition: |input: Option<Message>, s: MultiClusterState<S>| {
                &&& input is Some ==> self.side_of_msg(input->0) == side
                &&& (base.precondition)(input, s)
            },
            transition: base.transition,
        }
    }

    // The garbage collector of `side` looks at that side's store only.
    pub open spec fn builtin_controllers_next(self, side: S) -> Action<MultiClusterState<S>, (BuiltinControllerChoice, ObjectRef), ()> {
        let base = self.on_side(side, self.cluster.builtin_controllers_next());
        Action {
            precondition: |input: (BuiltinControllerChoice, ObjectRef), s: MultiClusterState<S>| {
                &&& self.side_of_kind(input.1.kind) == side
                &&& (base.precondition)(input, s)
            },
            transition: base.transition,
        }
    }

    // A reconcile is scheduled from the store of the object's kind.
    pub open spec fn schedule_controller_reconcile(self, side: S) -> Action<MultiClusterState<S>, (int, ObjectRef), ()> {
        let base = self.on_side(side, self.cluster.schedule_controller_reconcile());
        Action {
            precondition: |input: (int, ObjectRef), s: MultiClusterState<S>| {
                &&& self.side_of_kind(input.1.kind) == side
                &&& (base.precondition)(input, s)
            },
            transition: base.transition,
        }
    }

    // Steps that touch no store are taken on the home projection. (External
    // systems read the home store; a cluster whose controllers have external
    // systems is outside the refinement.)
    pub open spec fn controller_next(self) -> Action<MultiClusterState<S>, (int, Option<Message>, Option<ObjectRef>), ()> {
        self.on_side(self.home, self.cluster.controller_next())
    }

    pub open spec fn restart_controller(self) -> Action<MultiClusterState<S>, int, ()> {
        self.on_side(self.home, self.cluster.restart_controller())
    }

    pub open spec fn disable_crash(self) -> Action<MultiClusterState<S>, int, ()> {
        self.on_side(self.home, self.cluster.disable_crash())
    }

    pub open spec fn drop_req(self) -> Action<MultiClusterState<S>, (Message, APIError), ()> {
        self.on_side(self.home, self.cluster.drop_req())
    }

    pub open spec fn disable_req_drop(self) -> Action<MultiClusterState<S>, (), ()> {
        self.on_side(self.home, self.cluster.disable_req_drop())
    }

    // The pod monkey writes only named pods that carry no server-assigned field,
    // no owner reference and no annotation: such a pod reads the same in both
    // models. The refinement needs that because which of the monkey's actions
    // runs is a `choose` over the monkey's input, which the proof cannot equate
    // between a pod and its relabeling. The price is that the stale-write and
    // garbage-collection behaviours the one-store monkey exercises on pods are
    // not exercised here.
    pub open spec fn pod_monkey_next(self) -> Action<MultiClusterState<S>, PodView, ()> {
        let base = self.on_side(self.home, self.cluster.pod_monkey_next());
        Action {
            precondition: |input: PodView, s: MultiClusterState<S>| {
                &&& self.pod_ok(input)
                &&& (base.precondition)(input, s)
            },
            transition: base.transition,
        }
    }

    pub open spec fn disable_pod_monkey(self) -> Action<MultiClusterState<S>, (), ()> {
        self.on_side(self.home, self.cluster.disable_pod_monkey())
    }

    pub open spec fn external_next(self) -> Action<MultiClusterState<S>, (int, Option<Message>), ()> {
        self.on_side(self.home, self.cluster.external_next())
    }

    pub open spec fn stutter(self) -> Action<MultiClusterState<S>, (), ()> {
        self.on_side(self.home, self.cluster.stutter())
    }

    // A kind the cluster knows: built in, or an installed custom resource type.
    pub open spec fn kind_ok(self, kind: Kind) -> bool {
        kind is CustomResourceKind ==> self.cluster.installed_types.contains_key(kind->CustomResourceKind_0)
    }

    // An object that may be written to a store: of a known kind, with owner
    // references to kinds of its own side only.
    pub open spec fn object_ok(self, o: DynamicObjectView) -> bool {
        &&& self.kind_ok(o.kind)
        &&& o.metadata.owner_references is Some ==> forall |i: int| 0 <= i < o.metadata.owner_references->0.len()
            ==> self.side_of_kind((#[trigger] o.metadata.owner_references->0[i]).kind) == self.side_of_kind(o.kind)
    }

    // A request the refinement handles: the object it writes is object_ok and a
    // Create names it (a generated name is drawn per store, which the one-store
    // model cannot follow). A status write asks only for a known kind, because the
    // API server takes the stored object's metadata, not the request's; a Patch
    // asks nothing, because it reaches only the spec or the status and so cannot
    // add an owner reference.
    pub open spec fn request_ok(self, req: APIRequest) -> bool {
        match req {
            APIRequest::CreateRequest(r) => self.object_ok(r.obj) && r.obj.metadata.name is Some,
            APIRequest::UpdateRequest(r) => self.object_ok(r.obj),
            APIRequest::UpdateStatusRequest(r) => self.kind_ok(r.obj.kind),
            APIRequest::GetThenUpdateRequest(r) => self.object_ok(r.obj),
            APIRequest::GetThenUpdateStatusRequest(r) => self.kind_ok(r.obj.kind),
            _ => true,
        }
    }

    pub open spec fn pod_ok(self, pod: PodView) -> bool {
        &&& pod.metadata.name is Some
        &&& pod.metadata.uid is None
        &&& pod.metadata.resource_version is None
        &&& pod.metadata.owner_references is None
        &&& pod.metadata.annotations is None
    }

    // Every side has a store, each one initialized with its counters at zero;
    // the shared state is the one-store initial state.
    pub open spec fn init(self) -> StatePred<MultiClusterState<S>> {
        |s: MultiClusterState<S>| {
            &&& self.cluster.init()(s.project(self.home))
            &&& s.stores.dom() == self.sides
            &&& forall |side: S| #[trigger] self.sides.contains(side) ==> {
                &&& (api_server(self.cluster.installed_types).init)(s.stores[side])
                &&& s.stores[side].uid_counter == 0
                &&& s.stores[side].resource_version_counter == 0
            }
        }
    }

    pub open spec fn next_step(self, s: MultiClusterState<S>, s_prime: MultiClusterState<S>, side: S, step: Step) -> bool {
        &&& self.sides.contains(side)
        &&& match step {
            Step::APIServerStep(input) => self.api_server_next(side).forward(input)(s, s_prime),
            Step::BuiltinControllersStep(input) => self.builtin_controllers_next(side).forward(input)(s, s_prime),
            Step::ControllerStep(input) => self.controller_next().forward(input)(s, s_prime),
            Step::ScheduleControllerReconcileStep(input) => self.schedule_controller_reconcile(side).forward(input)(s, s_prime),
            Step::RestartControllerStep(input) => self.restart_controller().forward(input)(s, s_prime),
            Step::DisableCrashStep(input) => self.disable_crash().forward(input)(s, s_prime),
            Step::DropReqStep(input) => self.drop_req().forward(input)(s, s_prime),
            Step::DisableReqDropStep => self.disable_req_drop().forward(())(s, s_prime),
            Step::PodMonkeyStep(input) => self.pod_monkey_next().forward(input)(s, s_prime),
            Step::DisablePodMonkeyStep => self.disable_pod_monkey().forward(())(s, s_prime),
            Step::ExternalStep(input) => self.external_next().forward(input)(s, s_prime),
            Step::StutterStep => self.stutter().forward(())(s, s_prime),
        }
    }

    pub open spec fn next(self) -> ActionPred<MultiClusterState<S>> {
        |s: MultiClusterState<S>, s_prime: MultiClusterState<S>| exists |side: S, step: Step| self.next_step(s, s_prime, side, step)
    }
}

// The kind a request is addressed to.
pub open spec fn request_kind(req: APIRequest) -> Kind {
    match req {
        APIRequest::GetRequest(r) => r.key.kind,
        APIRequest::ListRequest(r) => r.kind,
        APIRequest::CreateRequest(r) => r.obj.kind,
        APIRequest::DeleteRequest(r) => r.key.kind,
        APIRequest::UpdateRequest(r) => r.obj.kind,
        APIRequest::UpdateStatusRequest(r) => r.obj.kind,
        APIRequest::GetThenDeleteRequest(r) => r.key.kind,
        APIRequest::GetThenUpdateRequest(r) => r.obj.kind,
        APIRequest::GetThenUpdateStatusRequest(r) => r.obj.kind,
        APIRequest::PatchRequest(r) => r.kind,
        APIRequest::PatchStatusRequest(r) => r.kind,
    }
}

}
