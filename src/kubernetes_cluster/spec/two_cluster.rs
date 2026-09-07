// A cluster model with two API servers.
//
// The one-store model (Cluster) keeps every object of every kind in one store
// with one uid counter and one resource-version counter. TwoCluster splits the
// kinds between two API servers, `Primary` and `Remote`, each with its own
// store and counters. Everything else (controllers, network, failures) is
// shared, as it is for a controller that runs in one cluster and talks to
// another.
//
// Every step of TwoCluster is a step of Cluster taken on one of its two
// projections (the shared state plus one of the two stores), with the other
// store unchanged. A request is handled by the API server of its kind; the
// garbage collector of a side looks only at that side's store; a reconcile is
// scheduled from the store of the controller's kind. Steps that touch no store
// are taken on the primary projection.
//
// The refinement of TwoCluster into Cluster (kubernetes_cluster::proof::two_cluster)
// is what lets a property proved on Cluster be read as a property of two
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

pub enum Side {
    Primary,
    Remote,
}

impl Side {
    pub open spec fn other(self) -> Side {
        match self {
            Side::Primary => Side::Remote,
            Side::Remote => Side::Primary,
        }
    }
}

pub struct TwoClusterState {
    pub primary: APIServerState,
    pub remote: APIServerState,
    pub controller_and_externals: Map<int, ControllerAndExternalState>,
    pub network: NetworkState,
    pub rpc_id_allocator: RPCIdAllocator,
    pub req_drop_enabled: bool,
    pub pod_monkey_enabled: bool,
}

impl TwoClusterState {
    pub open spec fn store(self, side: Side) -> APIServerState {
        match side {
            Side::Primary => self.primary,
            Side::Remote => self.remote,
        }
    }

    // The one-store view of this state that sees the store of `side`.
    pub open spec fn project(self, side: Side) -> ClusterState {
        ClusterState {
            api_server: self.store(side),
            controller_and_externals: self.controller_and_externals,
            network: self.network,
            rpc_id_allocator: self.rpc_id_allocator,
            req_drop_enabled: self.req_drop_enabled,
            pod_monkey_enabled: self.pod_monkey_enabled,
        }
    }

    // This state with the projection on `side` replaced by `c`; the other store is kept.
    pub open spec fn with_projection(self, side: Side, c: ClusterState) -> TwoClusterState {
        TwoClusterState {
            primary: if side is Primary { c.api_server } else { self.primary },
            remote: if side is Remote { c.api_server } else { self.remote },
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
    pub open spec fn resources_of(self, side: Side) -> StoredState {
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

// A one-store cluster whose kinds are split between two API servers: the kinds in
// `remote_kinds` live in the remote one, every other kind in the primary one.
pub struct TwoCluster {
    pub cluster: Cluster,
    pub remote_kinds: Set<Kind>,
}

impl TwoCluster {
    pub open spec fn side_of_kind(self, kind: Kind) -> Side {
        if self.remote_kinds.contains(kind) { Side::Remote } else { Side::Primary }
    }

    // The API server a request is for.
    pub open spec fn side_of_request(self, req: APIRequest) -> Side {
        match req {
            APIRequest::GetRequest(r) => self.side_of_kind(r.key.kind),
            APIRequest::ListRequest(r) => self.side_of_kind(r.kind),
            APIRequest::CreateRequest(r) => self.side_of_kind(r.obj.kind),
            APIRequest::DeleteRequest(r) => self.side_of_kind(r.key.kind),
            APIRequest::UpdateRequest(r) => self.side_of_kind(r.obj.kind),
            APIRequest::UpdateStatusRequest(r) => self.side_of_kind(r.obj.kind),
            APIRequest::GetThenDeleteRequest(r) => self.side_of_kind(r.key.kind),
            APIRequest::GetThenUpdateRequest(r) => self.side_of_kind(r.obj.kind),
            APIRequest::GetThenUpdateStatusRequest(r) => self.side_of_kind(r.obj.kind),
            APIRequest::PatchRequest(r) => self.side_of_kind(r.kind),
            APIRequest::PatchStatusRequest(r) => self.side_of_kind(r.kind),
        }
    }

    pub open spec fn side_of_msg(self, msg: Message) -> Side {
        if msg.content is APIRequest { self.side_of_request(msg.content->APIRequest_0) } else { Side::Primary }
    }

    // A one-store action, taken on the projection of `side`.
    pub open spec fn on_side<I>(self, side: Side, action: Action<ClusterState, I, ()>) -> Action<TwoClusterState, I, ()> {
        Action {
            precondition: |input: I, s: TwoClusterState| (action.precondition)(input, s.project(side)),
            transition: |input: I, s: TwoClusterState| {
                (s.with_projection(side, (action.transition)(input, s.project(side)).0), ())
            },
        }
    }

    // The API server of `side` handles one request for one of its kinds.
    pub open spec fn api_server_next(self, side: Side) -> Action<TwoClusterState, Option<Message>, ()> {
        let base = self.on_side(side, self.cluster.api_server_next());
        Action {
            precondition: |input: Option<Message>, s: TwoClusterState| {
                &&& input is Some ==> self.side_of_msg(input->0) == side
                &&& (base.precondition)(input, s)
            },
            transition: base.transition,
        }
    }

    // The garbage collector of `side` looks at that side's store only.
    pub open spec fn builtin_controllers_next(self, side: Side) -> Action<TwoClusterState, (BuiltinControllerChoice, ObjectRef), ()> {
        let base = self.on_side(side, self.cluster.builtin_controllers_next());
        Action {
            precondition: |input: (BuiltinControllerChoice, ObjectRef), s: TwoClusterState| {
                &&& self.side_of_kind(input.1.kind) == side
                &&& (base.precondition)(input, s)
            },
            transition: base.transition,
        }
    }

    // A reconcile is scheduled from the store of the object's kind.
    pub open spec fn schedule_controller_reconcile(self, side: Side) -> Action<TwoClusterState, (int, ObjectRef), ()> {
        let base = self.on_side(side, self.cluster.schedule_controller_reconcile());
        Action {
            precondition: |input: (int, ObjectRef), s: TwoClusterState| {
                &&& self.side_of_kind(input.1.kind) == side
                &&& (base.precondition)(input, s)
            },
            transition: base.transition,
        }
    }

    // Steps that touch no store are taken on the primary projection. (External
    // systems read the primary store; a cluster whose controllers have external
    // systems is outside the refinement.)
    pub open spec fn controller_next(self) -> Action<TwoClusterState, (int, Option<Message>, Option<ObjectRef>), ()> {
        self.on_side(Side::Primary, self.cluster.controller_next())
    }

    pub open spec fn restart_controller(self) -> Action<TwoClusterState, int, ()> {
        self.on_side(Side::Primary, self.cluster.restart_controller())
    }

    pub open spec fn disable_crash(self) -> Action<TwoClusterState, int, ()> {
        self.on_side(Side::Primary, self.cluster.disable_crash())
    }

    pub open spec fn drop_req(self) -> Action<TwoClusterState, (Message, APIError), ()> {
        self.on_side(Side::Primary, self.cluster.drop_req())
    }

    pub open spec fn disable_req_drop(self) -> Action<TwoClusterState, (), ()> {
        self.on_side(Side::Primary, self.cluster.disable_req_drop())
    }

    // The pod monkey writes only named pods that carry no server-assigned field
    // and no owner reference: such a pod reads the same in both models. (A pod
    // with an owner reference to a kind of the other side would be collected by
    // the garbage collector of its own side, which the one-store model cannot
    // express; and which of the monkey's actions runs is chosen from the pod, so
    // the pod must not change under the abstraction.)
    pub open spec fn pod_monkey_next(self) -> Action<TwoClusterState, PodView, ()> {
        let base = self.on_side(Side::Primary, self.cluster.pod_monkey_next());
        Action {
            precondition: |input: PodView, s: TwoClusterState| {
                &&& self.pod_ok(input)
                &&& (base.precondition)(input, s)
            },
            transition: base.transition,
        }
    }

    pub open spec fn disable_pod_monkey(self) -> Action<TwoClusterState, (), ()> {
        self.on_side(Side::Primary, self.cluster.disable_pod_monkey())
    }

    pub open spec fn external_next(self) -> Action<TwoClusterState, (int, Option<Message>), ()> {
        self.on_side(Side::Primary, self.cluster.external_next())
    }

    pub open spec fn stutter(self) -> Action<TwoClusterState, (), ()> {
        self.on_side(Side::Primary, self.cluster.stutter())
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
    // model cannot follow).
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

    pub open spec fn init(self) -> StatePred<TwoClusterState> {
        |s: TwoClusterState| {
            &&& self.cluster.init()(s.project(Side::Primary))
            &&& (api_server(self.cluster.installed_types).init)(s.remote)
            &&& s.primary.uid_counter == 0
            &&& s.primary.resource_version_counter == 0
            &&& s.remote.uid_counter == 0
            &&& s.remote.resource_version_counter == 0
        }
    }

    pub open spec fn next_step(self, s: TwoClusterState, s_prime: TwoClusterState, side: Side, step: Step) -> bool {
        match step {
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

    pub open spec fn next(self) -> ActionPred<TwoClusterState> {
        |s: TwoClusterState, s_prime: TwoClusterState| exists |side: Side, step: Step| self.next_step(s, s_prime, side, step)
    }
}

}
