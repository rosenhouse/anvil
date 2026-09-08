use crate::kubernetes_api_objects::spec::resource::{CustomResourceView, Marshallable, ResourceView};
use crate::kubernetes_api_objects::spec::synced_object::DynamicObjectLike;
use crate::kubernetes_cluster::spec::controller::types::ReconcileModel;
use crate::kubernetes_cluster::spec::install_helpers::*;
use crate::reconciler::exec::io::*;
use crate::reconciler::spec::reconciler::Reconciler as ModelReconciler;
use vstd::prelude::*;

verus! {

// Reconciler is used to implement the custom controller as a state machine
// that interacts with Kubernetes API server via the shim_layer::controller_runtime.
pub trait Reconciler
where
    Self::S: View,
    Self::K: View,
    <Self::K as View>::V: CustomResourceView,
    Self::EReq: View,
    Self::EResp: View,
    // The ModelReconciler is built using the view of S, K, EReq and EResp.
    // This is a workaround of missing type equality constraint in Rust.
    Self::M: ModelReconciler<<Self::S as View>::V, <Self::K as View>::V, <Self::EReq as View>::V, <Self::EResp as View>::V>,
{
    // S: type of the reconciler state of the reconciler.
    type S;
    // K: type of the custom resource.
    type K;
    // EReq: type of request the controller sends to the external systems (if any).
    type EReq;
    // EResp: type of response the controller receives from the external systems (if any).
    type EResp;
    // M: type of the ModelReconciler that this implementation should conform to.
    type M;

    // reconcile_init_state returns the initial local state that the reconciler starts
    // its reconcile function with.
    // It conforms to the model's reconcile_init_state.
    fn reconcile_init_state() -> (state: Self::S)
        ensures state@ == Self::M::reconcile_init_state();

    // reconcile_core describes the logic of reconcile function and is the key logic we want to verify.
    // Each reconcile_core should take the local state and a response of the previous request (if any) as input
    // and outputs the next local state and the request to send to API server (if any).
    // It conforms to the model's reconcile_core.
    fn reconcile_core(cr: &Self::K, resp_o: Option<Response<Self::EResp>>, state: Self::S) -> (res: (Self::S, Option<Request<Self::EReq>>))
        requires cr@.metadata().well_formed_for_namespaced() && cr@.state_validation(),
        ensures (res.0@, res.1.deep_view()) == Self::M::reconcile_core(cr@, resp_o.deep_view(), state@);

    // reconcile_done is used to tell the controller_runtime whether this reconcile round is done.
    // If it is true, controller_runtime will requeue the reconcile.
    // It conforms to the model's reconcile_done.
    fn reconcile_done(state: &Self::S) -> (res: bool)
        ensures res == Self::M::reconcile_done(state@);

    // reconcile_error is used to tell the controller_runtime whether this reconcile round returns with error.
    // If it is true, controller_runtime will requeue the reconcile with a typically shorter waiting time.
    // It conforms to the model's reconciler_error.
    fn reconcile_error(state: &Self::S) -> (res: bool)
        ensures res == Self::M::reconcile_error(state@);
}

// DynReconciler is a reconciler whose behaviour is a function of data it holds
// (a kind, a binding, a registry entry) rather than of its type, so that one
// implementation serves every kind it is instantiated for at boot. Its methods
// take &self, and its model is a ReconcileModel value computed from the same
// data (Cluster::synced_reconcile_model builds one from spec functions over the
// shape). The postconditions relate each method to the model's closure applied
// to the marshalled views, which is how the cluster model runs the closures;
// lemma_synced_reconcile_model_transition and
// lemma_synced_reconcile_model_init_done_error reduce them to the typed spec
// functions the model was built from.
//
// The shim calls reconcile_core on an object it fetched from the cluster and
// wrapped for the kind the controller was started for, which is what the
// precondition on the kind trusts (shim_layer::controller_runtime::
// reconcile_dyn_with).
//
// reconcile_core requires only that the object is well formed for a namespaced
// kind and that its kind is the one the reconciler was built for. It does not
// require state_validation, which the static Reconciler above does: a dyn
// reconciler is instantiated at boot for a kind whose spec it has never seen, so
// there is no typed state_validation to require -- what validates a spec is the
// CRD's own schema, a parameter of the shape's installed type
// (Cluster::synced_installed_type). A dyn reconciler must work for any spec, and
// its proof may not lean on the spec being anything in particular.
pub trait DynReconciler
where
    Self::S: View,
    <Self::S as View>::V: Marshallable,
    Self::K: View,
    <Self::K as View>::V: DynamicObjectLike,
    Self::EReq: View,
    <Self::EReq as View>::V: Marshallable,
    Self::EResp: View,
    <Self::EResp as View>::V: Marshallable,
{
    // S: type of the reconciler state of the reconciler.
    type S;
    // K: type of the triggering object (SyncedObject for a kind of the shape).
    type K;
    // EReq: type of request the controller sends to the external systems (if any).
    type EReq;
    // EResp: type of response the controller receives from the external systems (if any).
    type EResp;

    // The model this reconciler conforms to.
    spec fn model(&self) -> ReconcileModel;

    fn reconcile_init_state(&self) -> (state: Self::S)
        ensures state@.marshal() == (self.model().init)();

    fn reconcile_core(&self, cr: &Self::K, resp_o: Option<Response<Self::EResp>>, state: Self::S) -> (res: (Self::S, Option<Request<Self::EReq>>))
        requires
            cr@.metadata().well_formed_for_namespaced(),
            cr@.kind() == self.model().kind,
        ensures
            (self.model().transition)(cr@.marshal(), marshal_response_view::<<Self::EResp as View>::V>(resp_o.deep_view()), state@.marshal())
                == (res.0@.marshal(), marshal_request_view::<<Self::EReq as View>::V>(res.1.deep_view()));

    fn reconcile_done(&self, state: &Self::S) -> (res: bool)
        ensures res == (self.model().done)(state@.marshal());

    fn reconcile_error(&self, state: &Self::S) -> (res: bool)
        ensures res == (self.model().error)(state@.marshal());
}

}
