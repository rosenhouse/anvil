// A minimal DynReconciler over the shape, kept as the worked example of the
// trait: a reconciler that reads its triggering object back once and is done.
// It exists to show, in verified code, how a reconciler built from data (a
// registry entry and a cluster) states its model with
// Cluster::synced_reconcile_model and proves conformance with
// lemma_synced_reconcile_model_transition. Nothing runs it.
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::{api_method::*, api_resource::*, registry::*, synced_object::*};
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::spec::cluster::Cluster;
use crate::kubernetes_cluster::spec::controller::types::ReconcileModel;
use crate::kubernetes_cluster::spec::install_helpers::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::reconciler::spec::io::*;
use vstd::prelude::*;

verus! {

// The model.

pub enum ProbeStepView {
    Init,
    AfterGet,
    Done,
}

pub struct ProbeStateView {
    pub step: ProbeStepView,
}

impl Marshallable for ProbeStateView {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0
    {}
}

pub open spec fn probe_init() -> ProbeStateView {
    ProbeStateView { step: ProbeStepView::Init }
}

pub open spec fn probe_core(cr: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, state: ProbeStateView) -> (ProbeStateView, Option<RequestView<VoidEReqView>>) {
    match state.step {
        ProbeStepView::Init => (
            ProbeStateView { step: ProbeStepView::AfterGet },
            Some(RequestView::KRequest(APIRequest::GetRequest(GetRequest { key: cr.object_ref() }))),
        ),
        _ => (ProbeStateView { step: ProbeStepView::Done }, None),
    }
}

pub open spec fn probe_done(state: ProbeStateView) -> bool {
    state.step is Done
}

pub open spec fn probe_error(state: ProbeStateView) -> bool {
    false
}

// The reconcile model of the probe for a kind: data in, model out.
pub open spec fn probe_model(kind: Kind) -> ReconcileModel {
    Cluster::synced_reconcile_model::<ProbeStateView, VoidEReqView, VoidERespView>(
        kind,
        || probe_init(),
        |cr, resp_o, s| probe_core(cr, resp_o, s),
        |s| probe_done(s),
        |s| probe_error(s),
    )
}

// The exec reconciler.

pub enum ProbeStep {
    Init,
    AfterGet,
    Done,
}

impl View for ProbeStep {
    type V = ProbeStepView;

    open spec fn view(&self) -> ProbeStepView {
        match self {
            ProbeStep::Init => ProbeStepView::Init,
            ProbeStep::AfterGet => ProbeStepView::AfterGet,
            ProbeStep::Done => ProbeStepView::Done,
        }
    }
}

pub struct ProbeState {
    pub step: ProbeStep,
}

impl View for ProbeState {
    type V = ProbeStateView;

    open spec fn view(&self) -> ProbeStateView {
        ProbeStateView { step: self.step@ }
    }
}

// The data the reconciler is instantiated with: the kind it runs for and the
// cluster its objects live in.
pub struct ProbeReconciler {
    pub entry: RegistryEntry,
    pub cluster: ClusterId,
}

impl DynReconciler for ProbeReconciler {
    type S = ProbeState;
    type K = SyncedObject;
    type EReq = VoidEReq;
    type EResp = VoidEResp;

    open spec fn model(&self) -> ReconcileModel {
        probe_model(model_kind(self.entry@, self.cluster@))
    }

    fn reconcile_init_state(&self) -> (state: ProbeState) {
        proof {
            lemma_synced_reconcile_model_init_done_error::<ProbeStateView, VoidEReqView, VoidERespView>(
                self.model().kind, || probe_init(), |cr, resp_o, s| probe_core(cr, resp_o, s), |s| probe_done(s), |s| probe_error(s), probe_init(),
            );
        }
        ProbeState { step: ProbeStep::Init }
    }

    fn reconcile_core(&self, cr: &SyncedObject, resp_o: Option<Response<VoidEResp>>, state: ProbeState) -> (res: (ProbeState, Option<Request<VoidEReq>>)) {
        proof {
            synced_object_status_is_representable(*cr);
            lemma_synced_reconcile_model_transition::<ProbeStateView, VoidEReqView, VoidERespView>(
                self.model().kind, || probe_init(), |cr, resp_o, s| probe_core(cr, resp_o, s), |s| probe_done(s), |s| probe_error(s),
                cr@, resp_o.deep_view(), state@,
            );
        }
        // What the lemma gives, restated on the exec views: the postcondition
        // then follows from the branch below computing probe_core.
        assert((self.model().transition)(cr@.marshal(), marshal_response_view::<VoidERespView>(resp_o.deep_view()), state@.marshal())
            == (probe_core(cr@, resp_o.deep_view(), state@).0.marshal(), marshal_request_view::<VoidEReqView>(probe_core(cr@, resp_o.deep_view(), state@).1)));
        let res = match state.step {
            ProbeStep::Init => {
                let metadata = cr.metadata();
                let req = KubeAPIRequest::GetRequest(KubeGetRequest {
                    api_resource: cr.api_resource(),
                    name: metadata.name().unwrap(),
                    namespace: metadata.namespace().unwrap(),
                });
                (ProbeState { step: ProbeStep::AfterGet }, Some(Request::KRequest(req)))
            }
            _ => (ProbeState { step: ProbeStep::Done }, None),
        };
        // The exec branch computes the model's core, component by component.
        assert(res.0@ == probe_core(cr@, resp_o.deep_view(), state@).0);
        assert(res.1.deep_view() == probe_core(cr@, resp_o.deep_view(), state@).1);
        res
    }

    fn reconcile_done(&self, state: &ProbeState) -> (res: bool) {
        proof {
            lemma_synced_reconcile_model_init_done_error::<ProbeStateView, VoidEReqView, VoidERespView>(
                self.model().kind, || probe_init(), |cr, resp_o, s| probe_core(cr, resp_o, s), |s| probe_done(s), |s| probe_error(s), state@,
            );
        }
        match state.step {
            ProbeStep::Done => true,
            _ => false,
        }
    }

    fn reconcile_error(&self, state: &ProbeState) -> (res: bool) {
        proof {
            lemma_synced_reconcile_model_init_done_error::<ProbeStateView, VoidEReqView, VoidERespView>(
                self.model().kind, || probe_init(), |cr, resp_o, s| probe_core(cr, resp_o, s), |s| probe_done(s), |s| probe_error(s), state@,
            );
        }
        false
    }
}

}
