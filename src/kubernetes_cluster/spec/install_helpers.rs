// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::spec::{
    api_server::types::*, cluster::Cluster, controller::types::*,
};
use crate::reconciler::spec::{io::*, reconciler::*};
use vstd::prelude::*;

verus! {

// The marshalled forms of a reconciler's requests and responses, as a
// ReconcileModel exchanges them with the cluster model. installed_reconcile_model
// below inlines the same maps for the type-level reconcilers; these are the
// named versions the data-driven models and their conformance statements use.
pub open spec fn marshal_request_view<EReq: Marshallable>(req_o: Option<RequestView<EReq>>) -> Option<RequestContent> {
    match req_o {
        None => None,
        Some(req) => Some(match req {
            RequestView::<EReq>::KRequest(api_req) => RequestContent::KubernetesRequest(api_req),
            RequestView::<EReq>::ExternalRequest(ext_req) => RequestContent::ExternalRequest(ext_req.marshal()),
        })
    }
}

pub open spec fn unmarshal_response_content<EResp: Marshallable>(resp_o: Option<ResponseContent>) -> Option<ResponseView<EResp>> {
    match resp_o {
        None => None,
        Some(resp) => Some(match resp {
            ResponseContent::KubernetesResponse(api_resp) => ResponseView::<EResp>::KResponse(api_resp),
            ResponseContent::ExternalResponse(ext_resp) => ResponseView::<EResp>::ExternalResponse(EResp::unmarshal(ext_resp)->Ok_0),
        })
    }
}

pub open spec fn marshal_response_view<EResp: Marshallable>(resp_o: Option<ResponseView<EResp>>) -> Option<ResponseContent> {
    match resp_o {
        None => None,
        Some(resp) => Some(match resp {
            ResponseView::<EResp>::KResponse(api_resp) => ResponseContent::KubernetesResponse(api_resp),
            ResponseView::<EResp>::ExternalResponse(ext_resp) => ResponseContent::ExternalResponse(ext_resp.marshal()),
        })
    }
}

pub proof fn lemma_unmarshal_response_of_marshal<EResp: Marshallable>(resp_o: Option<ResponseView<EResp>>)
    ensures unmarshal_response_content::<EResp>(marshal_response_view::<EResp>(resp_o)) == resp_o,
{
    EResp::marshal_preserves_integrity();
}

impl Cluster {

pub open spec fn installed_type<T: CustomResourceView>() -> InstalledType {
    InstalledType {
        unmarshallable_spec: |v: Value| T::unmarshal_spec(v) is Ok,
        unmarshallable_status: |v: Value| T::unmarshal_status(v) is Ok,
        valid_object: |obj: DynamicObjectView| T::unmarshal(obj)->Ok_0.state_validation(),
        valid_transition: |obj, old_obj: DynamicObjectView| T::unmarshal(obj)->Ok_0.transition_validation(T::unmarshal(old_obj)->Ok_0),
        marshalled_default_status: || T::marshal_status(T::default().status()),
    }
}

pub open spec fn type_is_installed_in_cluster<T: CustomResourceView>(self) -> bool {
    let string = T::kind()->CustomResourceKind_0;
    &&& self.installed_types.contains_key(string)
    &&& self.installed_types[string] == Self::installed_type::<T>()
}

pub open spec fn installed_reconcile_model<R, S, K, EReq, EResp>() -> ReconcileModel
    where
        R: Reconciler<S, K, EReq, EResp>,
        K: CustomResourceView,
        S: Marshallable,
        EReq: Marshallable,
        EResp: Marshallable,
{
    ReconcileModel {
        kind: K::kind(),
        init: || R::reconcile_init_state().marshal(),
        transition: |obj, resp_o, s| {
            let obj_um = K::unmarshal(obj)->Ok_0;
            let resp_o_um = match resp_o {
                None => None,
                Some(resp) => Some(match resp {
                    ResponseContent::KubernetesResponse(api_resp) => ResponseView::<EResp>::KResponse(api_resp),
                    ResponseContent::ExternalResponse(ext_resp) => ResponseView::<EResp>::ExternalResponse(EResp::unmarshal(ext_resp)->Ok_0),
                })
            };
            let s_um = S::unmarshal(s)->Ok_0;
            let (s_prime_um, req_o_um) = R::reconcile_core(obj_um, resp_o_um, s_um);
            (s_prime_um.marshal(), match req_o_um {
                None => None,
                Some(req) => Some(match req {
                    RequestView::<EReq>::KRequest(api_req) => RequestContent::KubernetesRequest(api_req),
                    RequestView::<EReq>::ExternalRequest(ext_req) => RequestContent::ExternalRequest(ext_req.marshal()),
                })
            })
        },
        done: |s| R::reconcile_done(S::unmarshal(s)->Ok_0),
        error: |s| R::reconcile_error(S::unmarshal(s)->Ok_0),
    }
}

// A reconcile model built from data: the kind it is triggered by and its four
// spec functions over the typed state. The state, requests and responses cross
// to the cluster model marshalled, as in installed_reconcile_model; the
// triggering object is handed to `core` as the stored DynamicObjectView.
pub open spec fn reconcile_model_from<S, EReq, EResp>(
    kind: Kind,
    init: spec_fn() -> S,
    core: spec_fn(DynamicObjectView, Option<ResponseView<EResp>>, S) -> (S, Option<RequestView<EReq>>),
    done: spec_fn(S) -> bool,
    error: spec_fn(S) -> bool,
) -> ReconcileModel
    where
        S: Marshallable,
        EReq: Marshallable,
        EResp: Marshallable,
{
    ReconcileModel {
        kind: kind,
        init: || init().marshal(),
        transition: |obj, resp_o, s| {
            let (s_prime, req_o) = core(obj, unmarshal_response_content::<EResp>(resp_o), S::unmarshal(s)->Ok_0);
            (s_prime.marshal(), marshal_request_view::<EReq>(req_o))
        },
        done: |s| done(S::unmarshal(s)->Ok_0),
        error: |s| error(S::unmarshal(s)->Ok_0),
    }
}

// The reconcile model of a reconciler written over the shape
// (spec::synced_object::SyncedObjectView) of a kind given as data: `core` sees
// the triggering object unmarshalled at `kind`.
pub open spec fn synced_reconcile_model<S, EReq, EResp>(
    kind: Kind,
    init: spec_fn() -> S,
    core: spec_fn(SyncedObjectView, Option<ResponseView<EResp>>, S) -> (S, Option<RequestView<EReq>>),
    done: spec_fn(S) -> bool,
    error: spec_fn(S) -> bool,
) -> ReconcileModel
    where
        S: Marshallable,
        EReq: Marshallable,
        EResp: Marshallable,
{
    Self::reconcile_model_from::<S, EReq, EResp>(
        kind,
        init,
        |obj, resp_o, s| core(unmarshal(kind, obj)->Ok_0, resp_o, s),
        done,
        error,
    )
}

// The installed type of a kind of the shape (design, section 2.3): a function of
// the CRD's schema `spec_ok` and of the kind's cluster selector, whose
// immutability rule is the transition validation.
pub open spec fn synced_installed_type(spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector) -> InstalledType {
    InstalledType {
        unmarshallable_spec: |v: Value| true,
        unmarshallable_status: |v: Value| unmarshal_status(v) is Ok,
        valid_object: |obj: DynamicObjectView| spec_ok(obj.spec),
        // The cluster an object selects is immutable. A field selector needs a
        // rule for that; a name selector does not, because an object keeps the
        // name it is stored under -- Kubernetes has no rename -- so the real API
        // server enforces it with no rule at all
        // (lemma_api_server_step_preserves_cluster_of reads the name off the key).
        // Stating it as a rule anyway would make the validation read metadata,
        // which the multi-store refinement forbids.
        valid_transition: |obj, old_obj: DynamicObjectView|
            selector is Field ==> cluster_of_dynamic(selector, obj) == cluster_of_dynamic(selector, old_obj),
        marshalled_default_status: || marshal_status(None),
    }
}

}

// What synced_reconcile_model's transition computes on the marshalled forms of a
// typed input: the statement a conformance proof of a DynReconciler over the
// shape reduces to (reconciler::exec::reconciler::DynReconciler).
pub proof fn lemma_synced_reconcile_model_transition<S, EReq, EResp>(
    kind: Kind,
    init: spec_fn() -> S,
    core: spec_fn(SyncedObjectView, Option<ResponseView<EResp>>, S) -> (S, Option<RequestView<EReq>>),
    done: spec_fn(S) -> bool,
    error: spec_fn(S) -> bool,
    cr: SyncedObjectView,
    resp_o: Option<ResponseView<EResp>>,
    s: S,
)
    where
        S: Marshallable,
        EReq: Marshallable,
        EResp: Marshallable,
    requires
        cr.kind == kind,
        // Only a representable status survives the round trip through the
        // marshalled form, so only for such a cr do the two agree.
        status_ok(cr.status),
    ensures
        (Cluster::synced_reconcile_model::<S, EReq, EResp>(kind, init, core, done, error).transition)(marshal(cr), marshal_response_view::<EResp>(resp_o), s.marshal())
            == (core(cr, resp_o, s).0.marshal(), marshal_request_view::<EReq>(core(cr, resp_o, s).1)),
{
    unmarshal_of_marshal();
    S::marshal_preserves_integrity();
    lemma_unmarshal_response_of_marshal::<EResp>(resp_o);
    assert(unmarshal(kind, marshal(cr)) == Ok::<SyncedObjectView, UnmarshalError>(cr));
    assert(S::unmarshal(s.marshal()) == Ok::<S, UnmarshalError>(s));
}

// The two other closures of a synced model, on the marshalled state.
pub proof fn lemma_synced_reconcile_model_init_done_error<S, EReq, EResp>(
    kind: Kind,
    init: spec_fn() -> S,
    core: spec_fn(SyncedObjectView, Option<ResponseView<EResp>>, S) -> (S, Option<RequestView<EReq>>),
    done: spec_fn(S) -> bool,
    error: spec_fn(S) -> bool,
    s: S,
)
    where
        S: Marshallable,
        EReq: Marshallable,
        EResp: Marshallable,
    ensures
        (Cluster::synced_reconcile_model::<S, EReq, EResp>(kind, init, core, done, error).init)() == init().marshal(),
        (Cluster::synced_reconcile_model::<S, EReq, EResp>(kind, init, core, done, error).done)(s.marshal()) == done(s),
        (Cluster::synced_reconcile_model::<S, EReq, EResp>(kind, init, core, done, error).error)(s.marshal()) == error(s),
{
    S::marshal_preserves_integrity();
    assert(S::unmarshal(s.marshal()) == Ok::<S, UnmarshalError>(s));
}

}
