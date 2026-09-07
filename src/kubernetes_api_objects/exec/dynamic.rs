// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::{api_resource::*, object_meta::*, resource::*};
use crate::kubernetes_api_objects::spec::dynamic::*;
use vstd::prelude::*;

verus! {

// DynamicObject is mainly used to pass requests/response between reconcile_core and the shim layer.
// We use DynamicObject in KubeAPIRequest and KubeAPIResponse so that they can carry the requests and responses
// for all kinds of Kubernetes resource objects without exhaustive pattern matching.
//
// A DynamicObject carries the ClusterId it came from or is bound for; see
// api_resource::ClusterId.

#[verifier(external_body)]
pub struct DynamicObject {
    inner: kube::api::DynamicObject,
    cluster: ClusterId,
}

implement_view_trait!(DynamicObject, DynamicObjectView);
implement_deep_view_trait!(DynamicObject, DynamicObjectView);

#[verifier(external)]
impl ResourceWrapper<kube::api::DynamicObject> for DynamicObject {
    // from_kube tags the object as belonging to the primary cluster.
    fn from_kube(inner: kube::api::DynamicObject) -> DynamicObject {
        DynamicObject { inner: inner, cluster: ClusterId::Primary }
    }

    fn into_kube(self) -> kube::api::DynamicObject {
        self.inner
    }

    fn as_kube_ref(&self) -> &kube::api::DynamicObject {
        &self.inner
    }
}

impl std::clone::Clone for DynamicObject {
    #[verifier(external_body)]
    fn clone(&self) -> (res: DynamicObject)
        ensures res@ == self@
    {
        DynamicObject { inner: self.inner.clone(), cluster: self.cluster }
    }
}

impl DynamicObject {
    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    // cluster has no spec-level meaning on its own; see ApiResource::cluster.
    #[verifier(external_body)]
    pub fn cluster(&self) -> ClusterId {
        self.cluster
    }
}

#[verifier(external)]
impl DynamicObject {
    // from_kube_in tags the object with the given cluster. Called by the shim
    // layer (with the cluster of the client that returned the object) and by the
    // typed wrappers' marshal.
    pub fn from_kube_in(inner: kube::api::DynamicObject, cluster: ClusterId) -> DynamicObject {
        DynamicObject { inner: inner, cluster: cluster }
    }

    // as_kube_mut_ref is for the executable API server model's setters
    // (executable_model::common), not for controller code.
    pub fn as_kube_mut_ref(&mut self) -> &mut kube::api::DynamicObject {
        &mut self.inner
    }
}

#[verifier(external)]
impl std::fmt::Debug for DynamicObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.inner.fmt(f) }
}

}
