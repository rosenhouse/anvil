// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use vstd::prelude::*;

verus! {

// ClusterId names the API server an exec value belongs to or is bound for.
//
// A controller may talk to more than one cluster (e.g. a controller running in
// one cluster that mirrors objects into another). The verified model has a single
// logical store keyed by (kind, namespace, name), so objects of the same real kind
// living in different clusters must get different *model* kinds. The tag below is
// what the trusted wrappers use to make that distinction: an ApiResource or
// DynamicObject tagged Remote maps to the remote cluster's model kind, and the shim
// layer routes requests to the matching kube client by this tag. Primary is the
// default and denotes the cluster the controller itself runs against; every
// existing single-cluster controller only ever sees Primary.
pub enum ClusterId {
    Primary,
    Remote,
}

impl std::marker::Copy for ClusterId {}

#[verifier(external)]
impl std::fmt::Debug for ClusterId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClusterId::Primary => write!(f, "Primary"),
            ClusterId::Remote => write!(f, "Remote"),
        }
    }
}

impl std::clone::Clone for ClusterId {
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

impl ClusterId {
    pub fn eq(&self, other: &ClusterId) -> (b: bool)
        ensures b == (self == other),
    {
        match (self, other) {
            (ClusterId::Primary, ClusterId::Primary) => true,
            (ClusterId::Remote, ClusterId::Remote) => true,
            _ => false,
        }
    }

    pub fn is_remote(&self) -> (b: bool)
        ensures b == (self is Remote),
    {
        match self {
            ClusterId::Remote => true,
            _ => false,
        }
    }
}

// ApiResource is used for creating API handles for DynamicObject.
//
// This definition is a wrapper of ApiResource defined at
// https://github.com/kube-rs/kube/blob/main/kube-core/src/discovery.rs,
// plus the ClusterId the resource is bound for (see ClusterId above).
// It is supposed to be used in exec controller code.

#[verifier(external_body)]
pub struct ApiResource {
    inner: kube::api::ApiResource,
    cluster: ClusterId,
}

implement_view_trait!(ApiResource, ApiResourceView);
implement_deep_view_trait!(ApiResource, ApiResourceView);

#[verifier(external)]
impl ResourceWrapper<kube::api::ApiResource> for ApiResource {
    // from_kube binds the resource to the primary cluster.
    fn from_kube(inner: kube::api::ApiResource) -> ApiResource {
        ApiResource { inner: inner, cluster: ClusterId::Primary }
    }

    fn into_kube(self) -> kube::api::ApiResource {
        self.inner
    }

    fn as_kube_ref(&self) -> &kube::api::ApiResource {
        &self.inner
    }
}

#[verifier(external)]
impl ApiResource {
    // from_kube_in binds the resource to the given cluster. Only the typed
    // object wrappers (implement_object_wrapper_type) should call this, since
    // they are what tie the tag to the view's kind.
    pub fn from_kube_in(inner: kube::api::ApiResource, cluster: ClusterId) -> ApiResource {
        ApiResource { inner: inner, cluster: cluster }
    }
}

impl ApiResource {
    // cluster is read by the shim layer to pick the kube client. It carries no
    // spec-level meaning: the tag's effect on the model is entirely through the
    // typed wrappers' postconditions on kind.
    #[verifier(external_body)]
    pub fn cluster(&self) -> ClusterId {
        self.cluster
    }
}

}
