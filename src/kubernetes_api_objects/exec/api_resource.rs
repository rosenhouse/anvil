// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

// The cluster a wrapper type is bound to, as a type-level fact. The shim derives
// the cluster of a controller's primary watch from the controller's wrapper type,
// so the triggering object always comes from the cluster the wrapper's view kind
// stands for.
pub trait ClusterBound {
    fn cluster() -> ClusterId;
}

verus! {

// ClusterRef names a remote cluster by its binding: the namespace of the outer
// cluster the binding lives in and the cluster's name there. The shim keeps one
// pair of clients per bound ClusterRef and looks requests up by it.
pub struct ClusterRef {
    pub namespace: String,
    pub name: String,
}

impl View for ClusterRef {
    type V = ClusterRefView;

    open spec fn view(&self) -> ClusterRefView {
        ClusterRefView { namespace: self.namespace@, name: self.name@ }
    }
}

impl ClusterRef {
    pub fn new(namespace: String, name: String) -> (r: ClusterRef)
        ensures r@ == (ClusterRefView { namespace: namespace@, name: name@ }),
    {
        ClusterRef { namespace: namespace, name: name }
    }

    pub fn eq(&self, other: &ClusterRef) -> (b: bool)
        ensures b == (self@ == other@),
    {
        let b = string_equal(&self.namespace, other.namespace.as_str())
            && string_equal(&self.name, other.name.as_str());
        proof {
            if b {
                assert(self@ == other@);
            } else {
                assert(self@ != other@);
            }
        }
        b
    }
}

impl std::clone::Clone for ClusterRef {
    fn clone(&self) -> (r: Self)
        ensures r@ == self@,
    {
        ClusterRef { namespace: self.namespace.clone(), name: self.name.clone() }
    }
}

// ClusterId names the API server an exec value came from or is bound for. The
// model has one store keyed by (kind, namespace, name), so an object of a remote
// cluster gets a distinct view kind (for example `widget@inner`, or the
// registry's `widgets.anvil.dev@<namespace>/<name>`); the shim routes requests
// by this tag. Existing single-cluster controllers see only Primary.
pub enum ClusterId {
    Primary,
    Remote(ClusterRef),
}

impl View for ClusterId {
    type V = ClusterIdView;

    open spec fn view(&self) -> ClusterIdView {
        match self {
            ClusterId::Primary => ClusterIdView::Primary,
            ClusterId::Remote(r) => ClusterIdView::Remote(r@),
        }
    }
}

impl std::clone::Clone for ClusterId {
    fn clone(&self) -> (r: Self)
        ensures r@ == self@,
    {
        match self {
            ClusterId::Primary => ClusterId::Primary,
            ClusterId::Remote(r) => ClusterId::Remote(r.clone()),
        }
    }
}

impl ClusterId {
    pub fn primary() -> (c: ClusterId)
        ensures c@ == ClusterIdView::Primary,
    {
        ClusterId::Primary
    }

    pub fn remote(namespace: String, name: String) -> (c: ClusterId)
        ensures c@ == ClusterIdView::Remote(ClusterRefView { namespace: namespace@, name: name@ }),
    {
        ClusterId::Remote(ClusterRef::new(namespace, name))
    }

    pub fn eq(&self, other: &ClusterId) -> (b: bool)
        ensures b == (self@ == other@),
    {
        match (self, other) {
            (ClusterId::Primary, ClusterId::Primary) => true,
            (ClusterId::Remote(r1), ClusterId::Remote(r2)) => r1.eq(r2),
            _ => false,
        }
    }

    pub fn is_remote(&self) -> (b: bool)
        ensures b == (self@ is Remote),
    {
        match self {
            ClusterId::Remote(_) => true,
            _ => false,
        }
    }
}

// The kube side of ClusterRef and ClusterId: equality and hashing, so that a
// ClusterRef keys the shim's client map, and Debug for the logs.
#[verifier(external)]
impl PartialEq for ClusterRef {
    fn eq(&self, other: &ClusterRef) -> bool {
        self.namespace == other.namespace && self.name == other.name
    }
}

#[verifier(external)]
impl Eq for ClusterRef {}

#[verifier(external)]
impl std::hash::Hash for ClusterRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.namespace.hash(state);
        self.name.hash(state);
    }
}

#[verifier(external)]
impl std::fmt::Debug for ClusterRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.namespace, self.name)
    }
}

#[verifier(external)]
impl PartialEq for ClusterId {
    fn eq(&self, other: &ClusterId) -> bool {
        match (self, other) {
            (ClusterId::Primary, ClusterId::Primary) => true,
            (ClusterId::Remote(a), ClusterId::Remote(b)) => a == b,
            _ => false,
        }
    }
}

#[verifier(external)]
impl Eq for ClusterId {}

#[verifier(external)]
impl std::hash::Hash for ClusterId {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            ClusterId::Primary => 0u8.hash(state),
            ClusterId::Remote(r) => {
                1u8.hash(state);
                r.hash(state);
            }
        }
    }
}

#[verifier(external)]
impl std::fmt::Debug for ClusterId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClusterId::Primary => write!(f, "Primary"),
            ClusterId::Remote(r) => write!(f, "Remote({:?})", r),
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
        self.cluster.clone()
    }
}

}
