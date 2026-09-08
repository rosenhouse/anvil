// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::common::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// ApiResourceView is the ghost type of ApiResource.


pub struct ApiResourceView {
    pub kind: Kind,
}

// ClusterRefView is the ghost type of exec::api_resource::ClusterRef: a binding,
// the pair (namespace, cluster name) that names a remote cluster.
pub struct ClusterRefView {
    pub namespace: StringView,
    pub name: StringView,
}

// ClusterIdView is the ghost type of exec::api_resource::ClusterId. It is data
// on the spec side so that the model kind of an object can be a function of the
// cluster it lives in (spec::model_kind::model_kind).
pub enum ClusterIdView {
    Primary,
    Remote(ClusterRefView),
}

}
