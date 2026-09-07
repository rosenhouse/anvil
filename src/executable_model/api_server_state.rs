use crate::executable_model::object_map::ObjectMap;
use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::spec::{
    common::{Kind, ObjectRef},
    dynamic::DynamicObjectView,
    resource::StoredState,
};
use crate::kubernetes_cluster::spec::api_server::types as model_types;
use vstd::prelude::*;
use vstd::string::*;

verus! {

// This is the exec version of crate::kubernetes_cluster::spec::api_server::types::ApiServerState
// and is used as the "state" of the exec API server model.
pub struct ApiServerState {
    pub resources: ObjectMap,
    pub uid_counter: i64,
    pub resource_version_counter: i64,
}

impl ApiServerState {
    pub fn new() -> ApiServerState {
        ApiServerState {
            resources: ObjectMap::new(),
            uid_counter: 0,
            resource_version_counter: 0,
        }
    }
}

impl View for ApiServerState {
    type V = model_types::APIServerState;
    open spec fn view(&self) -> model_types::APIServerState {
        model_types::APIServerState {
            resources: self.resources@,
            uid_counter: self.uid_counter as int,
            resource_version_counter: self.resource_version_counter as int,
        }
    }
}

}
