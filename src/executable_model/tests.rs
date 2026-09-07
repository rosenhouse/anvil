// Tests of the executable API server model that need no cluster.
//
// They pin the Patch behaviors the spec-level model bakes in (see
// handle_patch_request in kubernetes_cluster::spec::api_server::state_machine):
// a failed `test` is Invalid, a patch goes through the update path (so the no-op
// rule and the resource-version bump are the update path's), and generation is
// bumped by spec changes only.
//
// The crate only builds through Verus, so build the test harness with
//   cargo verus build --lib --tests -- --no-verify
// and run the resulting target/debug/deps/verifiable_controllers-<hash>
// binary with the filter `executable_model`.
use crate::executable_model::prelude::*;
use crate::kubernetes_api_objects::{
    error::APIError,
    exec::{
        api_resource::ApiResource, dynamic::DynamicObject, patch_tests::PatchTests, prelude::*,
        resource::ResourceWrapper,
    },
};
use serde_json::{json, Value};

const NAMESPACE: &str = "default";

// A custom resource whose kind string is SimpleCRView::kind(), the kind
// SimpleExecutableApiServerModel is instantiated with. Only custom resources
// carry a generation in the model.
fn simple_api_resource() -> ApiResource {
    ApiResource::from_kube(kube::api::ApiResource {
        group: "anvil.dev".to_string(),
        version: "v1".to_string(),
        api_version: "anvil.dev/v1".to_string(),
        kind: "simple".to_string(),
        plural: "simples".to_string(),
    })
}

fn simple_object(name: &str, data: Value) -> DynamicObject {
    let api_resource = simple_api_resource();
    DynamicObject::from_kube(
        kube::api::DynamicObject::new(name, api_resource.as_kube_ref())
            .within(NAMESPACE)
            .data(data),
    )
}

fn create(s: &mut ApiServerState, name: &str, spec: Value) -> DynamicObject {
    let req = KubeCreateRequest {
        api_resource: simple_api_resource(),
        namespace: NAMESPACE.to_string(),
        obj: simple_object(name, json!({ "spec": spec })),
    };
    SimpleExecutableApiServerModel::handle_create_request(&req, s)
        .res
        .expect("create")
}

fn delete(s: &mut ApiServerState, name: &str) {
    let req = KubeDeleteRequest {
        api_resource: simple_api_resource(),
        name: name.to_string(),
        namespace: NAMESPACE.to_string(),
        preconditions: None,
    };
    SimpleExecutableApiServerModel::handle_delete_request(&req, s)
        .res
        .expect("delete");
}

fn get(s: &ApiServerState, name: &str) -> DynamicObject {
    let req = KubeGetRequest {
        api_resource: simple_api_resource(),
        name: name.to_string(),
        namespace: NAMESPACE.to_string(),
    };
    SimpleExecutableApiServerModel::handle_get_request(&req, s)
        .res
        .expect("get")
}

// The tests a controller sends: the uid and generation of the object it read.
fn tests_from(obj: &DynamicObject) -> PatchTests {
    let mut tests = PatchTests::default();
    tests.set_uid_from_object_meta(obj.metadata());
    tests.set_generation_from_object_meta(obj.metadata());
    tests
}

fn patch(
    s: &mut ApiServerState,
    name: &str,
    tests: PatchTests,
    spec: Value,
) -> Result<DynamicObject, APIError> {
    let req = KubePatchRequest {
        api_resource: simple_api_resource(),
        name: name.to_string(),
        namespace: NAMESPACE.to_string(),
        tests: tests,
        obj: simple_object(name, json!({ "spec": spec })),
    };
    SimpleExecutableApiServerModel::handle_patch_request(&req, s).res
}

fn patch_status(
    s: &mut ApiServerState,
    name: &str,
    tests: PatchTests,
    status: Value,
) -> Result<DynamicObject, APIError> {
    let req = KubePatchStatusRequest {
        api_resource: simple_api_resource(),
        name: name.to_string(),
        namespace: NAMESPACE.to_string(),
        tests: tests,
        obj: simple_object(name, json!({ "status": status })),
    };
    SimpleExecutableApiServerModel::handle_patch_status_request(&req, s).res
}

fn generation(obj: &DynamicObject) -> Option<i64> {
    obj.metadata().generation()
}

fn resource_version(obj: &DynamicObject) -> Option<String> {
    obj.metadata().resource_version()
}

// Everything but the type and object metadata: the model's spec and status.
fn data(obj: &DynamicObject) -> &Value {
    &obj.as_kube_ref().data
}

#[test]
fn patch_of_missing_object_is_not_found() {
    let mut s = ApiServerState::new();
    let resp = patch(&mut s, "a", PatchTests::default(), json!({ "x": 1 }));
    assert!(matches!(resp, Err(APIError::ObjectNotFound)));
}

#[test]
fn patch_with_failed_uid_test_is_invalid() {
    let mut s = ApiServerState::new();
    let stale = create(&mut s, "a", json!({ "x": 1 }));
    delete(&mut s, "a");
    let recreated = create(&mut s, "a", json!({ "x": 1 }));
    let counter = s.resource_version_counter;
    // Same name and generation, different incarnation.
    assert_eq!(generation(&stale), generation(&recreated));
    let resp = patch(&mut s, "a", tests_from(&stale), json!({ "x": 2 }));
    assert!(matches!(resp, Err(APIError::Invalid)));
    assert_eq!(s.resource_version_counter, counter);
    assert!(get(&s, "a").eq(&recreated));
}

#[test]
fn patch_with_failed_generation_test_is_invalid() {
    let mut s = ApiServerState::new();
    let stale = create(&mut s, "a", json!({ "x": 1 }));
    let current = patch(&mut s, "a", tests_from(&stale), json!({ "x": 2 })).expect("first patch");
    let counter = s.resource_version_counter;
    // The spec changed since stale was read.
    let resp = patch(&mut s, "a", tests_from(&stale), json!({ "x": 3 }));
    assert!(matches!(resp, Err(APIError::Invalid)));
    assert_eq!(s.resource_version_counter, counter);
    assert!(get(&s, "a").eq(&current));
}

#[test]
fn noop_patch_changes_nothing() {
    let mut s = ApiServerState::new();
    let obj = create(&mut s, "a", json!({ "x": 1 }));
    let counter = s.resource_version_counter;
    let patched = patch(&mut s, "a", tests_from(&obj), json!({ "x": 1 })).expect("patch");
    assert_eq!(generation(&patched), Some(1));
    assert_eq!(resource_version(&patched), resource_version(&obj));
    assert_eq!(s.resource_version_counter, counter);
    assert!(patched.eq(&obj));
}

#[test]
fn spec_patch_bumps_generation_and_resource_version() {
    let mut s = ApiServerState::new();
    let obj = create(&mut s, "a", json!({ "x": 1 }));
    let counter = s.resource_version_counter;
    let patched = patch(&mut s, "a", tests_from(&obj), json!({ "x": 2 })).expect("patch");
    assert_eq!(generation(&patched), Some(2));
    assert_eq!(resource_version(&patched), Some(counter.to_string()));
    assert_eq!(s.resource_version_counter, counter + 1);
    assert_eq!(data(&patched), &json!({ "spec": { "x": 2 } }));
    assert!(get(&s, "a").eq(&patched));
}

#[test]
fn status_patch_leaves_generation_alone() {
    let mut s = ApiServerState::new();
    let obj = create(&mut s, "a", json!({ "x": 1 }));
    let counter = s.resource_version_counter;
    let patched = patch_status(&mut s, "a", tests_from(&obj), json!({ "observedGeneration": 1 }))
        .expect("patch status");
    assert_eq!(generation(&patched), Some(1));
    assert_eq!(resource_version(&patched), Some(counter.to_string()));
    assert_eq!(
        data(&patched),
        &json!({ "spec": { "x": 1 }, "status": { "observedGeneration": 1 } })
    );
    // Generation still pins the spec: tests read before the status write pass.
    let repatched = patch(&mut s, "a", tests_from(&obj), json!({ "x": 2 })).expect("patch");
    assert_eq!(generation(&repatched), Some(2));
    assert_eq!(
        data(&repatched),
        &json!({ "spec": { "x": 2 }, "status": { "observedGeneration": 1 } })
    );
}
