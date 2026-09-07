use crate::external_shim_layer::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::prelude::Preconditions;
use crate::kubernetes_api_objects::exec::{api_method::*, api_resource::*, dynamic::*, patch_tests::*, resource::*};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::shim_layer::fault_injection::*;
use core::fmt::Debug;
use core::hash::Hash;
use anyhow::Result;
use futures::StreamExt;
use k8s_openapi::api::core::v1::Pod;
use kube::{
    api::{Api, DeleteParams, ListParams, Patch, PatchParams, PostParams, Resource, ResourceExt},
    config::{KubeConfigOptions, Kubeconfig},
    runtime::{
        controller::{Action, Controller},
        reflector::ObjectRef,
        watcher,
    },
    Client, Config, CustomResourceExt,
};
use kube_core::{ErrorResponse, NamespaceResourceScope};
use serde::{de::DeserializeOwned, Serialize};
use tracing::{error, info, warn};
use crate::crds::Error;
use std::sync::Arc;
use std::time::Duration;
use vstd::string::*;

// The shim layer connects the verified reconciler to the trusted kube-rs APIs.
// The key is to implement the reconcile function (impl FnMut(Arc<K>, Arc<Ctx>) -> ReconcilerFut),
// which is required by the kube-rs framework to build a controller,
// on top of reconcile_core, which is provided by the developer.

// ClusterClients holds the kube clients for each ClusterId. Every request the
// reconciler emits names its cluster through the ApiResource it carries (see
// kubernetes_api_objects::exec::api_resource::ClusterId), and the shim routes the
// request to the matching client and tags the objects in the response with the
// same cluster. Single-cluster controllers only ever use `primary`.
//
// The remote cluster gets two clients: `remote` for reconcile requests, built with
// short timeouts so a partition surfaces as an error within one reconcile, and
// `remote_watch` for the long-lived watch stream, which must keep kube's default
// (long) read timeout or the stream is cut every time the remote cluster is idle.
#[derive(Clone)]
pub struct ClusterClients {
    pub primary: Client,
    pub remote: Option<RemoteClients>,
}

#[derive(Clone)]
pub struct RemoteClients {
    pub requests: Client,
    pub watch: Client,
}

impl ClusterClients {
    pub fn single(primary: Client) -> Self {
        ClusterClients { primary, remote: None }
    }

    // client_of returns the client that handles reconcile requests for `cluster`.
    // A request for a remote cluster without a configured client is a deployment
    // error; it is reported as a request failure rather than a panic so the
    // reconciler ends in its error state and the controller keeps running.
    pub fn client_of(&self, cluster: ClusterId) -> Result<&Client, Error> {
        match cluster {
            ClusterId::Primary => Ok(&self.primary),
            ClusterId::Remote => self
                .remote
                .as_ref()
                .map(|r| &r.requests)
                .ok_or_else(|| Error::ShimLayerError("no client configured for the remote cluster".to_string())),
        }
    }

    pub fn client_for(&self, api_resource: &ApiResource) -> Result<&Client, Error> {
        self.client_of(api_resource.cluster())
    }

    // watch_client_of returns the client to build a watch stream on for `cluster`.
    pub fn watch_client_of(&self, cluster: ClusterId) -> Result<&Client, Error> {
        match cluster {
            ClusterId::Primary => Ok(&self.primary),
            ClusterId::Remote => self
                .remote
                .as_ref()
                .map(|r| &r.watch)
                .ok_or_else(|| Error::ShimLayerError("no client configured for the remote cluster".to_string())),
        }
    }
}

// remote_clients_from_kubeconfig builds the pair of clients for another cluster
// from a kubeconfig file (e.g. one mounted from a Secret). `request_timeout` bounds
// each reconcile request; the watch client keeps kube's defaults.
pub async fn remote_clients_from_kubeconfig(path: &str, request_timeout: Duration) -> Result<RemoteClients> {
    let kubeconfig = Kubeconfig::read_from(path)?;
    let watch_config = Config::from_custom_kubeconfig(kubeconfig.clone(), &KubeConfigOptions::default()).await?;
    let mut request_config = Config::from_custom_kubeconfig(kubeconfig, &KubeConfigOptions::default()).await?;
    request_config.connect_timeout = Some(request_timeout);
    request_config.read_timeout = Some(request_timeout);
    request_config.write_timeout = Some(request_timeout);
    Ok(RemoteClients {
        requests: Client::try_from(request_config)?,
        watch: Client::try_from(watch_config)?,
    })
}

// run_controller prepares and runs the controller. It requires:
// K: the custom resource type
// R: the reconciler type
pub async fn run_controller<K, R, E>(fault_injection: bool) -> Result<()>
where
    K: Clone
        + Resource<Scope = NamespaceResourceScope>
        + CustomResourceExt
        + DeserializeOwned
        + Debug
        + Send
        + Serialize
        + Sync
        + 'static,
    K::DynamicType: Default + Eq + Hash + Clone + Debug + Unpin,
    R: Reconciler + Send + Sync,
    R::K: ResourceWrapper<K> + Send,
    <R::K as View>::V: CustomResourceView,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    let client = Client::try_default().await?;
    let crs = Api::<K>::all(client.clone());

    // Build the async closure on top of reconcile_with
    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, R, E>(cr, ctx, fault_injection).await;
    };

    info!("starting controller");
    Controller::new(crs, watcher::Config::default()) // The controller's reconcile is triggered when a CR is created/updated
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { clusters: ClusterClients::single(client), cr_cluster: ClusterId::Primary })) // The reconcile function is registered
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller terminated");
    Ok(())
}

pub async fn run_controller_watching_owned<K, R, E, O>(fault_injection: bool) -> Result<()>
where
    K: Clone
        + Resource<Scope = NamespaceResourceScope>
        + CustomResourceExt
        + DeserializeOwned
        + Debug
        + Send
        + Serialize
        + Sync
        + 'static,
    K::DynamicType: Default + Eq + Hash + Clone + Debug + Unpin,
    R: Reconciler + Send + Sync,
    R::K: ResourceWrapper<K> + Send,
    <R::K as View>::V: CustomResourceView,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
    O: Clone
        + Resource<Scope = NamespaceResourceScope, DynamicType = ()>
        + DeserializeOwned
        + Debug
        + Send
        + Sync
        + 'static,
{
    let client = Client::try_default().await?;
    let crs = Api::<K>::all(client.clone());

    // Build the async closure on top of reconcile_with
    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, R, E>(cr, ctx, fault_injection).await;
    };

    info!("starting controller");
    Controller::new(crs, watcher::Config::default()) // The controller's reconcile is triggered when a CR is created/updated
        .owns(Api::<Pod>::all(client.clone()), watcher::Config::default()) // Watch owned Pods
        .owns(Api::<O>::all(client.clone()), watcher::Config::default()) // Watch owned CRs of type O
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { clusters: ClusterClients::single(client), cr_cluster: ClusterId::Primary })) // The reconcile function is registered
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller terminated");
    Ok(())
}

// run_controller_in_clusters runs a controller whose custom resource K lives in
// `cr_cluster` (its watch and quorum reads go to that cluster's client) and whose
// requests may target either cluster.
pub async fn run_controller_in_clusters<K, R, E>(
    clusters: ClusterClients,
    cr_cluster: ClusterId,
    fault_injection: bool,
) -> Result<()>
where
    K: Clone
        + Resource<Scope = NamespaceResourceScope>
        + CustomResourceExt
        + DeserializeOwned
        + Debug
        + Send
        + Serialize
        + Sync
        + 'static,
    K::DynamicType: Default + Eq + Hash + Clone + Debug + Unpin,
    R: Reconciler + Send + Sync,
    R::K: ResourceWrapper<K> + Send,
    <R::K as View>::V: CustomResourceView,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    // The primary watch stream is long-lived, so it uses the watch client of its cluster.
    let crs = Api::<K>::all(clusters.watch_client_of(cr_cluster)?.clone());

    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, R, E>(cr, ctx, fault_injection).await;
    };

    info!("starting controller (custom resource in {:?} cluster)", cr_cluster);
    Controller::new(crs, watcher::Config::default())
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { clusters, cr_cluster }))
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller terminated");
    Ok(())
}

// run_controller_with_same_name_watch is run_controller_in_clusters plus a
// secondary watch on objects of type O in `watched_cluster`: a change to
// O{namespace, name} triggers a reconcile of K{namespace, name}. This is the
// trigger a mirroring controller uses to notice status changes on the mirror in
// the other cluster. It is a latency optimization only: liveness rests on the
// periodic requeue, not on this watch.
pub async fn run_controller_with_same_name_watch<K, R, E, O>(
    clusters: ClusterClients,
    cr_cluster: ClusterId,
    watched_cluster: ClusterId,
    fault_injection: bool,
) -> Result<()>
where
    K: Clone
        + Resource<Scope = NamespaceResourceScope, DynamicType = ()>
        + CustomResourceExt
        + DeserializeOwned
        + Debug
        + Send
        + Serialize
        + Sync
        + 'static,
    R: Reconciler + Send + Sync,
    R::K: ResourceWrapper<K> + Send,
    <R::K as View>::V: CustomResourceView,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
    O: Clone
        + Resource<Scope = NamespaceResourceScope, DynamicType = ()>
        + DeserializeOwned
        + Debug
        + Send
        + Sync
        + 'static,
{
    let crs = Api::<K>::all(clusters.watch_client_of(cr_cluster)?.clone());
    let watched = Api::<O>::all(clusters.watch_client_of(watched_cluster)?.clone());

    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, R, E>(cr, ctx, fault_injection).await;
    };

    info!(
        "starting controller (custom resource in {:?} cluster, watching {:?} cluster by name)",
        cr_cluster, watched_cluster
    );
    Controller::new(crs, watcher::Config::default())
        .watches(watched, watcher::Config::default(), |o: O| {
            o.namespace()
                .map(|ns| ObjectRef::<K>::new(&o.name_any()).within(&ns))
        })
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { clusters, cr_cluster }))
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller terminated");
    Ok(())
}

// reconcile_with implements the reconcile function by repeatedly invoking R::reconcile_core.
// reconcile_with will be invoked by kube-rs whenever kube-rs's watcher receives any relevant event to the controller.
// In each invocation, reconcile_with invokes R::reconcile_core in a loop:
// it starts with R::reconcile_init_state, and in each iteration it invokes R::reconcile_core
// with the new state returned by the previous invocation.
// For each request from R::reconcile_core, it invokes kube-rs APIs to send the request to the Kubernetes API.
// It ends the loop when the R reports the reconcile is done (R::reconcile_done)
// or encounters error (R::reconcile_error).
pub async fn reconcile_with<K, R, E>(
    cr: Arc<K>,
    ctx: Arc<Data>,
    fault_injection: bool,
) -> Result<Action, Error>
where
    K: Clone
        + Resource<Scope = NamespaceResourceScope>
        + CustomResourceExt
        + DeserializeOwned
        + Debug
        + Serialize,
    K::DynamicType: Default + Clone + Debug,
    R: Reconciler,
    R::K: ResourceWrapper<K>,
    <R::K as View>::V: CustomResourceView,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    // The custom resource is read from the cluster it lives in; every other request
    // is routed by the cluster named in its ApiResource.
    let cr_client = ctx.clusters.client_of(ctx.cr_cluster)?;

    let cr_name = cr.meta().name.as_ref().ok_or_else(|| {
        Error::ShimLayerError("Custom resource misses \".metadata.name\"".to_string())
    })?;
    let cr_namespace = cr.meta().namespace.as_ref().ok_or_else(|| {
        Error::ShimLayerError("Custom resources misses \".metadata.namespace\"".to_string())
    })?;
    let cr_kind = K::kind(&K::DynamicType::default()).to_string();

    let cr_key = format!("{}/{}/{}", cr_kind, cr_namespace, cr_name);
    let log_header = format!("Reconciling {}:", cr_key);

    let cr_api = Api::<K>::namespaced(cr_client.clone(), &cr_namespace);
    // Get the custom resource by a quorum read to Kubernetes' storage (etcd) to get the most updated custom resource
    let get_cr_resp = cr_api.get(&cr_name).await;
    match get_cr_resp {
        Err(kube_client::error::Error::Api(ErrorResponse { reason, .. }))
            if &reason == "NotFound" =>
        {
            warn!(
                "{} Custom resource {} not found, end reconcile",
                log_header, cr_name
            );
            return Ok(Action::await_change());
        }
        Err(err) => {
            warn!(
                "{} Get custom resource {} failed with error: {}, will retry reconcile",
                log_header, cr_name, err
            );
            return Ok(Action::requeue(Duration::from_secs(60)));
        }
        _ => {}
    }
    // Wrap the custom resource with Verus-friendly wrapper type (which has a ghost version, i.e., view)
    let cr = get_cr_resp.unwrap();
    info!(
        "{} Get cr {}",
        log_header,
        k8s_openapi::serde_json::to_string(&cr).unwrap()
    );

    let cr_wrapper = R::K::from_kube(cr);
    let mut state = R::reconcile_init_state();
    let mut resp_option: Option<Response<R::EResp>> = None;
    // check_fault_timing is only set to true right after the controller issues any create, update or delete request,
    // or external request
    let mut check_fault_timing: bool;

    // Call reconcile_core in a loop
    loop {
        check_fault_timing = false;
        // If reconcile core is done, then breaks the loop
        if R::reconcile_done(&state) {
            info!("{} done", log_header);
            break;
        }
        if R::reconcile_error(&state) {
            warn!("{} error", log_header);
            return Err(Error::ReconcileCoreError);
        }
        // Feed the current reconcile state and get the new state and the pending request
        let (state_prime, request_option) = R::reconcile_core(&cr_wrapper, resp_option, state);
        // Pattern match the request and send requests to the Kubernetes API via kube-rs methods
        match request_option {
            Some(request) => match request {
                Request::KRequest(req) => {
                    let kube_resp: KubeAPIResponse;
                    match req {
                        KubeAPIRequest::GetRequest(get_req) => {
                            let cluster = get_req.api_resource.cluster();
                            let api = Api::<kube::api::DynamicObject>::namespaced_with(
                                ctx.clusters.client_of(cluster)?.clone(),
                                &get_req.namespace,
                                get_req.api_resource.as_kube_ref(),
                            );
                            let key = get_req.key();
                            match api.get(&get_req.name).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::GetResponse(KubeGetResponse {
                                        res: Err(kube_error_to_api_error(&err)),
                                    });
                                    info!("{} Get {} failed with error: {}", log_header, key, err);
                                }
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::GetResponse(KubeGetResponse {
                                        res: Ok(DynamicObject::from_kube_in(obj, cluster)),
                                    });
                                    info!("{} Get {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::ListRequest(list_req) => {
                            let cluster = list_req.api_resource.cluster();
                            let api = Api::<kube::api::DynamicObject>::namespaced_with(
                                ctx.clusters.client_of(cluster)?.clone(),
                                &list_req.namespace,
                                list_req.api_resource.as_kube_ref(),
                            );
                            let key = list_req.key();
                            let lp = ListParams::default();
                            match api.list(&lp).await {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::ListResponse(KubeListResponse {
                                        res: Err(kube_error_to_api_error(&err)),
                                    });
                                    info!("{} List {} failed with error: {}", log_header, key, err);
                                }
                                Ok(obj_list) => {
                                    kube_resp = KubeAPIResponse::ListResponse(KubeListResponse {
                                        res: Ok(obj_list
                                            .items
                                            .into_iter()
                                            .map(|obj| DynamicObject::from_kube_in(obj, cluster))
                                            .collect()),
                                    });
                                    info!("{} List {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::CreateRequest(create_req) => {
                            check_fault_timing = true;
                            let cluster = create_req.api_resource.cluster();
                            let api = Api::<kube::api::DynamicObject>::namespaced_with(
                                ctx.clusters.client_of(cluster)?.clone(),
                                &create_req.namespace,
                                create_req.api_resource.as_kube_ref(),
                            );
                            let pp = PostParams::default();
                            let key = create_req.key();
                            let obj_to_create = create_req.obj.into_kube();
                            match api.create(&pp, &obj_to_create).await {
                                Err(err) => {
                                    kube_resp =
                                        KubeAPIResponse::CreateResponse(KubeCreateResponse {
                                            res: Err(kube_error_to_api_error(&err)),
                                        });
                                    info!(
                                        "{} Create {} failed with error: {}",
                                        log_header, key, err
                                    );
                                }
                                Ok(obj) => {
                                    kube_resp =
                                        KubeAPIResponse::CreateResponse(KubeCreateResponse {
                                            res: Ok(DynamicObject::from_kube_in(obj, cluster)),
                                        });
                                    info!("{} Create {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::DeleteRequest(delete_req) => {
                            check_fault_timing = true;
                            let api = Api::<kube::api::DynamicObject>::namespaced_with(
                                ctx.clusters.client_for(&delete_req.api_resource)?.clone(),
                                &delete_req.namespace,
                                delete_req.api_resource.as_kube_ref(),
                            );
                            let mut dp = DeleteParams::default();
                            if delete_req.preconditions.is_some() {
                                dp = dp.preconditions(
                                    delete_req.preconditions.clone().unwrap().into_kube(),
                                );
                            }
                            let key = delete_req.key();
                            match api.delete(&delete_req.name, &dp).await {
                                Err(err) => {
                                    kube_resp =
                                        KubeAPIResponse::DeleteResponse(KubeDeleteResponse {
                                            res: Err(kube_error_to_api_error(&err)),
                                        });
                                    info!(
                                        "{} Delete {} failed with error: {}",
                                        log_header, key, err
                                    );
                                }
                                Ok(_) => {
                                    kube_resp =
                                        KubeAPIResponse::DeleteResponse(KubeDeleteResponse {
                                            res: Ok(()),
                                        });
                                    info!("{} Delete {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::UpdateRequest(update_req) => {
                            check_fault_timing = true;
                            let cluster = update_req.api_resource.cluster();
                            let api = Api::<kube::api::DynamicObject>::namespaced_with(
                                ctx.clusters.client_of(cluster)?.clone(),
                                &update_req.namespace,
                                update_req.api_resource.as_kube_ref(),
                            );
                            let pp = PostParams::default();
                            let key = update_req.key();
                            let obj_to_update = update_req.obj.into_kube();
                            match api.replace(&update_req.name, &pp, &obj_to_update).await {
                                Err(err) => {
                                    kube_resp =
                                        KubeAPIResponse::UpdateResponse(KubeUpdateResponse {
                                            res: Err(kube_error_to_api_error(&err)),
                                        });
                                    info!(
                                        "{} Update {} failed with error: {}",
                                        log_header, key, err
                                    );
                                }
                                Ok(obj) => {
                                    kube_resp =
                                        KubeAPIResponse::UpdateResponse(KubeUpdateResponse {
                                            res: Ok(DynamicObject::from_kube_in(obj, cluster)),
                                        });
                                    info!("{} Update {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::UpdateStatusRequest(update_status_req) => {
                            check_fault_timing = true;
                            let cluster = update_status_req.api_resource.cluster();
                            let api = Api::<kube::api::DynamicObject>::namespaced_with(
                                ctx.clusters.client_of(cluster)?.clone(),
                                &update_status_req.namespace,
                                update_status_req.api_resource.as_kube_ref(),
                            );
                            let pp = PostParams::default();
                            let key = update_status_req.key();
                            let obj_to_update = update_status_req.obj.into_kube();
                            // Here we assume serde_json always succeed
                            match api
                                .replace_status(
                                    &update_status_req.name,
                                    &pp,
                                    k8s_openapi::serde_json::to_vec(&obj_to_update)
                                        .unwrap(),
                                )
                                .await
                            {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::UpdateStatusResponse(
                                        KubeUpdateStatusResponse {
                                            res: Err(kube_error_to_api_error(&err)),
                                        },
                                    );
                                    info!(
                                        "{} UpdateStatus {} failed with error: {}",
                                        log_header, key, err
                                    );
                                }
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::UpdateStatusResponse(
                                        KubeUpdateStatusResponse {
                                            res: Ok(DynamicObject::from_kube_in(obj, cluster)),
                                        },
                                    );
                                    info!("{} UpdateStatus {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::PatchRequest(patch_req) => {
                            check_fault_timing = true;
                            let cluster = patch_req.api_resource.cluster();
                            let api = Api::<kube::api::DynamicObject>::namespaced_with(
                                ctx.clusters.client_of(cluster)?.clone(),
                                &patch_req.namespace,
                                patch_req.api_resource.as_kube_ref(),
                            );
                            let key = patch_req.key();
                            let spec = patch_req
                                .obj
                                .into_kube()
                                .data
                                .get("spec")
                                .cloned()
                                .unwrap_or(serde_json::Value::Null);
                            let patch = json_patch_with_tests(&patch_req.tests, "/spec", spec);
                            match api
                                .patch(&patch_req.name, &PatchParams::default(), &Patch::<()>::Json(patch))
                                .await
                            {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::PatchResponse(KubePatchResponse {
                                        res: Err(kube_error_to_api_error(&err)),
                                    });
                                    info!("{} Patch {} failed with error: {}", log_header, key, err);
                                }
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::PatchResponse(KubePatchResponse {
                                        res: Ok(DynamicObject::from_kube_in(obj, cluster)),
                                    });
                                    info!("{} Patch {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::PatchStatusRequest(patch_status_req) => {
                            check_fault_timing = true;
                            let cluster = patch_status_req.api_resource.cluster();
                            let api = Api::<kube::api::DynamicObject>::namespaced_with(
                                ctx.clusters.client_of(cluster)?.clone(),
                                &patch_status_req.namespace,
                                patch_status_req.api_resource.as_kube_ref(),
                            );
                            let key = patch_status_req.key();
                            let status = patch_status_req
                                .obj
                                .into_kube()
                                .data
                                .get("status")
                                .cloned()
                                .unwrap_or(serde_json::Value::Null);
                            let patch = json_patch_with_tests(&patch_status_req.tests, "/status", status);
                            match api
                                .patch_status(&patch_status_req.name, &PatchParams::default(), &Patch::<()>::Json(patch))
                                .await
                            {
                                Err(err) => {
                                    kube_resp = KubeAPIResponse::PatchStatusResponse(KubePatchStatusResponse {
                                        res: Err(kube_error_to_api_error(&err)),
                                    });
                                    info!("{} PatchStatus {} failed with error: {}", log_header, key, err);
                                }
                                Ok(obj) => {
                                    kube_resp = KubeAPIResponse::PatchStatusResponse(KubePatchStatusResponse {
                                        res: Ok(DynamicObject::from_kube_in(obj, cluster)),
                                    });
                                    info!("{} PatchStatus {} done", log_header, key);
                                }
                            }
                        }
                        KubeAPIRequest::GetThenDeleteRequest(req) => {
                            check_fault_timing = true;
                            kube_resp = KubeAPIResponse::GetThenDeleteResponse(
                                transactional_get_then_delete_by_retry(
                                    ctx.clusters.client_for(&req.api_resource)?,
                                    req,
                                    log_header.clone(),
                                )
                                .await,
                            );
                        }
                        KubeAPIRequest::GetThenUpdateRequest(req) => {
                            check_fault_timing = true;
                            kube_resp = KubeAPIResponse::GetThenUpdateResponse(
                                transactional_get_then_update_by_retry(
                                    ctx.clusters.client_for(&req.api_resource)?,
                                    req,
                                    log_header.clone(),
                                )
                                .await,
                            );
                        }
                        KubeAPIRequest::GetThenUpdateStatusRequest(req) => {
                            check_fault_timing = true;
                            kube_resp = KubeAPIResponse::GetThenUpdateStatusResponse(
                                transactional_get_then_update_status_by_retry(
                                    ctx.clusters.client_for(&req.api_resource)?,
                                    req,
                                    log_header.clone(),
                                )
                                .await,
                            );
                        }
                    }
                    resp_option = Some(Response::KResponse(kube_resp));
                }
                Request::ExternalRequest(external_req) => {
                    check_fault_timing = true;
                    let external_resp = E::external_call(external_req);
                    resp_option = Some(Response::ExternalResponse(external_resp));
                }
            },
            _ => resp_option = None,
        }
        if check_fault_timing && fault_injection {
            // If the controller just issues create, update, delete or external request,
            // and fault injection option is on, then check whether to crash at this point
            let result = crash_or_continue(&ctx.clusters.primary, &cr_key, &log_header).await;
            if result.is_err() {
                error!(
                    "{} crash_or_continue fails due to {}",
                    log_header,
                    result.unwrap_err()
                );
            }
        }
        state = state_prime;
    }

    return Ok(Action::requeue(Duration::from_secs(60)));
}

// transactional_get_then_delete_by_retry retries get and then delete upon conflict errors to simulate atomic operations.
// This guarantees that the entire get_then_delete operation will not fail due to conflicts between concurrent
// controllers. Note that transactional_get_then_delete_by_retry's termination depends on fairness assumptions.
pub async fn transactional_get_then_delete_by_retry(
    client: &Client,
    req: KubeGetThenDeleteRequest,
    log_header: String,
) -> KubeGetThenDeleteResponse {
    // sanity check, can be removed if type invariant is supported by Verus
    let api = Api::<kube::api::DynamicObject>::namespaced_with(
        client.clone(),
        &req.namespace,
        req.api_resource.as_kube_ref(),
    );
    let key = req.key();

    loop {
        // Step 1: get the object
        let get_result = api.get(&req.name).await;
        if let Err(err) = get_result {
            info!(
                "{} Get of Get-then-Delete {} failed with error: {}",
                log_header, key, err
            );
            return KubeGetThenDeleteResponse {
                res: Err(kube_error_to_api_error(&err)),
            };
        }
        // Step 2: if the object exists, perform a check using a predicate on object
        // The predicate: Is the current object owned by req.owner_ref?
        // TODO: the predicate should be provided by clients instead of the hardcoded one
        let current_obj = DynamicObject::from_kube_in(get_result.unwrap(), req.api_resource.cluster());
        if !current_obj
            .metadata()
            .owner_references_contains(&req.owner_ref)
        {
            return KubeGetThenDeleteResponse {
                res: Err(APIError::TransactionAbort),
            };
        }
        // Step 3: if the check passes, delete the object with a precondition
        // Note that resource_version and uid comes from the current object to avoid conflict error
        let dp = DeleteParams::default().preconditions(kube::api::Preconditions {
            resource_version: current_obj.as_kube_ref().metadata.resource_version.clone(),
            uid: current_obj.as_kube_ref().metadata.uid.clone(),
        });
        match api.delete(&req.name, &dp).await {
            Err(err) => {
                let api_err = kube_error_to_api_error(&err);
                match api_err {
                    APIError::Conflict => {
                        // Retry upon a conflict error
                        info!(
                            "{} Delete of Get-then-Delete {} failed with Conflict; retry...",
                            log_header, key
                        );
                        continue;
                    }
                    _ => {
                        info!(
                            "{} Delete of Get-then-Delete {} failed with error: {}",
                            log_header, key, err
                        );
                        return KubeGetThenDeleteResponse { res: Err(api_err) };
                    }
                }
            }
            Ok(obj) => {
                info!("{} Delete {} done", log_header, key);
                return KubeGetThenDeleteResponse { res: Ok(()) };
            }
        }
    }
}

// transactional_get_then_update_by_retry retries get and then update upon conflict errors to simulate atomic operations.
// This guarantees that the entire get_then_update operation will not fail due to conflicts between concurrent
// controllers. Note that transactional_get_then_update_by_retry's termination depends on fairness assumptions.
pub async fn transactional_get_then_update_by_retry(
    client: &Client,
    req: KubeGetThenUpdateRequest,
    log_header: String,
) -> KubeGetThenUpdateResponse {
    // sanity check, can be removed if type invariant is supported by Verus
    let api = Api::<kube::api::DynamicObject>::namespaced_with(
        client.clone(),
        &req.namespace,
        req.api_resource.as_kube_ref(),
    );
    let pp = PostParams::default();
    let key = req.key();
    let mut obj_to_update = req.obj.into_kube();

    loop {
        // Step 1: get the object
        let get_result = api.get(&req.name).await;
        if let Err(err) = get_result {
            info!(
                "{} Get of Get-then-Update {} failed with error: {}",
                log_header, key, err
            );
            return KubeGetThenUpdateResponse {
                res: Err(kube_error_to_api_error(&err)),
            };
        }
        // Step 2: if the object exists, perform a check using a predicate on object
        // The predicate: Is the current object owned by req.owner_ref?
        // TODO: the predicate should be provided by clients instead of the hardcoded one
        let current_obj = DynamicObject::from_kube_in(get_result.unwrap(), req.api_resource.cluster());
        if !current_obj
            .metadata()
            .owner_references_contains(&req.owner_ref)
        {
            return KubeGetThenUpdateResponse {
                res: Err(APIError::TransactionAbort),
            };
        }
        // Step 3: if the check passes, overwrite the object with the new one
        // Note that resource_version and uid comes from the current object to avoid conflict error
        obj_to_update.metadata.uid = current_obj.as_kube_ref().metadata.uid.clone();
        obj_to_update.metadata.resource_version =
            current_obj.as_kube_ref().metadata.resource_version.clone();
        match api.replace(&req.name, &pp, &obj_to_update).await {
            Err(err) => {
                let api_err = kube_error_to_api_error(&err);
                match api_err {
                    APIError::Conflict => {
                        // Retry upon a conflict error
                        info!(
                            "{} Update of Get-then-Update {} failed with Conflict; retry...",
                            log_header, key
                        );
                        continue;
                    }
                    _ => {
                        info!(
                            "{} Update of Get-then-Update {} failed with error: {}",
                            log_header, key, err
                        );
                        return KubeGetThenUpdateResponse { res: Err(api_err) };
                    }
                }
            }
            Ok(obj) => {
                info!("{} Update {} done", log_header, key);
                return KubeGetThenUpdateResponse {
                    res: Ok(DynamicObject::from_kube_in(obj, req.api_resource.cluster())),
                };
            }
        }
    }
}

// transactional_get_then_update_status_by_retry retries get and then update status upon conflict errors to simulate atomic operations.
// This guarantees that the entire get_then_update_status operation will not fail due to conflicts between concurrent
// controllers. Note that transactional_get_then_update_status_by_retry's termination depends on fairness assumptions.
pub async fn transactional_get_then_update_status_by_retry(
    client: &Client,
    req: KubeGetThenUpdateStatusRequest,
    log_header: String,
) -> KubeGetThenUpdateStatusResponse {
    // sanity check, can be removed if type invariant is supported by Verus
    let api = Api::<kube::api::DynamicObject>::namespaced_with(
        client.clone(),
        &req.namespace,
        req.api_resource.as_kube_ref(),
    );
    let pp = PostParams::default();
    let key = req.key();
    let mut obj_to_update = req.obj.into_kube();
    
    loop {
        // Step 1: get the object
        let get_result = api.get(&req.name).await;
        if let Err(err) = get_result {
            info!(
                "{} Get of Get-then-Update-Status {} failed with error: {}",
                log_header, key, err
            );
            return KubeGetThenUpdateStatusResponse {
                res: Err(kube_error_to_api_error(&err)),
            };
        }
        // Step 2: if the object exists, perform a check using a predicate on object
        // The predicate: Is the current object owned by req.owner_ref?
        let current_obj = DynamicObject::from_kube_in(get_result.unwrap(), req.api_resource.cluster());
        if !current_obj
            .metadata()
            .owner_references_contains(&req.owner_ref)
        {
            return KubeGetThenUpdateStatusResponse {
                res: Err(APIError::TransactionAbort),
            };
        }
        // Step 3: if the check passes, overwrite the status of the object with the new one
        // Note that resource_version and uid comes from the current object to avoid conflict error
        obj_to_update.metadata.uid = current_obj.as_kube_ref().metadata.uid.clone();
        obj_to_update.metadata.resource_version =
            current_obj.as_kube_ref().metadata.resource_version.clone();
        match api
            .replace_status(
                &req.name,
                &pp,
                k8s_openapi::serde_json::to_vec(&obj_to_update).unwrap(),
            )
            .await
        {
            Err(err) => {
                let api_err = kube_error_to_api_error(&err);
                match api_err {
                    APIError::Conflict => {
                        // Retry upon a conflict error
                        info!(
                            "{} UpdateStatus of Get-then-Update-Status {} failed with Conflict; retry...",
                            log_header, key
                        );
                        continue;
                    }
                    _ => {
                        info!(
                            "{} UpdateStatus of Get-then-Update-Status {} failed with error: {}",
                            log_header, key, err
                        );
                        return KubeGetThenUpdateStatusResponse { res: Err(api_err) };
                    }
                }
            }
            Ok(obj) => {
                info!("{} UpdateStatus {} done", log_header, key);
                return KubeGetThenUpdateStatusResponse {
                    res: Ok(DynamicObject::from_kube_in(obj, req.api_resource.cluster())),
                };
            }
        }
    }
}

// json_patch_with_tests builds the JSON patch that realizes a PatchRequest or
// PatchStatusRequest: one `test` per present test, then an `add` of the whole
// value at `path` (`add` on an existing member replaces it; on a missing one it
// creates it). The API server evaluates the whole document atomically against the
// current object, which is what the model's one-step handle_patch_request assumes.
fn json_patch_with_tests(tests: &PatchTests, path: &str, value: serde_json::Value) -> json_patch::Patch {
    use json_patch::{AddOperation, PatchOperation, TestOperation};
    let mut ops = Vec::new();
    if let Some(uid) = tests.uid_value() {
        ops.push(PatchOperation::Test(TestOperation {
            path: "/metadata/uid".to_string(),
            value: serde_json::Value::String(uid),
        }));
    }
    if let Some(generation) = tests.generation_value() {
        ops.push(PatchOperation::Test(TestOperation {
            path: "/metadata/generation".to_string(),
            value: serde_json::json!(generation),
        }));
    }
    ops.push(PatchOperation::Add(AddOperation {
        path: path.to_string(),
        value,
    }));
    json_patch::Patch(ops)
}

// error_policy defines the controller's behavior when the reconcile ends with an error.
pub fn error_policy<K>(_object: Arc<K>, _error: &Error, _ctx: Arc<Data>) -> Action
where
    K: Clone + Resource + DeserializeOwned + Debug + Send + Sync + 'static,
    K::DynamicType: Eq + Hash + Clone + Debug + Unpin,
{
    Action::requeue(Duration::from_secs(10))
}

// Data is passed to reconcile_with.
// It carries the clients that communicate with the Kubernetes API servers, and
// which of them hosts the custom resource this controller reconciles.
pub struct Data {
    pub clusters: ClusterClients,
    pub cr_cluster: ClusterId,
}

// kube_error_to_api_error translates the API error from kube-rs APIs
// to the form that can be processed by reconcile_core.

// TODO: match more error types.
pub fn kube_error_to_api_error(error: &kube::Error) -> APIError {
    match error {
        kube::Error::Api(error_resp) => {
            if &error_resp.reason == "NotFound" {
                APIError::ObjectNotFound
            } else if &error_resp.reason == "AlreadyExists" {
                APIError::ObjectAlreadyExists
            } else if &error_resp.reason == "BadRequest" {
                APIError::BadRequest
            } else if &error_resp.reason == "Conflict" {
                APIError::Conflict
            } else if &error_resp.reason == "Invalid" {
                APIError::Invalid
            } else if &error_resp.reason == "InternalError" {
                APIError::InternalError
            } else if &error_resp.reason == "Timeout" {
                APIError::Timeout
            } else if &error_resp.reason == "ServerTimeout" {
                APIError::ServerTimeout
            } else {
                APIError::Other
            }
        }
        _ => APIError::Other,
    }
}
