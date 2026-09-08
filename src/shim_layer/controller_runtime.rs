use crate::external_shim_layer::*;
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::exec::prelude::Preconditions;
use crate::kubernetes_api_objects::exec::{api_method::*, api_resource::*, dynamic::*, patch_tests::*, registry::*, resource::*, synced_object::*};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::kubernetes_api_objects::spec::synced_object::DynamicObjectLike;
use crate::reconciler::exec::{io::*, reconciler::*};
use crate::shim_layer::fault_injection::*;
use core::fmt::Debug;
use core::hash::Hash;
use anyhow::{bail, Result};
use futures::future::BoxFuture;
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
use tracing::{debug, error, info, warn};
use crate::crds::Error;
use std::collections::HashMap;
use std::future::Future;
use std::marker::PhantomData;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use vstd::string::*;

// The kube types the dynamic runners work on, as opposed to the wrappers of the
// same names in kubernetes_api_objects::exec.
type KubeDynamicObject = kube::api::DynamicObject;
type KubeApiResource = kube::api::ApiResource;

// The shim layer connects the verified reconciler to the trusted kube-rs APIs.
// The key is to implement the reconcile function (impl FnMut(Arc<K>, Arc<Ctx>) -> ReconcilerFut),
// which is required by the kube-rs framework to build a controller,
// on top of reconcile_core, which is provided by the developer.

// ClusterClients holds the kube clients of the process, one per ClusterId. Every
// request the reconciler emits names its cluster through the ApiResource it
// carries (see kubernetes_api_objects::exec::api_resource::ClusterId), and the
// shim routes the request to the matching client and tags the objects in the
// response with the same cluster. Single-cluster controllers only ever use
// `primary`.
//
// The remote clients are a map from the binding (ClusterRef) to its pair of
// clients and its status, shared by every controller of the process: the
// binding manager (shim_layer::bindings) binds, rebinds, refuses and unbinds
// clusters while the controllers run. A request to a binding that is not in the
// map fails as if the cluster were unreachable, one to a refused binding as if
// the cluster had denied it (see ClusterUnavailable).
#[derive(Clone)]
pub struct ClusterClients {
    pub primary: Client,
    remotes: Arc<RwLock<HashMap<ClusterRef, RemoteBinding>>>,
}

// The two clients of a remote cluster: `requests` for reconcile requests, built
// with short timeouts so a partition surfaces as an error within one reconcile,
// and `watch` for the long-lived watch streams, which must keep kube's default
// (long) read timeout or the stream is cut every time the remote cluster is idle.
#[derive(Clone)]
pub struct RemoteClients {
    pub requests: Client,
    pub watch: Client,
}

// Whether a bound cluster takes the process's requests. A binding is Refused
// when its inner cluster is claimed by another binding or its credential was
// denied a verb it needs (doc/widget_sync_fanout_design.md, sections 1.3 and
// 1.4): the clients are kept, so that the claim can be re-checked through them,
// but no request of a reconciler is sent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingStatus {
    Ready,
    Refused,
}

// A bound cluster: its clients and whether they may be used.
#[derive(Clone)]
struct RemoteBinding {
    clients: RemoteClients,
    status: BindingStatus,
}

// Why a request to a cluster cannot be sent, and the answer the reconciler gets
// for it. Unbound is the answer of an unreachable cluster (the model's
// `drop_req` fault, which the sync controller reports as InnerUnreachable): the
// binding's kubeconfig Secret is missing or does not parse, its inner cluster
// did not answer the access check, or the wrapper names a cluster this process
// never registered. Refused is the answer of a cluster that refused this
// controller, which the sync controller reports as Forbidden with Stalled=True;
// the shim gives it without asking the cluster, on behalf of the claim
// (doc/widget_sync_fanout_design.md, sections 1.3 and 1.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ClusterUnavailable {
    #[error("no client bound for the cluster")]
    Unbound,
    #[error("the binding is refused: its inner cluster is claimed by another binding, or its credential was denied")]
    Refused,
}

impl ClusterUnavailable {
    // The answer the reconciler sees for a request that was never sent.
    pub fn api_error(&self) -> APIError {
        match self {
            ClusterUnavailable::Unbound => APIError::Timeout,
            ClusterUnavailable::Refused => APIError::Forbidden,
        }
    }

    // The `cause` field of the log line of a request that was not sent.
    pub fn cause(&self) -> &'static str {
        match self {
            ClusterUnavailable::Unbound => "cluster not bound",
            ClusterUnavailable::Refused => "binding refused",
        }
    }
}

impl From<ClusterUnavailable> for Error {
    fn from(e: ClusterUnavailable) -> Error {
        Error::ShimLayerError(e.to_string())
    }
}

impl ClusterClients {
    // new starts with the primary client and no bound remote cluster.
    pub fn new(primary: Client) -> Self {
        ClusterClients { primary, remotes: Arc::new(RwLock::new(HashMap::new())) }
    }

    pub fn single(primary: Client) -> Self {
        Self::new(primary)
    }

    // with_remote is new plus one ready binding, for a process configured with a
    // fixed remote cluster.
    pub async fn with_remote(primary: Client, cluster: ClusterRef, clients: RemoteClients) -> Self {
        let clusters = Self::new(primary);
        clusters.insert_remote(cluster, clients, BindingStatus::Ready).await;
        clusters
    }

    // insert_remote binds `cluster` to `clients` with `status`, replacing and
    // returning the previous clients if the binding existed.
    pub async fn insert_remote(&self, cluster: ClusterRef, clients: RemoteClients, status: BindingStatus) -> Option<RemoteClients> {
        self.remotes.write().await.insert(cluster, RemoteBinding { clients, status }).map(|b| b.clients)
    }

    // replace_remote rebuilds the clients of a bound cluster in place (a rotated
    // credential) and returns the previous ones, keeping the binding's status; it
    // binds nothing new, so an unbound cluster is left unbound and `clients` is
    // handed back as the error.
    pub async fn replace_remote(&self, cluster: &ClusterRef, clients: RemoteClients) -> std::result::Result<RemoteClients, RemoteClients> {
        let mut remotes = self.remotes.write().await;
        match remotes.get_mut(cluster) {
            Some(slot) => Ok(std::mem::replace(&mut slot.clients, clients)),
            None => Err(clients),
        }
    }

    // remove_remote unbinds `cluster`; requests to it fail from now on.
    pub async fn remove_remote(&self, cluster: &ClusterRef) -> Option<RemoteClients> {
        self.remotes.write().await.remove(cluster).map(|b| b.clients)
    }

    // set_status refuses or re-admits a bound cluster and returns its previous
    // status, None if it is not bound. The caller logs the transition (the
    // binding manager logs a refusal once, at warn).
    pub async fn set_status(&self, cluster: &ClusterRef, status: BindingStatus) -> Option<BindingStatus> {
        let mut remotes = self.remotes.write().await;
        remotes.get_mut(cluster).map(|b| std::mem::replace(&mut b.status, status))
    }

    pub async fn status_of(&self, cluster: &ClusterRef) -> Option<BindingStatus> {
        self.remotes.read().await.get(cluster).map(|b| b.status)
    }

    pub async fn has_remote(&self, cluster: &ClusterRef) -> bool {
        self.remotes.read().await.contains_key(cluster)
    }

    pub async fn remote_refs(&self) -> Vec<ClusterRef> {
        self.remotes.read().await.keys().cloned().collect()
    }

    // remote_of returns the clients of a bound cluster whatever its status; the
    // binding manager talks to a refused cluster through them to re-check its claim.
    pub async fn remote_of(&self, cluster: &ClusterRef) -> Option<RemoteClients> {
        self.remotes.read().await.get(cluster).map(|b| b.clients.clone())
    }

    // client_of returns the client that handles reconcile requests for `cluster`.
    // A request for a remote cluster that is not bound, or one that is refused,
    // is reported as a request failure rather than a panic, so the reconciler
    // ends in its error state and the controller keeps running.
    pub async fn client_of(&self, cluster: &ClusterId) -> std::result::Result<Client, ClusterUnavailable> {
        match cluster {
            ClusterId::Primary => Ok(self.primary.clone()),
            ClusterId::Remote(r) => match self.remotes.read().await.get(r) {
                None => Err(ClusterUnavailable::Unbound),
                Some(b) => match b.status {
                    BindingStatus::Ready => Ok(b.clients.requests.clone()),
                    BindingStatus::Refused => Err(ClusterUnavailable::Refused),
                },
            },
        }
    }

    pub async fn client_for(&self, api_resource: &ApiResource) -> std::result::Result<Client, ClusterUnavailable> {
        self.client_of(&api_resource.cluster()).await
    }

    // watch_client_of returns the client to build a watch stream on for `cluster`.
    // A refused binding has no watch stream of ours: its runners are never started.
    pub async fn watch_client_of(&self, cluster: &ClusterId) -> std::result::Result<Client, ClusterUnavailable> {
        match cluster {
            ClusterId::Primary => Ok(self.primary.clone()),
            ClusterId::Remote(r) => match self.remotes.read().await.get(r) {
                None => Err(ClusterUnavailable::Unbound),
                Some(b) => match b.status {
                    BindingStatus::Ready => Ok(b.clients.watch.clone()),
                    BindingStatus::Refused => Err(ClusterUnavailable::Refused),
                },
            },
        }
    }
}

// remote_clients_from_kubeconfig builds the pair of clients for another cluster
// from a kubeconfig file (e.g. one mounted from a Secret). `request_timeout` bounds
// each reconcile request; the watch client keeps kube's defaults. It is for a
// process with one mounted credential; the widget sync controller reads a
// binding's kubeconfig out of its Secret instead
// (remote_clients_from_kubeconfig_yaml, shim_layer::bindings).
//
// The credential should be a `tokenFile` (a relative path is resolved against the
// kubeconfig's directory): kube re-reads it at least once a minute, so a rotated
// token is picked up without a restart. An inline `token` is read once and takes
// precedence over `tokenFile`, so it is warned about.
pub async fn remote_clients_from_kubeconfig(path: &str, request_timeout: Duration) -> Result<RemoteClients> {
    let kubeconfig = Kubeconfig::read_from(path)?;
    for named in &kubeconfig.auth_infos {
        if named.auth_info.as_ref().map(|a| a.token.is_some()).unwrap_or(false) {
            warn!(
                "remote kubeconfig {} user {} uses an inline token; it is never re-read, so rotation needs a restart (use tokenFile)",
                path, named.name
            );
        }
    }
    remote_clients_from(kubeconfig, request_timeout).await
}

// remote_clients_from_kubeconfig_yaml is remote_clients_from_kubeconfig for a
// kubeconfig held in memory: the `value` of a Cluster API `<name>-kubeconfig`
// Secret, whose credential is inline and whose rotation is the Secret changing
// (the binding manager rebuilds the clients then), so no warning about inline
// tokens applies.
pub async fn remote_clients_from_kubeconfig_yaml(yaml: &str, request_timeout: Duration) -> Result<RemoteClients> {
    let kubeconfig = Kubeconfig::from_yaml(yaml)?;
    remote_clients_from(kubeconfig, request_timeout).await
}

async fn remote_clients_from(kubeconfig: Kubeconfig, request_timeout: Duration) -> Result<RemoteClients> {
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

// discover_kinds resolves each configured kind in the cluster `client` reaches
// into a registry entry: the served ApiResource of the kind. A kind that is not
// served, or that is not namespaced, is refused; the caller reports the usage
// error and exits.
pub async fn discover_kinds(client: &Client, kinds: &[kube::api::GroupVersionKind]) -> Result<Registry> {
    let mut registry = Registry::new();
    for gvk in kinds {
        let (api_resource, capabilities) = kube::discovery::pinned_kind(client, gvk).await.map_err(|e| {
            anyhow::anyhow!("kind {}/{}/{} is not served: {}", gvk.group, gvk.version, gvk.kind, e)
        })?;
        if capabilities.scope != kube::discovery::Scope::Namespaced {
            bail!("kind {}/{}/{} is not namespaced", gvk.group, gvk.version, gvk.kind);
        }
        let entry = RegistryEntry::new(api_resource);
        info!("discovered kind {:?}", entry);
        registry.push(entry);
    }
    Ok(registry)
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
        .run(reconcile, error_policy, Arc::new(Data { clusters: ClusterClients::single(client), cr_cluster: ClusterId::Primary, field_manager: None, delete_pause_file: None })) // The reconcile function is registered
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
        .run(reconcile, error_policy, Arc::new(Data { clusters: ClusterClients::single(client), cr_cluster: ClusterId::Primary, field_manager: None, delete_pause_file: None })) // The reconcile function is registered
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
// the cluster its wrapper type R::K is bound to (its watch and quorum reads go to
// that cluster's client) and whose requests may target any bound cluster.
// `field_manager`, if set, is sent as the fieldManager of every create, update
// and patch the controller issues, so the API server records the controller by
// that name in the objects' managedFields. `delete_pause_file`, if set, is the
// path whose existence withholds the controller's Delete requests (see
// `deletes_withheld`).
pub async fn run_controller_in_clusters<K, R, E>(
    clusters: ClusterClients,
    field_manager: Option<String>,
    delete_pause_file: Option<String>,
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
    R::K: ResourceWrapper<K> + ClusterBound + Send,
    <R::K as View>::V: CustomResourceView,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    let cr_cluster = <R::K as ClusterBound>::cluster();
    // The primary watch stream is long-lived, so it uses the watch client of its cluster.
    let crs = Api::<K>::all(clusters.watch_client_of(&cr_cluster).await?);

    let reconcile = |cr: Arc<K>, ctx: Arc<Data>| async move {
        return reconcile_with::<K, R, E>(cr, ctx, fault_injection).await;
    };

    info!("starting controller (custom resource in {:?} cluster)", cr_cluster);
    Controller::new(crs, watcher::Config::default())
        .shutdown_on_signal()
        .run(reconcile, error_policy, Arc::new(Data { clusters, cr_cluster, field_manager, delete_pause_file }))
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
    watched_cluster: ClusterId,
    field_manager: Option<String>,
    delete_pause_file: Option<String>,
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
    R::K: ResourceWrapper<K> + ClusterBound + Send,
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
    let cr_cluster = <R::K as ClusterBound>::cluster();
    let crs = Api::<K>::all(clusters.watch_client_of(&cr_cluster).await?);
    let watched = Api::<O>::all(clusters.watch_client_of(&watched_cluster).await?);

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
        .run(reconcile, error_policy, Arc::new(Data { clusters, cr_cluster, field_manager, delete_pause_file }))
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

// ReconcilerFactory builds the reconciler value of one reconcile. The dynamic
// runners hold a factory rather than a reconciler so that a reconciler whose
// behaviour depends on the process's current bindings is built anew, from a
// snapshot taken at the start of the reconcile, and is then fixed for the whole
// of it: the sync reconciler of a kind takes the bound clusters
// (ClusterClients::remote_refs) as its binding set, and the model its conformance
// proof is about is the one of that snapshot (doc/widget_sync_fanout_design.md,
// section 3.2). A reconciler with no such state ignores the argument and returns
// a constant.
pub type ReconcilerFactory<R> = Arc<dyn Fn(ClusterClients) -> BoxFuture<'static, R> + Send + Sync>;

// run_dyn_controller runs a DynReconciler for one kind of the registry in the
// cluster `cr_api` names: the kube-runtime controller is built on
// Api<DynamicObject> with the entry's discovered ApiResource, and every
// triggering object is wrapped as a SyncedObject of that entry and cluster
// before the reconciler sees it. The kind and the cluster are data, so one
// reconciler implementation runs for every kind and binding the process is
// configured with; the runner is stopped by `shutdown` (a binding going away
// stops its controllers) and never by a signal, which the process handles.
// `field_manager`, `delete_pause_file` and `fault_injection` are as in
// run_controller_in_clusters.
pub async fn run_dyn_controller<R, E>(
    clusters: ClusterClients,
    make_reconciler: ReconcilerFactory<R>,
    entry: RegistryEntry,
    cr_cluster: ClusterId,
    field_manager: Option<String>,
    delete_pause_file: Option<String>,
    fault_injection: bool,
    shutdown: impl Future<Output = ()> + Send + Sync + 'static,
) -> Result<()>
where
    R: DynReconciler<K = SyncedObject> + Send + Sync + 'static,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    let api_resource = entry.kube_api_resource().clone();
    let crs = Api::<KubeDynamicObject>::all_with(clusters.watch_client_of(&cr_cluster).await?, &api_resource);
    let entry = Arc::new(entry);
    let reconcile = move |cr: Arc<KubeDynamicObject>, ctx: Arc<Data>| {
        let make_reconciler = make_reconciler.clone();
        let entry = entry.clone();
        async move { reconcile_dyn_with::<R, E>(cr, ctx, make_reconciler, entry, fault_injection).await }
    };

    info!("starting controller for {} (custom resource in {:?} cluster)", api_resource.kind, cr_cluster);
    Controller::new_with(crs, watcher::Config::default(), api_resource.clone())
        .graceful_shutdown_on(shutdown)
        .run(reconcile, error_policy, Arc::new(Data { clusters, cr_cluster, field_manager, delete_pause_file }))
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller for {} terminated", api_resource.kind);
    Ok(())
}

// run_dyn_controller_with_triggers is run_dyn_controller plus a stream of
// objects to reconcile on top of the kind's own watch. It is how the sync
// runner of a kind, which starts at boot and outlives every binding, gets the
// same-name trigger of each binding's mirrors: the binding manager watches the
// mirrors of a bound cluster and sends the outer object of each changed mirror
// into `triggers` (shim_layer::bindings::SameNameTriggers). A trigger for an
// object that does not exist is harmless: the reconcile reads it, finds
// NotFound and ends.
//
// The stream is the only way a running kube-runtime controller takes work from
// outside its own watches; it needs kube's `unstable-runtime-reconcile-on`
// feature (enabled in Cargo.toml). The triggers are a latency optimization
// only: liveness rests on the periodic requeue, so a dropped trigger costs at
// most one requeue interval.
pub async fn run_dyn_controller_with_triggers<R, E>(
    clusters: ClusterClients,
    make_reconciler: ReconcilerFactory<R>,
    entry: RegistryEntry,
    cr_cluster: ClusterId,
    triggers: impl futures::Stream<Item = ObjectRef<KubeDynamicObject>> + Send + 'static,
    field_manager: Option<String>,
    delete_pause_file: Option<String>,
    fault_injection: bool,
    shutdown: impl Future<Output = ()> + Send + Sync + 'static,
) -> Result<()>
where
    R: DynReconciler<K = SyncedObject> + Send + Sync + 'static,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    let api_resource = entry.kube_api_resource().clone();
    let crs = Api::<KubeDynamicObject>::all_with(clusters.watch_client_of(&cr_cluster).await?, &api_resource);
    let entry = Arc::new(entry);
    let reconcile = move |cr: Arc<KubeDynamicObject>, ctx: Arc<Data>| {
        let make_reconciler = make_reconciler.clone();
        let entry = entry.clone();
        async move { reconcile_dyn_with::<R, E>(cr, ctx, make_reconciler, entry, fault_injection).await }
    };

    info!(
        "starting controller for {} (custom resource in {:?} cluster, triggered by the bindings' mirrors)",
        api_resource.kind, cr_cluster
    );
    Controller::new_with(crs, watcher::Config::default(), api_resource.clone())
        .reconcile_on(triggers)
        .graceful_shutdown_on(shutdown)
        .run(reconcile, error_policy, Arc::new(Data { clusters, cr_cluster, field_manager, delete_pause_file }))
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller for {} terminated", api_resource.kind);
    Ok(())
}

// run_dyn_controller_with_same_name_watch is run_dyn_controller plus a
// secondary watch on objects of the kind `watched_entry` in `watched_cluster`:
// a change to one of them triggers a reconcile of the object of the same
// namespace and name of the controller's kind, the same-name trigger of
// run_controller_with_same_name_watch. The watched cluster is fixed at
// construction, so this is the runner of a process whose remote cluster is
// configured once; a controller whose bindings come and go takes the same
// triggers through run_dyn_controller_with_triggers.
pub async fn run_dyn_controller_with_same_name_watch<R, E>(
    clusters: ClusterClients,
    make_reconciler: ReconcilerFactory<R>,
    entry: RegistryEntry,
    cr_cluster: ClusterId,
    watched_entry: RegistryEntry,
    watched_cluster: ClusterId,
    field_manager: Option<String>,
    delete_pause_file: Option<String>,
    fault_injection: bool,
    shutdown: impl Future<Output = ()> + Send + Sync + 'static,
) -> Result<()>
where
    R: DynReconciler<K = SyncedObject> + Send + Sync + 'static,
    R::S: Send,
    R::EReq: Send,
    R::EResp: Send,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    let api_resource = entry.kube_api_resource().clone();
    let watched_resource = watched_entry.kube_api_resource().clone();
    let crs = Api::<KubeDynamicObject>::all_with(clusters.watch_client_of(&cr_cluster).await?, &api_resource);
    let watched = Api::<KubeDynamicObject>::all_with(clusters.watch_client_of(&watched_cluster).await?, &watched_resource);
    let entry = Arc::new(entry);
    let reconcile = move |cr: Arc<KubeDynamicObject>, ctx: Arc<Data>| {
        let make_reconciler = make_reconciler.clone();
        let entry = entry.clone();
        async move { reconcile_dyn_with::<R, E>(cr, ctx, make_reconciler, entry, fault_injection).await }
    };

    info!(
        "starting controller for {} (custom resource in {:?} cluster, watching {} in {:?} cluster by name)",
        api_resource.kind, cr_cluster, watched_resource.kind, watched_cluster
    );
    let mapped_resource = api_resource.clone();
    Controller::new_with(crs, watcher::Config::default(), api_resource.clone())
        .watches_with(watched, watched_resource, watcher::Config::default(), move |o: KubeDynamicObject| {
            o.namespace()
                .map(|ns| ObjectRef::<KubeDynamicObject>::new_with(&o.name_any(), mapped_resource.clone()).within(&ns))
        })
        .graceful_shutdown_on(shutdown)
        .run(reconcile, error_policy, Arc::new(Data { clusters, cr_cluster, field_manager, delete_pause_file }))
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    info!("controller for {} terminated", api_resource.kind);
    Ok(())
}

// ReconcileDriver is the shim's uniform handle on the two reconciler traits:
// the static Reconciler (StaticDriver) and the DynReconciler (DynDriver). The
// reconcile loop (run_reconcile) is written once over it.
trait ReconcileDriver {
    type S;
    type K;
    type EReq: View;
    type EResp: View;

    fn init_state(&self) -> Self::S;
    fn core(&self, cr: &Self::K, resp_o: Option<Response<Self::EResp>>, state: Self::S) -> (Self::S, Option<Request<Self::EReq>>);
    fn done(&self, state: &Self::S) -> bool;
    fn error(&self, state: &Self::S) -> bool;
}

struct StaticDriver<R>(PhantomData<R>);

impl<R> ReconcileDriver for StaticDriver<R>
where
    R: Reconciler,
    <R::K as View>::V: CustomResourceView,
{
    type S = R::S;
    type K = R::K;
    type EReq = R::EReq;
    type EResp = R::EResp;

    fn init_state(&self) -> R::S { R::reconcile_init_state() }
    fn core(&self, cr: &R::K, resp_o: Option<Response<R::EResp>>, state: R::S) -> (R::S, Option<Request<R::EReq>>) { R::reconcile_core(cr, resp_o, state) }
    fn done(&self, state: &R::S) -> bool { R::reconcile_done(state) }
    fn error(&self, state: &R::S) -> bool { R::reconcile_error(state) }
}

struct DynDriver<R>(Arc<R>);

impl<R> ReconcileDriver for DynDriver<R>
where
    R: DynReconciler,
    <R::K as View>::V: DynamicObjectLike,
{
    type S = R::S;
    type K = R::K;
    type EReq = R::EReq;
    type EResp = R::EResp;

    fn init_state(&self) -> R::S { self.0.reconcile_init_state() }
    fn core(&self, cr: &R::K, resp_o: Option<Response<R::EResp>>, state: R::S) -> (R::S, Option<Request<R::EReq>>) { self.0.reconcile_core(cr, resp_o, state) }
    fn done(&self, state: &R::S) -> bool { self.0.reconcile_done(state) }
    fn error(&self, state: &R::S) -> bool { self.0.reconcile_error(state) }
}

// The outcome of the quorum read of the triggering object: the object, or the
// action the reconcile ends with instead.
enum Fetched<K> {
    Object(K),
    End(Action),
}

// fetch_outcome turns the answer of the quorum read into what the reconcile does
// next: a NotFound ends it (the object is gone), any other error retries it.
fn fetch_outcome<K>(result: kube::Result<K>, log_header: &str, cr_name: &str) -> Fetched<K> {
    match result {
        Err(kube_client::error::Error::Api(ErrorResponse { reason, .. })) if &reason == "NotFound" => {
            warn!("{} Custom resource {} not found, end reconcile", log_header, cr_name);
            Fetched::End(Action::await_change())
        }
        Err(err) => {
            warn!("{} Get custom resource {} failed with error: {}, will retry reconcile", log_header, cr_name, err);
            Fetched::End(Action::requeue(Duration::from_secs(60)))
        }
        Ok(cr) => Fetched::Object(cr),
    }
}

// cr_identity reads the name and namespace the triggering object must have.
fn cr_identity(meta: &kube::api::ObjectMeta) -> Result<(String, String), Error> {
    let name = meta.name.clone().ok_or_else(|| {
        Error::ShimLayerError("Custom resource misses \".metadata.name\"".to_string())
    })?;
    let namespace = meta.namespace.clone().ok_or_else(|| {
        Error::ShimLayerError("Custom resources misses \".metadata.namespace\"".to_string())
    })?;
    Ok((name, namespace))
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
    let cr_client = ctx.clusters.client_of(&ctx.cr_cluster).await?;
    let (cr_name, cr_namespace) = cr_identity(cr.meta())?;
    let cr_kind = K::kind(&K::DynamicType::default()).to_string();
    let cr_key = format!("{}/{}/{}", cr_kind, cr_namespace, cr_name);
    let log_header = format!("Reconciling {}:", cr_key);

    let cr_api = Api::<K>::namespaced(cr_client, &cr_namespace);
    // Get the custom resource by a quorum read to Kubernetes' storage (etcd) to get the most updated custom resource
    let cr = match fetch_outcome(cr_api.get(&cr_name).await, &log_header, &cr_name) {
        Fetched::Object(cr) => cr,
        Fetched::End(action) => return Ok(action),
    };
    info!(
        object = %cr_key,
        generation = cr.meta().generation,
        "{} Get cr done",
        log_header
    );
    debug!(
        object = %cr_key,
        "{} cr {}",
        log_header,
        k8s_openapi::serde_json::to_string(&cr).unwrap()
    );

    // Wrap the custom resource with Verus-friendly wrapper type (which has a ghost version, i.e., view)
    let cr_wrapper = R::K::from_kube(cr);
    run_reconcile::<StaticDriver<R>, E>(&StaticDriver::<R>(PhantomData), cr_wrapper, &ctx, &cr_key, &log_header, fault_injection).await
}

// reconcile_dyn_with is reconcile_with for a DynReconciler over the shape: the
// triggering object is read back through the entry's ApiResource in the
// controller's cluster and wrapped as a SyncedObject of that entry and cluster.
// An object whose status is outside the shape (which the boot check makes
// impossible for stored objects, and unmarshal refuses) is left alone until it
// changes.
//
// The reconciler is built first, from the process's state as it is now: what it
// reads there (the bound clusters, for the sync reconciler) is fixed for the
// whole reconcile, so the reconcile conforms to one model rather than to a view
// that changes under it.
pub async fn reconcile_dyn_with<R, E>(
    cr: Arc<KubeDynamicObject>,
    ctx: Arc<Data>,
    make_reconciler: ReconcilerFactory<R>,
    entry: Arc<RegistryEntry>,
    fault_injection: bool,
) -> Result<Action, Error>
where
    R: DynReconciler<K = SyncedObject>,
    E: ExternalShimLayer<R::EReq, R::EResp>,
{
    let reconciler = Arc::new(make_reconciler(ctx.clusters.clone()).await);
    let cr_client = ctx.clusters.client_of(&ctx.cr_cluster).await?;
    let (cr_name, cr_namespace) = cr_identity(cr.meta())?;
    let cr_kind = entry.kube_api_resource().kind.clone();
    let cr_key = format!("{}/{}/{}", cr_kind, cr_namespace, cr_name);
    let log_header = format!("Reconciling {}:", cr_key);

    let cr_api = Api::<KubeDynamicObject>::namespaced_with(cr_client, &cr_namespace, entry.kube_api_resource());
    let cr = match fetch_outcome(cr_api.get(&cr_name).await, &log_header, &cr_name) {
        Fetched::Object(cr) => cr,
        Fetched::End(action) => return Ok(action),
    };
    info!(
        object = %cr_key,
        generation = cr.meta().generation,
        "{} Get cr done",
        log_header
    );
    debug!(
        object = %cr_key,
        "{} cr {}",
        log_header,
        k8s_openapi::serde_json::to_string(&cr).unwrap()
    );

    let cr_wrapper = match SyncedObject::unmarshal(&entry, &ctx.cr_cluster, DynamicObject::from_kube_in(cr, ctx.cr_cluster.clone())) {
        Ok(obj) => obj,
        Err(()) => {
            warn!(
                object = %cr_key,
                "{} the object's status is outside the shape the controller reconciles; it is left alone until it changes",
                log_header
            );
            return Ok(Action::await_change());
        }
    };
    run_reconcile::<DynDriver<R>, E>(&DynDriver(reconciler), cr_wrapper, &ctx, &cr_key, &log_header, fault_injection).await
}

// api_of builds the API handle a request goes through: the namespaced handle of
// the request's resource on the client bound for the resource's cluster. An
// unbound cluster is the error of client_of.
async fn api_of(ctx: &Data, api_resource: &ApiResource, namespace: &str) -> std::result::Result<Api<KubeDynamicObject>, ClusterUnavailable> {
    let client = ctx.clusters.client_for(api_resource).await?;
    Ok(Api::<KubeDynamicObject>::namespaced_with(client, namespace, api_resource.as_kube_ref()))
}

// unavailable_answer logs a request that was not sent, for want of a bound
// client or because the binding is refused, and gives the answer the reconciler
// sees for it (ClusterUnavailable::api_error: Timeout or Forbidden).
fn unavailable_answer(log_header: &str, request: &'static str, cluster: &ClusterId, key: &str, err: ClusterUnavailable) -> APIError {
    let answer = err.api_error();
    warn!(
        object = %key,
        request = request,
        cluster = ?cluster,
        cause = err.cause(),
        error = %err,
        "{} {} {} not sent: {}, answered with {:?}",
        log_header, request, key, err, answer
    );
    answer
}

// run_reconcile is the reconcile loop shared by reconcile_with and
// reconcile_dyn_with; see reconcile_with.
async fn run_reconcile<D, E>(
    driver: &D,
    cr_wrapper: D::K,
    ctx: &Data,
    cr_key: &str,
    log_header: &str,
    fault_injection: bool,
) -> Result<Action, Error>
where
    D: ReconcileDriver,
    E: ExternalShimLayer<D::EReq, D::EResp>,
{
    // Every write below carries the controller's field manager, if it has one.
    let post_params = PostParams { field_manager: ctx.field_manager.clone(), ..PostParams::default() };
    let patch_params = PatchParams { field_manager: ctx.field_manager.clone(), ..PatchParams::default() };

    let mut state = driver.init_state();
    let mut resp_option: Option<Response<D::EResp>> = None;
    // check_fault_timing is only set to true right after the controller issues any create, update or delete request,
    // or external request
    let mut check_fault_timing: bool;

    // Call reconcile_core in a loop
    loop {
        check_fault_timing = false;
        // If reconcile core is done, then breaks the loop
        if driver.done(&state) {
            info!("{} done", log_header);
            break;
        }
        if driver.error(&state) {
            warn!("{} error", log_header);
            return Err(Error::ReconcileCoreError);
        }
        // Feed the current reconcile state and get the new state and the pending request
        let (state_prime, request_option) = driver.core(&cr_wrapper, resp_option, state);
        // Pattern match the request and send requests to the Kubernetes API via kube-rs methods
        match request_option {
            Some(request) => match request {
                Request::KRequest(req) => {
                    let kube_resp: KubeAPIResponse;
                    match req {
                        KubeAPIRequest::GetRequest(get_req) => {
                            let cluster = get_req.api_resource.cluster();
                            let key = get_req.key();
                            let res = match api_of(ctx, &get_req.api_resource, &get_req.namespace).await {
                                Err(e) => Err(unavailable_answer(log_header, "Get", &cluster, &key, e)),
                                Ok(api) => match api.get(&get_req.name).await {
                                    Err(err) => {
                                        log_request_failure(log_header, "Get", &cluster, &key, &err);
                                        Err(kube_error_to_api_error(&err))
                                    }
                                    Ok(obj) => {
                                        info!("{} Get {} done", log_header, key);
                                        Ok(DynamicObject::from_kube_in(obj, cluster))
                                    }
                                },
                            };
                            kube_resp = KubeAPIResponse::GetResponse(KubeGetResponse { res });
                        }
                        KubeAPIRequest::ListRequest(list_req) => {
                            let cluster = list_req.api_resource.cluster();
                            let key = list_req.key();
                            let res = match api_of(ctx, &list_req.api_resource, &list_req.namespace).await {
                                Err(e) => Err(unavailable_answer(log_header, "List", &cluster, &key, e)),
                                Ok(api) => match api.list(&ListParams::default()).await {
                                    Err(err) => {
                                        log_request_failure(log_header, "List", &cluster, &key, &err);
                                        Err(kube_error_to_api_error(&err))
                                    }
                                    Ok(obj_list) => {
                                        // Items of a list carry no apiVersion/kind of their own;
                                        // stamp them from the resource listed so that every
                                        // DynamicObject the reconcilers see names its kind.
                                        let listed = list_req.api_resource.as_kube_ref();
                                        let types = kube::api::TypeMeta { api_version: listed.api_version.clone(), kind: listed.kind.clone() };
                                        info!("{} List {} done", log_header, key);
                                        Ok(obj_list
                                            .items
                                            .into_iter()
                                            .map(|mut obj| {
                                                if obj.types.is_none() {
                                                    obj.types = Some(types.clone());
                                                }
                                                DynamicObject::from_kube_in(obj, cluster.clone())
                                            })
                                            .collect())
                                    }
                                },
                            };
                            kube_resp = KubeAPIResponse::ListResponse(KubeListResponse { res });
                        }
                        KubeAPIRequest::CreateRequest(create_req) => {
                            check_fault_timing = true;
                            let cluster = create_req.api_resource.cluster();
                            let key = create_req.key();
                            let res = match api_of(ctx, &create_req.api_resource, &create_req.namespace).await {
                                Err(e) => Err(unavailable_answer(log_header, "Create", &cluster, &key, e)),
                                Ok(api) => match api.create(&post_params, &create_req.obj.into_kube()).await {
                                    Err(err) => {
                                        log_request_failure(log_header, "Create", &cluster, &key, &err);
                                        Err(kube_error_to_api_error(&err))
                                    }
                                    Ok(obj) => {
                                        info!("{} Create {} done", log_header, key);
                                        Ok(DynamicObject::from_kube_in(obj, cluster))
                                    }
                                },
                            };
                            kube_resp = KubeAPIResponse::CreateResponse(KubeCreateResponse { res });
                        }
                        KubeAPIRequest::DeleteRequest(delete_req) => {
                            check_fault_timing = true;
                            let cluster = delete_req.api_resource.cluster();
                            let key = delete_req.key();
                            let mut dp = DeleteParams::default();
                            if delete_req.preconditions.is_some() {
                                dp = dp.preconditions(
                                    delete_req.preconditions.clone().unwrap().into_kube(),
                                );
                            }
                            let res = if deletes_withheld(ctx.delete_pause_file.as_deref()) {
                                // The operator has paused deletes (deploy/widget_sync/README.md,
                                // "Before restoring the outer cluster"). The request is not sent.
                                // The reconciler is answered with Timeout: in the model's
                                // `drop_req` fault (kubernetes_cluster/spec/cluster.rs) that is
                                // the error of a request the network dropped before it reached
                                // the API server, which is what happened here, and the shim
                                // already produces it for a real timeout. The reconciler ends
                                // this reconcile in Error and is requeued by error_policy.
                                warn!(
                                    object = %key,
                                    request = "Delete",
                                    cluster = ?cluster,
                                    cause = "janitor paused",
                                    "{} Delete {} withheld: the pause file exists, the reconcile is retried",
                                    log_header, key
                                );
                                Err(APIError::Timeout)
                            } else {
                                match api_of(ctx, &delete_req.api_resource, &delete_req.namespace).await {
                                    Err(e) => Err(unavailable_answer(log_header, "Delete", &cluster, &key, e)),
                                    Ok(api) => match api.delete(&delete_req.name, &dp).await {
                                        Err(err) => {
                                            log_request_failure(log_header, "Delete", &cluster, &key, &err);
                                            Err(kube_error_to_api_error(&err))
                                        }
                                        Ok(_) => {
                                            info!("{} Delete {} done", log_header, key);
                                            Ok(())
                                        }
                                    },
                                }
                            };
                            kube_resp = KubeAPIResponse::DeleteResponse(KubeDeleteResponse { res });
                        }
                        KubeAPIRequest::UpdateRequest(update_req) => {
                            check_fault_timing = true;
                            let cluster = update_req.api_resource.cluster();
                            let key = update_req.key();
                            let res = match api_of(ctx, &update_req.api_resource, &update_req.namespace).await {
                                Err(e) => Err(unavailable_answer(log_header, "Update", &cluster, &key, e)),
                                Ok(api) => match api.replace(&update_req.name, &post_params, &update_req.obj.into_kube()).await {
                                    Err(err) => {
                                        log_request_failure(log_header, "Update", &cluster, &key, &err);
                                        Err(kube_error_to_api_error(&err))
                                    }
                                    Ok(obj) => {
                                        info!("{} Update {} done", log_header, key);
                                        Ok(DynamicObject::from_kube_in(obj, cluster))
                                    }
                                },
                            };
                            kube_resp = KubeAPIResponse::UpdateResponse(KubeUpdateResponse { res });
                        }
                        KubeAPIRequest::UpdateStatusRequest(update_status_req) => {
                            check_fault_timing = true;
                            let cluster = update_status_req.api_resource.cluster();
                            let key = update_status_req.key();
                            let res = match api_of(ctx, &update_status_req.api_resource, &update_status_req.namespace).await {
                                Err(e) => Err(unavailable_answer(log_header, "UpdateStatus", &cluster, &key, e)),
                                // Here we assume serde_json always succeed
                                Ok(api) => match api
                                    .replace_status(
                                        &update_status_req.name,
                                        &post_params,
                                        k8s_openapi::serde_json::to_vec(&update_status_req.obj.into_kube()).unwrap(),
                                    )
                                    .await
                                {
                                    Err(err) => {
                                        log_request_failure(log_header, "UpdateStatus", &cluster, &key, &err);
                                        Err(kube_error_to_api_error(&err))
                                    }
                                    Ok(obj) => {
                                        info!("{} UpdateStatus {} done", log_header, key);
                                        Ok(DynamicObject::from_kube_in(obj, cluster))
                                    }
                                },
                            };
                            kube_resp = KubeAPIResponse::UpdateStatusResponse(KubeUpdateStatusResponse { res });
                        }
                        KubeAPIRequest::PatchRequest(patch_req) => {
                            check_fault_timing = true;
                            let cluster = patch_req.api_resource.cluster();
                            let key = patch_req.key();
                            let res = match api_of(ctx, &patch_req.api_resource, &patch_req.namespace).await {
                                Err(e) => Err(unavailable_answer(log_header, "Patch", &cluster, &key, e)),
                                Ok(api) => {
                                    let spec = patch_req
                                        .obj
                                        .into_kube()
                                        .data
                                        .get("spec")
                                        .cloned()
                                        .unwrap_or(serde_json::Value::Null);
                                    let patch = json_patch_with_tests(&patch_req.tests, "/spec", spec);
                                    match api.patch(&patch_req.name, &patch_params, &Patch::<()>::Json(patch)).await {
                                        Err(err) => {
                                            log_request_failure(log_header, "Patch", &cluster, &key, &err);
                                            Err(kube_error_to_api_error(&err))
                                        }
                                        Ok(obj) => {
                                            info!("{} Patch {} done", log_header, key);
                                            Ok(DynamicObject::from_kube_in(obj, cluster))
                                        }
                                    }
                                }
                            };
                            kube_resp = KubeAPIResponse::PatchResponse(KubePatchResponse { res });
                        }
                        KubeAPIRequest::PatchStatusRequest(patch_status_req) => {
                            check_fault_timing = true;
                            let cluster = patch_status_req.api_resource.cluster();
                            let key = patch_status_req.key();
                            let res = match api_of(ctx, &patch_status_req.api_resource, &patch_status_req.namespace).await {
                                Err(e) => Err(unavailable_answer(log_header, "PatchStatus", &cluster, &key, e)),
                                Ok(api) => {
                                    let status = patch_status_req
                                        .obj
                                        .into_kube()
                                        .data
                                        .get("status")
                                        .cloned()
                                        .unwrap_or(serde_json::Value::Null);
                                    let patch = json_patch_with_tests(&patch_status_req.tests, "/status", status);
                                    match api.patch_status(&patch_status_req.name, &patch_params, &Patch::<()>::Json(patch)).await {
                                        Err(err) => {
                                            log_request_failure(log_header, "PatchStatus", &cluster, &key, &err);
                                            Err(kube_error_to_api_error(&err))
                                        }
                                        Ok(obj) => {
                                            info!("{} PatchStatus {} done", log_header, key);
                                            Ok(DynamicObject::from_kube_in(obj, cluster))
                                        }
                                    }
                                }
                            };
                            kube_resp = KubeAPIResponse::PatchStatusResponse(KubePatchStatusResponse { res });
                        }
                        KubeAPIRequest::GetThenDeleteRequest(req) => {
                            check_fault_timing = true;
                            let cluster = req.api_resource.cluster();
                            let key = req.key();
                            kube_resp = KubeAPIResponse::GetThenDeleteResponse(match ctx.clusters.client_for(&req.api_resource).await {
                                Err(e) => KubeGetThenDeleteResponse { res: Err(unavailable_answer(log_header, "GetThenDelete", &cluster, &key, e)) },
                                Ok(client) => transactional_get_then_delete_by_retry(&client, req, log_header.to_string()).await,
                            });
                        }
                        KubeAPIRequest::GetThenUpdateRequest(req) => {
                            check_fault_timing = true;
                            let cluster = req.api_resource.cluster();
                            let key = req.key();
                            kube_resp = KubeAPIResponse::GetThenUpdateResponse(match ctx.clusters.client_for(&req.api_resource).await {
                                Err(e) => KubeGetThenUpdateResponse { res: Err(unavailable_answer(log_header, "GetThenUpdate", &cluster, &key, e)) },
                                Ok(client) => transactional_get_then_update_by_retry(&client, req, log_header.to_string()).await,
                            });
                        }
                        KubeAPIRequest::GetThenUpdateStatusRequest(req) => {
                            check_fault_timing = true;
                            let cluster = req.api_resource.cluster();
                            let key = req.key();
                            kube_resp = KubeAPIResponse::GetThenUpdateStatusResponse(match ctx.clusters.client_for(&req.api_resource).await {
                                Err(e) => KubeGetThenUpdateStatusResponse { res: Err(unavailable_answer(log_header, "GetThenUpdateStatus", &cluster, &key, e)) },
                                Ok(client) => transactional_get_then_update_status_by_retry(&client, req, log_header.to_string()).await,
                            });
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
            let result = crash_or_continue(&ctx.clusters.primary, &cr_key.to_string(), &log_header.to_string()).await;
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
// It carries the clients that communicate with the Kubernetes API servers,
// the cluster that hosts the custom resource this controller reconciles, the
// fieldManager the controller's writes are sent with (None: unset, so the API
// server records them under the client's default manager name), and the path
// of the pause file that withholds the controller's Delete requests (None: no
// gate; see `deletes_withheld`).
pub struct Data {
    pub clusters: ClusterClients,
    pub cr_cluster: ClusterId,
    pub field_manager: Option<String>,
    pub delete_pause_file: Option<String>,
}

// deletes_withheld is the delete-withholding gate: true when a pause file is
// configured and exists at this moment. While it is true, reconcile_with does
// not send Delete requests and answers the reconciler with a Timeout instead,
// which to the verified reconciler is a failed request the model already covers
// (the `drop_req` fault), so no reconciler, model or proof knows about the gate.
// The file is checked per request so that the gate takes effect, and is
// released, without a restart; a mounted ConfigMap key is the intended file.
// The widget sync controller sets the path from $JANITOR_PAUSE_FILE so an
// operator can withhold the janitor's deletes while the outer cluster is
// restored with new uids (deploy/widget_sync/README.md). Withholding a delete
// can only defer cleanup: R3 and R3s promise that stale mirrors are removed,
// and resume once the gate is cleared; nothing promises a delete is sent now.
pub fn deletes_withheld(pause_file: Option<&str>) -> bool {
    match pause_file {
        Some(path) => Path::new(path).exists(),
        None => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The gate is true when the configured file exists and false when it does
    // not or when no path is configured. The dispatch that acts on it is not
    // tested here: it needs a kube client.
    #[test]
    fn deletes_withheld_follows_the_pause_file() {
        let dir = std::env::temp_dir().join(format!("anvil-janitor-pause-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let pause = dir.join("pause");
        let pause_path = pause.to_str().unwrap();

        assert!(!deletes_withheld(None));
        assert!(!deletes_withheld(Some(pause_path)));
        std::fs::write(&pause, b"").unwrap();
        assert!(deletes_withheld(Some(pause_path)));
        assert!(!deletes_withheld(None));
        std::fs::remove_file(&pause).unwrap();
        assert!(!deletes_withheld(Some(pause_path)));

        std::fs::remove_dir_all(&dir).unwrap();
    }
}

// The message the API server puts on a 422 it raises itself while applying a
// JSON patch (apiserver's jsonPatcher answers a failed Apply with
// NewGenericServerResponse(422, ...) and no resource, so the message is this
// fixed string). A 422 raised by validation of the patched object names the
// object and the offending field instead.
const JSON_PATCH_REJECTED_MESSAGE: &str = "the server rejected our request due to an error in our request";

// is_failed_patch_test reports whether `err` is the API server rejecting a JSON
// patch because it could not be applied, which for the patches this shim builds
// (json_patch_with_tests: tests, then one `add`) means a `test` operation failed:
// the object's uid or generation changed between the read the reconciler decided
// on and the write. That is the expected outcome of a lost race, not a fault.
pub fn is_failed_patch_test(err: &kube::Error) -> bool {
    match err {
        kube::Error::Api(ErrorResponse { code: 422, reason, message, .. }) => {
            reason == "Invalid" && message.starts_with(JSON_PATCH_REJECTED_MESSAGE)
        }
        _ => false,
    }
}

fn is_not_found(err: &kube::Error) -> bool {
    matches!(err, kube::Error::Api(ErrorResponse { reason, .. }) if reason == "NotFound")
}

// log_request_failure records a failed API request with the object key, the
// request kind, the cluster and the error as fields. A NotFound answer to a Get
// or Delete is an ordinary outcome the reconcilers branch on (create the missing
// object, treat the deleted one as gone), so it stays at info; every other
// failure is a warning. A Patch or PatchStatus rejected by its own test is
// reported as such: the object changed under the reconciler, which ends this
// reconcile in error and is retried by error_policy.
fn log_request_failure(log_header: &str, request: &'static str, cluster: &ClusterId, key: &str, err: &kube::Error) {
    if is_not_found(err) && (request == "Get" || request == "Delete") {
        info!(
            object = %key,
            request = request,
            cluster = ?cluster,
            "{} {} {} failed with NotFound",
            log_header, request, key
        );
    } else if is_failed_patch_test(err) {
        warn!(
            object = %key,
            request = request,
            cluster = ?cluster,
            cause = "patch test failed",
            error = %err,
            "{} {} {} rejected: the object changed since it was read, the reconcile is retried",
            log_header, request, key
        );
    } else {
        warn!(
            object = %key,
            request = request,
            cluster = ?cluster,
            error = %err,
            "{} {} {} failed",
            log_header, request, key
        );
    }
}

// kube_error_to_api_error translates the API error from kube-rs APIs
// to the form that can be processed by reconcile_core.

// TODO: match more error types.
pub fn kube_error_to_api_error(error: &kube::Error) -> APIError {
    // A JSON patch whose `test` failed comes back as a 422 Invalid, the same
    // status as a schema or webhook rejection. The two differ in what the
    // reconciler should report: a failed test means the object changed since it
    // was read and the next reconcile retries, a rejection is permanent. Only
    // the message tells them apart (is_failed_patch_test), so the failed test is
    // handed to the reconciler as Conflict, the model's transient "the object
    // moved under you" answer, and never as Invalid.
    if is_failed_patch_test(error) {
        return APIError::Conflict;
    }
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
            } else if &error_resp.reason == "Forbidden" {
                APIError::Forbidden
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
        // The request got no answer: the connection failed or the client's request
        // timeout fired, which is what a partition from a remote cluster looks like.
        kube::Error::HyperError(_) | kube::Error::Service(_) => APIError::Timeout,
        _ => APIError::Other,
    }
}
