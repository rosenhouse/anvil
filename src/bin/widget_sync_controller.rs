#![allow(unused_imports)]

// The widget sync controller binary. It runs against two clusters:
//   - the primary (outer) cluster, reached through the in-cluster (or default)
//     kubeconfig, where users create objects of the configured kind, and
//   - the remote (inner) cluster of the one binding this binary is built for,
//     reached through the kubeconfig at $REMOTE_KUBECONFIG, where the controller
//     maintains a mirror of each outer object.
//
// The verified pair is parameterized by a kind and a binding
// (doc/widget_sync_fanout_design.md, sections 2.1 and 3.4): the sync reconciler
// is one controller per kind and the janitor one controller per (kind, binding).
// This binary instantiates them at one kind and one binding; the kind flags of
// section 2.1 and the binding manager of section 3.4 are the follow-up issues.
// Two verified reconcilers run in one process: the sync reconciler (triggered by
// outer objects, and by same-named mirrors as a latency optimization) and the
// janitor reconciler (triggered by the binding's mirrors).
use anyhow::{bail, Result};
use k8s_openapi::api::authorization::v1::{ResourceAttributes, SelfSubjectAccessReview, SelfSubjectAccessReviewSpec};
use kube::api::{Api, PostParams};
use kube::Client;
use std::env;
use std::fs;
use std::process;
use std::time::Duration;
use tracing::{error, info, warn};
use verifiable_controllers::external_shim_layer::VoidExternalShimLayer;
use verifiable_controllers::kubernetes_api_objects::exec::api_resource::{ClusterId, ClusterRef};
use verifiable_controllers::kubernetes_api_objects::exec::registry::RegistryEntry;
use verifiable_controllers::kubernetes_api_objects::exec::synced_object::ClusterSelectorExec;
use verifiable_controllers::shim_layer::controller_runtime::{
    discover_kinds, remote_clients_from_kubeconfig, run_dyn_controller, run_dyn_controller_with_same_name_watch,
    ClusterClients,
};
use verifiable_controllers::shim_layer::crd_shape::check_crd;
use verifiable_controllers::shim_layer::kind_config::{ClusterSelector, KindConfig};
use verifiable_controllers::widget_sync_controller::exec::janitor_reconciler::JanitorReconciler;
use verifiable_controllers::widget_sync_controller::exec::sync_reconciler::SyncReconciler;
use verifiable_controllers::widget_sync_controller::trusted::exec_types::SyncKindExec;

const USAGE: &str = "usage: widget_sync_controller <export|run|crash>
  export  print the demo CRDs as YAML
  run     run the sync and janitor reconcilers
  crash   run them in crash-testing mode (fault injection)";

// The one kind this binary is built for, in the syntax of the `--kind` flag of
// doc/widget_sync_fanout_design.md, section 2.1. Taking it from the command line
// is issue #41; until then the pair is instantiated here.
const KIND: &str = "anvil.dev/v1/Widget:field:spec.clusterName";

// The one binding this binary is built for: the inner cluster named `inner` of
// the namespace `default`. Its credential is $REMOTE_KUBECONFIG. Discovering
// bindings from Secrets is issue #40.
const BINDING_NAMESPACE: &str = "default";
const BINDING_NAME: &str = "inner";

const DEFAULT_REMOTE_KUBECONFIG: &str = "/etc/widget-sync/remote-kubeconfig/kubeconfig";

// The fieldManager both reconcilers write with; the API server records it in
// the managedFields of the mirrors and of the outer status.
const FIELD_MANAGER: &str = "widget-sync";

// Requests to the remote cluster time out quickly so that a partition surfaces as
// a failed reconcile (which is retried) instead of a hung one.
const REMOTE_REQUEST_TIMEOUT: Duration = Duration::from_secs(10);

// If READY_FILE is set, the file is created once the remote credential has
// passed check_remote_access and the reconcilers are about to start, and is
// removed before the check so that a restarted container does not inherit the
// previous run's signal. deploy/widget_sync/deploy_local.yaml probes it as the
// pod's readiness. Nothing else is signalled: the binary has no health endpoint.
const READY_FILE_ENV: &str = "READY_FILE";

// If JANITOR_PAUSE_FILE is set, the shim withholds every Delete request of this
// process while a file exists at that path, answering the reconciler with a
// Timeout instead (controller_runtime::deletes_withheld). The janitor is the
// only reconciler here that deletes. deploy/widget_sync/deploy_local.yaml points
// it at the key `pause` of the ConfigMap widget-sync-janitor, so an operator can
// pause the janitor around a restore of the outer cluster that issues new uids
// (deploy/widget_sync/README.md, "Before restoring the outer cluster").
const JANITOR_PAUSE_FILE_ENV: &str = "JANITOR_PAUSE_FILE";

// The verbs the sync and janitor reconcilers issue on the configured kind in the
// remote cluster (see deploy/widget_sync/rbac_inner.yaml).
const REMOTE_VERBS: [&str; 6] = ["get", "list", "watch", "create", "patch", "delete"];

// check_remote_access asks the remote cluster, through a SelfSubjectAccessReview
// per verb, whether the mounted credential may perform every verb the reconcilers
// need on the configured resource in all namespaces. A missing verb is a
// deployment error: the controller reports it and exits instead of running
// reconciles that can never succeed.
async fn check_remote_access(remote: &Client, group: &str, plural: &str) -> Result<()> {
    let reviews: Api<SelfSubjectAccessReview> = Api::all(remote.clone());
    let resource = format!("{}.{}", plural, group);
    let mut denied = Vec::new();
    for verb in REMOTE_VERBS {
        let review = SelfSubjectAccessReview {
            spec: SelfSubjectAccessReviewSpec {
                resource_attributes: Some(ResourceAttributes {
                    group: Some(group.to_string()),
                    resource: Some(plural.to_string()),
                    verb: Some(verb.to_string()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            ..Default::default()
        };
        let status = reviews.create(&PostParams::default(), &review).await?.status.unwrap_or_default();
        if status.allowed {
            info!("remote cluster allows {} on {}", verb, resource);
        } else {
            error!(
                "remote cluster denies {} on {}: {}",
                verb,
                resource,
                status.reason.unwrap_or_else(|| "no reason given".to_string())
            );
            denied.push(verb);
        }
    }
    if !denied.is_empty() {
        bail!("remote credential lacks {} on {}", denied.join(", "), resource);
    }
    Ok(())
}

// The exec twin of the configured kind: the discovered registry entry, which
// ties the kind and a cluster to a model kind, and the cluster selector the
// reconcilers read an object's cluster with. Built afresh per reconciler so
// that neither has to be cloned.
fn sync_kind(entry: &RegistryEntry, config: &KindConfig) -> SyncKindExec {
    let selector = match &config.selector {
        ClusterSelector::Name => ClusterSelectorExec::Name,
        ClusterSelector::Field(path) => ClusterSelectorExec::Field(path.clone()),
    };
    SyncKindExec { entry: entry.clone(), selector }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    // A missing or unknown command is a usage error: say so and exit non-zero
    // instead of panicking on args[1] or silently doing nothing.
    let cmd = match args.get(1) {
        Some(cmd) => cmd.as_str(),
        None => {
            eprintln!("{}", USAGE);
            process::exit(2);
        }
    };

    match cmd {
        "export" => {
            for crd in verifiable_controllers::crds::demo_crds() {
                println!("---");
                print!("{}", serde_yaml::to_string(&crd)?);
            }
        }
        "run" | "crash" => {
            let fault_injection = cmd == "crash";
            if fault_injection {
                info!("running widget-sync-controller in crash-testing mode");
            } else {
                info!("running widget-sync-controller");
            }
            let kind_config: KindConfig = KIND.parse()?;
            let remote_kubeconfig =
                env::var("REMOTE_KUBECONFIG").unwrap_or_else(|_| DEFAULT_REMOTE_KUBECONFIG.to_string());
            let ready_file = env::var(READY_FILE_ENV).ok();
            let janitor_pause_file = env::var(JANITOR_PAUSE_FILE_ENV).ok();
            match &janitor_pause_file {
                Some(path) => info!("deletes are withheld while {} exists", path),
                None => info!("{} is unset; deletes cannot be paused", JANITOR_PAUSE_FILE_ENV),
            }
            if let Some(path) = &ready_file {
                // Ignore a missing file; anything else is reported when it is created.
                let _ = fs::remove_file(path);
            }
            let primary = Client::try_default().await?;

            // Discovery in the outer cluster resolves the plural and confirms the
            // kind is served and namespaced; the shape check then confirms the CRD
            // has the fields the reconcilers read and write
            // (doc/widget_sync_fanout_design.md, section 2.2). Both are boot
            // errors: a kind that is not there, or whose CRD is the wrong shape,
            // can never be reconciled.
            let registry = discover_kinds(&primary, &[kind_config.gvk()]).await?;
            let entry = registry.entry(0).clone();
            let plural = entry.kube_api_resource().plural.clone();
            check_crd(&primary, &kind_config, &plural).await?;
            info!("kind {} has the shape the sync controller needs", kind_config);

            let remote = remote_clients_from_kubeconfig(&remote_kubeconfig, REMOTE_REQUEST_TIMEOUT).await?;
            check_remote_access(&remote.requests, &kind_config.group, &plural).await?;
            // The mirrors are bound to the pair's one binding; the remote clients
            // are registered under it so that requests tagged with it find them.
            let binding = ClusterRef::new(BINDING_NAMESPACE.to_string(), BINDING_NAME.to_string());
            let inner_cluster = ClusterId::Remote(binding.clone());
            let clusters = ClusterClients::with_remote(primary, binding.clone(), remote).await;
            if let Some(path) = &ready_file {
                match fs::write(path, b"") {
                    Ok(()) => info!("ready: created {}", path),
                    Err(e) => warn!("could not create ready file {}: {}; the pod will not become ready", path, e),
                }
            }

            // One shutdown signal for both controllers: on SIGINT each stops
            // taking new work and drains, as `shutdown_on_signal` did.
            let (tx, shutdown_rx) = tokio::sync::watch::channel(false);
            tokio::spawn(async move {
                if tokio::signal::ctrl_c().await.is_ok() {
                    info!("shutting down");
                }
                let _ = tx.send(true);
            });
            let mut sync_shutdown_rx = shutdown_rx.clone();
            let sync_shutdown = async move {
                let _ = sync_shutdown_rx.changed().await;
            };
            let mut janitor_shutdown_rx = shutdown_rx;
            let janitor_shutdown = async move {
                let _ = janitor_shutdown_rx.changed().await;
            };

            // The sync reconciler runs on the outer copies and is woken by a
            // same-named mirror of the binding as well; the janitor runs on the
            // binding's mirrors. The sync reconciler never deletes (its
            // guarantee), so the pause file only ever acts on the janitor; it is
            // given to both so that the gate holds for every Delete this process
            // could send.
            let sync = run_dyn_controller_with_same_name_watch::<SyncReconciler, VoidExternalShimLayer>(
                clusters.clone(),
                SyncReconciler { kind: sync_kind(&entry, &kind_config) },
                entry.clone(),
                ClusterId::Primary,
                entry.clone(),
                inner_cluster.clone(),
                Some(FIELD_MANAGER.to_string()),
                janitor_pause_file.clone(),
                fault_injection,
                sync_shutdown,
            );
            let janitor = run_dyn_controller::<JanitorReconciler, VoidExternalShimLayer>(
                clusters,
                JanitorReconciler { kind: sync_kind(&entry, &kind_config), binding },
                entry,
                inner_cluster,
                Some(FIELD_MANAGER.to_string()),
                janitor_pause_file,
                fault_injection,
                janitor_shutdown,
            );
            tokio::try_join!(sync, janitor)?;
        }
        other => {
            eprintln!("unknown command {:?}\n{}", other, USAGE);
            process::exit(2);
        }
    }
    Ok(())
}
