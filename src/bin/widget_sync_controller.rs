#![allow(unused_imports)]

// The widget sync controller binary. It runs against two clusters:
//   - the primary (outer) cluster, reached through the in-cluster (or default)
//     kubeconfig, where users create Widgets, and
//   - the remote (inner) cluster, reached through the kubeconfig at
//     $REMOTE_KUBECONFIG, where the controller maintains a mirror of each Widget.
// Two verified reconcilers run in one process: the sync reconciler (triggered by
// outer Widgets, and by same-named inner Widgets as a latency optimization) and
// the janitor reconciler (triggered by inner Widgets).
use anyhow::{bail, Result};
use k8s_openapi::api::authorization::v1::{ResourceAttributes, SelfSubjectAccessReview, SelfSubjectAccessReviewSpec};
use kube::api::{Api, PostParams};
use kube::{Client, CustomResourceExt};
use std::env;
use std::process;
use std::time::Duration;
use tracing::{error, info};
use verifiable_controllers::crds::Widget;
use verifiable_controllers::external_shim_layer::VoidExternalShimLayer;
use verifiable_controllers::kubernetes_api_objects::exec::api_resource::ClusterId;
use verifiable_controllers::shim_layer::controller_runtime::{
    remote_clients_from_kubeconfig, run_controller_in_clusters, run_controller_with_same_name_watch,
    ClusterClients,
};
use verifiable_controllers::widget_sync_controller::exec::janitor_reconciler::WidgetJanitorReconciler;
use verifiable_controllers::widget_sync_controller::exec::sync_reconciler::WidgetSyncReconciler;

const USAGE: &str = "usage: widget_sync_controller <export|run|crash>
  export  print the Widget CRD as YAML
  run     run the sync and janitor reconcilers
  crash   run them in crash-testing mode (fault injection)";

const DEFAULT_REMOTE_KUBECONFIG: &str = "/etc/widget-sync/remote-kubeconfig/kubeconfig";

// The fieldManager both reconcilers write with; the API server records it in
// the managedFields of the mirrors and of the outer status.
const FIELD_MANAGER: &str = "widget-sync";

// Requests to the remote cluster time out quickly so that a partition surfaces as
// a failed reconcile (which is retried) instead of a hung one.
const REMOTE_REQUEST_TIMEOUT: Duration = Duration::from_secs(10);

// The verbs the sync and janitor reconcilers issue on Widgets in the remote
// cluster (see deploy/widget_sync/rbac_inner.yaml).
const REMOTE_WIDGET_VERBS: [&str; 6] = ["get", "list", "watch", "create", "patch", "delete"];

// check_remote_access asks the remote cluster, through a SelfSubjectAccessReview
// per verb, whether the mounted credential may perform every verb the reconcilers
// need on widgets.anvil.dev in all namespaces. A missing verb is a deployment
// error: the controller reports it and exits instead of running reconciles that
// can never succeed.
async fn check_remote_access(remote: &Client) -> Result<()> {
    let reviews: Api<SelfSubjectAccessReview> = Api::all(remote.clone());
    let mut denied = Vec::new();
    for verb in REMOTE_WIDGET_VERBS {
        let review = SelfSubjectAccessReview {
            spec: SelfSubjectAccessReviewSpec {
                resource_attributes: Some(ResourceAttributes {
                    group: Some("anvil.dev".to_string()),
                    resource: Some("widgets".to_string()),
                    verb: Some(verb.to_string()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            ..Default::default()
        };
        let status = reviews.create(&PostParams::default(), &review).await?.status.unwrap_or_default();
        if status.allowed {
            info!("remote cluster allows {} on widgets.anvil.dev", verb);
        } else {
            error!(
                "remote cluster denies {} on widgets.anvil.dev: {}",
                verb,
                status.reason.unwrap_or_else(|| "no reason given".to_string())
            );
            denied.push(verb);
        }
    }
    if !denied.is_empty() {
        bail!("remote credential lacks {} on widgets.anvil.dev", denied.join(", "));
    }
    Ok(())
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
            println!("{}", serde_yaml::to_string(&Widget::crd())?);
        }
        "run" | "crash" => {
            let fault_injection = cmd == "crash";
            if fault_injection {
                info!("running widget-sync-controller in crash-testing mode");
            } else {
                info!("running widget-sync-controller");
            }
            let remote_kubeconfig =
                env::var("REMOTE_KUBECONFIG").unwrap_or_else(|_| DEFAULT_REMOTE_KUBECONFIG.to_string());
            let primary = Client::try_default().await?;
            let remote = remote_clients_from_kubeconfig(&remote_kubeconfig, REMOTE_REQUEST_TIMEOUT).await?;
            check_remote_access(&remote.requests).await?;
            let clusters = ClusterClients { primary, remote: Some(remote) };

            let sync = run_controller_with_same_name_watch::<Widget, WidgetSyncReconciler, VoidExternalShimLayer, Widget>(
                clusters.clone(),
                ClusterId::Remote,
                Some(FIELD_MANAGER.to_string()),
                fault_injection,
            );
            let janitor = run_controller_in_clusters::<Widget, WidgetJanitorReconciler, VoidExternalShimLayer>(
                clusters,
                Some(FIELD_MANAGER.to_string()),
                fault_injection,
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
