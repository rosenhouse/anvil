#![allow(unused_imports)]

// The widget sync controller binary. It runs against two clusters:
//   - the primary (outer) cluster, reached through the in-cluster (or default)
//     kubeconfig, where users create Widgets, and
//   - the remote (inner) cluster, reached through the kubeconfig at
//     $REMOTE_KUBECONFIG, where the controller maintains a mirror of each Widget.
// Two verified reconcilers run in one process: the sync reconciler (triggered by
// outer Widgets, and by same-named inner Widgets as a latency optimization) and
// the janitor reconciler (triggered by inner Widgets).
use anyhow::Result;
use kube::{Client, CustomResourceExt};
use std::env;
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

const DEFAULT_REMOTE_KUBECONFIG: &str = "/etc/widget-sync/remote-kubeconfig/kubeconfig";

// Requests to the remote cluster time out quickly so that a partition surfaces as
// a failed reconcile (which is retried) instead of a hung one.
const REMOTE_REQUEST_TIMEOUT: Duration = Duration::from_secs(10);

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let args: Vec<String> = env::args().collect();
    let cmd = args.get(1).cloned().unwrap_or_default();

    if cmd == String::from("export") {
        println!("{}", serde_yaml::to_string(&Widget::crd())?);
    } else if cmd == String::from("run") || cmd == String::from("crash") {
        let fault_injection = cmd == String::from("crash");
        if fault_injection {
            info!("running widget-sync-controller in crash-testing mode");
        } else {
            info!("running widget-sync-controller");
        }
        let remote_kubeconfig =
            env::var("REMOTE_KUBECONFIG").unwrap_or_else(|_| DEFAULT_REMOTE_KUBECONFIG.to_string());
        let primary = Client::try_default().await?;
        let remote = remote_clients_from_kubeconfig(&remote_kubeconfig, REMOTE_REQUEST_TIMEOUT).await?;
        let clusters = ClusterClients { primary, remote: Some(remote) };

        let sync = run_controller_with_same_name_watch::<Widget, WidgetSyncReconciler, VoidExternalShimLayer, Widget>(
            clusters.clone(),
            ClusterId::Remote,
            fault_injection,
        );
        let janitor = run_controller_in_clusters::<Widget, WidgetJanitorReconciler, VoidExternalShimLayer>(
            clusters,
            fault_injection,
        );
        tokio::try_join!(sync, janitor)?;
    } else {
        error!("wrong command; please use \"export\", \"run\" or \"crash\"");
    }
    Ok(())
}
