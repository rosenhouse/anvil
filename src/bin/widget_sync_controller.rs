#![allow(unused_imports)]

// The widget sync controller binary. It runs against many clusters:
//   - the primary (outer) cluster, reached through the in-cluster (or default)
//     kubeconfig, where users create objects of the configured kind, and
//   - the inner cluster of every binding, reached through the kubeconfig in the
//     Secret `<clusterName>-kubeconfig` of the binding's namespace, where the
//     controller maintains a mirror of each outer object.
//
// The verified pair is parameterized by a kind and a binding
// (doc/widget_sync_fanout_design.md, sections 2.1 and 3.4): the sync reconciler
// is one controller per kind and the janitor one controller per (kind, binding).
// This binary instantiates the pair at one kind (the kind flags of section 2.1
// are the follow-up issue) and at every binding the binding manager finds. Two
// kinds of verified reconciler run in one process: the sync reconciler
// (triggered by outer objects, and by same-named mirrors as a latency
// optimization), started at boot and outliving every binding, and the janitor
// (triggered by one binding's mirrors), started and stopped with its binding.
use anyhow::{bail, Result};
use kube::Client;
use std::env;
use std::fs;
use std::process;
use std::sync::Arc;
use std::time::Duration;
use tracing::{error, info, warn};
use verifiable_controllers::external_shim_layer::VoidExternalShimLayer;
use verifiable_controllers::kubernetes_api_objects::exec::api_resource::{ClusterId, ClusterRef};
use verifiable_controllers::kubernetes_api_objects::exec::registry::RegistryEntry;
use verifiable_controllers::kubernetes_api_objects::exec::synced_object::ClusterSelectorExec;
use verifiable_controllers::shim_layer::bindings::{
    outer_cluster_id, same_name_triggers, BindingKind, BindingManager,
};
use verifiable_controllers::shim_layer::controller_runtime::{
    discover_kinds, run_dyn_controller, run_dyn_controller_with_triggers, ClusterClients,
};
use verifiable_controllers::shim_layer::crd_shape::check_crd;
use verifiable_controllers::shim_layer::kind_config::{ClusterSelector, KindConfig};
use verifiable_controllers::widget_sync_controller::exec::janitor_reconciler::JanitorReconciler;
use verifiable_controllers::widget_sync_controller::exec::sync_reconciler::SyncReconciler;
use verifiable_controllers::widget_sync_controller::trusted::exec_types::SyncKindExec;

const USAGE: &str = "usage: widget_sync_controller <export|run|crash> [--outer-cluster-id <id>]
  export  print the demo CRDs as YAML
  run     run the sync and janitor reconcilers
  crash   run them in crash-testing mode (fault injection)

  --outer-cluster-id <id>  the identity the claim of each inner cluster records
                           (default: the uid of the outer kube-system namespace;
                           env OUTER_CLUSTER_ID)";

// The one kind this binary is built for, in the syntax of the `--kind` flag of
// doc/widget_sync_fanout_design.md, section 2.1. Taking it from the command line
// is issue #41; until then the pair is instantiated here.
const KIND: &str = "anvil.dev/v1/Widget:field:spec.clusterName";

// The fieldManager both reconcilers write with; the API server records it in
// the managedFields of the mirrors and of the outer status.
const FIELD_MANAGER: &str = "widget-sync";

// Requests to an inner cluster time out quickly so that a partition surfaces as
// a failed reconcile (which is retried) instead of a hung one. The binding
// manager's own requests (the access check, the claim) are bounded the same way.
const REMOTE_REQUEST_TIMEOUT: Duration = Duration::from_secs(10);

// The identity the claim in each inner cluster records as its owner
// (doc/widget_sync_fanout_design.md, section 1.3). Unset, it is the uid of the
// outer cluster's kube-system namespace; an operator overrides it after a
// restore that recreated that namespace.
const OUTER_CLUSTER_ID_ENV: &str = "OUTER_CLUSTER_ID";
const OUTER_CLUSTER_ID_FLAG: &str = "--outer-cluster-id";

// If READY_FILE is set, the file is created once the boot checks have passed and
// the sync runners are started, and is removed before the checks so that a
// restarted container does not inherit the previous run's signal.
// deploy/widget_sync/deploy_local.yaml probes it as the pod's readiness. The
// bindings are deliberately not part of it: an inner cluster that is down must
// not keep the pod from becoming ready (section 1.4).
const READY_FILE_ENV: &str = "READY_FILE";

// If JANITOR_PAUSE_FILE is set, the shim withholds every Delete request of this
// process while a file exists at that path, answering the reconciler with a
// Timeout instead (controller_runtime::deletes_withheld). The janitor is the
// only reconciler here that deletes. deploy/widget_sync/deploy_local.yaml points
// it at the key `pause` of the ConfigMap widget-sync-janitor, so an operator can
// pause the janitor around a restore of the outer cluster that issues new uids
// (deploy/widget_sync/README.md, "Before restoring the outer cluster").
const JANITOR_PAUSE_FILE_ENV: &str = "JANITOR_PAUSE_FILE";

// The verbs the sync and janitor reconcilers issue on the configured kind in an
// inner cluster (see deploy/widget_sync/rbac_inner.yaml). The binding manager
// asks each binding's credential for them, in the binding's namespace, before it
// binds the cluster.
const REMOTE_VERBS: [&str; 6] = ["get", "list", "watch", "create", "patch", "delete"];

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

// The value of `--outer-cluster-id`, if the flag is given; an unknown flag is a
// usage error, as an unknown command is.
fn outer_cluster_id_flag(args: &[String]) -> Result<Option<String>> {
    let mut id = None;
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        if arg != OUTER_CLUSTER_ID_FLAG {
            bail!("unknown argument {:?}", arg);
        }
        match rest.next() {
            Some(value) => id = Some(value.clone()),
            None => bail!("{} needs a value", OUTER_CLUSTER_ID_FLAG),
        }
    }
    Ok(id)
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
            let cluster_id_override = match outer_cluster_id_flag(&args[2..]) {
                Ok(id) => id.or_else(|| env::var(OUTER_CLUSTER_ID_ENV).ok()),
                Err(e) => {
                    eprintln!("{}\n{}", e, USAGE);
                    process::exit(2);
                }
            };
            let kind_config: KindConfig = KIND.parse()?;
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
            // can never be reconciled. An inner cluster, by contrast, is never a
            // boot error: it is one binding, and the binding manager degrades it.
            let registry = discover_kinds(&primary, &[kind_config.gvk()]).await?;
            let entry = registry.entry(0).clone();
            let plural = entry.kube_api_resource().plural.clone();
            check_crd(&primary, &kind_config, &plural).await?;
            info!("kind {} has the shape the sync controller needs", kind_config);
            let outer_id = outer_cluster_id(&primary, cluster_id_override).await?;

            let clusters = ClusterClients::new(primary);

            // One shutdown signal for the whole process: on SIGINT the sync
            // runners and the binding manager stop taking new work and drain,
            // and the manager stops every binding's runners.
            let (tx, shutdown_rx) = tokio::sync::watch::channel(false);
            tokio::spawn(async move {
                if tokio::signal::ctrl_c().await.is_ok() {
                    info!("shutting down");
                }
                let _ = tx.send(true);
            });
            let signalled = |mut rx: tokio::sync::watch::Receiver<bool>| async move {
                let _ = rx.changed().await;
            };

            // The sync reconciler of the kind runs on the outer copies and is
            // independent of the bindings: it routes each object to the binding
            // its cluster field names, and an unbound one is answered by the shim.
            // Its trigger stream carries the same-name triggers of every bound
            // cluster's mirrors (shim_layer::bindings).
            let (triggers, trigger_stream) = same_name_triggers();
            let sync = tokio::spawn(run_dyn_controller_with_triggers::<SyncReconciler, VoidExternalShimLayer>(
                clusters.clone(),
                SyncReconciler { kind: sync_kind(&entry, &kind_config) },
                entry.clone(),
                ClusterId::Primary,
                trigger_stream,
                Some(FIELD_MANAGER.to_string()),
                janitor_pause_file.clone(),
                fault_injection,
                signalled(shutdown_rx.clone()),
            ));

            // The janitors of a binding, started by the binding manager once the
            // binding's credential and claim are good and stopped when its Secret
            // changes or goes away. The sync reconciler never deletes (its
            // guarantee), so the pause file only ever acts on the janitor; it is
            // given to both so that the gate holds for every Delete this process
            // could send.
            let janitor_clusters = clusters.clone();
            let janitor_entry = entry.clone();
            let janitor_kind_config = kind_config.clone();
            let janitor_pause = janitor_pause_file.clone();
            let start_runners = Arc::new(move |binding: &ClusterRef, stop: tokio::sync::watch::Receiver<bool>| {
                let clusters = janitor_clusters.clone();
                let entry = janitor_entry.clone();
                let reconciler = JanitorReconciler {
                    kind: sync_kind(&janitor_entry, &janitor_kind_config),
                    binding: binding.clone(),
                };
                let cluster = ClusterId::Remote(binding.clone());
                let field_manager = Some(FIELD_MANAGER.to_string());
                let pause_file = janitor_pause.clone();
                let binding = binding.clone();
                tokio::spawn(async move {
                    let stopped = async move {
                        let mut stop = stop;
                        let _ = stop.changed().await;
                    };
                    if let Err(e) = run_dyn_controller::<JanitorReconciler, VoidExternalShimLayer>(
                        clusters,
                        reconciler,
                        entry,
                        cluster,
                        field_manager,
                        pause_file,
                        fault_injection,
                        stopped,
                    )
                    .await
                    {
                        warn!("the janitor of binding {}/{} stopped: {}", binding.namespace, binding.name, e);
                    }
                });
            });

            let kinds = vec![BindingKind {
                entry: entry.clone(),
                group: kind_config.group.clone(),
                plural: plural.clone(),
                triggers,
            }];
            let manager = BindingManager::new(
                clusters,
                kinds,
                REMOTE_VERBS.iter().map(|v| v.to_string()).collect(),
                outer_id,
                REMOTE_REQUEST_TIMEOUT,
                start_runners,
            );
            let bindings = tokio::spawn(manager.run(signalled(shutdown_rx)));

            // Ready: the kind is served and has the right shape, and the sync
            // runners are up. Whether any binding is usable is not part of it.
            if let Some(path) = &ready_file {
                match fs::write(path, b"") {
                    Ok(()) => info!("ready: created {}", path),
                    Err(e) => warn!("could not create ready file {}: {}; the pod will not become ready", path, e),
                }
            }

            let (sync, bindings) = tokio::try_join!(sync, bindings)?;
            sync?;
            bindings?;
        }
        other => {
            eprintln!("unknown command {:?}\n{}", other, USAGE);
            process::exit(2);
        }
    }
    Ok(())
}
