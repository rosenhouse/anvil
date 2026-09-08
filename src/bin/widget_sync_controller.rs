#![allow(unused_imports)]

// The widget sync controller binary. It runs against many clusters:
//   - the primary (outer) cluster, reached through the in-cluster (or default)
//     kubeconfig, where users create objects of the configured kinds, and
//   - the inner cluster of every binding, reached through the kubeconfig in the
//     Secret `<clusterName>-kubeconfig` of the binding's namespace, where the
//     controller maintains a mirror of each outer object.
//
// The verified pair is parameterized by a kind and a binding
// (doc/widget_sync_fanout_design.md, sections 2.1 and 3.4): the sync reconciler
// is one controller per kind and the janitor one controller per (kind, binding).
// This binary instantiates them at the kinds of the `--kind` flags and at every
// binding the binding manager finds. Two kinds of verified reconciler run in one
// process: the sync reconciler of a kind (triggered by outer objects of it, and
// by same-named mirrors as a latency optimization), started at boot and
// outliving every binding, and the janitor of a (kind, binding), started and
// stopped with its binding.
use anyhow::{bail, Result};
use kube::Client;
use std::env;
use std::fs;
use std::future::Future;
use std::pin::Pin;
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
use verifiable_controllers::shim_layer::crd_shape::{check_crd, check_kind_name, CrdCheckError};
use verifiable_controllers::shim_layer::kind_config::{ClusterSelector, KindConfig};
use verifiable_controllers::widget_sync_controller::exec::janitor_reconciler::JanitorReconciler;
use verifiable_controllers::widget_sync_controller::exec::sync_reconciler::SyncReconciler;
use verifiable_controllers::widget_sync_controller::trusted::exec_types::SyncKindExec;

const USAGE: &str = "usage: widget_sync_controller export
       widget_sync_controller <run|crash> --kind <group>/<version>/<Kind>:<selector> ...
  export  print the demo CRDs as YAML
  run     run one sync reconciler per configured kind, and one janitor per
          configured kind and bound inner cluster
  crash   run them in crash-testing mode (fault injection)
  --kind  a kind and the field that names an object's cluster, repeated; at
          least one is required. The selector is `name` (metadata.name is the
          cluster name) or `field:<path>` (a required, immutable string field of
          the spec), for example
            --kind anvil.dev/v1/Widget:field:spec.clusterName
            --kind anvil.dev/v1/Gadget:name
  --outer-cluster-id <id>
          the identity the claim of each inner cluster records as its owner
          (default: the uid of the outer kube-system namespace; env
          OUTER_CLUSTER_ID)";

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

// The verbs the sync and janitor reconcilers issue on a configured kind in an
// inner cluster (see deploy/widget_sync/rbac_inner.yaml). The binding manager
// asks each binding's credential for them, in the binding's namespace, before it
// binds the cluster; a denial makes that one binding refused, never a process
// that exits.
const REMOTE_VERBS: [&str; 6] = ["get", "list", "watch", "create", "patch", "delete"];

// The flags of `run` and `crash`: the kinds, in the order they were given, and
// the outer cluster id if it was overridden. `--kind <value>` and
// `--kind=<value>` are both accepted, as for the echo controller, so one list
// can be pasted between the two binaries. Anything else on the command line is a
// usage error.
#[derive(Debug)]
struct Flags {
    kinds: Vec<String>,
    outer_cluster_id: Option<String>,
}

fn parse_flags(args: &[String]) -> Result<Flags, String> {
    let mut flags = Flags { kinds: Vec::new(), outer_cluster_id: None };
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--kind" => {
                i += 1;
                match args.get(i) {
                    Some(value) => flags.kinds.push(value.clone()),
                    None => return Err("--kind needs a value".to_string()),
                }
            }
            arg if arg.starts_with("--kind=") => flags.kinds.push(arg["--kind=".len()..].to_string()),
            "--outer-cluster-id" => {
                i += 1;
                match args.get(i) {
                    Some(value) => flags.outer_cluster_id = Some(value.clone()),
                    None => return Err("--outer-cluster-id needs a value".to_string()),
                }
            }
            arg if arg.starts_with("--outer-cluster-id=") => {
                flags.outer_cluster_id = Some(arg["--outer-cluster-id=".len()..].to_string())
            }
            arg => return Err(format!("unexpected argument {:?}", arg)),
        }
        i += 1;
    }
    Ok(flags)
}

// The configured kinds: the `--kind` flags, parsed (shim_layer::kind_config). An
// empty list is a usage error, because a process with no kind would watch
// nothing; so are a malformed flag and a repeated kind, since a kind named twice
// would start two sync controllers on the same objects, which the proofs exclude.
fn configured_kinds(args: &[String]) -> Result<Vec<KindConfig>, String> {
    let flags = parse_flags(args)?;
    if flags.kinds.is_empty() {
        return Err("no --kind given; at least one kind is required".to_string());
    }
    let kinds = KindConfig::parse_all(flags.kinds).map_err(|e| e.to_string())?;
    for (i, kind) in kinds.iter().enumerate() {
        if kinds[..i].iter().any(|earlier| earlier.gvk() == kind.gvk()) {
            return Err(format!("kind {}/{}/{} is configured twice", kind.group, kind.version, kind.kind));
        }
    }
    Ok(kinds)
}

// What a refused kind prints: the flag it came from and, for a shape failure,
// one line per failing row of the table of doc/widget_sync_fanout_design.md,
// section 2.2. The boot check runs before any controller starts, so a refused
// kind is a usage error and the process exits with status 2.
fn refused_kind(kind: &KindConfig, err: &impl std::fmt::Display) -> String {
    format!("--kind {}: {}", kind, err)
}

// The exec twin of a configured kind: the discovered registry entry, which ties
// the kind and a cluster to a model kind, and the cluster selector the
// reconcilers read an object's cluster with. Built afresh per reconciler so
// that neither has to be cloned.
fn sync_kind(entry: &RegistryEntry, config: &KindConfig) -> SyncKindExec {
    let selector = match &config.selector {
        ClusterSelector::Name => ClusterSelectorExec::Name,
        ClusterSelector::Field(path) => ClusterSelectorExec::Field(path.clone()),
    };
    SyncKindExec { entry: entry.clone(), selector }
}

// The signals that mean stop. SIGTERM is the one that matters in a cluster: it
// is what the kubelet sends first when a pod is deleted, a Deployment rolls or
// a node drains, and only after `terminationGracePeriodSeconds` does SIGKILL
// follow. This process is PID 1 in its container, and PID 1 has no default
// action for SIGTERM, so a binary that waits on ctrl_c alone ignores it and
// every restart costs the whole grace period. SIGINT is kept for a run from a
// terminal.
#[cfg(unix)]
async fn termination_signal() {
    use tokio::signal::unix::{signal, SignalKind};
    let mut terminate = match signal(SignalKind::terminate()) {
        Ok(terminate) => terminate,
        Err(e) => {
            // Nothing can be done about it, but say so: the pod would take the
            // full grace period to restart and the reason would be invisible.
            warn!("cannot listen for SIGTERM ({}); only SIGINT will shut this process down", e);
            let _ = tokio::signal::ctrl_c().await;
            return;
        }
    };
    tokio::select! {
        _ = tokio::signal::ctrl_c() => info!("SIGINT received"),
        _ = terminate.recv() => info!("SIGTERM received"),
    }
}

#[cfg(not(unix))]
async fn termination_signal() {
    let _ = tokio::signal::ctrl_c().await;
    info!("interrupt received");
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
            // The kinds and the cluster id come from the command line; a bad or
            // missing flag is a usage error, reported before any client is built.
            let (kinds, cluster_id_override) = match (configured_kinds(&args[2..]), parse_flags(&args[2..])) {
                (Ok(kinds), Ok(flags)) => {
                    (kinds, flags.outer_cluster_id.or_else(|| env::var(OUTER_CLUSTER_ID_ENV).ok()))
                }
                (Err(message), _) | (_, Err(message)) => {
                    eprintln!("{}\n{}", message, USAGE);
                    process::exit(2);
                }
            };
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
            // boot error: it is one binding, which the manager degrades and retries.
            let gvks: Vec<_> = kinds.iter().map(|k| k.gvk()).collect();
            let registry = match discover_kinds(&primary, &gvks).await {
                Ok(registry) => registry,
                Err(e) => {
                    // A kind that is not served, or is cluster-scoped, is as much
                    // a usage error as a CRD of the wrong shape; report it the
                    // same way rather than as a generic startup failure.
                    error!("{}", e);
                    eprintln!("{}", e);
                    process::exit(2);
                }
            };
            // (kind, its registry entry, its plural), in configuration order.
            let mut configured = Vec::with_capacity(kinds.len());
            for (i, kind) in kinds.iter().enumerate() {
                let entry = registry.entry(i).clone();
                let plural = entry.kube_api_resource().plural.clone();
                // The exec side of model_kind's injectivity hypothesis: the CRD
                // name is what a mirror's model kind is built from, with '@'
                // and '/' as its separators. A DNS name has neither, so this is
                // defensive, but it is a hypothesis the proofs rest on.
                if let Err(e) = check_kind_name(&entry.crd_name()) {
                    let message = refused_kind(kind, &e);
                    error!("{}", message);
                    eprintln!("{}", message);
                    process::exit(2);
                }
                if let Err(e) = check_crd(&primary, kind, &plural).await {
                    // Nothing has been started yet: print the failing rows and
                    // exit as on any other usage error.
                    let message = refused_kind(kind, &e);
                    error!("{}", message);
                    eprintln!("{}", message);
                    process::exit(2);
                }
                info!("kind {} has the shape the sync controller needs", kind);
                configured.push((kind.clone(), entry, plural));
            }
            let outer_id = outer_cluster_id(&primary, cluster_id_override).await?;

            let clusters = ClusterClients::new(primary);

            // One shutdown signal for the whole process: on SIGTERM (or SIGINT)
            // the sync runners and the binding manager stop taking new work and
            // drain, and the manager stops every binding's runners.
            let (tx, shutdown_rx) = tokio::sync::watch::channel(false);
            tokio::spawn(async move {
                termination_signal().await;
                info!("shutting down");
                let _ = tx.send(true);
            });
            let signalled = |mut rx: tokio::sync::watch::Receiver<bool>| async move {
                let _ = rx.changed().await;
            };

            // One sync reconciler per configured kind. It runs on the outer
            // copies of its kind and is independent of the bindings: it routes
            // each object to the binding its cluster selector names, and an
            // unbound or refused one is answered by the shim. Its trigger stream
            // carries the same-name triggers of every bound cluster's mirrors of
            // that kind (shim_layer::bindings).
            let mut runners: Vec<tokio::task::JoinHandle<Result<()>>> = Vec::new();
            // What each runner is called in the log line that says it stopped;
            // same index as `runners`.
            let mut runner_names: Vec<String> = Vec::new();
            let mut binding_kinds = Vec::with_capacity(configured.len());
            for (kind, entry, plural) in &configured {
                let (triggers, trigger_stream) = same_name_triggers();
                runner_names.push(format!("the sync runner of {}", kind));
                runners.push(tokio::spawn(run_dyn_controller_with_triggers::<SyncReconciler, VoidExternalShimLayer>(
                    clusters.clone(),
                    SyncReconciler { kind: sync_kind(entry, kind) },
                    entry.clone(),
                    ClusterId::Primary,
                    trigger_stream,
                    Some(FIELD_MANAGER.to_string()),
                    janitor_pause_file.clone(),
                    fault_injection,
                    signalled(shutdown_rx.clone()),
                )));
                binding_kinds.push(BindingKind {
                    entry: entry.clone(),
                    group: kind.group.clone(),
                    plural: plural.clone(),
                    triggers,
                });
            }

            // The janitors of a binding, one per configured kind, started by the
            // binding manager once the binding's credential and claim are good
            // and stopped when its Secret changes or goes away. The sync
            // reconciler never deletes (its guarantee), so the pause file only
            // ever acts on the janitors; it is given to every runner so that the
            // gate holds for every Delete this process could send.
            let janitor_clusters = clusters.clone();
            let janitor_kinds: Vec<(KindConfig, RegistryEntry)> =
                configured.iter().map(|(kind, entry, _)| (kind.clone(), entry.clone())).collect();
            let janitor_pause = janitor_pause_file.clone();
            let start_runners = Arc::new(move |binding: &ClusterRef, stop: tokio::sync::watch::Receiver<bool>| {
                for (kind, entry) in &janitor_kinds {
                    let clusters = janitor_clusters.clone();
                    let reconciler =
                        JanitorReconciler { kind: sync_kind(entry, kind), binding: binding.clone() };
                    let entry = entry.clone();
                    let cluster = ClusterId::Remote(binding.clone());
                    let pause_file = janitor_pause.clone();
                    let binding = binding.clone();
                    let kind_name = kind.to_string();
                    let asked_to_stop = stop.clone();
                    let mut stop = stop.clone();
                    tokio::spawn(async move {
                        let stopped = async move {
                            let _ = stop.changed().await;
                        };
                        let outcome = run_dyn_controller::<JanitorReconciler, VoidExternalShimLayer>(
                            clusters,
                            reconciler,
                            entry,
                            cluster,
                            Some(FIELD_MANAGER.to_string()),
                            pause_file,
                            fault_injection,
                            stopped,
                        )
                        .await;
                        // A janitor returns when the manager stops it: its
                        // Secret changed or went away, or the process is
                        // shutting down. Anything else is a janitor that has
                        // stopped collecting stale mirrors of a live binding
                        // with nothing to restart it, so the process exits and
                        // the kubelet brings the container back.
                        let janitor = format!("the janitor of {} for binding {}/{}", kind_name, binding.namespace, binding.name);
                        match (*asked_to_stop.borrow(), outcome) {
                            (true, Ok(())) => info!("{} stopped with its binding", janitor),
                            (true, Err(e)) => {
                                warn!("{} stopped with its binding, reporting: {}", janitor, e)
                            }
                            (false, Ok(())) => {
                                error!("{} ended although its binding is up; exiting so the pod restarts", janitor);
                                process::exit(1);
                            }
                            (false, Err(e)) => {
                                error!("{} failed although its binding is up: {}; exiting so the pod restarts", janitor, e);
                                process::exit(1);
                            }
                        }
                    });
                }
            });

            let manager = BindingManager::new(
                clusters,
                binding_kinds,
                REMOTE_VERBS.iter().map(|v| v.to_string()).collect(),
                outer_id,
                REMOTE_REQUEST_TIMEOUT,
                start_runners,
            );
            runner_names.push("the binding manager".to_string());
            let shutting_down = shutdown_rx.clone();
            runners.push(tokio::spawn(manager.run(signalled(shutdown_rx))));

            // Ready: every configured kind is served and has the right shape, and
            // the sync runners are up. Whether any binding is usable is not part
            // of it.
            if let Some(path) = &ready_file {
                match fs::write(path, b"") {
                    Ok(()) => info!("ready: created {}", path),
                    Err(e) => warn!("could not create ready file {}: {}; the pod will not become ready", path, e),
                }
            }

            // The first runner to return decides what happens to the process.
            // Away from shutdown there is no good reason for one to return:
            // nothing restarts it, so the pod would go on running, and passing
            // its startup probe, with a kind that is no longer reconciled or a
            // binding manager that no longer notices a Secret. Exiting non-zero
            // is what makes the kubelet restart the container, and the error log
            // is what says which runner it was.
            let (first, index, rest) = futures::future::select_all(runners).await;
            let name = runner_names[index].clone();
            if *shutting_down.borrow() {
                info!("{} stopped; draining the others", name);
                for handle in rest {
                    match handle.await {
                        Ok(Ok(())) | Err(_) => {}
                        Ok(Err(e)) => warn!("a runner reported on its way out: {}", e),
                    }
                }
                info!("every runner has stopped");
            } else {
                match first {
                    Ok(Ok(())) => error!("{} returned unexpectedly; exiting so the pod restarts", name),
                    Ok(Err(e)) => error!("{} failed: {}; exiting so the pod restarts", name, e),
                    Err(e) => error!("{} did not finish ({}); exiting so the pod restarts", name, e),
                }
                process::exit(1);
            }
        }
        other => {
            eprintln!("unknown command {:?}\n{}", other, USAGE);
            process::exit(2);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
    use verifiable_controllers::shim_layer::crd_shape::{check_shape, crd_name};

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn kinds_come_from_repeated_flags_in_order() {
        let kinds = configured_kinds(&args(&[
            "--kind",
            "anvil.dev/v1/Widget:field:spec.clusterName",
            "--kind=anvil.dev/v1/Gadget:name",
        ]))
        .unwrap();
        let names: Vec<String> = kinds.iter().map(|k| k.to_string()).collect();
        assert_eq!(
            names,
            vec!["anvil.dev/v1/Widget:field:spec.clusterName", "anvil.dev/v1/Gadget:name"]
        );
        // The gvks handed to discover_kinds line up with `kinds` index by index,
        // which is what lets the registry entry of kind i be entry(i).
        assert_eq!(kinds[1].gvk().kind, "Gadget");
    }

    #[test]
    fn the_outer_cluster_id_is_optional_and_takes_a_value() {
        let with_flag = args(&["--kind", "anvil.dev/v1/Widget:name", "--outer-cluster-id", "some-uid"]);
        assert_eq!(parse_flags(&with_flag).unwrap().outer_cluster_id.as_deref(), Some("some-uid"));
        // It does not disturb the kinds, and it may be written with an equals sign.
        assert_eq!(configured_kinds(&with_flag).unwrap().len(), 1);
        let joined = args(&["--outer-cluster-id=some-uid", "--kind=anvil.dev/v1/Widget:name"]);
        assert_eq!(parse_flags(&joined).unwrap().outer_cluster_id.as_deref(), Some("some-uid"));
        let without = args(&["--kind", "anvil.dev/v1/Widget:name"]);
        assert_eq!(parse_flags(&without).unwrap().outer_cluster_id, None);
        assert!(parse_flags(&args(&["--outer-cluster-id"])).unwrap_err().contains("needs a value"));
    }

    #[test]
    fn a_missing_or_malformed_flag_is_a_usage_error() {
        for bad in [
            vec![],
            args(&["--kind"]),
            args(&["--bogus", "x"]),
            args(&["anvil.dev/v1/Widget:name"]),
            args(&["--kind", "anvil.dev/v1/widget:name"]),
            // The same kind twice would start two sync controllers on the same
            // objects, which the proofs exclude.
            args(&["--kind", "anvil.dev/v1/Widget:name", "--kind", "anvil.dev/v1/Widget:field:spec.clusterName"]),
        ] {
            assert!(configured_kinds(&bad).is_err(), "{:?} should be a usage error", bad);
        }
        assert!(configured_kinds(&args(&["--kind"])).unwrap_err().contains("needs a value"));
        assert!(configured_kinds(&[]).unwrap_err().contains("at least one"));
    }

    // Everything but the CEL immutability rules of the demo's Widget CRD, which
    // is what applying a rule-less variant installs on the testbed
    // (deploy/widget_sync/README.md, "Kinds and their shape").
    fn widget_crd_without_the_rule() -> CustomResourceDefinition {
        fn strip(value: &mut serde_yaml::Value) {
            match value {
                serde_yaml::Value::Mapping(map) => {
                    map.remove(serde_yaml::Value::String("x-kubernetes-validations".to_string()));
                    for (_, v) in map.iter_mut() {
                        strip(v);
                    }
                }
                serde_yaml::Value::Sequence(seq) => seq.iter_mut().for_each(strip),
                _ => {}
            }
        }
        let mut value: serde_yaml::Value =
            serde_yaml::from_str(include_str!("../../deploy/widget_sync/crd.yaml")).unwrap();
        strip(&mut value);
        serde_yaml::from_value(value).unwrap()
    }

    #[test]
    fn a_field_selector_without_the_immutability_rule_is_refused() {
        let kind: KindConfig = "anvil.dev/v1/Widget:field:spec.clusterName".parse().unwrap();
        let crd = widget_crd_without_the_rule();
        let errors = check_shape(&crd, &kind).unwrap_err();
        let message = refused_kind(&kind, &CrdCheckError::Shape { name: crd_name(&kind, "widgets"), errors });
        // The flag that has to be fixed, the CRD, the row of the table of design
        // section 2.2 that failed, and the rule that is missing.
        assert!(message.starts_with("--kind anvil.dev/v1/Widget:field:spec.clusterName: "), "{}", message);
        assert!(message.contains("CRD widgets.anvil.dev does not have the shape"), "{}", message);
        assert!(message.contains("spec: selector field spec.clusterName"), "{}", message);
        assert!(message.contains("self == oldSelf"), "{}", message);

        // Only the selector row fails: the same CRD is fine for a `name`
        // selector, which needs no rule, so the reproduction on the testbed
        // isolates the rule.
        let by_name: KindConfig = "anvil.dev/v1/Widget:name".parse().unwrap();
        assert_eq!(check_shape(&crd, &by_name), Ok(()));
    }
}
