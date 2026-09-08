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
// This binary instantiates them at the kinds of the `--kind` flags and at one
// binding; the binding manager of section 3.4 is the follow-up issue. Two kinds
// of verified reconciler run in one process, one pair per configured kind: the
// sync reconciler (triggered by outer objects, and by same-named mirrors as a
// latency optimization) and the janitor reconciler (triggered by the binding's
// mirrors).
use anyhow::{bail, Result};
use k8s_openapi::api::authorization::v1::{ResourceAttributes, SelfSubjectAccessReview, SelfSubjectAccessReviewSpec};
use kube::api::{Api, PostParams};
use kube::Client;
use std::env;
use std::fs;
use std::future::Future;
use std::pin::Pin;
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
use verifiable_controllers::shim_layer::crd_shape::{check_crd, CrdCheckError};
use verifiable_controllers::shim_layer::kind_config::{ClusterSelector, KindConfig};
use verifiable_controllers::widget_sync_controller::exec::janitor_reconciler::JanitorReconciler;
use verifiable_controllers::widget_sync_controller::exec::sync_reconciler::SyncReconciler;
use verifiable_controllers::widget_sync_controller::trusted::exec_types::SyncKindExec;

const USAGE: &str = "usage: widget_sync_controller export
       widget_sync_controller <run|crash> --kind <group>/<version>/<Kind>:<selector> ...
  export  print the demo CRDs as YAML
  run     run one sync and one janitor reconciler per configured kind
  crash   run them in crash-testing mode (fault injection)
  --kind  a kind and the field that names an object's cluster, repeated; at
          least one is required. The selector is `name` (metadata.name is the
          cluster name) or `field:<path>` (a required, immutable string field of
          the spec), for example
            --kind anvil.dev/v1/Widget:field:spec.clusterName
            --kind anvil.dev/v1/Gadget:name";

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

// The `--kind` flag values of `run` and `crash`, in the order they were given.
// Both `--kind <value>` and `--kind=<value>` are accepted, as for the echo
// controller, so one list can be pasted between the two binaries. Anything else
// on the command line is a usage error; so is an empty list, because a process
// with no kind would watch nothing.
fn kind_flags(args: &[String]) -> Result<Vec<String>, String> {
    let mut flags = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--kind" => {
                i += 1;
                match args.get(i) {
                    Some(value) => flags.push(value.clone()),
                    None => return Err("--kind needs a value".to_string()),
                }
            }
            arg if arg.starts_with("--kind=") => flags.push(arg["--kind=".len()..].to_string()),
            arg => return Err(format!("unexpected argument {:?}", arg)),
        }
        i += 1;
    }
    if flags.is_empty() {
        return Err("no --kind given; at least one kind is required".to_string());
    }
    Ok(flags)
}

// The configured kinds: the flags, parsed (shim_layer::kind_config). A malformed
// flag and a repeated kind are both usage errors; a kind named twice would start
// two sync controllers on the same objects, which the proofs exclude.
fn configured_kinds(args: &[String]) -> Result<Vec<KindConfig>, String> {
    let kinds = KindConfig::parse_all(kind_flags(args)?).map_err(|e| e.to_string())?;
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
fn refused_kind(kind: &KindConfig, err: &CrdCheckError) -> String {
    format!("--kind {}: {}", kind, err)
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
            // The kinds come from the command line; a bad or missing flag is a
            // usage error, reported before any client is built.
            let kinds = match configured_kinds(&args[2..]) {
                Ok(kinds) => kinds,
                Err(message) => {
                    eprintln!("{}\n{}", message, USAGE);
                    process::exit(2);
                }
            };
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
            let gvks: Vec<_> = kinds.iter().map(|k| k.gvk()).collect();
            let registry = discover_kinds(&primary, &gvks).await?;
            // (kind, its registry entry, its plural), in configuration order.
            let mut configured = Vec::with_capacity(kinds.len());
            for (i, kind) in kinds.iter().enumerate() {
                let entry = registry.entry(i).clone();
                let plural = entry.kube_api_resource().plural.clone();
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

            let remote = remote_clients_from_kubeconfig(&remote_kubeconfig, REMOTE_REQUEST_TIMEOUT).await?;
            for (kind, _, plural) in &configured {
                check_remote_access(&remote.requests, &kind.group, plural).await?;
            }
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

            // One shutdown signal for every controller: on SIGINT each stops
            // taking new work and drains, as `shutdown_on_signal` did.
            let (tx, shutdown_rx) = tokio::sync::watch::channel(false);
            tokio::spawn(async move {
                if tokio::signal::ctrl_c().await.is_ok() {
                    info!("shutting down");
                }
                let _ = tx.send(true);
            });
            // One sync reconciler and one janitor per configured kind: the sync
            // reconciler runs on the outer copies of its kind and is woken by a
            // same-named mirror of the binding as well; the janitor runs on the
            // binding's mirrors of that kind. The sync reconciler never deletes
            // (its guarantee), so the pause file only ever acts on the janitors;
            // it is given to every runner so that the gate holds for every
            // Delete this process could send. Each runner gets its own receiver
            // on the one shutdown signal, so a SIGINT drains all of them.
            let mut runners: Vec<Pin<Box<dyn Future<Output = Result<()>> + Send>>> = Vec::new();
            for (kind, entry, _) in &configured {
                let mut sync_shutdown_rx = shutdown_rx.clone();
                let sync_shutdown = async move {
                    let _ = sync_shutdown_rx.changed().await;
                };
                runners.push(Box::pin(run_dyn_controller_with_same_name_watch::<SyncReconciler, VoidExternalShimLayer>(
                    clusters.clone(),
                    SyncReconciler { kind: sync_kind(entry, kind) },
                    entry.clone(),
                    ClusterId::Primary,
                    entry.clone(),
                    inner_cluster.clone(),
                    Some(FIELD_MANAGER.to_string()),
                    janitor_pause_file.clone(),
                    fault_injection,
                    sync_shutdown,
                )));
                let mut janitor_shutdown_rx = shutdown_rx.clone();
                let janitor_shutdown = async move {
                    let _ = janitor_shutdown_rx.changed().await;
                };
                runners.push(Box::pin(run_dyn_controller::<JanitorReconciler, VoidExternalShimLayer>(
                    clusters.clone(),
                    JanitorReconciler { kind: sync_kind(entry, kind), binding: binding.clone() },
                    entry.clone(),
                    inner_cluster.clone(),
                    Some(FIELD_MANAGER.to_string()),
                    janitor_pause_file.clone(),
                    fault_injection,
                    janitor_shutdown,
                )));
            }
            futures::future::try_join_all(runners).await?;
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
