// The widget echo controller: the stand-in for "whatever implements the kinds
// in the inner cluster" in the demo. It is an ordinary, unverified kube-rs
// controller, generic over the kinds it is given (doc/widget_sync_fanout_design.md,
// section 4). For every object of each kind in its cluster it writes a status
// that echoes the spec:
//
//   observedGeneration: metadata.generation
//   conditions: [ { type: Ready, status: "True", reason: Echoed,
//                   message: spec.message (when present),
//                   observedGeneration: metadata.generation } ]
//
// plus, per kind, what a real implementation of that kind would report: for
// Widget `ready: true` and `observedCount: spec.count`, for Gadget
// `observedSize: spec.size`. The per-kind part is the ECHOES table; a new kind
// is one line there. It writes status with a merge patch on the status
// subresource, the way a typical operator does, and never touches spec or
// metadata.
//
// Usage:
//   widget_echo_controller [run] --kind <group>/<version>/<Kind> ...
//   widget_echo_controller export
// The kinds may instead come from WIDGET_ECHO_KINDS, comma-separated. A kind
// value may carry the sync controller's `:<selector>` suffix, which is ignored,
// so one list can serve both binaries. `export` prints the demo CRDs.
// WIDGET_ECHO_DELAY_SECONDS (default 0) delays each status write, so a demo can
// show the outer copy's Synced condition passing through InnerConverging.
use anyhow::{anyhow, bail, Context as _, Result};
use futures::StreamExt;
use kube::api::{Api, DynamicObject, Patch, PatchParams};
use kube::core::GroupVersionKind;
use kube::discovery::{pinned_kind, ApiResource, Scope};
use kube::runtime::controller::{Action, Controller};
use kube::runtime::watcher;
use kube::{Client, ResourceExt};
use serde_json::{json, Map, Value};
use std::env;
use std::sync::Arc;
use std::time::Duration;
use tracing::{error, info};

const USAGE: &str = "usage: widget_echo_controller [run] --kind <group>/<version>/<Kind> ...
       widget_echo_controller export
  --kind    a kind to echo, repeated; or WIDGET_ECHO_KINDS=<kind>,<kind>,...
  export    print the demo CRDs as YAML";

// The kind-specific part of an echoed status: what a real implementation of the
// kind would report about the spec. A kind with no entry gets only the generic
// part (observedGeneration and the Ready condition).
type Echo = fn(spec: &Value, status: &mut Map<String, Value>);

const ECHOES: &[(&str, Echo)] = &[("Widget", echo_widget), ("Gadget", echo_gadget)];

fn echo_widget(spec: &Value, status: &mut Map<String, Value>) {
    status.insert("ready".to_string(), json!(true));
    status.insert("observedCount".to_string(), spec["count"].clone());
}

fn echo_gadget(spec: &Value, status: &mut Map<String, Value>) {
    status.insert("observedSize".to_string(), spec["size"].clone());
}

fn echo_for(kind: &str) -> Option<Echo> {
    ECHOES.iter().find(|(k, _)| *k == kind).map(|(_, echo)| *echo)
}

// The status an object of `kind` gets, as JSON: the generic part plus the
// kind's echo. `spec.message`, when it is a string, becomes the condition's
// message; when absent the condition carries none.
fn echoed_status(kind: &str, obj: &DynamicObject) -> Value {
    let generation = obj.metadata.generation;
    let spec = &obj.data["spec"];
    let mut condition = Map::new();
    condition.insert("type".to_string(), json!("Ready"));
    condition.insert("status".to_string(), json!("True"));
    condition.insert("reason".to_string(), json!("Echoed"));
    if let Some(message) = spec["message"].as_str() {
        condition.insert("message".to_string(), json!(message));
    }
    condition.insert("observedGeneration".to_string(), json!(generation));
    let mut status = Map::new();
    status.insert("observedGeneration".to_string(), json!(generation));
    status.insert("conditions".to_string(), Value::Array(vec![Value::Object(condition)]));
    if let Some(echo) = echo_for(kind) {
        echo(spec, &mut status);
    }
    Value::Object(status)
}

struct Context {
    client: Client,
    delay: Duration,
    resource: ApiResource,
}

async fn reconcile(obj: Arc<DynamicObject>, ctx: Arc<Context>) -> Result<Action, kube::Error> {
    let namespace = match obj.namespace() {
        Some(namespace) => namespace,
        None => return Ok(Action::await_change()),
    };
    let name = obj.name_any();
    if obj.metadata.deletion_timestamp.is_some() {
        return Ok(Action::await_change());
    }
    let desired = echoed_status(&ctx.resource.kind, &obj);
    if obj.data["status"] == desired {
        return Ok(Action::requeue(Duration::from_secs(60)));
    }
    if !ctx.delay.is_zero() {
        tokio::time::sleep(ctx.delay).await;
    }
    let api: Api<DynamicObject> = Api::namespaced_with(ctx.client.clone(), &namespace, &ctx.resource);
    let patch = json!({ "status": desired });
    api.patch_status(&name, &PatchParams::default(), &Patch::Merge(&patch)).await?;
    info!("echoed status of {} {}/{}", ctx.resource.kind, namespace, name);
    Ok(Action::requeue(Duration::from_secs(60)))
}

fn error_policy(obj: Arc<DynamicObject>, error: &kube::Error, ctx: Arc<Context>) -> Action {
    error!("reconcile of {} {} failed: {}", ctx.resource.kind, obj.name_any(), error);
    Action::requeue(Duration::from_secs(5))
}

// `<group>/<version>/<Kind>`, with an optional `:<selector>` suffix ignored.
fn parse_kind(flag: &str) -> Result<GroupVersionKind> {
    let gvk = flag.split_once(':').map_or(flag, |(gvk, _)| gvk);
    match gvk.split('/').collect::<Vec<_>>().as_slice() {
        [group, version, kind] if !group.is_empty() && !version.is_empty() && !kind.is_empty() => {
            Ok(GroupVersionKind::gvk(group, version, kind))
        }
        _ => bail!("kind {:?} must be <group>/<version>/<Kind>", flag),
    }
}

// The kinds from `--kind` flags, else from WIDGET_ECHO_KINDS.
fn configured_kinds(args: &[String]) -> Result<Vec<GroupVersionKind>> {
    let mut flags = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--kind" => {
                i += 1;
                let value = args.get(i).ok_or_else(|| anyhow!("--kind needs a value\n{}", USAGE))?;
                flags.push(value.clone());
            }
            arg if arg.starts_with("--kind=") => flags.push(arg["--kind=".len()..].to_string()),
            arg => bail!("unexpected argument {:?}\n{}", arg, USAGE),
        }
        i += 1;
    }
    if flags.is_empty() {
        if let Ok(list) = env::var("WIDGET_ECHO_KINDS") {
            flags.extend(list.split(',').map(str::trim).filter(|s| !s.is_empty()).map(str::to_string));
        }
    }
    if flags.is_empty() {
        bail!("no kinds given\n{}", USAGE);
    }
    flags.iter().map(|f| parse_kind(f)).collect()
}

async fn discover(client: &Client, gvk: &GroupVersionKind) -> Result<ApiResource> {
    let (resource, capabilities) = pinned_kind(client, gvk)
        .await
        .with_context(|| format!("kind {} is not served", gvk.api_version()))?;
    if capabilities.scope != Scope::Namespaced {
        bail!("kind {}/{} is not namespaced", gvk.api_version(), gvk.kind);
    }
    // Discovery names a subresource by its own name ("status"), not
    // "<plural>/status" (kube_core::discovery::ApiCapabilities).
    if !capabilities.subresources.iter().any(|(sub, _)| sub.plural == "status") {
        bail!("kind {}/{} has no status subresource", gvk.api_version(), gvk.kind);
    }
    Ok(resource)
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let mut args: Vec<String> = env::args().skip(1).collect();
    // The container image's entrypoint passes `run` first, as for the other controllers.
    if args.first().map(String::as_str) == Some("run") {
        args.remove(0);
    }
    if args.first().map(String::as_str) == Some("export") {
        for crd in verifiable_controllers::crds::demo_crds() {
            println!("---");
            print!("{}", serde_yaml::to_string(&crd)?);
        }
        return Ok(());
    }
    let kinds = configured_kinds(&args)?;
    let delay_seconds: u64 = env::var("WIDGET_ECHO_DELAY_SECONDS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0);
    let delay = Duration::from_secs(delay_seconds);
    let client = Client::try_default().await?;

    let mut controllers = Vec::new();
    for gvk in &kinds {
        let resource = discover(&client, gvk).await?;
        if echo_for(&resource.kind).is_none() {
            info!("kind {} has no kind-specific echo; only the generic status is written", resource.kind);
        }
        let api = Api::<DynamicObject>::all_with(client.clone(), &resource);
        let kind = resource.kind.clone();
        let ctx = Arc::new(Context { client: client.clone(), delay, resource: resource.clone() });
        info!("running widget-echo-controller for {} (delay {}s)", kind, delay_seconds);
        let run = Controller::new_with(api, watcher::Config::default(), resource)
            .shutdown_on_signal()
            .run(reconcile, error_policy, ctx)
            .for_each(move |res| {
                let kind = kind.clone();
                async move {
                    match res {
                        Ok(o) => info!("reconciled {} {:?}", kind, o),
                        Err(e) => info!("reconcile of a {} failed: {}", kind, e),
                    }
                }
            });
        controllers.push(run);
    }
    futures::future::join_all(controllers).await;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn object(kind: &str, generation: i64, spec: Value) -> DynamicObject {
        let resource = ApiResource::from_gvk(&GroupVersionKind::gvk("anvil.dev", "v1", kind));
        let mut obj = DynamicObject::new("demo", &resource).data(json!({ "spec": spec }));
        obj.metadata.generation = Some(generation);
        obj
    }

    #[test]
    fn a_widget_echoes_count_and_message() {
        let obj = object("Widget", 3, json!({ "clusterName": "a", "count": 7, "message": "hi" }));
        assert_eq!(
            echoed_status("Widget", &obj),
            json!({
                "observedGeneration": 3,
                "ready": true,
                "observedCount": 7,
                "conditions": [{
                    "type": "Ready", "status": "True", "reason": "Echoed",
                    "message": "hi", "observedGeneration": 3
                }]
            })
        );
    }

    #[test]
    fn a_gadget_echoes_size_and_has_no_message() {
        let obj = object("Gadget", 1, json!({ "size": 2, "labels": ["x"] }));
        assert_eq!(
            echoed_status("Gadget", &obj),
            json!({
                "observedGeneration": 1,
                "observedSize": 2,
                "conditions": [{
                    "type": "Ready", "status": "True", "reason": "Echoed", "observedGeneration": 1
                }]
            })
        );
    }

    #[test]
    fn an_unknown_kind_gets_the_generic_status_only() {
        let obj = object("Thing", 5, json!({ "whatever": 1 }));
        assert_eq!(
            echoed_status("Thing", &obj),
            json!({
                "observedGeneration": 5,
                "conditions": [{
                    "type": "Ready", "status": "True", "reason": "Echoed", "observedGeneration": 5
                }]
            })
        );
    }

    #[test]
    fn kind_flags_parse_with_or_without_a_selector() {
        let args: Vec<String> = ["--kind", "anvil.dev/v1/Widget:field:spec.clusterName", "--kind=anvil.dev/v1/Gadget"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let kinds = configured_kinds(&args).unwrap();
        assert_eq!(kinds, vec![
            GroupVersionKind::gvk("anvil.dev", "v1", "Widget"),
            GroupVersionKind::gvk("anvil.dev", "v1", "Gadget"),
        ]);
        assert!(parse_kind("anvil.dev/Widget").is_err());
        assert!(parse_kind("/v1/Widget").is_err());
        assert!(configured_kinds(&["--kind".to_string()]).is_err());
        assert!(configured_kinds(&["--bogus".to_string()]).is_err());
    }
}
