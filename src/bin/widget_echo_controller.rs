// The widget echo controller: the stand-in for "whatever implements Widgets in
// the inner cluster" in the two-cluster demo. It is an ordinary, unverified
// kube-rs controller. For every Widget in its cluster it writes a status that
// echoes the spec: observedGeneration = metadata.generation, ready = true,
// observedCount = spec.count, and a Ready condition. It writes status with a
// merge patch on the status subresource, the way a typical operator does, and
// never touches spec or metadata.
//
// WIDGET_ECHO_DELAY_SECONDS (default 0) delays each status write, so a demo can
// show the outer copy's Synced condition passing through InnerConverging.
use anyhow::Result;
use futures::StreamExt;
use kube::api::{Api, Patch, PatchParams};
use kube::runtime::controller::{Action, Controller};
use kube::runtime::watcher;
use kube::{Client, ResourceExt};
use std::env;
use std::sync::Arc;
use std::time::Duration;
use tracing::{error, info};
use verifiable_controllers::crds::{Widget, WidgetCondition, WidgetStatus};

struct Context {
    client: Client,
    delay: Duration,
}

fn echoed_status(widget: &Widget) -> WidgetStatus {
    let generation = widget.metadata.generation;
    WidgetStatus {
        observed_generation: generation,
        ready: Some(true),
        observed_count: Some(widget.spec.count),
        conditions: Some(vec![WidgetCondition {
            type_: "Ready".to_string(),
            status: "True".to_string(),
            observed_generation: generation,
            reason: Some("Echoed".to_string()),
            message: widget.spec.message.clone(),
        }]),
    }
}

async fn reconcile(widget: Arc<Widget>, ctx: Arc<Context>) -> Result<Action, kube::Error> {
    let namespace = match widget.namespace() {
        Some(namespace) => namespace,
        None => return Ok(Action::await_change()),
    };
    let name = widget.name_any();
    if widget.metadata.deletion_timestamp.is_some() {
        return Ok(Action::await_change());
    }
    let desired = echoed_status(&widget);
    if widget.status.as_ref() == Some(&desired) {
        return Ok(Action::requeue(Duration::from_secs(60)));
    }
    if !ctx.delay.is_zero() {
        tokio::time::sleep(ctx.delay).await;
    }
    let api: Api<Widget> = Api::namespaced(ctx.client.clone(), &namespace);
    let patch = serde_json::json!({ "status": desired });
    api.patch_status(&name, &PatchParams::default(), &Patch::Merge(&patch)).await?;
    info!("echoed status of widget {}/{}", namespace, name);
    Ok(Action::requeue(Duration::from_secs(60)))
}

fn error_policy(_widget: Arc<Widget>, error: &kube::Error, _ctx: Arc<Context>) -> Action {
    error!("reconcile failed: {}", error);
    Action::requeue(Duration::from_secs(5))
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let delay_seconds: u64 = env::var("WIDGET_ECHO_DELAY_SECONDS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0);
    let client = Client::try_default().await?;
    let widgets = Api::<Widget>::all(client.clone());
    let ctx = Arc::new(Context { client, delay: Duration::from_secs(delay_seconds) });
    info!("running widget-echo-controller (delay {}s)", delay_seconds);
    Controller::new(widgets, watcher::Config::default())
        .shutdown_on_signal()
        .run(reconcile, error_policy, ctx)
        .for_each(|res| async move {
            match res {
                Ok(o) => info!("reconciled {:?}", o),
                Err(e) => info!("reconcile failed: {}", e),
            }
        })
        .await;
    Ok(())
}
