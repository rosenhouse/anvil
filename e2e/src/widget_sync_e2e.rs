#![allow(unused_imports)]
#![allow(unused_variables)]
// End-to-end test of the widget sync example across the two kind clusters that
// tools/two-cluster-test.sh creates (kubectl contexts kind-widget-sync-outer and
// kind-widget-sync-inner). It checks, in order:
//   1. a Widget created in the outer cluster gets a mirror in the inner cluster
//      with the same spec, our label and parent-uid annotation, and no owner
//      references;
//   2. the outer copy's status reports the inner copy's status, stamped with the
//      outer generation and a true Synced condition;
//   3. a spec change propagates and the status catches up at the new generation;
//   4. a foreign inner object with the same name is refused, not adopted: it stays
//      untouched and the outer copy reports Synced=False/ForeignObject;
//   5. deleting the outer copy makes the janitor remove the mirror, while the
//      foreign object survives the deletion of its outer namesake.
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
use kube::{
    api::{Api, DeleteParams, ListParams, Patch, PatchParams, PostParams, ResourceExt},
    config::{KubeConfigOptions, Kubeconfig},
    Client, Config,
};
use serde_json::json;
use std::time::{Duration, Instant};
use tokio::time::sleep;
use tracing::*;
use verifiable_controllers::crds::{Widget, WidgetCondition, WidgetSpec, WidgetStatus};

use crate::common::*;

const OUTER_CONTEXT: &str = "kind-widget-sync-outer";
const INNER_CONTEXT: &str = "kind-widget-sync-inner";
const MANAGED_BY_KEY: &str = "anvil.dev/managed-by";
const MANAGED_BY_VALUE: &str = "widget-sync";
const PARENT_UID_KEY: &str = "anvil.dev/parent-uid";
const POLL: Duration = Duration::from_secs(3);
const TIMEOUT: Duration = Duration::from_secs(300);

async fn client_for_context(context: &str) -> Result<Client, Error> {
    let options = KubeConfigOptions { context: Some(context.to_string()), ..Default::default() };
    let config = Config::from_kubeconfig(&options).await.map_err(|e| {
        error!("cannot load kubeconfig context {}: {}", context, e);
        Error::WidgetSyncFailed
    })?;
    Ok(Client::try_from(config)?)
}

fn widget(name: &str, count: i32, message: &str) -> Widget {
    let mut w = Widget::new(name, WidgetSpec { count, message: Some(message.to_string()) });
    w.metadata.namespace = Some("default".to_string());
    w
}

fn synced_condition(status: &WidgetStatus) -> Option<&WidgetCondition> {
    status.conditions.as_ref()?.iter().find(|c| c.type_ == "Synced")
}

// The outer copy reports `count` at its current generation with Synced=True.
fn outer_reports(outer: &Widget, count: i32) -> bool {
    let status = match &outer.status {
        Some(s) => s,
        None => return false,
    };
    let generation = outer.metadata.generation;
    let condition = synced_condition(status);
    generation.is_some()
        && status.observed_generation == generation
        && status.ready == Some(true)
        && status.observed_count == Some(count)
        && condition.map(|c| c.status == "True" && c.observed_generation == generation).unwrap_or(false)
}

fn is_mirror_of(inner: &Widget, outer: &Widget) -> bool {
    let labels = inner.metadata.labels.as_ref();
    let annotations = inner.metadata.annotations.as_ref();
    labels.and_then(|l| l.get(MANAGED_BY_KEY)).map(|v| v == MANAGED_BY_VALUE).unwrap_or(false)
        && annotations.and_then(|a| a.get(PARENT_UID_KEY)) == outer.metadata.uid.as_ref()
        && inner.metadata.owner_references.as_ref().map(|o| o.is_empty()).unwrap_or(true)
        && inner.spec == outer.spec
}

async fn wait_until<F>(what: &str, mut check: F) -> Result<(), Error>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<bool, Error>> + Send>>,
{
    let start = Instant::now();
    loop {
        if check().await? {
            info!("{}: ok", what);
            return Ok(());
        }
        if start.elapsed() > TIMEOUT {
            error!("{}: timed out", what);
            return Err(Error::Timeout);
        }
        sleep(POLL).await;
    }
}

async fn get_opt(api: &Api<Widget>, name: &str) -> Result<Option<Widget>, Error> {
    match api.get_opt(name).await {
        Ok(w) => Ok(w),
        Err(e) => {
            info!("get {} failed: {}", name, e);
            Ok(None)
        }
    }
}

pub async fn widget_sync_e2e_test() -> Result<(), Error> {
    let outer_client = client_for_context(OUTER_CONTEXT).await?;
    let inner_client = client_for_context(INNER_CONTEXT).await?;
    for (label, client) in [("outer", outer_client.clone()), ("inner", inner_client.clone())] {
        let crd_api: Api<CustomResourceDefinition> = Api::all(client);
        if let Err(e) = crd_api.get("widgets.anvil.dev").await {
            error!("No Widget CRD found in the {} cluster; run tools/two-cluster-test.sh first.", label);
            return Err(Error::CRDGetFailed(e));
        }
    }
    let outer: Api<Widget> = Api::namespaced(outer_client.clone(), "default");
    let inner: Api<Widget> = Api::namespaced(inner_client.clone(), "default");

    // 1. Create the outer Widget and wait for its mirror.
    outer.create(&PostParams::default(), &widget("demo", 3, "hello")).await.map_err(|e| {
        error!("create outer widget failed: {}", e);
        Error::WidgetSyncFailed
    })?;
    let (o, i) = (outer.clone(), inner.clone());
    wait_until("mirror exists with the outer spec", move || {
        let (o, i) = (o.clone(), i.clone());
        Box::pin(async move {
            let outer_obj = match get_opt(&o, "demo").await? { Some(w) => w, None => return Ok(false) };
            let inner_obj = match get_opt(&i, "demo").await? { Some(w) => w, None => return Ok(false) };
            Ok(is_mirror_of(&inner_obj, &outer_obj))
        })
    })
    .await?;

    // 2. The outer status mirrors the inner status at the outer generation.
    let o = outer.clone();
    wait_until("outer status reports count 3 at its generation with Synced=True", move || {
        let o = o.clone();
        Box::pin(async move {
            Ok(get_opt(&o, "demo").await?.map(|w| outer_reports(&w, 3)).unwrap_or(false))
        })
    })
    .await?;

    // 3. A spec change propagates and the status catches up at the new generation.
    outer
        .patch("demo", &PatchParams::default(), &Patch::Merge(json!({ "spec": { "count": 5 } })))
        .await
        .map_err(|e| {
            error!("patch outer widget failed: {}", e);
            Error::WidgetSyncFailed
        })?;
    let (o, i) = (outer.clone(), inner.clone());
    wait_until("mirror carries count 5 and outer status reports it at generation 2", move || {
        let (o, i) = (o.clone(), i.clone());
        Box::pin(async move {
            let outer_obj = match get_opt(&o, "demo").await? { Some(w) => w, None => return Ok(false) };
            let inner_obj = match get_opt(&i, "demo").await? { Some(w) => w, None => return Ok(false) };
            Ok(outer_obj.metadata.generation == Some(2)
                && is_mirror_of(&inner_obj, &outer_obj)
                && inner_obj.spec.count == 5
                && outer_reports(&outer_obj, 5))
        })
    })
    .await?;

    // 4. A foreign inner object is refused, never adopted.
    let mut foreign = widget("foreign", 7, "not yours");
    foreign.metadata.labels = Some([("owner".to_string(), "someone-else".to_string())].into());
    inner.create(&PostParams::default(), &foreign).await.map_err(|e| {
        error!("create foreign inner widget failed: {}", e);
        Error::WidgetSyncFailed
    })?;
    outer.create(&PostParams::default(), &widget("foreign", 1, "mine")).await.map_err(|e| {
        error!("create outer widget failed: {}", e);
        Error::WidgetSyncFailed
    })?;
    let (o, i) = (outer.clone(), inner.clone());
    wait_until("outer copy reports ForeignObject and the foreign object is untouched", move || {
        let (o, i) = (o.clone(), i.clone());
        Box::pin(async move {
            let outer_obj = match get_opt(&o, "foreign").await? { Some(w) => w, None => return Ok(false) };
            let inner_obj = match get_opt(&i, "foreign").await? { Some(w) => w, None => return Ok(false) };
            if inner_obj.spec.count != 7 || inner_obj.metadata.labels.as_ref().and_then(|l| l.get(MANAGED_BY_KEY)).is_some() {
                error!("the sync controller touched a foreign object: {:?}", inner_obj);
                return Err(Error::WidgetSyncFailed);
            }
            let status = match &outer_obj.status { Some(s) => s, None => return Ok(false) };
            let condition = synced_condition(status);
            Ok(status.observed_generation == outer_obj.metadata.generation
                && condition
                    .map(|c| c.status == "False" && c.reason.as_deref() == Some("ForeignObject"))
                    .unwrap_or(false))
        })
    })
    .await?;

    // 5. Deleting the outer copies: the mirror is collected, the foreign object survives.
    outer.delete("demo", &DeleteParams::default()).await.map_err(|e| {
        error!("delete outer widget failed: {}", e);
        Error::WidgetSyncFailed
    })?;
    outer.delete("foreign", &DeleteParams::default()).await.map_err(|e| {
        error!("delete outer widget failed: {}", e);
        Error::WidgetSyncFailed
    })?;
    let i = inner.clone();
    wait_until("mirror is collected by the janitor", move || {
        let i = i.clone();
        Box::pin(async move { Ok(get_opt(&i, "demo").await?.is_none()) })
    })
    .await?;
    // The janitor has run by now (it reconciles every inner Widget on its own schedule
    // and was triggered by the same deletion); the foreign object must still be there.
    sleep(Duration::from_secs(20)).await;
    match inner.get_opt("foreign").await {
        Ok(Some(w)) if w.metadata.deletion_timestamp.is_none() => info!("foreign object survived: ok"),
        other => {
            error!("the foreign object did not survive: {:?}", other);
            return Err(Error::WidgetSyncFailed);
        }
    }

    info!("E2e test passed.");
    Ok(())
}
