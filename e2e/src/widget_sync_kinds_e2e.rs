#![allow(unused_imports)]
#![allow(unused_variables)]
// End-to-end test of the sync controller's genericity over kinds
// (doc/widget_sync_fanout_design.md, section 2), against the binding `default/a`
// of the three kind clusters tools/two-cluster-test.sh creates. The controller
// is deployed with two `--kind` flags,
// `anvil.dev/v1/Widget:field:spec.clusterName` and
// `anvil.dev/v1/Gadget:name`, so the same reconcilers run for a kind whose spec
// it has never been compiled against and whose cluster is selected by
// `metadata.name` instead of a spec field. It checks, in order:
//   1. a Gadget named after the binding's cluster is mirrored into the inner
//      cluster with its spec verbatim -- a spec with nothing in common with a
//      Widget's -- carrying our label, the parent-uid annotation and no owner
//      references;
//   2. the echo controller's status comes back on the outer copy: observedSize,
//      the mirrored payload the sync controller knows nothing about, a Ready
//      condition, and Synced=True at the outer generation;
//   3. a Gadget whose name is not a binding of this process ("elsewhere") is
//      answered as an unreachable inner cluster: the outer copy reports
//      Synced=False/InnerUnreachable, not Stalled, and nothing is ever created
//      in the inner cluster for it;
//   4. adding a kind did not rename anything on the outer Widget status: it
//      still carries exactly observedGeneration, conditions, ready and
//      observedCount, with `ready` and `observedCount` mirrored through the
//      opaque remainder that replaced the typed status.
//
// The Gadget of check 1 is named `a`, the cluster of the binding `default/a`:
// a `name`-selected object reaches an inner cluster exactly when it is named
// after a binding of its namespace.
//
// The test cleans up after itself, so it can run before or after
// widget_sync_e2e against the same clusters; it uses its own object names.
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
use kube::{
    api::{Api, ApiResource, DeleteParams, DynamicObject, PostParams, ResourceExt},
    core::{ErrorResponse, GroupVersionKind},
    Client,
};
use serde_json::{json, Value};
use std::time::Duration;
use tokio::time::sleep;
use tracing::*;
use verifiable_controllers::crds::{Gadget, GadgetSpec, GadgetStatus, Widget, WidgetCondition, WidgetSpec};

use crate::common::*;
use crate::widget_sync_e2e::{
    client_for_context, failed, wait_for, wait_until, INNER_CONTEXT, MANAGED_BY_KEY, MANAGED_BY_VALUE, MARGIN,
    ONE_RECONCILE, OUTER_CONTEXT, PARENT_UID_KEY, REQUEUE, TIMEOUT,
};

// The cluster of the binding this file runs against: an object of a
// `name`-selected kind reaches that inner cluster exactly when it carries this
// name.
const BOUND_CLUSTER: &str = "a";
// A cluster name no binding of this process has: no Secret `elsewhere-kubeconfig`
// exists in the namespace. The binding is not in the snapshot the reconcile was
// built with, so the sync reconciler reports InnerUnreachable and ends without
// addressing the inner side at all; the shim's Timeout for an unbound cluster
// (controller_runtime::ClusterUnavailable) is the fallback behind it and reads
// the same way (doc/widget_sync_fanout_design.md, sections 1.2 and 3.2).
const UNBOUND_CLUSTER: &str = "elsewhere";
// The Widget of check 4; a name of its own so the test does not collide with
// widget_sync_e2e's objects.
const WIDGET_NAME: &str = "kinds-demo";
const NAMESPACE: &str = "default";

// The window the negative check below runs for: long enough that a controller
// that were going to create the mirror of an unbound cluster has had several
// goes at it. An object of an unbound cluster fails every reconcile, so it is
// not on the requeue but on error_policy's backoff, and the attempts inside a
// window of this length fall at about RETRY_BASE, three times RETRY_BASE and
// seven times RETRY_BASE after the first failure -- four attempts counting the
// first. Waiting for more would mean waiting out the cap, which buys nothing:
// what the check discriminates is a reconciler that addresses an unbound
// cluster at all, and such a reconciler would do it on its first attempt.
// This window is spent in full on every run, so it is kept short on purpose.
const RETRY_WINDOW: Duration = Duration::from_secs(REQUEUE.as_secs() + MARGIN.as_secs());

fn gadget(name: &str, size: i32) -> Gadget {
    let spec = GadgetSpec { size, labels: Some(vec!["demo".to_string(), name.to_string()]) };
    let mut g = Gadget::new(name, spec);
    g.metadata.namespace = Some(NAMESPACE.to_string());
    g
}

fn widget(name: &str, count: i32, message: &str) -> Widget {
    let spec =
        WidgetSpec { cluster_name: BOUND_CLUSTER.to_string(), count, message: Some(message.to_string()) };
    let mut w = Widget::new(name, spec);
    w.metadata.namespace = Some(NAMESPACE.to_string());
    w
}

// Gadgets in namespace `default` of one cluster, with the same 404-only
// absence rule as widget_sync_e2e's Widgets: any other error fails the test, so
// an absence check never passes because the cluster was unreachable.
#[derive(Clone)]
struct Gadgets {
    cluster: &'static str,
    api: Api<Gadget>,
}

impl Gadgets {
    async fn get_opt(&self, name: &str) -> Result<Option<Gadget>, Error> {
        match self.api.get(name).await {
            Ok(g) => Ok(Some(g)),
            Err(kube::Error::Api(ErrorResponse { code: 404, .. })) => Ok(None),
            Err(e) => {
                error!("get Gadget {} in the {} cluster failed (not a 404): {}", name, self.cluster, e);
                Err(Error::WidgetLookupFailed(e))
            }
        }
    }

    async fn get(&self, name: &str) -> Result<Gadget, Error> {
        self.get_opt(name).await?.ok_or_else(|| {
            error!("Gadget {} is absent from the {} cluster but must exist now", name, self.cluster);
            Error::WidgetSyncFailed
        })
    }
}

fn condition<'a>(conditions: &'a Option<Vec<WidgetCondition>>, type_: &str) -> Option<&'a WidgetCondition> {
    conditions.as_ref()?.iter().find(|c| c.type_ == type_)
}

// The mirror of `outer`: our label, the parent uid, no owner references, and the
// outer spec verbatim (`size` and `labels`, neither of which the sync controller
// knows anything about).
fn is_mirror_of(inner: &Gadget, outer: &Gadget) -> bool {
    let labels = inner.metadata.labels.as_ref();
    let annotations = inner.metadata.annotations.as_ref();
    labels.and_then(|l| l.get(MANAGED_BY_KEY)).map(|v| v == MANAGED_BY_VALUE).unwrap_or(false)
        && annotations.and_then(|a| a.get(PARENT_UID_KEY)) == outer.metadata.uid.as_ref()
        && inner.metadata.owner_references.as_ref().map(|o| o.is_empty()).unwrap_or(true)
        && inner.spec == outer.spec
}

// The inner implementation has processed the mirror's current spec.
fn inner_caught_up(inner: &Gadget) -> bool {
    let observed = inner.status.as_ref().and_then(|s| s.observed_generation);
    observed.is_some() && observed == inner.metadata.generation
}

// The outer Gadget reports `size` at its current generation with Synced=True and
// Ready=True. `observedSize` is the echo controller's own payload: the sync
// controller mirrors it without a line of code about it.
fn outer_reports(outer: &Gadget, size: i32) -> bool {
    let status = match &outer.status {
        Some(s) => s,
        None => return false,
    };
    let generation = outer.metadata.generation;
    let synced = condition(&status.conditions, "Synced");
    let ready = condition(&status.conditions, "Ready");
    generation.is_some()
        && status.observed_generation == generation
        && status.observed_size == Some(size)
        && synced.map(|c| c.status == "True" && c.observed_generation == generation).unwrap_or(false)
        && ready.map(|c| c.status == "True").unwrap_or(false)
}

// The outer copy of an object whose cluster no binding serves: the reason the
// design assigns to an unreachable inner cluster, at the object's generation,
// and not Stalled (the condition clears by itself once the binding exists).
fn reports_inner_unreachable(outer: &Gadget) -> Result<bool, Error> {
    let status = match &outer.status {
        Some(s) => s,
        None => return Ok(false),
    };
    let synced = match condition(&status.conditions, "Synced") {
        Some(c) => c,
        None => return Ok(false),
    };
    if synced.status == "True" {
        error!("the Gadget of an unbound cluster reports Synced=True: {:?}", status);
        return Err(Error::WidgetSyncFailed);
    }
    if synced.reason.as_deref() != Some("InnerUnreachable") {
        // Any other reason is a transient step on the way, so keep waiting;
        // Synced=True above is the only outright failure.
        return Ok(false);
    }
    if status.observed_generation != outer.metadata.generation {
        return Ok(false);
    }
    if condition(&status.conditions, "Stalled").map(|c| c.status == "True").unwrap_or(false) {
        error!("InnerUnreachable is reported as Stalled, which the design calls a transient reason: {:?}", status);
        return Err(Error::WidgetSyncFailed);
    }
    Ok(true)
}

// The status of the outer object as the API server stores it, so the check is on
// the JSON the controller writes and not on the field names the typed wrapper
// happens to accept.
async fn raw_status(client: &Client, kind: &str, name: &str) -> Result<Value, Error> {
    let resource = ApiResource::from_gvk(&GroupVersionKind::gvk("anvil.dev", "v1", kind));
    let api: Api<DynamicObject> = Api::namespaced_with(client.clone(), NAMESPACE, &resource);
    let obj = api.get(name).await.map_err(failed(&format!("get the raw outer {} {}", kind, name)))?;
    Ok(obj.data["status"].clone())
}

// The status object's field names, sorted.
fn field_names(status: &Value) -> Result<Vec<String>, Error> {
    match status.as_object() {
        Some(map) => {
            let mut names: Vec<String> = map.keys().cloned().collect();
            names.sort();
            Ok(names)
        }
        None => {
            error!("the outer status is not a JSON object: {}", status);
            Err(Error::WidgetSyncFailed)
        }
    }
}

pub async fn widget_sync_kinds_e2e_test() -> Result<(), Error> {
    let outer_client = client_for_context(OUTER_CONTEXT).await?;
    let inner_client = client_for_context(INNER_CONTEXT).await?;
    // Both kinds must be installed in both clusters: the controller is
    // configured with both, so a missing CRD would have kept it from booting.
    for (label, client) in [("outer", outer_client.clone()), ("inner", inner_client.clone())] {
        let crd_api: Api<CustomResourceDefinition> = Api::all(client);
        for crd in ["widgets.anvil.dev", "gadgets.anvil.dev"] {
            if let Err(e) = crd_api.get(crd).await {
                error!("No {} CRD in the {} cluster; run tools/two-cluster-test.sh first.", crd, label);
                return Err(Error::CRDGetFailed(e));
            }
        }
    }
    let outer = Gadgets { cluster: "outer", api: Api::namespaced(outer_client.clone(), NAMESPACE) };
    let inner = Gadgets { cluster: "inner", api: Api::namespaced(inner_client.clone(), NAMESPACE) };

    // 1. A Gadget named after the binding's cluster is mirrored with its spec
    //    verbatim. Its cluster comes from metadata.name (the kind's selector is
    //    `name`), so nothing in the spec says where it goes.
    outer
        .api
        .create(&PostParams::default(), &gadget(BOUND_CLUSTER, 2))
        .await
        .map_err(failed("create outer gadget"))?;
    let (o, i) = (outer.clone(), inner.clone());
    let mirror_uid = wait_for("gadget mirror exists with the outer spec", TIMEOUT, move || {
        let (o, i) = (o.clone(), i.clone());
        async move {
            let outer_obj = match o.get_opt(BOUND_CLUSTER).await? { Some(g) => g, None => return Ok(None) };
            let inner_obj = match i.get_opt(BOUND_CLUSTER).await? { Some(g) => g, None => return Ok(None) };
            if !is_mirror_of(&inner_obj, &outer_obj) {
                return Ok(None);
            }
            // The whole spec, not only the fields the test built it from.
            if inner_obj.spec.size != 2 || inner_obj.spec.labels != outer_obj.spec.labels {
                error!("the mirror's spec is not the outer spec: {:?}", inner_obj.spec);
                return Err(Error::WidgetSyncFailed);
            }
            Ok(inner_obj.metadata.uid.clone())
        }
    })
    .await?;
    info!("gadget mirror {} has uid {}", BOUND_CLUSTER, mirror_uid);

    // 2. The echo controller's status comes back through the sync controller:
    //    observedSize is payload the sync controller has no knowledge of, and it
    //    arrives on the outer copy stamped with the outer generation, which is 1
    //    for a fresh object.
    let (o, i) = (outer.clone(), inner.clone());
    wait_until("outer gadget reports observedSize 2 at generation 1 with Synced=True", TIMEOUT, move || {
        let (o, i) = (o.clone(), i.clone());
        async move {
            let inner_obj = i.get(BOUND_CLUSTER).await?;
            let outer_obj = o.get(BOUND_CLUSTER).await?;
            Ok(inner_caught_up(&inner_obj)
                && outer_obj.metadata.generation == Some(1)
                && outer_reports(&outer_obj, 2))
        }
    })
    .await?;
    // The mirrored remainder is the whole payload of the kind and nothing else:
    // the sync controller replaces observedGeneration and conditions and copies
    // the rest as it found it.
    let status = raw_status(&outer_client, "Gadget", BOUND_CLUSTER).await?;
    let names = field_names(&status)?;
    if names != vec!["conditions", "observedGeneration", "observedSize"] {
        error!("the outer Gadget status carries {:?}, expected the mirrored remainder only: {}", names, status);
        return Err(Error::WidgetSyncFailed);
    }
    info!("outer Gadget status fields: {:?}", names);

    // 3. A Gadget whose name is no binding of this process: the reconciler does
    //    not serve that binding, so the outer copy reports InnerUnreachable and
    //    no mirror is ever created. The first reconcile ends without a network
    //    round trip, so the status is written as soon as the outer watch has
    //    delivered the create; ONE_RECONCILE bounds it even if the very first
    //    attempt is lost. The object has no history of failures when it is
    //    created, so this first report is at the head of the backoff schedule
    //    however long the object goes on failing afterwards.
    outer
        .api
        .create(&PostParams::default(), &gadget(UNBOUND_CLUSTER, 5))
        .await
        .map_err(failed("create outer gadget for an unbound cluster"))?;
    let (o, i) = (outer.clone(), inner.clone());
    wait_until("outer gadget of an unbound cluster reports Synced=False/InnerUnreachable", ONE_RECONCILE, move || {
        let (o, i) = (o.clone(), i.clone());
        async move {
            if let Some(created) = i.get_opt(UNBOUND_CLUSTER).await? {
                error!("the controller created {:?} in the inner cluster for an unbound cluster", created.metadata);
                return Err(Error::WidgetSyncFailed);
            }
            reports_inner_unreachable(&o.get(UNBOUND_CLUSTER).await?)
        }
    })
    .await?;
    // ... and it stays that way: through a window that contains several of the
    // object's failed attempts (see RETRY_WINDOW), nothing appears. This wait is
    // spent in full: it ends on the clock, not on a condition.
    let (o, i) = (outer.clone(), inner.clone());
    let started = std::time::Instant::now();
    wait_until("no mirror is created for an unbound cluster through a requeue window", RETRY_WINDOW + MARGIN, move || {
        let (o, i) = (o.clone(), i.clone());
        async move {
            if let Some(created) = i.get_opt(UNBOUND_CLUSTER).await? {
                error!("the controller created {:?} in the inner cluster for an unbound cluster", created.metadata);
                return Err(Error::WidgetSyncFailed);
            }
            reports_inner_unreachable(&o.get(UNBOUND_CLUSTER).await?)?;
            Ok(started.elapsed() >= RETRY_WINDOW)
        }
    })
    .await?;

    // 4. The Widget's outer status is unchanged by the second kind: the same
    //    JSON field names as before, `ready` and `observedCount` among them,
    //    which now travel as the opaque remainder of the mirrored status.
    let widgets: Api<Widget> = Api::namespaced(outer_client.clone(), NAMESPACE);
    widgets
        .create(&PostParams::default(), &widget(WIDGET_NAME, 4, "kinds"))
        .await
        .map_err(failed("create outer widget"))?;
    let w = widgets.clone();
    wait_until("outer widget reports count 4 at generation 1 with Synced=True", TIMEOUT, move || {
        let w = w.clone();
        async move {
            let outer_obj = w.get(WIDGET_NAME).await.map_err(failed("get outer widget"))?;
            let status = match &outer_obj.status { Some(s) => s, None => return Ok(false) };
            let synced = status.conditions.as_ref().and_then(|c| c.iter().find(|c| c.type_ == "Synced"));
            Ok(outer_obj.metadata.generation == Some(1)
                && status.observed_generation == Some(1)
                && status.ready == Some(true)
                && status.observed_count == Some(4)
                && synced.map(|c| c.status == "True").unwrap_or(false))
        }
    })
    .await?;
    let status = raw_status(&outer_client, "Widget", WIDGET_NAME).await?;
    let names = field_names(&status)?;
    if names != vec!["conditions", "observedCount", "observedGeneration", "ready"] {
        error!("the outer Widget status carries {:?}, which renames what it reported before: {}", names, status);
        return Err(Error::WidgetSyncFailed);
    }
    if status["ready"] != json!(true) || status["observedCount"] != json!(4) {
        error!("the outer Widget status does not report ready and observedCount as before: {}", status);
        return Err(Error::WidgetSyncFailed);
    }
    info!("outer Widget status fields: {:?}", names);

    // Clean up: the janitor collects the mirrors of the deleted outer copies,
    // which also shows it runs for both kinds.
    outer.api.delete(BOUND_CLUSTER, &DeleteParams::default()).await.map_err(failed("delete outer gadget"))?;
    outer
        .api
        .delete(UNBOUND_CLUSTER, &DeleteParams::default())
        .await
        .map_err(failed("delete outer gadget of the unbound cluster"))?;
    widgets.delete(WIDGET_NAME, &DeleteParams::default()).await.map_err(failed("delete outer widget"))?;
    // The janitors have been reconciling both mirrors successfully all along, so
    // their next run is a resync away and not a backed-off retry: ONE_RECONCILE.
    let i = inner.clone();
    wait_until("the gadget mirror is collected by the janitor", ONE_RECONCILE, move || {
        let i = i.clone();
        async move { Ok(i.get_opt(BOUND_CLUSTER).await?.is_none()) }
    })
    .await?;
    let inner_widgets: Api<Widget> = Api::namespaced(inner_client.clone(), NAMESPACE);
    wait_until("the widget mirror is collected by the janitor", ONE_RECONCILE, move || {
        let inner_widgets = inner_widgets.clone();
        async move {
            match inner_widgets.get(WIDGET_NAME).await {
                Ok(_) => Ok(false),
                Err(kube::Error::Api(ErrorResponse { code: 404, .. })) => Ok(true),
                Err(e) => Err(Error::WidgetLookupFailed(e)),
            }
        }
    })
    .await?;

    info!("E2e test passed.");
    Ok(())
}
