#![allow(unused_imports)]
#![allow(unused_variables)]
// End-to-end test of the widget sync example against the binding `default/a` of
// the three kind clusters tools/two-cluster-test.sh creates (kubectl contexts
// kind-widget-sync-outer and kind-widget-sync-inner-a). The scenarios of the
// bindings themselves, which use the second inner cluster too, are in
// widget_sync_bindings_e2e.rs. It checks, in order:
//   1. a Widget created in the outer cluster gets a mirror in the inner cluster
//      with the same spec, our label and parent-uid annotation, and no owner
//      references;
//   2. the outer copy's status reports the inner copy's status, stamped with the
//      outer generation (1 for a fresh object) and a true Synced condition;
//   3. a spec change bumps the outer generation by exactly one, propagates, and
//      the status catches up at the new generation;
//   4. an out-of-band edit of the mirror's spec in the inner cluster is
//      overwritten with the outer spec within the sync reconciler's requeue
//      interval, and the outer status never reports the count of the edit;
//   5. a foreign inner object with the same name is refused, not adopted: it stays
//      untouched and the outer copy reports Synced=False/ForeignObject;
//   6. a mirror whose parent is alive survives the janitor: for longer than the
//      janitor's resync interval, from the moment step 1 first saw it, it keeps
//      its uid and never carries a deletion timestamp (a janitor that recognised
//      no parent would delete it and the sync reconciler would recreate it under
//      a new uid);
//   7. an out-of-band delete of the mirror is repaired: the sync reconciler
//      recreates it with the outer spec and the same parent uid, and the outer
//      status is Synced=True against the recreated mirror;
//   8. deleting the outer copy and recreating it at once under the same name with
//      another spec makes the janitor collect the stale mirror (meanwhile the
//      outer copy reports it as ForeignObject or StaleMirror, never as Synced),
//      a fresh mirror with the new parent uid and spec appears, and the outer
//      status converges to Synced=True at generation 1 of the new object;
//   9. deleting the outer copies makes the janitor remove the mirror, while the
//      foreign object survives the deletion of its outer namesake.
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
use kube::{
    api::{Api, DeleteParams, ListParams, Patch, PatchParams, PostParams, ResourceExt},
    config::{KubeConfigOptions, Kubeconfig},
    core::ErrorResponse,
    Client, Config,
};
use serde_json::json;
use std::future::Future;
use std::time::{Duration, Instant};
use tokio::time::sleep;
use tracing::*;
use verifiable_controllers::crds::{Widget, WidgetCondition, WidgetSpec, WidgetStatus};

use crate::common::*;

pub(crate) const OUTER_CONTEXT: &str = "kind-widget-sync-outer";
pub(crate) const INNER_CONTEXT: &str = "kind-widget-sync-inner-a";
pub(crate) const MANAGED_BY_KEY: &str = "anvil.dev/managed-by";
pub(crate) const MANAGED_BY_VALUE: &str = "widget-sync";
pub(crate) const PARENT_UID_KEY: &str = "anvil.dev/parent-uid";
pub(crate) const POLL: Duration = Duration::from_secs(3);
// The generous bound for convergence that also involves the echo controller.
pub(crate) const TIMEOUT: Duration = Duration::from_secs(300);

// Intervals of the controller under test, from src/shim_layer/controller_runtime.rs.
// reconcile_with requeues a finished reconcile after 60s: that is the sync
// reconciler's requeue and the janitor's resync (neither watch relists on its
// own). A failed reconcile is retried by error_policy on a schedule of its own,
// per object: RETRY_BASE after the object's first failure, twice the last delay
// after each further consecutive failure, up to RETRY_CAP -- 10, 20, 40, 80,
// 160, 300, 300, ... seconds -- and back to RETRY_BASE as soon as a reconcile
// of that object succeeds. So an object that has just been reconciled
// successfully is never more than RETRY_BASE from its next attempt, while one
// that has been failing for a few minutes is up to RETRY_CAP from it. A remote
// request times out after 10s (src/bin/widget_sync_controller.rs), so one failed
// attempt costs at most REMOTE_TIMEOUT plus the delay the schedule is at.
pub(crate) const REQUEUE: Duration = Duration::from_secs(60);
pub(crate) const RETRY_BASE: Duration = Duration::from_secs(10);
pub(crate) const RETRY_CAP: Duration = Duration::from_secs(300);
pub(crate) const REMOTE_TIMEOUT: Duration = Duration::from_secs(10);
// Slack for the reconcile itself, the watch latency and the poll period.
pub(crate) const MARGIN: Duration = Duration::from_secs(30);
// Within this bound a controller that was healthy when the trigger arrived has
// run at least one full reconcile of the object, even if its first two attempts
// failed: the requeue, then two attempts at the head of the backoff schedule
// (RETRY_BASE and twice RETRY_BASE), and slack. That the object was healthy is
// what makes the head of the schedule the right part of it: its last reconcile
// succeeded, so its count was forgotten and its next delay is RETRY_BASE. An
// object that has been failing for a while is bounded by BACKED_OFF_RETRY.
pub(crate) const ONE_RECONCILE: Duration = Duration::from_secs(
    REQUEUE.as_secs()
        + 2 * REMOTE_TIMEOUT.as_secs()
        + 3 * RETRY_BASE.as_secs()
        + MARGIN.as_secs(),
);
// The bound for a scenario that repairs a fault an object has been failing on
// long enough to have reached the cap. Nothing in the object's own cluster
// changed when the fault was repaired, so in the worst case the repair reaches
// it only at its next retry: RETRY_CAP, one attempt, and slack. Every scenario
// that can do better does -- it makes the repair produce an event the sync
// runner acts on at once, an edit of the outer object or the same-name trigger
// a re-bound binding's mirror watch emits on its initial list -- and then
// finishes in seconds; this bound is what is left if such an event is lost, and
// costs nothing when it is not.
pub(crate) const BACKED_OFF_RETRY: Duration =
    Duration::from_secs(RETRY_CAP.as_secs() + REMOTE_TIMEOUT.as_secs() + MARGIN.as_secs());
// A window in which the janitor has certainly resynced a mirror at least once.
// The janitor's reconciles of a live mirror succeed, so this is its requeue and
// not its retry schedule.
pub(crate) const JANITOR_WINDOW: Duration = Duration::from_secs(REQUEUE.as_secs() + MARGIN.as_secs());

pub(crate) async fn client_for_context(context: &str) -> Result<Client, Error> {
    let options = KubeConfigOptions { context: Some(context.to_string()), ..Default::default() };
    let config = Config::from_kubeconfig(&options).await.map_err(|e| {
        error!("cannot load kubeconfig context {}: {}", context, e);
        Error::WidgetSyncFailed
    })?;
    Ok(Client::try_from(config)?)
}

fn widget(name: &str, count: i32, message: &str) -> Widget {
    // The binding whose inner cluster these scenarios run against.
    let spec = WidgetSpec { cluster_name: "a".to_string(), count, message: Some(message.to_string()) };
    let mut w = Widget::new(name, spec);
    w.metadata.namespace = Some("default".to_string());
    w
}

// Widgets in namespace `default` of one cluster.
#[derive(Clone)]
pub(crate) struct Widgets {
    pub(crate) cluster: &'static str,
    pub(crate) api: Api<Widget>,
}

impl Widgets {
    // Ok(None) for a 404 only. Every other error fails the test: an absence check
    // must not pass because the cluster was unreachable or the credential forbidden.
    pub(crate) async fn get_opt(&self, name: &str) -> Result<Option<Widget>, Error> {
        match self.api.get(name).await {
            Ok(w) => Ok(Some(w)),
            Err(kube::Error::Api(ErrorResponse { code: 404, .. })) => Ok(None),
            Err(e) => {
                error!("get Widget {} in the {} cluster failed (not a 404): {}", name, self.cluster, e);
                Err(Error::WidgetLookupFailed(e))
            }
        }
    }

    // The Widget, which must exist at this point of the test.
    pub(crate) async fn get(&self, name: &str) -> Result<Widget, Error> {
        self.get_opt(name).await?.ok_or_else(|| {
            error!("Widget {} is absent from the {} cluster but must exist now", name, self.cluster);
            Error::WidgetSyncFailed
        })
    }
}

pub(crate) fn failed(what: &str) -> impl FnOnce(kube::Error) -> Error + '_ {
    move |e| {
        error!("{} failed: {}", what, e);
        Error::WidgetSyncFailed
    }
}

pub(crate) fn uid(w: &Widget) -> Result<String, Error> {
    w.metadata.uid.clone().ok_or_else(|| {
        error!("Widget {} has no uid", w.name_any());
        Error::WidgetSyncFailed
    })
}

pub(crate) fn synced_condition(status: &WidgetStatus) -> Option<&WidgetCondition> {
    status.conditions.as_ref()?.iter().find(|c| c.type_ == "Synced")
}

// The outer copy reports `count` at its current generation with Synced=True.
pub(crate) fn outer_reports(outer: &Widget, count: i32) -> bool {
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

pub(crate) fn is_mirror_of(inner: &Widget, outer: &Widget) -> bool {
    let labels = inner.metadata.labels.as_ref();
    let annotations = inner.metadata.annotations.as_ref();
    labels.and_then(|l| l.get(MANAGED_BY_KEY)).map(|v| v == MANAGED_BY_VALUE).unwrap_or(false)
        && annotations.and_then(|a| a.get(PARENT_UID_KEY)) == outer.metadata.uid.as_ref()
        && inner.metadata.owner_references.as_ref().map(|o| o.is_empty()).unwrap_or(true)
        && inner.spec == outer.spec
}

// The inner implementation has processed the mirror's current spec (the sync
// reconciler copies status only then).
pub(crate) fn inner_caught_up(inner: &Widget) -> bool {
    let observed = inner.status.as_ref().and_then(|s| s.observed_generation);
    observed.is_some() && observed == inner.metadata.generation
}

// The mirror is the object it was: same uid and no deletion timestamp. A janitor
// pass that recognised no parent would delete the mirror and the sync reconciler
// would recreate it under a new uid; the uid comparison catches that even when
// the gap falls between two polls.
pub(crate) fn still_the_same_mirror(inner: &Widget, mirror_uid: &str) -> Result<(), Error> {
    if inner.metadata.uid.as_deref() != Some(mirror_uid) {
        error!(
            "the mirror {} was replaced: uid {} is now {:?}; a janitor pass deleted a mirror whose parent is alive",
            inner.name_any(),
            mirror_uid,
            inner.metadata.uid
        );
        return Err(Error::WidgetSyncFailed);
    }
    if inner.metadata.deletion_timestamp.is_some() {
        error!("the mirror {} (uid {}) is being deleted while its parent is alive", inner.name_any(), mirror_uid);
        return Err(Error::WidgetSyncFailed);
    }
    Ok(())
}

// The outer status never carries a count only an out-of-band edit of the mirror
// asked for.
fn never_reports(outer: &Widget, count: i32) -> Result<(), Error> {
    if outer.status.as_ref().and_then(|s| s.observed_count) == Some(count) {
        error!(
            "the outer copy reports count {}, which only an out-of-band edit of the mirror asked for: {:?}",
            count, outer.status
        );
        return Err(Error::WidgetSyncFailed);
    }
    Ok(())
}

// While the mirror of a previous incarnation of the outer copy is still there, the
// new outer copy may report it as not its own; it must never report Synced=True
// nor InnerConverging, either of which means the stale mirror was adopted.
fn not_synced_to_stale_mirror(outer: &Widget) -> Result<(), Error> {
    let condition = match outer.status.as_ref().and_then(synced_condition) {
        Some(c) => c,
        None => return Ok(()),
    };
    // InnerTerminating is the state the design assigns to a mirror that is being
    // deleted; it cannot show up here without a finalizer on the mirror, but it
    // is not adoption either.
    let stale_reasons = ["ForeignObject", "StaleMirror", "InnerTerminating"];
    if condition.status == "False" && stale_reasons.contains(&condition.reason.as_deref().unwrap_or("")) {
        return Ok(());
    }
    error!(
        "the recreated outer copy reports the stale mirror of its predecessor as {:?}/{:?}, expected Synced=False with one of {:?}",
        condition.status, condition.reason, stale_reasons
    );
    Err(Error::WidgetSyncFailed)
}

// Poll `check` every POLL until it yields a value, or `timeout` elapses.
pub(crate) async fn wait_for<T, F, Fut>(what: &str, timeout: Duration, mut check: F) -> Result<T, Error>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<Option<T>, Error>>,
{
    info!("{}: waiting (up to {:?})", what, timeout);
    let start = Instant::now();
    loop {
        if let Some(value) = check().await? {
            info!("{}: ok after {:?}", what, start.elapsed());
            return Ok(value);
        }
        if start.elapsed() > timeout {
            error!("{}: timed out after {:?}", what, timeout);
            return Err(Error::Timeout);
        }
        sleep(POLL).await;
    }
}

pub(crate) async fn wait_until<F, Fut>(what: &str, timeout: Duration, mut check: F) -> Result<(), Error>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<bool, Error>>,
{
    wait_for(what, timeout, || {
        let fut = check();
        async move { Ok(if fut.await? { Some(()) } else { None }) }
    })
    .await
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
    let outer = Widgets { cluster: "outer", api: Api::namespaced(outer_client.clone(), "default") };
    let inner = Widgets { cluster: "inner", api: Api::namespaced(inner_client.clone(), "default") };

    // 1. Create the outer Widget and wait for its mirror. The uid of the mirror
    //    seen here is what check 6 holds the controller to until the mirror is
    //    deleted on purpose in step 7.
    outer.api.create(&PostParams::default(), &widget("demo", 3, "hello")).await.map_err(failed("create outer widget demo"))?;
    let (o, i) = (outer.clone(), inner.clone());
    let mirror_uid = wait_for("mirror exists with the outer spec", TIMEOUT, move || {
        let (o, i) = (o.clone(), i.clone());
        async move {
            let outer_obj = match o.get_opt("demo").await? { Some(w) => w, None => return Ok(None) };
            let inner_obj = match i.get_opt("demo").await? { Some(w) => w, None => return Ok(None) };
            Ok(if is_mirror_of(&inner_obj, &outer_obj) { Some(uid(&inner_obj)?) } else { None })
        }
    })
    .await?;
    let mirror_seen_at = Instant::now();
    info!("mirror demo has uid {}", mirror_uid);

    // 2. The outer status mirrors the inner status at the outer generation, which
    //    is 1 for a fresh object.
    let (o, i, u) = (outer.clone(), inner.clone(), mirror_uid.clone());
    wait_until("outer status reports count 3 at generation 1 with Synced=True", TIMEOUT, move || {
        let (o, i, u) = (o.clone(), i.clone(), u.clone());
        async move {
            still_the_same_mirror(&i.get("demo").await?, &u)?;
            let outer_obj = o.get("demo").await?;
            Ok(outer_obj.metadata.generation == Some(1) && outer_reports(&outer_obj, 3))
        }
    })
    .await?;

    // 3. A spec change bumps the generation by exactly one, propagates, and the
    //    status catches up at the new generation.
    let generation_before = outer.get("demo").await?.metadata.generation.unwrap_or(0);
    if generation_before != 1 {
        error!("outer demo is at generation {} before its first spec change, expected 1", generation_before);
        return Err(Error::WidgetSyncFailed);
    }
    let patched = outer
        .api
        .patch("demo", &PatchParams::default(), &Patch::Merge(json!({ "spec": { "count": 5 } })))
        .await
        .map_err(failed("patch outer widget demo"))?;
    let generation_after = generation_before + 1;
    if patched.metadata.generation != Some(generation_after) {
        error!(
            "the spec change moved the outer generation from {} to {:?}, expected {}",
            generation_before, patched.metadata.generation, generation_after
        );
        return Err(Error::WidgetSyncFailed);
    }
    info!("spec change bumped the outer generation from {} to {}: ok", generation_before, generation_after);
    let (o, i, u) = (outer.clone(), inner.clone(), mirror_uid.clone());
    wait_until("mirror carries count 5 and outer status reports it at generation 2", TIMEOUT, move || {
        let (o, i, u) = (o.clone(), i.clone(), u.clone());
        async move {
            let inner_obj = i.get("demo").await?;
            still_the_same_mirror(&inner_obj, &u)?;
            let outer_obj = o.get("demo").await?;
            Ok(outer_obj.metadata.generation == Some(generation_after)
                && is_mirror_of(&inner_obj, &outer_obj)
                && inner_obj.spec.count == 5
                && outer_reports(&outer_obj, 5))
        }
    })
    .await?;

    // 4. An out-of-band edit of the mirror's spec is overwritten with the outer
    //    spec, and the count it asked for never reaches the outer status. The
    //    edit bumps the mirror's generation once and the overwrite once more; the
    //    overwrite is a JSON patch that tests the generation, so it lands exactly
    //    once. The inner watch triggers the reconcile at once; the bound is the
    //    requeue that liveness rests on. ONE_RECONCILE and not BACKED_OFF_RETRY
    //    because the reconciler has been succeeding on this object up to the
    //    edit, so its retry schedule is at its head and not at the cap.
    const EDITED_COUNT: i32 = 99;
    let mirror_before = inner.get("demo").await?;
    still_the_same_mirror(&mirror_before, &mirror_uid)?;
    let mirror_generation = mirror_before.metadata.generation.ok_or_else(|| {
        error!("the mirror has no generation: {:?}", mirror_before.metadata);
        Error::WidgetSyncFailed
    })?;
    inner
        .api
        .patch("demo", &PatchParams::default(), &Patch::Merge(json!({ "spec": { "count": EDITED_COUNT } })))
        .await
        .map_err(failed("patch the mirror's spec out of band"))?;
    let (o, i, u) = (outer.clone(), inner.clone(), mirror_uid.clone());
    wait_until("out-of-band spec edit of the mirror is overwritten with the outer spec", ONE_RECONCILE, move || {
        let (o, i, u) = (o.clone(), i.clone(), u.clone());
        async move {
            let inner_obj = i.get("demo").await?;
            still_the_same_mirror(&inner_obj, &u)?;
            let outer_obj = o.get("demo").await?;
            never_reports(&outer_obj, EDITED_COUNT)?;
            if inner_obj.spec != outer_obj.spec {
                return Ok(false);
            }
            if inner_obj.metadata.generation != Some(mirror_generation + 2) {
                error!(
                    "the mirror carries the outer spec again at generation {:?}, expected {} (one edit, one overwrite)",
                    inner_obj.metadata.generation,
                    mirror_generation + 2
                );
                return Err(Error::WidgetSyncFailed);
            }
            Ok(true)
        }
    })
    .await?;
    let (o, i, u) = (outer.clone(), inner.clone(), mirror_uid.clone());
    wait_until("outer status reports count 5 at generation 2 with Synced=True against the overwritten mirror", TIMEOUT, move || {
        let (o, i, u) = (o.clone(), i.clone(), u.clone());
        async move {
            let inner_obj = i.get("demo").await?;
            still_the_same_mirror(&inner_obj, &u)?;
            let outer_obj = o.get("demo").await?;
            never_reports(&outer_obj, EDITED_COUNT)?;
            Ok(inner_obj.spec == outer_obj.spec && inner_caught_up(&inner_obj) && outer_reports(&outer_obj, 5))
        }
    })
    .await?;

    // 5. A foreign inner object is refused, never adopted.
    let mut foreign = widget("foreign", 7, "not yours");
    foreign.metadata.labels = Some([("owner".to_string(), "someone-else".to_string())].into());
    inner.api.create(&PostParams::default(), &foreign).await.map_err(failed("create foreign inner widget"))?;
    outer.api.create(&PostParams::default(), &widget("foreign", 1, "mine")).await.map_err(failed("create outer widget foreign"))?;
    let (o, i, u) = (outer.clone(), inner.clone(), mirror_uid.clone());
    wait_until("outer copy reports ForeignObject and the foreign object is untouched", TIMEOUT, move || {
        let (o, i, u) = (o.clone(), i.clone(), u.clone());
        async move {
            still_the_same_mirror(&i.get("demo").await?, &u)?;
            let outer_obj = o.get("foreign").await?;
            let inner_obj = i.get("foreign").await?;
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
        }
    })
    .await?;

    // 6. The mirror survives the janitor while its parent is alive. Every poll
    //    since step 1 has checked its uid and deletion timestamp; this wait covers
    //    whatever is left of a window that contains at least one janitor resync
    //    of the mirror (the janitor also ran on every event of the mirror so far).
    info!(
        "mirror survival: {:?} of the {:?} window covered by the checks so far",
        mirror_seen_at.elapsed(),
        JANITOR_WINDOW
    );
    let (i, u) = (inner.clone(), mirror_uid.clone());
    wait_until("mirror with a live parent keeps its uid through the janitor's resync window", JANITOR_WINDOW + MARGIN, move || {
        let (i, u) = (i.clone(), u.clone());
        async move {
            still_the_same_mirror(&i.get("demo").await?, &u)?;
            Ok(mirror_seen_at.elapsed() >= JANITOR_WINDOW)
        }
    })
    .await?;

    // 7. An out-of-band delete of the mirror is repaired: the sync reconciler,
    //    triggered by the inner watch and at the latest by its requeue, finds
    //    NotFound and creates the mirror again for the same parent. The delete
    //    is the fault and the repair in one: it is itself the event that
    //    triggers the reconcile, so there is no interval in which the object
    //    fails and backs off, and the bound is ONE_RECONCILE.
    inner.api.delete("demo", &DeleteParams::default()).await.map_err(failed("delete the mirror out of band"))?;
    let (o, i, old) = (outer.clone(), inner.clone(), mirror_uid.clone());
    let recreated_uid = wait_for("mirror deleted out of band is recreated with the outer spec and parent uid", ONE_RECONCILE, move || {
        let (o, i, old) = (o.clone(), i.clone(), old.clone());
        async move {
            let outer_obj = o.get("demo").await?;
            let inner_obj = match i.get_opt("demo").await? { Some(w) => w, None => return Ok(None) };
            if uid(&inner_obj)? == old {
                // The delete has not gone through yet.
                return Ok(None);
            }
            Ok(if is_mirror_of(&inner_obj, &outer_obj) { Some(uid(&inner_obj)?) } else { None })
        }
    })
    .await?;
    info!("recreated mirror demo has uid {}", recreated_uid);
    let (o, i, u) = (outer.clone(), inner.clone(), recreated_uid.clone());
    wait_until("outer status reports count 5 at generation 2 with Synced=True against the recreated mirror", TIMEOUT, move || {
        let (o, i, u) = (o.clone(), i.clone(), u.clone());
        async move {
            let inner_obj = i.get("demo").await?;
            still_the_same_mirror(&inner_obj, &u)?;
            let outer_obj = o.get("demo").await?;
            Ok(inner_obj.spec == outer_obj.spec && inner_caught_up(&inner_obj) && outer_reports(&outer_obj, 5))
        }
    })
    .await?;

    // 8. Delete the outer copy and recreate it at once under the same name with
    //    another spec. The outer copy has no finalizers, so the delete is final
    //    when it returns and the name is free. Nothing in the inner cluster
    //    changes on the outer delete, so the stale mirror is collected at the
    //    janitor's next resync; the delete event then triggers the sync
    //    reconciler, which creates the mirror of the new object. ONE_RECONCILE:
    //    the janitor has been reconciling this mirror successfully every
    //    JANITOR_WINDOW (it found a live parent each time), so its next run is
    //    its resync away, not a backed-off retry. The recreated outer copy
    //    reports the stale mirror through the success path (StaleMirror is a
    //    reported outcome, not a failed request), so it does not back off
    //    either.
    let old_parent_uid = uid(&outer.get("demo").await?)?;
    let stale_mirror_uid = recreated_uid.clone();
    outer.api.delete("demo", &DeleteParams::default()).await.map_err(failed("delete outer widget demo"))?;
    let new_outer =
        outer.api.create(&PostParams::default(), &widget("demo", 8, "again")).await.map_err(failed("recreate outer widget demo"))?;
    let new_parent_uid = uid(&new_outer)?;
    if new_parent_uid == old_parent_uid {
        error!("the recreated outer copy has the uid of the deleted one, {}", old_parent_uid);
        return Err(Error::WidgetSyncFailed);
    }
    info!("outer demo recreated: uid {} replaces {}", new_parent_uid, old_parent_uid);
    let (o, i, stale, parent) = (outer.clone(), inner.clone(), stale_mirror_uid.clone(), new_parent_uid.clone());
    wait_until("stale mirror of the deleted outer copy is collected by the janitor", ONE_RECONCILE, move || {
        let (o, i, stale, parent) = (o.clone(), i.clone(), stale.clone(), parent.clone());
        async move {
            // Outer first, inner second: if the stale mirror is still there at the
            // second read, it was there when the outer status was read, and that
            // status cannot legitimately be Synced.
            let outer_obj = o.get("demo").await?;
            if uid(&outer_obj)? != parent {
                error!("outer demo is not the object the test recreated: {:?}", outer_obj.metadata.uid);
                return Err(Error::WidgetSyncFailed);
            }
            let inner_obj = match i.get_opt("demo").await? { Some(w) => w, None => return Ok(true) };
            if uid(&inner_obj)? != stale {
                return Ok(true);
            }
            not_synced_to_stale_mirror(&outer_obj)?;
            Ok(false)
        }
    })
    .await?;
    let (o, i, stale, parent) = (outer.clone(), inner.clone(), stale_mirror_uid.clone(), new_parent_uid.clone());
    wait_until("new mirror carries the new parent uid and count 8, and the outer status reports it at generation 1", TIMEOUT, move || {
        let (o, i, stale, parent) = (o.clone(), i.clone(), stale.clone(), parent.clone());
        async move {
            let outer_obj = o.get("demo").await?;
            if uid(&outer_obj)? != parent {
                error!("outer demo is not the object the test recreated: {:?}", outer_obj.metadata.uid);
                return Err(Error::WidgetSyncFailed);
            }
            let inner_obj = match i.get_opt("demo").await? { Some(w) => w, None => return Ok(false) };
            if uid(&inner_obj)? == stale {
                error!("the stale mirror {} is back after it was collected", stale);
                return Err(Error::WidgetSyncFailed);
            }
            Ok(outer_obj.metadata.generation == Some(1)
                && is_mirror_of(&inner_obj, &outer_obj)
                && inner_obj.spec.count == 8
                && outer_reports(&outer_obj, 8))
        }
    })
    .await?;

    // 9. Deleting the outer copies: the mirror is collected, the foreign object
    //    survives. ONE_RECONCILE for the same reason as step 8: the janitor was
    //    succeeding on this mirror right up to the outer delete.
    outer.api.delete("demo", &DeleteParams::default()).await.map_err(failed("delete outer widget demo"))?;
    outer.api.delete("foreign", &DeleteParams::default()).await.map_err(failed("delete outer widget foreign"))?;
    let i = inner.clone();
    wait_until("mirror is collected by the janitor", ONE_RECONCILE, move || {
        let i = i.clone();
        async move { Ok(i.get_opt("demo").await?.is_none()) }
    })
    .await?;
    // The janitor has run by now (it reconciles every inner Widget on its own schedule
    // and was triggered by the same deletion); the foreign object must still be there.
    sleep(Duration::from_secs(20)).await;
    match inner.get_opt("foreign").await? {
        Some(w) if w.metadata.deletion_timestamp.is_none() => info!("foreign object survived: ok"),
        other => {
            error!("the foreign object did not survive: {:?}", other);
            return Err(Error::WidgetSyncFailed);
        }
    }

    info!("E2e test passed.");
    Ok(())
}
