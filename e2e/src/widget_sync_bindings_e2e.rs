#![allow(unused_imports)]
#![allow(unused_variables)]
// End-to-end test of the bindings of the widget sync controller
// (doc/widget_sync_fanout_design.md, sections 1.2 to 1.4), against the three
// kind clusters tools/two-cluster-test.sh creates: the outer cluster
// (kind-widget-sync-outer) and the inner clusters of the bindings `default/a`
// (kind-widget-sync-inner-a) and `default/b` (kind-widget-sync-inner-b), whose
// credentials are the Secrets `a-kubeconfig` and `b-kubeconfig` of the outer
// namespace `default`. The scenarios of one binding are widget_sync_e2e.rs;
// this file checks, in order:
//   1. fan-out: two Widgets of the same namespace, one bound to `a` and one to
//      `b`, are each mirrored into their own inner cluster and into no other;
//   2. the claim: a copy of `a-kubeconfig` in a second namespace `tenant` is the
//      binding `tenant/a`, which points at a cluster claimed by `default/a`. It
//      is refused: a Widget of `tenant` bound to `a` reports
//      Synced=False/Forbidden with Stalled=True, no mirror of it is ever
//      created, and the mirrors of namespace `default` in cluster `a` survive a
//      janitor window untouched (a refused binding runs no janitor);
//   3. a missing Secret reads as an unreachable cluster: deleting `b-kubeconfig`
//      makes the Widget bound to `b` report Synced=False/InnerUnreachable within
//      two requeues, and re-creating the Secret brings it back to Synced=True.
use k8s_openapi::api::core::v1::{Namespace, Secret};
use k8s_openapi::apiextensions_apiserver::pkg::apis::apiextensions::v1::CustomResourceDefinition;
use kube::{
    api::{Api, DeleteParams, ObjectMeta, PostParams, ResourceExt},
    core::ErrorResponse,
    Client,
};
use std::time::{Duration, Instant};
use tokio::time::sleep;
use tracing::*;
use verifiable_controllers::crds::{Widget, WidgetCondition, WidgetSpec, WidgetStatus};
use verifiable_controllers::shim_layer::bindings::{CLUSTER_NAME_LABEL, SECRET_TYPE};

use crate::common::*;
use crate::widget_sync_e2e::{
    client_for_context, failed, is_mirror_of, outer_reports, still_the_same_mirror, synced_condition, uid, wait_for,
    wait_until, Widgets, JANITOR_WINDOW, MARGIN, ONE_RECONCILE, OUTER_CONTEXT, REQUEUE, TIMEOUT,
};

const INNER_A_CONTEXT: &str = "kind-widget-sync-inner-a";
const INNER_B_CONTEXT: &str = "kind-widget-sync-inner-b";
// The namespace the copied kubeconfig Secret is put in, and the binding it makes.
const TENANT: &str = "tenant";
// The Secret of a binding, by the Cluster API convention the controller reads.
const A_SECRET: &str = "a-kubeconfig";
const B_SECRET: &str = "b-kubeconfig";

// A binding whose Secret went away is not noticed by any watch of the object's
// own cluster: the outer copy is repaired at its requeue, and the first attempt
// after the Secret went may still be the one that ran just before. Two requeues
// plus a failed attempt and slack is the bound a healthy controller meets.
const TWO_RECONCILES: Duration = Duration::from_secs(2 * REQUEUE.as_secs() + ONE_RECONCILE.as_secs() - REQUEUE.as_secs());

fn widget_in(namespace: &str, name: &str, cluster: &str, count: i32) -> Widget {
    let spec = WidgetSpec {
        cluster_name: cluster.to_string(),
        count,
        message: Some(format!("bound to {}", cluster)),
    };
    let mut w = Widget::new(name, spec);
    w.metadata.namespace = Some(namespace.to_string());
    w
}

// The condition of the given type on the outer copy, if it has one.
fn condition_of<'a>(outer: &'a Widget, type_: &str) -> Option<&'a WidgetCondition> {
    outer.status.as_ref()?.conditions.as_ref()?.iter().find(|c| c.type_ == type_)
}

// The outer copy reports the reconciler's permanent refusal: Synced=False with
// the given reason, and Stalled=True, which is what an operator alerts on.
fn reports_stalled(outer: &Widget, reason: &str) -> bool {
    let synced = match condition_of(outer, "Synced") {
        Some(c) => c,
        None => return false,
    };
    let stalled = condition_of(outer, "Stalled");
    synced.status == "False"
        && synced.reason.as_deref() == Some(reason)
        && stalled.map(|c| c.status == "True").unwrap_or(false)
}

// The outer copy reports the reason of a transient failure; Stalled is not
// asserted here, since InnerUnreachable is by design not a stalled condition.
fn reports_reason(outer: &Widget, reason: &str) -> bool {
    condition_of(outer, "Synced")
        .map(|c| c.status == "False" && c.reason.as_deref() == Some(reason))
        .unwrap_or(false)
}

// An object of the inner cluster must never appear. Anything but a 404 fails the
// test, so an absence is never the answer of an unreachable cluster.
async fn must_stay_absent(widgets: &Widgets, name: &str, why: &str) -> Result<(), Error> {
    if let Some(found) = widgets.get_opt(name).await? {
        error!("{}: Widget {} is in the {} cluster: {:?}", why, name, widgets.cluster, found.metadata);
        return Err(Error::WidgetSyncFailed);
    }
    Ok(())
}

// The kubeconfig Secret of a binding, as the controller reads it: the Cluster
// API convention, checked here so that a testbed that stopped writing the type
// or the label fails as itself rather than as a controller that binds nothing.
async fn get_secret(secrets: &Api<Secret>, name: &str) -> Result<Secret, Error> {
    let secret = secrets.get(name).await.map_err(|e| {
        error!("the binding Secret {} is not in the outer cluster: {}", name, e);
        Error::WidgetSyncFailed
    })?;
    let cluster = name.strip_suffix("-kubeconfig").unwrap_or(name);
    if secret.type_.as_deref() != Some(SECRET_TYPE)
        || secret.labels().get(CLUSTER_NAME_LABEL).map(|s| s.as_str()) != Some(cluster)
    {
        error!(
            "the binding Secret {} is not of the Cluster API convention (type {:?}, labels {:?}); tools/two-cluster-test.sh writes it",
            name, secret.type_, secret.metadata.labels
        );
        return Err(Error::WidgetSyncFailed);
    }
    Ok(secret)
}

// A copy of `secret` under `name` in `namespace`, carrying its data, its type
// and its labels: a re-created binding credential, or the copied one of the
// claim scenario. The type `cluster.x-k8s.io/secret` and the label
// `cluster.x-k8s.io/cluster-name` are what makes a Secret a binding
// (doc/widget_sync_fanout_design.md, section 1.2), so a copy without them would
// be no binding at all and the scenario would prove nothing.
fn copy_of(secret: &Secret, namespace: &str, name: &str) -> Secret {
    Secret {
        metadata: ObjectMeta {
            name: Some(name.to_string()),
            namespace: Some(namespace.to_string()),
            labels: secret.metadata.labels.clone(),
            ..ObjectMeta::default()
        },
        data: secret.data.clone(),
        string_data: secret.string_data.clone(),
        type_: secret.type_.clone(),
        ..Secret::default()
    }
}

pub async fn widget_sync_bindings_e2e_test() -> Result<(), Error> {
    let outer_client = client_for_context(OUTER_CONTEXT).await?;
    let inner_a_client = client_for_context(INNER_A_CONTEXT).await?;
    let inner_b_client = client_for_context(INNER_B_CONTEXT).await?;
    for (label, client) in [
        ("outer", outer_client.clone()),
        ("inner-a", inner_a_client.clone()),
        ("inner-b", inner_b_client.clone()),
    ] {
        let crd_api: Api<CustomResourceDefinition> = Api::all(client);
        if let Err(e) = crd_api.get("widgets.anvil.dev").await {
            error!("No Widget CRD found in the {} cluster; run tools/two-cluster-test.sh first.", label);
            return Err(Error::CRDGetFailed(e));
        }
    }
    let outer = Widgets { cluster: "outer", api: Api::namespaced(outer_client.clone(), "default") };
    let inner_a = Widgets { cluster: "inner-a", api: Api::namespaced(inner_a_client.clone(), "default") };
    let inner_b = Widgets { cluster: "inner-b", api: Api::namespaced(inner_b_client.clone(), "default") };
    let tenant_outer = Widgets { cluster: "outer", api: Api::namespaced(outer_client.clone(), TENANT) };
    let tenant_inner_a = Widgets { cluster: "inner-a", api: Api::namespaced(inner_a_client.clone(), TENANT) };
    let secrets: Api<Secret> = Api::namespaced(outer_client.clone(), "default");
    let tenant_secrets: Api<Secret> = Api::namespaced(outer_client.clone(), TENANT);
    let namespaces: Api<Namespace> = Api::all(outer_client.clone());

    // 1. Fan-out: one Widget per binding, in the same outer namespace.
    outer
        .api
        .create(&PostParams::default(), &widget_in("default", "alpha", "a", 3))
        .await
        .map_err(failed("create outer widget alpha"))?;
    outer
        .api
        .create(&PostParams::default(), &widget_in("default", "beta", "b", 4))
        .await
        .map_err(failed("create outer widget beta"))?;
    let (o, i) = (outer.clone(), inner_a.clone());
    let alpha_mirror_uid = wait_for("alpha is mirrored into cluster a and reports Synced=True", TIMEOUT, move || {
        let (o, i) = (o.clone(), i.clone());
        async move {
            let outer_obj = o.get("alpha").await?;
            let inner_obj = match i.get_opt("alpha").await? { Some(w) => w, None => return Ok(None) };
            Ok(if is_mirror_of(&inner_obj, &outer_obj) && outer_reports(&outer_obj, 3) {
                Some(uid(&inner_obj)?)
            } else {
                None
            })
        }
    })
    .await?;
    let (o, i) = (outer.clone(), inner_b.clone());
    wait_until("beta is mirrored into cluster b and reports Synced=True", TIMEOUT, move || {
        let (o, i) = (o.clone(), i.clone());
        async move {
            let outer_obj = o.get("beta").await?;
            let inner_obj = match i.get_opt("beta").await? { Some(w) => w, None => return Ok(false) };
            Ok(is_mirror_of(&inner_obj, &outer_obj) && outer_reports(&outer_obj, 4))
        }
    })
    .await?;
    // Each mirror is in its own cluster only: a mirror in the other one would
    // mean the binding of an object is not the cluster its spec names.
    must_stay_absent(&inner_b, "alpha", "the Widget bound to a was mirrored into cluster b").await?;
    must_stay_absent(&inner_a, "beta", "the Widget bound to b was mirrored into cluster a").await?;
    info!("fan-out: alpha is in cluster a only, beta in cluster b only");

    // 2. The claim: a copy of a-kubeconfig in another namespace is a second
    //    binding onto the same inner cluster, which is claimed by default/a.
    let a_secret = get_secret(&secrets, A_SECRET).await?;
    let tenant_namespace = Namespace {
        metadata: ObjectMeta { name: Some(TENANT.to_string()), ..ObjectMeta::default() },
        ..Namespace::default()
    };
    match namespaces.create(&PostParams::default(), &tenant_namespace).await {
        Ok(_) => info!("created the outer namespace {}", TENANT),
        Err(kube::Error::Api(ErrorResponse { code: 409, .. })) => info!("the outer namespace {} is already there", TENANT),
        Err(e) => return Err(failed("create the tenant namespace")(e)),
    }
    // From here the second binding onto cluster a exists; the survival check
    // below covers a janitor window that starts now, so that what it shows is
    // that the refused binding ran no janitor, not that the window passed
    // before it existed.
    let refused_at = Instant::now();
    tenant_secrets
        .create(&PostParams::default(), &copy_of(&a_secret, TENANT, A_SECRET))
        .await
        .map_err(failed("copy a-kubeconfig into the tenant namespace"))?;
    tenant_outer
        .api
        .create(&PostParams::default(), &widget_in(TENANT, "gamma", "a", 5))
        .await
        .map_err(failed("create the tenant widget gamma"))?;
    let t = tenant_outer.clone();
    wait_until("the tenant Widget reports Synced=False/Forbidden with Stalled=True", TIMEOUT, move || {
        let t = t.clone();
        async move { Ok(reports_stalled(&t.get("gamma").await?, "Forbidden")) }
    })
    .await?;
    // Nothing of the refused binding ever reached its inner cluster, and the
    // mirrors of the binding that holds the claim are untouched: a refused
    // binding runs no janitor.
    let (ta, i, u) = (tenant_inner_a.clone(), inner_a.clone(), alpha_mirror_uid.clone());
    wait_until(
        "the mirrors of namespace default in cluster a survive the refused binding's janitor window",
        JANITOR_WINDOW + MARGIN,
        move || {
            let (ta, i, u) = (ta.clone(), i.clone(), u.clone());
            async move {
                must_stay_absent(&ta, "gamma", "the refused binding wrote into its inner cluster").await?;
                still_the_same_mirror(&i.get("alpha").await?, &u)?;
                Ok(refused_at.elapsed() >= JANITOR_WINDOW)
            }
        },
    )
    .await?;
    info!("the claim refused the binding {}/a and cost the binding default/a nothing", TENANT);

    // 3. A binding whose Secret goes away is an unreachable inner cluster; the
    //    Secret coming back binds it again.
    let b_secret = get_secret(&secrets, B_SECRET).await?;
    secrets.delete(B_SECRET, &DeleteParams::default()).await.map_err(failed("delete b-kubeconfig"))?;
    info!("deleted the binding Secret {}", B_SECRET);
    let o = outer.clone();
    wait_until("the Widget bound to b reports Synced=False/InnerUnreachable", TWO_RECONCILES, move || {
        let o = o.clone();
        async move { Ok(reports_reason(&o.get("beta").await?, "InnerUnreachable")) }
    })
    .await?;
    secrets
        .create(&PostParams::default(), &copy_of(&b_secret, "default", B_SECRET))
        .await
        .map_err(failed("re-create b-kubeconfig"))?;
    info!("re-created the binding Secret {}", B_SECRET);
    let (o, i) = (outer.clone(), inner_b.clone());
    wait_until("the Widget bound to b is Synced=True again", TWO_RECONCILES, move || {
        let (o, i) = (o.clone(), i.clone());
        async move {
            let outer_obj = o.get("beta").await?;
            let inner_obj = match i.get_opt("beta").await? { Some(w) => w, None => return Ok(false) };
            Ok(is_mirror_of(&inner_obj, &outer_obj) && outer_reports(&outer_obj, 4))
        }
    })
    .await?;

    // Leave the clusters as they were found: the outer copies go, their janitors
    // collect the mirrors, and the copied credential of the refused binding is
    // removed so that a later run starts from one binding per inner cluster.
    tenant_outer.api.delete("gamma", &DeleteParams::default()).await.map_err(failed("delete the tenant widget"))?;
    tenant_secrets.delete(A_SECRET, &DeleteParams::default()).await.map_err(failed("delete the copied Secret"))?;
    namespaces.delete(TENANT, &DeleteParams::default()).await.map_err(failed("delete the tenant namespace"))?;
    outer.api.delete("alpha", &DeleteParams::default()).await.map_err(failed("delete outer widget alpha"))?;
    outer.api.delete("beta", &DeleteParams::default()).await.map_err(failed("delete outer widget beta"))?;
    let (a, b) = (inner_a.clone(), inner_b.clone());
    wait_until("both mirrors are collected by their janitors", ONE_RECONCILE, move || {
        let (a, b) = (a.clone(), b.clone());
        async move { Ok(a.get_opt("alpha").await?.is_none() && b.get_opt("beta").await?.is_none()) }
    })
    .await?;

    info!("E2e test passed.");
    Ok(())
}
