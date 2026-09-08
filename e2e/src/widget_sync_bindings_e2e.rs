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
//      two requeues, and re-creating the Secret brings it back to Synced=True;
//   4. a rotated credential: the `value` of `a-kubeconfig` is replaced by an
//      equivalent kubeconfig with different bytes, which rebuilds the binding's
//      clients and restarts its janitors. The bound Widget keeps its mirror and
//      keeps reporting Synced=True, and an edit made after the rotation still
//      reaches the inner cluster -- so the rebuilt clients are the working ones;
//   5. the claim is re-created: deleting `kube-system/anvil-sync-claim` in
//      inner-a is answered, within the bound binding's re-check interval, by the
//      same claim written again, which is what keeps a released cluster from
//      being taken by a second binding unnoticed.
use k8s_openapi::api::core::v1::{ConfigMap, Namespace, Secret};
use k8s_openapi::ByteString;
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
use verifiable_controllers::shim_layer::bindings::{
    BOUND_RECHECK_INTERVAL, CLAIM_NAME, CLAIM_NAMESPACE, CLUSTER_NAME_LABEL, SECRET_KEY, SECRET_TYPE,
};

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

// A claim that was deleted is written again at the bound binding's next
// re-check; this is that interval with the slack of a poll and a round trip.
const CLAIM_RECHECK: Duration = Duration::from_secs(BOUND_RECHECK_INTERVAL.as_secs() + MARGIN.as_secs());

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

// The same Secret with the same kubeconfig, byte for byte different: a YAML
// comment ahead of it, which every parser ignores. A rotation writes new bytes
// into the same Secret, and new bytes are exactly what the controller compares,
// so this is a rotation as far as it is concerned -- while the credential still
// works, which is what lets the test say what a rebuilt binding must go on
// doing. Keeping the resourceVersion makes it a replace of the object read.
fn rotated(secret: &Secret) -> Result<Secret, Error> {
    let mut rotated = secret.clone();
    let data = rotated.data.as_mut().ok_or_else(|| {
        error!("the binding Secret has no data");
        Error::WidgetSyncFailed
    })?;
    let value = data.get(SECRET_KEY).ok_or_else(|| {
        error!("the binding Secret has no {:?} key", SECRET_KEY);
        Error::WidgetSyncFailed
    })?;
    let mut bytes = b"# rotated by the bindings e2e; the same credential, other bytes\n".to_vec();
    bytes.extend_from_slice(&value.0);
    data.insert(SECRET_KEY.to_string(), ByteString(bytes));
    Ok(rotated)
}

// Create `name` if it is not there. Both clusters need the tenant namespace:
// the outer one to hold the copied Secret and the refused binding's Widget, the
// inner one so that "no mirror of it was ever created" is a statement about the
// mirror and not about a namespace that does not exist -- a get in a missing
// namespace is a 404 too.
async fn ensure_namespace(namespaces: &Api<Namespace>, name: &str, cluster: &str) -> Result<(), Error> {
    let namespace = Namespace {
        metadata: ObjectMeta { name: Some(name.to_string()), ..ObjectMeta::default() },
        ..Namespace::default()
    };
    match namespaces.create(&PostParams::default(), &namespace).await {
        Ok(_) => info!("created the namespace {} in the {} cluster", name, cluster),
        Err(kube::Error::Api(ErrorResponse { code: 409, .. })) => {
            info!("the namespace {} is already in the {} cluster", name, cluster)
        }
        Err(e) => return Err(failed("create the tenant namespace")(e)),
    }
    Ok(())
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
    let inner_a_namespaces: Api<Namespace> = Api::all(inner_a_client.clone());
    // The claim of the binding default/a, in its inner cluster.
    let claims: Api<ConfigMap> = Api::namespaced(inner_a_client.clone(), CLAIM_NAMESPACE);

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
    ensure_namespace(&namespaces, TENANT, "outer").await?;
    // The same namespace in the inner cluster, so that "gamma never reached
    // cluster a" is about the mirror: without it the check would pass on a 404
    // for the namespace and would say nothing at all.
    ensure_namespace(&inner_a_namespaces, TENANT, "inner-a").await?;
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
    // The survival window starts here, when the refusal is first observed, not
    // when the copied Secret was created: until the controller has answered
    // `gamma` with Forbidden the refused binding may not have been attempted at
    // all, and a window measured from before that could pass without the
    // refused binding ever having had the chance to run a janitor.
    let refused_at = Instant::now();
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

    // 4. A rotated credential. The same kubeconfig with other bytes is what
    //    Cluster API writes when it rotates one: the binding's clients are
    //    rebuilt and its janitors restarted, in place, with no restart of the
    //    pod. What must survive that is the binding's work -- the mirror is not
    //    collected and not replaced -- and what must follow it is the next edit,
    //    which can only reach the inner cluster through the new clients.
    let rotated_a = rotated(&get_secret(&secrets, A_SECRET).await?)?;
    secrets
        .replace(A_SECRET, &PostParams::default(), &rotated_a)
        .await
        .map_err(failed("rotate the credential of the binding default/a"))?;
    info!("rotated the credential in {}: the same kubeconfig, other bytes", A_SECRET);
    let mut edited = outer.get("alpha").await?;
    edited.spec.count = 7;
    outer
        .api
        .replace("alpha", &PostParams::default(), &edited)
        .await
        .map_err(failed("edit alpha after the rotation"))?;
    let (o, i, u) = (outer.clone(), inner_a.clone(), alpha_mirror_uid.clone());
    wait_until("after the rotation alpha reaches Synced=True at its new spec", TIMEOUT, move || {
        let (o, i, u) = (o.clone(), i.clone(), u.clone());
        async move {
            let outer_obj = o.get("alpha").await?;
            // A rebuild that lost the cluster would say so here, and it is a
            // failure of the test rather than something to wait out.
            for reason in ["Forbidden", "InnerUnreachable"] {
                if reports_reason(&outer_obj, reason) {
                    error!("the rotated credential left the binding unusable: alpha reports {}", reason);
                    return Err(Error::WidgetSyncFailed);
                }
            }
            let inner_obj = match i.get_opt("alpha").await? { Some(w) => w, None => return Ok(false) };
            // The mirror is the one from before the rotation: restarting the
            // janitors is not an occasion to collect and recreate mirrors.
            still_the_same_mirror(&inner_obj, &u)?;
            Ok(is_mirror_of(&inner_obj, &outer_obj) && outer_reports(&outer_obj, 7))
        }
    })
    .await?;
    info!("the rotated credential rebuilt the binding default/a without disturbing its mirrors");

    // 5. The claim of a bound binding is re-created when it is removed. Deleting
    //    it by hand is how an operator releases a cluster; while it is gone the
    //    cluster is unclaimed and a second binding could take it, so the binding
    //    that is still there writes its claim again at its next re-check (and
    //    says so at warn).
    let held = claims.get(CLAIM_NAME).await.map_err(failed("read the claim of the binding default/a"))?;
    let held_data = held.data.clone();
    claims
        .delete(CLAIM_NAME, &DeleteParams::default())
        .await
        .map_err(failed("delete the claim in inner-a"))?;
    info!("deleted {}/{} in inner-a", CLAIM_NAMESPACE, CLAIM_NAME);
    let c = claims.clone();
    wait_until("the claim of default/a is written again, with the same owner", CLAIM_RECHECK, move || {
        let (c, held_data) = (c.clone(), held_data.clone());
        async move {
            match c.get_opt(CLAIM_NAME).await.map_err(failed("read the claim in inner-a"))? {
                None => Ok(false),
                Some(claim) => {
                    if claim.data != held_data {
                        error!("the claim was re-created with other data: {:?}, was {:?}", claim.data, held_data);
                        return Err(Error::WidgetSyncFailed);
                    }
                    Ok(true)
                }
            }
        }
    })
    .await?;
    info!("the released claim was taken again by the binding that holds the cluster");

    // Leave the clusters as they were found: the outer copies go, their janitors
    // collect the mirrors, and the copied credential of the refused binding is
    // removed so that a later run starts from one binding per inner cluster.
    tenant_outer.api.delete("gamma", &DeleteParams::default()).await.map_err(failed("delete the tenant widget"))?;
    tenant_secrets.delete(A_SECRET, &DeleteParams::default()).await.map_err(failed("delete the copied Secret"))?;
    namespaces.delete(TENANT, &DeleteParams::default()).await.map_err(failed("delete the tenant namespace"))?;
    inner_a_namespaces
        .delete(TENANT, &DeleteParams::default())
        .await
        .map_err(failed("delete the tenant namespace in inner-a"))?;
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
