# Widget sync demo

The Widget sync controller runs in an *outer* cluster and keeps, for every
`Widget` created there, a mirror `Widget` with the same namespace, name and spec
in an *inner* cluster, where a real `Widget` implementation acts on it. It
copies the inner status back onto the outer copy. Design and proofs:
`doc/widget_sync_design.md`.

## Clusters

| Cluster | kind name / kubectl context | Runs |
|---|---|---|
| outer | `widget-sync-outer` / `kind-widget-sync-outer` | the Widget CRD; users' `Widget`s; the verified sync controller (namespace `widget-sync`, one replica, sync reconciler and janitor in one process) |
| inner | `widget-sync-inner` / `kind-widget-sync-inner` | the same CRD; the mirrors; the unverified echo controller (namespace `widget-echo`), which writes only status |

The controller reaches the inner cluster through a kubeconfig mounted from the
Secret `widget-sync-remote-kubeconfig`; see "Operating the controller" below.

## Run

Prerequisites: docker, kind, kubectl, and the toolchain `tools/deploy.sh` uses.

```sh
./tools/two-cluster-test.sh --build          # build images, create both clusters, deploy
kubectl --context kind-widget-sync-outer apply -f deploy/widget_sync/widget.yaml
kubectl --context kind-widget-sync-outer get widget demo -o yaml
kubectl --context kind-widget-sync-inner get widget demo -o yaml
cd e2e && cargo run -- widget-sync           # the end-to-end test against the same clusters
```

Without `--build` the script reuses the images
`local/widget-sync-controller:v0.1.0` and `local/widget-echo-controller:v0.1.0`.

## What to look at

On the outer copy:

- `status.observedGeneration == metadata.generation`: the controller has
  processed the current spec.
- Condition `Synced` with `status: "True"` and `observedGeneration ==
  metadata.generation`: the spec is in the inner cluster and `ready` and
  `observedCount` are the inner implementation's status for it.
- Otherwise `Synced` is `False` with reason `InnerConverging`,
  `InnerTerminating` or `ForeignObject`.

The mirror carries `anvil.dev/managed-by: widget-sync` and
`anvil.dev/parent-uid: <outer uid>`, no owner references and no finalizers of
ours.

## Scenarios

- Edit the outer spec. The mirror's spec and generation follow, then the echo
  controller's status, then the outer status at the new generation.
- Patch the mirror's spec in the inner cluster. The controller overwrites it on
  its next reconcile and never copies a status the inner side computed for
  that edit; the outer copy shows at most `Synced=False/InnerConverging`
  briefly.
- Create `Widget{default, other}` in the inner cluster without the label, then
  in the outer cluster. The inner object is never modified; the outer copy
  reports `ForeignObject`.
- Delete the outer copy. The janitor removes the mirror. Delete and recreate
  with the same name: the stale mirror is removed and a new one created.
- Disconnect `widget-sync-inner-control-plane` from the `kind` docker network,
  edit the outer spec, reconnect. `observedGeneration` lags while the inner
  cluster is unreachable and catches up after the heal.

## Operating the controller

Manifests: `rbac_inner.yaml` (inner cluster), `rbac.yaml` and
`deploy_local.yaml` (outer cluster).

**Remote credential.** The Secret `widget-sync-remote-kubeconfig` in the outer
cluster has two keys, mounted into one directory: `kubeconfig`, which names the
inner API server and its CA, and `token`, the bearer token of the inner
service account `widget-sync/widget-sync-remote`. The kubeconfig refers to the
token as `tokenFile: token` (relative to the kubeconfig's directory); kube
re-reads a token file at least once a minute, whereas an inline `token:` is
read once. To rotate, write the new token into the `token` key of the Secret;
the kubelet refreshes the mounted directory and the controller picks it up
within about two minutes with no restart. The testbed uses the inner cluster's
long-lived service-account token Secret (`widget-sync-remote-token`); a
production deployment would rather feed a bound token (`kubectl create token
widget-sync-remote --duration ...`) into the same key on a schedule. At
startup the binary asks the inner cluster, with one `SelfSubjectAccessReview`
per verb, whether the credential may get, list, watch, create, patch and
delete `widgets.anvil.dev`; a 401, 403 or denied verb is logged and the
process exits, so a wrong credential shows up as a crash-looping, never-ready
pod rather than as failing reconciles.

**Probes.** A startup probe, `test -f /run/widget-sync/ready`, waits for a
file the binary creates (path from `READY_FILE`, on a small emptyDir) once the
access check has passed and just before the reconcilers start; it is removed
at startup so a restarted container does not inherit it. It is a startup
probe rather than a readiness probe because the file never disappears again:
after the access check nothing the binary knows about can make the pod
un-ready, and a credential that goes bad at runtime shows up in the warn logs
of failed requests, not in the pod's status. There is no liveness probe: the
binary exposes no health endpoint and nothing else that says whether the
reconcilers are still making progress, and a probe that does not measure that
would only restart healthy pods.

**One replica is not at-most-one.** The proofs assume a single active sync
controller. `replicas: 1` with `strategy: Recreate` keeps the Deployment from
running two pods on purpose, but Kubernetes does not guarantee it: a node that
stops reporting keeps its pod running while the controller-manager, after the
eviction timeout, starts a replacement elsewhere, and a `kubectl delete pod`
during a slow shutdown overlaps the old and new process briefly. Leader
election, which would close that gap, is not implemented.

**Pod hardening.** The image runs as uid 65532 and the pod repeats it with
`runAsNonRoot`; the container drops all capabilities, forbids privilege
escalation, uses the `RuntimeDefault` seccomp profile and a read-only root
filesystem (the ready file's emptyDir is the only writable mount), and has
CPU and memory requests and limits sized for the demo.

**RBAC.** In the outer cluster the controller reads `widgets` and patches
`widgets/status`. `rbac.yaml` also binds, in namespace `default`, `get` and
`update` on the single ConfigMap `fault-injection-config`, which only the
crash-testing mode (`controller crash`) touches; `run` mode never uses it. No
`events` verbs: the controller emits none.
