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
  acted on the current spec, whether or not it succeeded; the outcome is in
  the conditions, all of which carry the same `observedGeneration`.
- Condition `Synced` with `status: "True"` and `observedGeneration ==
  metadata.generation`: the spec is in the inner cluster and `ready` and
  `observedCount` are the inner implementation's status for it.
- Condition `Ready`: `True` exactly when `Synced` is `True` and the inner
  copy's own `Ready` condition (if present) is `True` and its own `Stalled`
  condition (if present) is not; otherwise `False`, with reason `NotSynced`
  when not synced and the inner condition's reason and message otherwise.
- Condition `Stalled`: `True` when the controller is in a permanent case
  (`ForeignObject`, `Forbidden`, `Rejected`) or the inner copy's own
  `Stalled` condition is `True`; the reason is the controller's own when it
  has one, else the inner condition's. `Ready` and `Stalled` are never both
  `True`.

The reasons of a `False` `Synced` condition:

| Reason | Meaning | Stalled | Clears when |
|---|---|---|---|
| `InnerConverging` | the mirror carries the spec; the inner status is for an older generation of it | no | the inner implementation catches up |
| `InnerTerminating` | the mirror has a deletion timestamp | no | the inner side releases it and a new mirror is created |
| `StaleMirror` | the object at the mirror's name is a mirror of a previous incarnation of this copy (label present, other `parent-uid`) | no | the janitor removes it |
| `ForeignObject` | the object at the mirror's name has no mirror identity; it is never touched | yes | the object is removed in the inner cluster |
| `Forbidden` | the inner cluster refused a request for lack of authorization | yes | the credential's RBAC is fixed |
| `InnerUnreachable` | a request timed out or failed server-side; the inner cluster is not answering | no | the inner cluster answers again |
| `CreateFailed` | the Create of the mirror was answered NotFound: the inner namespace is missing | no | the namespace is created |
| `Rejected` | a request was rejected as invalid by the API server's schema or an admission webhook (a patch whose `test` failed after a race on the mirror is reported as `RequestFailed` instead, and the next reconcile retries) | yes | the schema or the object is fixed |
| `RequestFailed` | any other error (a conflict, an object that appeared or vanished between two requests) | no | the next reconcile |

After a failed request the controller writes the status once and requeues;
`ready` and `observedCount` keep their last reported values.

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
  reports `ForeignObject` with `Stalled=True`.
- Delete the outer copy. The janitor removes the mirror. Delete and recreate
  with the same name: the new copy may briefly report `StaleMirror` until the
  janitor removes the old mirror, then a new one is created.
- Disconnect `widget-sync-inner-control-plane` from the `kind` docker network,
  edit the outer spec, reconnect. While the inner cluster is unreachable the
  outer copy reports `Synced=False/InnerUnreachable` at the new generation;
  after the heal it reaches `Synced=True`.

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

**Before restoring the outer cluster.** The janitor recognizes a mirror's
parent by uid: the mirror's `anvil.dev/parent-uid` annotation must equal the
uid of the outer `Widget` of the same namespace and name. A restore of the
outer cluster that issues new uids (Velero, re-applied manifests, a recreated
namespace, a GitOps re-bootstrap; an etcd snapshot restore keeps uids) makes
every mirror's annotation stale at once, so the janitor would delete every
mirror and the sync reconciler would then create each one afresh, which in
the Cluster API setting means every workload cluster is torn down and
rebuilt. To withhold the janitor's deletes for the duration of such an event,
add the key `pause` to the ConfigMap `widget-sync-janitor`; the binary checks
the mounted file before every Delete, so the pause takes effect within the
kubelet's ConfigMap sync period (about a minute) and needs no restart:

```sh
kubectl --context kind-widget-sync-outer -n widget-sync patch configmap widget-sync-janitor --type merge -p '{"data":{"pause":""}}'
kubectl --context kind-widget-sync-outer -n widget-sync logs deploy/widget-sync-controller | grep 'janitor paused'   # each withheld delete
kubectl --context kind-widget-sync-outer -n widget-sync patch configmap widget-sync-janitor --type json -p '[{"op":"remove","path":"/data/pause"}]'
```

The recommended sequence is: pause, restore the outer cluster, look at what
the restore produced, decide, resume. While paused, the janitor answers each
stale mirror with a withheld delete (a warn log with `cause="janitor
paused"`) and retries it; nothing else changes, and the sync reconciler never
adopts: a restored outer `Widget` whose uid differs from the mirror's
annotation reports `Synced=False/ForeignObject` and gets a new mirror only
after the old one is gone. Resuming therefore lets the janitor delete every
mirror whose annotation no longer matches, and the sync reconciler then
recreates them; what the pause buys is the time to confirm that the restore
is the intended one, or to redo it from an etcd snapshot, which keeps uids,
before that happens. Re-stamping a mirror's annotation or stripping its label
by hand is an edit the proofs' rely excludes (`doc/widget_sync_design.md`,
section 2.3) and is not a way out. Withholding a delete cannot violate
anything the controller is verified for: R3 and R3s promise that a stale
mirror is eventually removed, and they resume once the key is deleted; the
paused period only defers that cleanup.

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
filesystem (the ready file's emptyDir is the only writable mount; the pause
gate's ConfigMap is mounted read-only), and has CPU and memory requests and
limits sized for the demo.

**RBAC.** In the outer cluster the controller reads `widgets` and patches
`widgets/status`. `rbac.yaml` also binds, in namespace `default`, `get` and
`update` on the single ConfigMap `fault-injection-config`, which only the
crash-testing mode (`controller crash`) touches; `run` mode never uses it. No
`events` verbs: the controller emits none.
