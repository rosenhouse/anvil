# Widget sync demo

The Widget sync controller runs in an *outer* cluster and keeps, for every
object of a configured kind created there, a mirror with the same namespace,
name and spec in an *inner* cluster, where a real implementation of that kind
acts on it. It copies the inner status back onto the outer copy. The kinds are
given at boot, not compiled in ("Kinds and their shape" below); the demo runs
`Widget` and `Gadget`. Design and proofs: `doc/widget_sync_design.md` and, for
the kinds and the bindings, `doc/widget_sync_fanout_design.md`.

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

## Kinds and their shape

The controller is not compiled against a kind: it runs for the kinds it is
given at boot (`doc/widget_sync_fanout_design.md`, section 2). The demo
configures two, in `deploy_local.yaml`:

```
widget_sync_controller run \
  --kind anvil.dev/v1/Widget:field:spec.clusterName \
  --kind anvil.dev/v1/Gadget:name
```

`--kind <group>/<version>/<Kind>:<selector>`, repeated; at least one is
required and the same kind twice is refused (two sync controllers on the same
objects is what the proofs exclude). Each kind gets its own sync reconciler
and, per binding, its own janitor. `widget_sync_controller export` prints the
demo CRDs.

The **selector** is the field that says which inner cluster an object belongs
to:

| Selector | The object's cluster is | What the CRD must carry |
|---|---|---|
| `name` | `metadata.name` | nothing; `metadata.name` is immutable by construction |
| `field:spec.<path>` (the `field:` prefix may be dropped) | the string at that path | the field, required and a string, guarded by `x-kubernetes-validations: [{rule: "self == oldSelf"}]` on the field, or the equivalent rule `self.<path> == oldSelf.<path>` on `spec` |

`Widget` uses `field:spec.clusterName`, `Gadget` uses `name` — its own name is
the cluster, the shape of Cluster API's `Cluster` object. Immutability matters
beyond the operational point that editing the field would tear a workload
cluster down and rebuild it: the janitor's delete-soundness invariant rests on
a listed outer object staying selected for the binding it was seen in
(`doc/widget_sync_fanout_design.md`, section 1.1).

**The shape.** The controller reads and writes exactly these fields, and at
boot it fetches each configured kind's CRD in the outer cluster and checks
them:

| Field | Read or written | Requirement on the CRD |
|---|---|---|
| `metadata` | read; the mirror's name, namespace, label and annotation written on create | namespaced scope |
| `spec` | copied verbatim outer to inner; the selector field read when the selector is `field` | the selector field, when used: required string with the immutability rule |
| `status.observedGeneration` | read on the inner copy, written on the outer copy | integer |
| `status.conditions[]` | read on the inner copy (`Ready`, `Stalled`); written on the outer copy (`Synced`, `Ready`, `Stalled`) | array of objects with `type` (string, required), `status` (string, required), `reason`, `message` (strings), `observedGeneration` (integer) |
| every other status field | mirrored verbatim inner to outer while `Synced` | none |
| the status subresource | | enabled, so `metadata.generation` follows the spec |

A status (or a `conditions` item) declared with
`x-kubernetes-preserve-unknown-fields` passes the rows it does not declare;
what it does declare is still checked, since a declared string
`observedGeneration` would reject the integer the controller writes. Anything
outside the table is opaque: `Gadget`'s `spec.size` is copied without the
controller knowing it exists, and its `status.observedSize` comes back on the
outer copy as part of the mirrored remainder.

Inner clusters are not checked for schema parity beyond serving the kind;
parity stays an operational assumption. So does this, for now: **fields are
not removed from a CRD while the controller runs**, so the boot check, once it
passes, stays true. Adding fields is fine. A later pass can watch the CRDs and
stop a kind whose shape breaks.

**A refused kind.** A kind that is not served, is cluster-scoped, or whose CRD
fails a row is a usage error: the controller prints the failing rows and exits
with status 2 before it builds a client or starts a single controller, so the
pod crash-loops and never becomes ready. To see it on the testbed, install a
`Widget` CRD without the immutability rule and restart the controller:

```sh
# The demo CRD minus every x-kubernetes-validations block.
python3 -c 'import sys,yaml
d=yaml.safe_load(open("deploy/widget_sync/crd.yaml"))
def strip(x):
    if isinstance(x,dict): x.pop("x-kubernetes-validations",None); [strip(v) for v in x.values()]
    elif isinstance(x,list): [strip(v) for v in x]
strip(d); yaml.safe_dump(d,sys.stdout)' > /tmp/crd-no-rule.yaml
kubectl --context kind-widget-sync-outer apply -f /tmp/crd-no-rule.yaml
kubectl --context kind-widget-sync-outer -n widget-sync rollout restart deployment/widget-sync-controller
kubectl --context kind-widget-sync-outer -n widget-sync logs deploy/widget-sync-controller
```

The log ends with

```
--kind anvil.dev/v1/Widget:field:spec.clusterName: CRD widgets.anvil.dev does not have the shape the sync controller needs:
  - spec: selector field spec.clusterName: must carry the x-kubernetes-validations rule `self == oldSelf` (or spec the rule `self.clusterName == oldSelf.clusterName`)
```

and the container exits 2. `kubectl apply -f deploy/widget_sync/crd.yaml`
puts the rule back; the next restart boots. The same CRD is accepted for a
`name` selector, which needs no rule, so the reproduction isolates exactly
the row it removes. `cargo test --bin widget_sync_controller` checks that
message without a cluster.

**Adding a kind.** Its CRD in both clusters, one `--kind` flag in
`deploy_local.yaml`, its `<plural>` and `<plural>/status` rules in
`rbac.yaml`, its `<plural>` rules in `rbac_inner.yaml`, and — for the demo —
one `--kind` and the matching rules for the echo controller in
`echo_inner.yaml`, plus a line in that binary's `ECHOES` table if the kind
should report a payload of its own.

## Operating the controller

Manifests: `rbac_inner.yaml` (inner cluster), `rbac.yaml` and
`deploy_local.yaml` (outer cluster).

**The binding.** The reconcilers are parameterized by a kind and a binding
(`doc/widget_sync_fanout_design.md`, sections 2.1 and 3.4). The kinds come
from the `--kind` flags ("Kinds and their shape" above); the binding is still
one, named in `src/bin/widget_sync_controller.rs`: `default/inner`, whose
credential is the kubeconfig at `$REMOTE_KUBECONFIG` (default
`/etc/widget-sync/remote-kubeconfig/kubeconfig`). An object whose selector
names any other cluster has no binding, so every request for it is answered as
if the inner cluster were unreachable and the outer copy reports
`Synced=False/InnerUnreachable`. Discovering the bindings from Secrets is the
follow-up issue.

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
per verb and configured kind, whether the credential may get, list, watch,
create, patch and delete it; a 401, 403 or denied verb is logged and the
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

**RBAC.** In the outer cluster the controller reads `<plural>` and patches
`<plural>/status` for each configured kind, and gets the CRD of each at boot
for the shape check. `rbac.yaml` also binds, in namespace `default`, `get` and
`update` on the single ConfigMap `fault-injection-config`, which only the
crash-testing mode (`controller crash`) touches; `run` mode never uses it. No
`events` verbs: the controller emits none.
