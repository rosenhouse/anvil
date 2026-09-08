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
| outer | `widget-sync-outer` / `kind-widget-sync-outer` | the demo CRDs; users' objects; the verified sync controller (namespace `widget-sync`, one replica, the sync reconcilers and every binding's janitors in one process) |
| inner of binding `default/a` | `widget-sync-inner-a` / `kind-widget-sync-inner-a` | the same CRDs; the mirrors of objects bound to `a`; the unverified echo controller (namespace `widget-echo`), which writes only status |
| inner of binding `default/b` | `widget-sync-inner-b` / `kind-widget-sync-inner-b` | the same, for the objects bound to `b` |

Which inner cluster an object goes to is its **binding**, the pair (namespace,
cluster name), and the controller reaches that cluster through the Secret
`<clusterName>-kubeconfig` of the namespace: `default/a-kubeconfig` and
`default/b-kubeconfig` here. See "Bindings and the claim" below.

## Run

Prerequisites: docker, kind, kubectl, and the toolchain `tools/deploy.sh` uses.

```sh
./tools/two-cluster-test.sh --build          # build images, create the three clusters, deploy
kubectl --context kind-widget-sync-outer apply -f deploy/widget_sync/widget.yaml
kubectl --context kind-widget-sync-outer get widget demo -o yaml
kubectl --context kind-widget-sync-inner-a get widget demo -o yaml
cd e2e && cargo run -- widget-sync           # the end-to-end tests against the same clusters
cd e2e && cargo run -- widget-sync-kinds
cd e2e && cargo run -- widget-sync-bindings
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
- Disconnect `widget-sync-inner-a-control-plane` from the `kind` docker
  network, edit the outer spec, reconnect. While the inner cluster is
  unreachable the outer copy reports `Synced=False/InnerUnreachable` at the new
  generation; after the heal it reaches `Synced=True`. Deleting the binding's
  Secret `default/a-kubeconfig` reads the same way, without touching the
  network; re-creating it binds the cluster again.
- Copy `default/a-kubeconfig` into another namespace under the same name and
  create an object there bound to `a`. The claim refuses the second binding:
  the object reports `Synced=False/Forbidden` with `Stalled=True` and nothing
  of it ever reaches the inner cluster ("Bindings and the claim" below).

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

**Adding a kind.** Its CRD in the outer cluster and in every inner one, one
`--kind` flag in `deploy_local.yaml`, its `<plural>` and `<plural>/status` rules in
`rbac.yaml`, its `<plural>` rules in `rbac_inner.yaml`, and — for the demo —
one `--kind` and the matching rules for the echo controller in
`echo_inner.yaml`, plus a line in that binary's `ECHOES` table if the kind
should report a payload of its own.

## Bindings and the claim

A **binding** is a pair (namespace, cluster name): the objects of that
namespace whose cluster selector names that cluster, and the inner cluster
they are mirrored into. Its credential is the Secret
`<clusterName>-kubeconfig` of that namespace, key `value`, holding a
self-contained kubeconfig — the Cluster API convention, so a management
cluster provides it without any help from us. The controller watches the
Secrets of every namespace (`rbac.yaml` grants `secrets` get, list and watch)
and keeps one pair of clients per binding whose Secret exists. Nothing is
mounted and nothing is configured per binding: adding an inner cluster is
adding its Secret, removing one is removing its Secret.

```sh
kubectl --context kind-widget-sync-outer -n default create secret generic c-kubeconfig --from-file=value=./kubeconfig-of-c
kubectl --context kind-widget-sync-outer -n widget-sync logs deploy/widget-sync-controller | grep '^.*binding default/c'
```

| The binding's Secret | What its objects report | What the controller does |
|---|---|---|
| missing, or without a `value` key | `Synced=False/InnerUnreachable` | nothing: no client is bound, so every request is answered `Timeout` without a round trip. Its janitors do not run, so its mirrors are left alone |
| present but not a parseable kubeconfig, or one the validation below refuses | `Synced=False/InnerUnreachable` | the same, plus one warn line naming the rule it broke; it is retried when the Secret changes |
| present, its cluster unreachable or its credential denied a verb | `InnerUnreachable` (unreachable) or `Forbidden` with `Stalled=True` (denied) | retried with backoff, 1s doubling to 1min, for an unreachable cluster; re-checked every 5 minutes for a denied one |
| present and its cluster claimed by another binding | `Synced=False/Forbidden` with `Stalled=True` | refused: no janitor runs and no request is sent, and it is re-checked every 5 minutes |
| present and good | `Synced=True` once the mirror is there | the janitors of every configured kind run against it |

A changed Secret (a rotated credential; Cluster API rewrites the Secret)
rebuilds the binding's clients and restarts its janitors, with no restart of
the pod.

**What a kubeconfig may contain.** A kubeconfig is a program as much as it is a
credential: the client library it is handed to will run the command a `users[].user.exec`
block names, or the `cmd-path` of an `auth-provider`, inside this pod; it will
read the file a `tokenFile`, `client-certificate`, `client-key` or
`certificate-authority` names — the pod's own ServiceAccount token, for
instance — and send it to whatever `server` the same document names; and
`proxy-url` and `insecure-skip-tls-verify` decide who may answer for the inner
cluster. **Whoever can create such a Secret in a namespace therefore decides
what this controller does for that namespace's bindings.** Grant that right in
a namespace only to whoever you would let run code in the controller's pod.

The controller narrows that to the shape a Cluster API workload cluster's
kubeconfig has, before it builds a client. A Secret whose `value` breaks one of
these rules is logged once at warn with the rule it broke and leaves the
binding unbound (its objects read `InnerUnreachable`); nothing retries it on a
timer, only a change of the Secret does:

- exactly one cluster, one user and one context, and the `current-context` is
  that context and names that cluster and that user;
- the server starts with `https://`;
- no `exec`, no `auth-provider`, no `tokenFile`, no `client-certificate`, no
  `client-key`, no `certificate-authority` — the data forms
  (`certificate-authority-data`, `client-certificate-data`, `client-key-data`,
  an inline `token`) are what a Cluster API kubeconfig uses and are what is
  accepted;
- no `proxy-url` and no `insecure-skip-tls-verify: true` (an explicit `false`
  is the default and is accepted).

This bounds what a Secret can do to: naming an API server this controller then
talks to with the credential in the same document. It does not bound *which*
server that is, so a Secret can still point a binding at a cluster of the
Secret author's choosing — which is what the claim below is about.

**The access check.** Before a binding is used, the controller asks its inner
cluster, with one `SelfSubjectAccessReview` per verb and configured kind in the
binding's namespace, whether the credential may get, list, watch, create,
patch and delete the kind, and whether it may `get` and `create` configmaps in
`kube-system` for the claim. A denial marks that one binding degraded — its
requests are answered `Forbidden` — and is logged; an error means the cluster
did not answer, which leaves the binding unbound and retried. Neither ever
exits the process: one bad inner cluster must not stop the others.

**The claim.** On first contact the controller creates, in the inner cluster,
the ConfigMap `kube-system/anvil-sync-claim` with

```
owner:       <outer cluster id>
namespace:   <binding namespace>
clusterName: <binding cluster name>
```

If it is already there, all three fields are compared. A match is the
binding's own claim (a restart, a re-created Secret); a mismatch means another
binding owns that cluster — the usual cause is a kubeconfig copied into a
second namespace or under a second name — and the binding is **refused**: no
janitor of it is started and the shim answers its every request `Forbidden`,
so its objects report `Synced=False/Forbidden` with `Stalled=True`. This is
what makes "one outer binding per inner cluster", an assumption of the proofs,
true in practice. The refusal is logged once, at warn, with the holder:

```
WARN binding tenant/a: refused, its inner cluster is claimed by owner="7f3c…" binding=default/a.
     Its objects report Synced=False/Forbidden with Stalled=True and no janitor runs for it;
     it is re-checked every 300s.
```

To **release** a claim — the inner cluster is genuinely being handed to
another binding — delete the ConfigMap by hand, with a credential of your own
(the controller may only get and create it):

```sh
kubectl --context kind-widget-sync-inner-a -n kube-system get configmap anvil-sync-claim -o yaml
kubectl --context kind-widget-sync-inner-a -n kube-system delete configmap anvil-sync-claim
```

The next re-check, at most five minutes later or at once if the binding's
Secret is touched, claims it for the binding that is still there.

**The outer cluster id** is the uid of the outer cluster's `kube-system`
namespace, read once at boot: the de facto stable identity of a cluster.
`--outer-cluster-id <id>` (env `OUTER_CLUSTER_ID`) overrides it, for a restore
that recreated that namespace — the claims of the inner clusters name the old
uid and every binding would be refused — and for the case the claim cannot
otherwise tell apart, two management clusters cloned with the same
`kube-system` uid, where the operator must give one of them an id of its own.

## Operating the controller

Manifests: `rbac_inner.yaml` (inner cluster), `rbac.yaml` and
`deploy_local.yaml` (outer cluster).

**The kinds and the bindings.** The reconcilers are parameterized by a kind
and a binding (`doc/widget_sync_fanout_design.md`, sections 2.1 and 3.4). The
kinds come from the `--kind` flags ("Kinds and their shape" above) and the
bindings from Secrets ("Bindings and the claim" above): one sync reconciler
per kind, started at boot, and one janitor per kind and bound inner cluster,
started and stopped with its binding.

**Probes.** A startup probe, `test -f /run/widget-sync/ready`, waits for a
file the binary creates (path from `READY_FILE`, on a small emptyDir) once
every configured kind has passed the boot checks and the sync controllers are
running; it is removed at startup so a restarted container does not inherit
it. The bindings are deliberately not part of readiness: an inner cluster that
is down, or one that refuses this controller, is one binding among many, and a
pod that never became ready for it would take down the bindings that are fine.
It is a startup probe rather than a readiness probe because the file never
disappears again: after the boot checks nothing the binary knows about can
make the pod un-ready, and a binding that goes bad at runtime shows up in the
warn logs and in its objects' conditions, not in the pod's status. There is no
liveness probe: the binary exposes no health endpoint and nothing else that says whether the
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
`<plural>/status` for each configured kind, gets the CRD of each at boot for
the shape check, gets, lists and watches `secrets` in every namespace (the
bindings) and gets the `kube-system` namespace (the outer cluster id). In an
inner cluster its credential needs `<plural>` get, list, watch, create, patch
and delete per kind, and `configmaps` create in `kube-system` with get on
`anvil-sync-claim` (`rbac_inner.yaml`). `rbac.yaml` also binds, in namespace `default`, `get` and
`update` on the single ConfigMap `fault-injection-config`, which only the
crash-testing mode (`controller crash`) touches; `run` mode never uses it. No
`events` verbs: the controller emits none.
