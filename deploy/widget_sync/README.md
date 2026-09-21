# Widget sync demo

The Widget sync controller runs in an *outer* cluster and keeps, for every
object of a configured kind created there, a mirror with the same namespace,
name and spec in an *inner* cluster, where a real implementation of that kind
acts on it. It copies the inner status back onto the outer copy. The kinds are
given at boot, not compiled in ("Kinds and their shape" below); the demo runs
`Widget` and `Gadget`. `doc/widget_sync_design.md` states the design and the
proofs; `doc/widget_sync_fanout_design.md` covers the kinds and the bindings.

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

You need docker, kind, kubectl, and the toolchain `tools/deploy.sh` uses.

```sh
./tools/two-cluster-test.sh --build          # build images, create the three clusters, deploy
kubectl --context kind-widget-sync-outer apply -f deploy/widget_sync/widget.yaml
kubectl --context kind-widget-sync-outer get widget demo -o yaml
kubectl --context kind-widget-sync-inner-a get widget demo -o yaml
kubectl --context kind-widget-sync-outer get widget demo   # once the controller has reconciled it
cd e2e && cargo run -- widget-sync           # the end-to-end tests against the same clusters
cd e2e && cargo run -- widget-sync-kinds
cd e2e && cargo run -- widget-sync-bindings
```

Without `--build` the script reuses the images
`local/widget-sync-controller:v0.1.0` and `local/widget-echo-controller:v0.1.0`.

## What to look at

On an outer copy, `kubectl get widget` prints the binding it names and the three
conditions below; `-o wide` adds the reason of each. Until the controller has
reconciled the object the four condition columns are empty.

```
$ kubectl --context kind-widget-sync-outer get widget
NAME   CLUSTER   SYNCED   READY   STALLED   AGE
demo   a         True     True    False     45s

$ kubectl --context kind-widget-sync-outer get widget -o wide
NAME   CLUSTER   SYNCED   READY   STALLED   AGE   SYNCED-REASON   READY-REASON   STALLED-REASON
demo   a         True     True    False     45s   Synced          Echoed         Synced
```

`READY-REASON` is `Echoed` because that is the reason the demo's inner
implementation writes; a mirror's own reasons come through `Ready` and
`Stalled` once `Synced` is `True`. All three reasons are printed because a
column's JSONPath cannot pick whichever one explains the row: read the one the
condition columns point at. A `Gadget` prints the same without the cluster
column, its own name being the binding. An inner copy has no `Synced` or
`Stalled` of its own, so those columns are empty there. Everything else is in
`-o yaml`.

On the outer copy:

- `status.observedGeneration == metadata.generation`: the controller has
  acted on the current spec, whether or not it succeeded; the outcome is in
  the `Synced`, `Ready` and `Stalled` conditions, which carry the same
  `observedGeneration`.
- Condition `Synced` with `status: "True"` and `observedGeneration ==
  metadata.generation`: the spec is in the inner cluster and `ready` and
  `observedCount` are the inner implementation's status for it.
- Condition `Ready`: `True`, `False` or `Unknown`. While `Synced` is `True`
  it repeats the inner copy's own `Ready` condition (its reason and message
  when it has them, and its status if that is `True`, `False` or `Unknown`;
  any other status reads `Unknown`). Two exceptions: an inner `Stalled=True`
  forces `Ready=False` with that condition's reason and message, and a mirror
  with no `Ready` condition reads `Unknown` with reason
  `NoInnerReadyCondition`. The inner condition's own `observedGeneration` is
  not read; the outer stamp is the generation the sync controller reconciled.
  While `Synced` is `False` the reason is `NotSynced`. The status is
  `Unknown` where the controller has no caught-up inner status for the
  current spec and `False` where it knows no mirror runs that spec. The
  `Ready` column of the table below says which.
- Condition `Stalled`: `True` with the controller's own reason in a case
  nothing the controller does again gets out of; the `Stalled` column of the
  table below says which. Otherwise, while `Synced` is `True` and the inner
  copy has a `Stalled` condition, that condition (same normalization as
  `Ready`). Otherwise `False` with `Synced`'s reason, so a synced mirror with
  no `Stalled` condition reads `Stalled=False/Synced`. `Ready` and `Stalled`
  are never both `True`.
- The conditions after those three: every condition the inner copy carries
  of another type, in the inner order, the first of each type, with status,
  reason and message as the inner copy wrote them and `observedGeneration`
  set to the outer generation at which it was read; the inner condition's
  own `observedGeneration` is not read. While `Synced` is `False` they are
  kept as last reported, with the `observedGeneration` they were read at,
  and filtered the same way: `Synced=False` says the copies are kept, not
  the stamp, which can equal the current generation. An inner `Synced`
  condition is dropped (a Crossplane-style implementation loses its `Synced`
  and has its `Ready` merged). No condition carries `lastTransitionTime`,
  and a CRD whose conditions require it is refused at boot ("Kinds and
  their shape"). In the demo the echo controller writes `Echoed`, which the
  outer copy carries. The rules: `doc/widget_sync_design.md`, section 1.4.

Wait on `Synced`, which the sync controller writes for every kind it serves.
`kubectl wait --for=condition=` reads the condition's status only, not its
`observedGeneration`, so right after a spec edit it returns on the previous
generation's `Synced=True`; wait for
`--for=jsonpath='{.status.observedGeneration}'=<generation>` first. Alert on
`Ready != True`, which covers `False` and `Unknown` alike. It fires on every
spec edit while the inner side converges, so hold it for the convergence time
you tolerate. There is no `lastTransitionTime` to hold it on. `kubectl wait
--for=condition=Ready` waits for `True`, so it times out for a kind whose
implementation reports no `Ready` condition: the outer copy reads
`Ready=Unknown/NoInnerReadyCondition` for it.

A `False` `Synced` condition carries one of these reasons, which is the
`SYNCED-REASON` column of `kubectl get widget -o wide`. The `Stalled` and
`Ready` columns are what the controller reports beside it, asserted by
`unit_tests::widget_sync_controller::outer_status_for`:

| Reason | Meaning | Stalled | Ready | Clears when |
|---|---|---|---|---|
| `InnerConverging` | the mirror carries the spec; the inner status is for an older generation of it | `False` | `Unknown` | the inner implementation catches up |
| `InnerTerminating` | the mirror has a deletion timestamp while the outer copy is alive (someone deleted it in the inner cluster and the inner side holds it under a finalizer) | `False` | `Unknown` | the inner side releases it and a new mirror is created |
| `StaleMirror` | the object at the mirror's name is a mirror of a previous incarnation of this copy (label present, other `parent-uid`) | `False` | `False` | the janitor removes it |
| `ForeignObject` | the object at the mirror's name has no mirror identity; it is never touched | `True` | `False` | the object is removed in the inner cluster |
| `Forbidden` | the inner cluster refused a request for lack of authorization | `True` | `Unknown` | the credential's RBAC is fixed |
| `InnerUnreachable` | the object's binding has no bound inner cluster (no kubeconfig Secret, or one that does not parse), or a request to it timed out or failed server-side; the inner cluster is not answering | `False` | `Unknown` | the inner cluster answers again, or its Secret appears |
| `CreateFailed` | the Create of the mirror was answered NotFound: the inner namespace is missing, or the kind is not installed in the inner cluster, and the controller creates neither | `True` | `False` | the namespace or the CRD is created |
| `Rejected` | a request was rejected as invalid by the API server's schema or an admission webhook (a patch whose `test` failed after a race on the mirror is reported as `RequestFailed` instead, and the next reconcile retries) | `True` | `False` | the schema or the object is fixed |
| `SpecRewritten` | the spec written to the mirror came back different: most often the inner CRD's schema is older than the outer one and prunes a field, otherwise a webhook or a default rewrote it | `True` | `False` | the inner CRD is brought level, or the webhook or default that rewrites the spec is removed |
| `RequestFailed` | any other error (a conflict, an object that appeared or vanished between two requests) | `False` | `Unknown` | the next reconcile |

After a failed request the controller writes the status once and requeues; that
requeue is the per-object backoff of "Retries" below, not the 60-second one.
`SpecRewritten` follows a request that succeeded, so it takes the 60-second
requeue and keeps re-patching the mirror on it; the reason says why nothing
changes.
`ready` and `observedCount` keep their last reported values. `ready` is a
mirrored data field, not the `Ready` condition: while `Synced` is `False` the
two can disagree, and the condition is the controller's assessment.

The mirror carries `anvil.dev/managed-by: widget-sync` and
`anvil.dev/parent-uid: <outer uid>`, no owner references and no finalizers of
ours. The outer copy carries the sync finalizer, `anvil.dev/widget-sync`,
from its first reconcile on: deleting it makes the controller delete the
mirror, confirm it gone and release the finalizer, and only then does the copy
disappear ("Scenarios" below; `doc/widget_sync_design.md`, section 1.5). Once
the teardown has started, the copy gets no status writes; the controller's log
shows each request the teardown sends and which one failed.

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
- Delete the outer copy. It stays, terminating, while the controller deletes
  the mirror, confirms with a List that nothing is left at its name and
  removes the sync finalizer; then it disappears. Recreate it under the same
  name once it is gone: a fresh mirror, and no `StaleMirror` in between. To
  watch the release on its own, put a finalizer of your own on the copy once
  it carries the sync finalizer and before deleting it
  (`kubectl --context kind-widget-sync-outer patch widget demo --type json -p '[{"op":"add","path":"/metadata/finalizers/-","value":"example.com/hold"}]'`):
  the controller releases the sync finalizer, the mirror is gone and never
  recreated, and the copy stays under yours until you remove it.
- Delete the outer copy while its inner cluster is unreachable or refusing
  this controller, or while the mirror carries a finalizer someone put on it
  in the inner cluster. The copy stays terminating under the sync finalizer
  and gets no status writes. (A copy whose binding has no kubeconfig Secret at
  all is not this case: it is released at once, "Removing objects, bindings
  and clusters" below.) The log shows which request failed; for a mirror the inner side
  holds, the mirror's own `deletionTimestamp` in the inner cluster is what to
  look at. Reconnect, or remove the inner finalizer, and the copy disappears
  at the controller's next attempt. The escape hatch, if the inner cluster is
  not coming back, is the conventional one: remove the sync finalizer by hand,
  with a `test` that guards against removing someone else's,
  `kubectl --context kind-widget-sync-outer patch widget demo --type json -p '[{"op":"test","path":"/metadata/finalizers/0","value":"anvil.dev/widget-sync"},{"op":"remove","path":"/metadata/finalizers/0"}]'`
  (if the test fails, the sync finalizer is not first: see the list with
  `kubectl --context kind-widget-sync-outer get widget demo -o jsonpath='{.metadata.finalizers}'`
  and use its index). The copy disappears at once; the mirror is then the
  janitor's to collect once the inner cluster answers, at its next pass.
- Plant a stale mirror by hand: create a `Widget` in the inner cluster with
  the label `anvil.dev/managed-by: widget-sync` and the annotation
  `anvil.dev/parent-uid: <any uid no outer copy of that name has>`. The
  janitor deletes it at its next pass -- within the interval of "Operating the
  controller" below, a minute in this demo -- while the mirrors of live copies
  are untouched.
- Disconnect `widget-sync-inner-a-control-plane` from the `kind` docker
  network, edit the outer spec, reconnect. While the inner cluster is
  unreachable the outer copy reports `Synced=False/InnerUnreachable` at the new
  generation; after the heal it reaches `Synced=True`. Deleting the binding's
  Secret `default/a-kubeconfig` reads the same way for a live copy, without
  touching the network; re-creating it binds the cluster again. A terminating
  copy of that binding is released instead, at once.
- Copy `default/a-kubeconfig` into another namespace under the same name and
  create an object there bound to `a`. The claim refuses the second binding:
  the object reports `Synced=False/Forbidden` with `Stalled=True` and nothing
  of it ever reaches the inner cluster ("Bindings and the claim" below).
- Rotate a credential: write the same kubeconfig back into
  `default/a-kubeconfig` with a byte changed (a comment line will do). The
  binding's clients are rebuilt and its janitors restarted in place, the
  mirrors are untouched, and the next edit goes through the new clients.
- Delete `kube-system/anvil-sync-claim` in `widget-sync-inner-a`. Within a
  minute the binding that holds the cluster writes it again and says so at
  warn — a released claim that nobody else took is taken back.

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
demo CRDs — exactly the two manifests in this directory, immutability rule
included, so what it prints is what this binary accepts at boot (a test holds
the two to being the same document).

The **selector** is the field that says which inner cluster an object belongs
to:

| Selector | The object's cluster is | What the CRD must carry |
|---|---|---|
| `name` | `metadata.name` | nothing; `metadata.name` is immutable by construction |
| `field:spec.<path>` (the `field:` prefix may be dropped) | the string at that path | the field, required and a string, and every step of the path required in its parent, guarded by `x-kubernetes-validations: [{rule: "self == oldSelf"}]` on the field itself, or the equivalent rule naming the field on `spec` or on the object that holds it (see below) |

The rule is matched as text, so only these spellings count, on the field, on
the object holding it, and on `spec` — with `oldSelf` allowed on either side
and any spacing (`self==oldSelf` is the rule `self  ==  oldSelf` is):

| Where the rule sits | Accepted spellings, for the selector `field:spec.placement.clusterName` |
|---|---|
| the field itself | `self == oldSelf`, `oldSelf == self` |
| the object that holds the field (`spec.placement`) | `self.clusterName == oldSelf.clusterName`, `oldSelf.clusterName == self.clusterName` |
| `spec` | `self.placement.clusterName == oldSelf.placement.clusterName`, and the same with the sides swapped |

Anything else — a rule that says the same thing another way, a rule with a
`has()` guard — is refused: recognising it would mean evaluating CEL. A CRD
whose rule is written differently is not wrong, but this controller will not
run against it until the rule is spelled one of these ways.

The rule must be in **every served version** of the CRD, not only the
configured one: an object is one object whichever version it is written
through, so a served version without the rule is a way to move an object to
another inner cluster. A version that is not served is not checked.

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
| `status.conditions[]` | read on the inner copy (all: `Ready` and `Stalled` are merged, `Synced` dropped, the other types copied); written on the outer copy (`Synced`, `Ready`, `Stalled`, then the copies) | array of objects with `type` (string, required, not restricted to the three own types), `status` (string, required), `reason`, `message` (strings), `observedGeneration` (integer); an item requires nothing else; `x-kubernetes-list-type: map` keyed by `type` is recommended, not checked |
| every other status field | mirrored verbatim inner to outer while `Synced` | none, and `status` requires none of them |
| the status subresource | | enabled, so `metadata.generation` follows the spec |

The fields in the table must be **declared, with these types**, even on a
status (or a `conditions` item) that carries
`x-kubernetes-preserve-unknown-fields`. That setting makes the API server keep
a field it does not know; it does not make it check one. The controller — and
the model it is verified against — takes every stored status to be of this
shape, and the only thing that holds another writer to it is the CRD's own
schema: an undeclared `observedGeneration` accepts the string `"three"`, and
then the mirror's status cannot be read at all. Anything *outside* the table is
opaque and needs no declaration: `Gadget`'s `spec.size` is copied without the
controller knowing it exists, and its `status.observedSize` comes back on the
outer copy as part of the mirrored remainder;
`x-kubernetes-preserve-unknown-fields` on the status is how a CRD keeps such a
remainder it does not declare.

A schema may **require** only what the controller always writes: at the status
level `observedGeneration` and `conditions`, and in a condition `type`,
`status` and `observedGeneration`. The controller writes no
`lastTransitionTime`, because it reads no clocks. The `Synced` condition never
carries a `message`. `Ready`, `Stalled` and a copied condition carry neither
`reason` nor `message` from an inner condition that has none. A copied
condition kept while `Synced` is `False` is rewritten with the fields it was
stored with, which the same schema admitted.

The demo CRDs declare `status.conditions` a map list keyed by `type`
(`x-kubernetes-list-type: map`, issue #31). The API server then refuses any
write that repeats a type, in the inner clusters too, where the same manifest
is installed: an inner implementation that writes two conditions of one type
gets a 422. The sync controller's own write is a JSON patch that replaces the
whole list, not a server-side apply, so the map type does not make it merge: a
condition another manager applies to the outer copy is removed on the
controller's next synced write. Changing an installed CRD from an atomic list
to a map is accepted; stored objects are not rewritten, and an object that
already repeats a type is refused updates until its list is fixed (on a server
without validation ratcheting) -- the outer copy heals on the controller's next
write, an inner copy when its implementation rewrites the list.

A CRD generated from `metav1.Condition` declares all five condition fields with
the types the table demands and marks `lastTransitionTime`, `message` and
`reason` required, so it passes every other row and the boot check refuses it on
this one. Without that check the API server would reject every status write with
422 and nothing would report it: the object would carry no status at all, the
only sign one WARN per attempt. A required field that declares a `default` is
accepted, because defaulting runs before validation.

A status that declares nothing beyond `observedGeneration` and `conditions`
and does not set `x-kubernetes-preserve-unknown-fields` keeps no remainder at
all: the outer copy shows conditions and nothing else. The controller warns
about that shape at boot and serves the kind anyway
(`doc/widget_sync_fanout_design.md`, section 2.2). It is one shape, not a test
for pruning: a CRD that declares one unrelated field draws no warning and still
prunes everything the inner side reports.

An inner cluster is not checked at all: not for serving the kind, not for
schema parity. Parity is an operational assumption. So is this, for now: **fields are
not removed from a CRD while the controller runs**, so the boot check, once it
passes, stays true. Adding optional fields is fine; adding a required one the
controller does not write breaks status writes, and the check does not re-run.
A later pass can watch the CRDs and
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
  - spec: selector field spec.clusterName: must carry the x-kubernetes-validations rule `self == oldSelf` (or spec the rule `self.clusterName == oldSelf.clusterName`; either side may come first and the spacing does not matter)
```

and the container exits 2. `kubectl apply -f deploy/widget_sync/crd.yaml`
puts the rule back; the next restart boots. The same CRD is accepted for a
`name` selector, which needs no rule, so the reproduction isolates exactly
the row it removes. `cargo test --features dyn-runtime --bin widget_sync_controller`
checks that message without a cluster.

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
cluster provides it without any help from us. The whole convention is
required, not the name alone:

| | |
|---|---|
| name | `<clusterName>-kubeconfig` |
| `type` | `cluster.x-k8s.io/secret` |
| label | `cluster.x-k8s.io/cluster-name: <clusterName>`, which must be the cluster the name says it is |
| `data.value` | a self-contained kubeconfig of the shape below |

The controller watches the Secrets of every namespace that carry the
`cluster.x-k8s.io/cluster-name` label (`rbac.yaml` grants `secrets` get, list
and watch; the label is a selector on the watch, so no other Secret is sent to
this process at all) and checks the type and the label's value on every event.
A Secret merely *named* `something-kubeconfig` — a backup, an operator's own
kubeconfig — is not a binding. It keeps one pair of clients per binding whose
Secret exists. Nothing is mounted and nothing is configured per binding: adding
an inner cluster is adding its Secret, removing one is removing its Secret.

```sh
kubectl --context kind-widget-sync-outer -n default create secret generic c-kubeconfig \
    --type=cluster.x-k8s.io/secret --from-file=value=./kubeconfig-of-c
kubectl --context kind-widget-sync-outer -n default label secret c-kubeconfig cluster.x-k8s.io/cluster-name=c
kubectl --context kind-widget-sync-outer -n widget-sync logs deploy/widget-sync-controller | grep '^.*binding default/c'
```

| The binding's Secret | What its objects report | What the controller does |
|---|---|---|
| missing, not of type `cluster.x-k8s.io/secret`, not labelled with its cluster name, or without a `value` key | `Synced=False/InnerUnreachable` | nothing: the binding is not bound, so the reconciler does not address it at all -- it reports the status and requeues, without a round trip. Its janitors do not run, so its mirrors are left alone |
| present but not a parseable kubeconfig, or one the validation below refuses | `Synced=False/InnerUnreachable` | the same, plus one warn line naming the rule it broke; nothing retries it on a timer, only a change of the Secret's `value` |
| present, its cluster unreachable or its credential denied a verb | `InnerUnreachable` (unreachable) or `Forbidden` with `Stalled=True` (denied) | the *binding* is retried with backoff, 1s doubling to 1min, for an unreachable cluster, and re-checked every 5 minutes for a denied one; its *objects* are retried on their own schedule ("Retries" below) |
| present and its cluster claimed by another binding | `Synced=False/Forbidden` with `Stalled=True` | refused: no janitor runs and no request is sent, and it is re-checked every 5 minutes, or at once when the Secret's `value` changes |
| present and good | `Synced=True` once the mirror is there | the janitors of every configured kind run against it; its access and its claim are re-checked every minute |

A changed Secret rebuilds the binding's clients and restarts its janitors,
with no restart of the pod. What counts as changed is the `value` itself: a
rotated credential, which is how Cluster API rotates one, or the Secret deleted
and created again. Editing a label or another key of the same Secret, or a
relist of the watch, leaves a bound binding running and an unbound one on its
existing retry schedule — nothing is rebuilt and no janitor of the process is
restarted by a relist.

**Who may create a binding's Secret.** `<clusterName>-kubeconfig` Secrets are
created by **Cluster API only** — the
management cluster's own controllers — and by nobody else. That is the
deployment this controller is built for and the one it is supported in. The
type and label filter on the Secret watch, and the kubeconfig validation below,
are **defence in depth; they are not an authorization boundary.** They narrow
what a malformed or unexpected Secret can do, and they do not decide who is
allowed to write one: they are not designed to hold against a principal who is
trying to get past them. A namespace in which principals other than Cluster API
may create Secrets of this name is **outside the supported deployment** — put
the other way round, whoever can create such a Secret in a namespace is as
trusted as Cluster API is, which is what the next paragraph spells out the
consequences of. The place to enforce that is RBAC on `secrets` in the
namespaces this controller watches, not anything in this process.

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

This bounds what a Secret can do to naming an API server that this controller
then talks to with the credential in the same document. It does not bound *which*
server that is, so a Secret can still point a binding at a cluster of the
Secret author's choosing — which is what the claim below is about.

**The access check.** Before a binding is used, the controller asks its inner
cluster, with one `SelfSubjectAccessReview` per verb and configured kind in the
binding's namespace, whether the credential may get, list, watch, create,
patch and delete the kind, and whether it may `get` and `create` configmaps in
`kube-system` for the claim. A denial marks that one binding degraded — its
requests are answered `Forbidden` — and is logged; an error means the cluster
did not answer, which leaves the binding unbound and retried. Neither ever
exits the process: one bad inner cluster must not stop the others. The reviews
of one check are sent together, not one after another.

Creating a `SelfSubjectAccessReview` is itself a right, and the credential is
not granted it by `rbac_inner.yaml`: it comes from the default ClusterRoleBinding
`system:basic-user`, which every Kubernetes cluster binds to
`system:authenticated` and which allows `create` on
`selfsubjectaccessreviews` and `selfsubjectrulesreviews`. A cluster whose
administrator has removed or narrowed that binding answers the reviews with
`Forbidden`, which the controller reports as an error of the check rather than
as a denial, so the binding stays unbound and retried with backoff and the log
line names the review that failed. Grant the credential
`create` on `authorization.k8s.io/selfsubjectaccessreviews` explicitly in such
a cluster.

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

The next re-check, at most five minutes later for a refused binding — or at
once if its Secret's `value` changes — claims it for the binding that is still
there.

**The claim is re-checked.** A *bound* binding re-runs its access check and its
claim every **60 seconds**; a *refused* one every **300**. The bound case is the
faster of the two because it is the one nothing else would report: no request
fails and no condition changes when a claim is deleted or taken over in an
inner cluster, and the claim is this process's only evidence that no second
binding is writing the same mirrors. Both cases are logged at warn, once each
time they happen:

```
WARN binding default/a: its claim was gone and has been created again (owner="7f3c…" binding=default/a).
     Someone removed kube-system/anvil-sync-claim in its inner cluster; while it was gone another
     binding could have claimed the cluster.
WARN binding default/a: its claim now names owner="7f3c…" binding=tenant/a; its inner cluster has
     been taken by another binding since the last check
```

The second is followed by the refusal: the binding stops its janitors and its
objects report `Synced=False/Forbidden`. Which binding wins a contested
re-claim is whichever one asked first — re-creating the claim does not take a
cluster back from a binding that already holds it.

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

**Retries.** A reconcile that ends without a failure is requeued after **60
seconds** — that is the sync reconciler's interval, and it is what liveness
rests on; the janitor's is the interval of the next paragraph. A reconcile that **fails** is retried per
object on an exponential backoff instead: **10 seconds** after that object's
first failure, twice the last delay after each further consecutive failure of
the same object, up to a cap of **5 minutes** — 10, 20, 40, 80, 160, 300, 300,
... seconds. The count is **per object, not per controller**: one object
failing does not slow the retries of any other, and each walks the schedule on
its own.

What puts an object back at the 10-second base is **a reconcile of that object
succeeding**; its count is dropped then, and also when the object turns out to
be gone or to have a status outside the shape. Nothing else resets it — not
another object recovering, not a binding coming back, not time passing. So an
object that has been failing for a few minutes is up to 5 minutes from its next
attempt, and a fault repaired outside its own cluster (a binding's Secret
restored, an inner cluster answering again) reaches it within those 5 minutes
at the latest. It is usually much sooner, because the repair itself tends to
produce an event the controller acts on at once: any edit of the outer object,
and the same-name trigger a re-bound binding's mirror watch emits for every
existing mirror when it starts. An object whose reconcile ends by *reporting* a
condition — `ForeignObject`, `StaleMirror`, `InnerConverging` — has not failed
and stays on the 60-second requeue.

The backoff is what keeps a binding that is down or refused from being a steady
load on the API server its objects are read from: at a fixed 10 seconds a
namespace of a thousand such objects is a hundred reads a second that cannot
succeed, for as long as the fault lasts; at the cap it is between three and
four a second.

**The janitor's interval and watch.** A janitor revisits each mirror every
**10 minutes** unless `--janitor-interval` says otherwise (a number with the
unit `s`, `m` or `h`; `deploy_local.yaml` sets `60s` so that the e2e tests
see a collection within a minute). Its watch of the mirrors triggers a
reconcile on a change of a mirror's `metadata.generation` only -- a spec
change or a deletion stamp -- and not on the status writes of the inner
implementation, which are the bulk of a workload cluster's events. The long
interval is deliberate. The sync controller tears a mirror down before it
lets its outer copy go; the janitor is the safety net behind that teardown
(`doc/widget_sync_design.md`, section 1.3), and a stale mirror costs nothing
but a name until the next pass. A read of the mirror that fails before its
reconcile runs is retried after the 60-second requeue of "Retries", not the
interval. The e2e tests wait for a collection within the interval plus a
margin (`JANITOR_WINDOW` in `e2e/src/widget_sync_e2e.rs`), and the binary's
unit tests hold the default and the manifest's value to what this paragraph
says.

**Removing objects, bindings, kinds and the controller.** A copy is released
only once its mirror is confirmed gone, which needs the copy's inner cluster,
so order matters: delete the copies that name a cluster and wait for them to
go before you delete that cluster. Deleting the binding Secret first, or the
Cluster API `Cluster` that owns it, is not fatal: a copy whose binding has no
kubeconfig Secret is released at once. The mirror is then left in a workload
cluster that is still running, with nobody to collect it until that binding
comes back. What is left is the mirrors carrying the controller's label:

```sh
kubectl --context <inner> get <kind> -A -l anvil.dev/managed-by=widget-sync
```

A cluster that is merely unreachable, or one whose claim refuses this
controller, is still bound: its copies stay terminating until it answers, and
a namespace deleted around them stays `Terminating` too. So is a binding whose
Secret is there but unusable — a kubeconfig that does not parse, or one this
controller refuses — which the process keeps retrying. Only a Secret that is
gone releases a terminating copy; the escape hatch below is for the rest.

The controller itself and a configured kind need the same order: stop the
controller, or drop a `--kind`, only after the copies of every kind it serves
are gone, and remove a CRD only after that, since only a running controller
releases the finalizer. A build without the finalizer cannot release it
either, so before rolling back to one, strip the finalizer from every served
copy. The escape hatch applies to any of these, one object at a time as in
"Scenarios" or a namespace at a time:

```sh
kubectl --context kind-widget-sync-outer -n default get widgets -o name \
  | xargs -n1 kubectl --context kind-widget-sync-outer -n default patch --type json \
      -p '[{"op":"test","path":"/metadata/finalizers/0","value":"anvil.dev/widget-sync"},{"op":"remove","path":"/metadata/finalizers/0"}]'
```

The `test` refuses an object whose first finalizer is someone else's; look at
that one by hand. A copy stripped this way is deleted by the API server at
once if it was terminating, and its mirror is the janitor's to collect once
its cluster answers.

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

What takes the place of a liveness probe is the process exiting. **A runner
that ends when it was not asked to takes the process down with it**: if a sync
runner of a kind, the binding manager (the Secret watch ending counts as a
failure, not as a clean finish) or the janitor of a live binding returns — with
an error or without one — the binary logs at error which runner it was and
exits non-zero, and the kubelet restarts the container. Nothing restarts a
runner in place, so the alternative is a pod that passes its startup probe
while a kind is no longer reconciled. On SIGTERM the same returns are expected:
the runners drain and the process exits 0.

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
the restore produced, decide, resume. The gate withholds every Delete the
process sends, the one the teardown of a deleted outer copy sends for its own
mirror included: an outer copy deleted while paused stays terminating until
the key is removed. It withholds Deletes and nothing else, so a copy whose
binding has no kubeconfig Secret is still released while paused, and its
mirror is then an orphan the janitor deletes once the pause is lifted and the
binding is back. Keep the Secrets in place for the length of a restore.
While paused, the janitor answers each
stale mirror with a withheld delete (a warn log with `cause="janitor
paused"`) and retries it — and that retry is the backed-off one of "Retries"
above. The gate answers a withheld Delete with a `Timeout`, which the janitor's
reconcile ends in `Error` on, so each withheld mirror walks the retry schedule
up to the 5-minute cap while the pause is on. **Deleting the `pause` key
therefore does not resume the deletes within one requeue.** Clearing the gate
changes nothing in either cluster, so no watch fires and each mirror waits for
the retry it is already scheduled for: the deletes resume within **at most 5
minutes, plus the reconcile itself**, and a mirror withheld for any length of
time will be at that cap rather than below it. Nothing is lost by the wait —
withholding a delete and deferring it are the same thing here, as the end of
this section says — but do not read the log going quiet in the first minute
after clearing the key as the deletes having resumed. Nothing else changes
while paused, and the sync reconciler never adopts: a restored outer `Widget`
whose uid differs from the mirror's annotation reports
`Synced=False/StaleMirror` and gets a new mirror only after the old one is
gone. Resuming therefore lets the janitor delete every
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

**RBAC.** In the outer cluster the controller reads `<plural>`, updates it
(the finalizer it owns on each object; it never writes a spec) and patches
`<plural>/status` for each configured kind, gets the CRD of each at boot for
the shape check, gets, lists and watches `secrets` in every namespace (the
bindings) and gets the `kube-system` namespace (the outer cluster id). In an
inner cluster its credential needs `<plural>` get, list, watch, create, patch
and delete per kind, and `configmaps` create in `kube-system` with get on
`anvil-sync-claim` (`rbac_inner.yaml`). `rbac.yaml` also binds, in namespace `default`, `get` and
`update` on the single ConfigMap `fault-injection-config`, which only the
crash-testing mode (`controller crash`) touches; `run` mode never uses it. The controller needs no
`events` verbs: it emits none.
