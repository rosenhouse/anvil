# Widget sync: a verified two-cluster controller, demoed on two kind clusters

The Widget sync controller runs in an *outer* cluster and, for every `Widget`
created there, keeps a mirror `Widget` with the same namespace, name and spec in
a separate *inner* cluster, where a real `Widget` implementation acts on it. It
copies the inner implementation's status back onto the outer copy. The
controller is verified in Anvil; the design and the properties proved are in
`discussion/multi-cluster/sync_controller_evaluation.md`.

## What runs where

| Cluster | kind name / kubectl context | What runs there |
|---|---|---|
| outer | `widget-sync-outer` / `kind-widget-sync-outer` | the Widget CRD; users' `Widget`s; the verified sync controller (`widget-sync` namespace, one replica, two reconcilers in one process: the *sync* reconciler and the *janitor*) |
| inner | `widget-sync-inner` / `kind-widget-sync-inner` | the same Widget CRD; the mirrors; the unverified *echo* controller (`widget-echo` namespace) standing in for a real Widget implementation |

The sync controller reaches the inner cluster through a kubeconfig built from a
service-account token, mounted from the Secret `widget-sync-remote-kubeconfig`,
exactly as a production deployment would. Its inner-cluster permissions are a
ClusterRole on `widgets` (get, list, watch, create, patch, delete); it never
writes a mirror's status. The echo controller writes only status
(`observedGeneration`, `ready`, `observedCount`, a `Ready` condition).

## Running it

Prerequisites: docker, kind, kubectl, and the Rust/Verus toolchain used by
`tools/deploy.sh` if you build the images yourself.

```sh
# Build both controller images, create both clusters, deploy everything.
./tools/two-cluster-test.sh --build

# Then create a Widget in the outer cluster and watch it flow.
kubectl --context kind-widget-sync-outer apply -f deploy/widget_sync/widget.yaml
kubectl --context kind-widget-sync-outer get widget demo -o yaml
kubectl --context kind-widget-sync-inner get widget demo -o yaml
```

Without `--build` the script reuses the images
`local/widget-sync-controller:v0.1.0` and `local/widget-echo-controller:v0.1.0`.

The end-to-end test drives the same clusters:

```sh
cd e2e && cargo run -- widget-sync
```

It checks, in order: the mirror appears with the outer spec, label and
parent-uid annotation; the outer status reports the echo controller's count at
the outer generation with `Synced=True`; a spec change propagates and the
status follows at generation 2; a foreign `Widget` pre-created in the inner
cluster is reported as `ForeignObject` and never touched; deleting the outer
copy makes the janitor collect the mirror.

## What to look at

On the **inner** copy nothing is unusual: it is an ordinary `Widget` whose spec
the sync controller writes (bumping `metadata.generation` as any spec writer
would) and whose status the echo controller writes, with
`status.observedGeneration` set from its own `metadata.generation`. The mirror
carries the label `anvil.dev/managed-by: outer-sync` and the annotation
`anvil.dev/parent-uid: <uid of the outer copy>`, no owner references and no
finalizers of ours.

On the **outer** copy the status follows the convention of the built-in
workload controllers:

- `status.observedGeneration == metadata.generation` means the sync controller
  has acted on the current spec. Every status write stamps it.
- The condition `Synced` with `status: "True"` and
  `observedGeneration == metadata.generation` means the current spec is in the
  inner cluster and the mirrored fields (`ready`, `observedCount`) are the inner
  implementation's status *for that spec*. Otherwise `Synced` is `False` with a
  reason: `InnerConverging` (spec is in place, the inner side has not yet
  observed it), `InnerTerminating` (the old mirror is still being released by
  the inner side), or `ForeignObject`. A reconcile that creates or patches the
  mirror ends without a status write; the watch on the mirror triggers the next
  reconcile, which reports.

Things worth trying by hand:

- **Edit the outer spec.** `kubectl --context kind-widget-sync-outer patch
  widget demo --type merge -p '{"spec":{"count":5}}'`. The mirror's spec and
  generation follow, then the echo controller's status, then the outer status,
  now at the new generation. Between the spec edit and the status write the
  outer copy shows the old status with `observedGeneration` behind
  `generation`, which is what "in progress" looks like to kstatus-style tools.
- **Fat-finger the mirror.** `kubectl --context kind-widget-sync-inner patch
  widget demo --type merge -p '{"spec":{"count":99}}'`. The echo controller
  may briefly report `observedCount: 99` on the mirror, but the sync controller
  overwrites the mirror's spec on its next reconcile and never copies a status
  the inner side computed for a generation of the mirror other than the
  current one. The outer copy at most shows `Synced=False/InnerConverging` for
  a moment and never reports 99.
- **Create a foreign object first.** Create `Widget{default, other}` in the
  inner cluster without the label, then `Widget{default, other}` in the outer
  cluster. The inner object is never modified (the echo controller keeps
  serving it); the outer copy reports `Synced=False/ForeignObject`.
- **Delete the outer copy.** The mirror disappears within one janitor requeue
  (the janitor lists outer `Widget`s in the namespace and deletes a mirror
  whose parent uid is not among them, with a uid precondition). Delete and
  recreate with the same name: the stale mirror is collected, a new one is
  created, nothing is adopted.
- **Cut the link.** `docker network disconnect kind
  widget-sync-inner-control-plane`, edit the outer spec, reconnect (with the
  same IP). The outer copy shows `observedGeneration` behind `generation`
  while the inner cluster is unreachable, and convergence resumes after the
  heal.

## Where the code is

| Piece | Path |
|---|---|
| CRD, RBAC, manifests | `deploy/widget_sync/` |
| exec reconcilers (what runs) | `src/controllers/widget_sync_controller/exec/` |
| model reconcilers (what is proved about) | `src/controllers/widget_sync_controller/model/` |
| trusted specification: types, rely/guarantee, R1/R2/R3, D3 | `src/controllers/widget_sync_controller/trusted/` |
| proofs: invariants, guarantees, termination, liveness | `src/controllers/widget_sync_controller/proof/` |
| Welder controller specs and the janitor+sync composition | `src/controllers/composition/widget_janitor_reconciler.rs`, `widget_sync_reconciler.rs` |
| binaries | `src/bin/widget_sync_controller.rs`, `src/bin/widget_echo_controller.rs` |
| testbed script and e2e test | `tools/two-cluster-test.sh`, `e2e/src/widget_sync_e2e.rs` |
