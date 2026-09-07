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

The controller reaches the inner cluster through a kubeconfig built from a
service-account token, mounted from the Secret `widget-sync-remote-kubeconfig`.

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
