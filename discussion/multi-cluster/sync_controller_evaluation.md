# Technical evaluation: a two-cluster "Outer → Inner" sync controller in Anvil

## The question

We want an example controller that runs in an *outer* cluster, reconciles an
`Outer` custom resource by ensuring an `Inner` custom resource with the same
namespace, name and spec exists in a separate *inner* cluster, and copies the
`Inner` status back into the `Outer` status. Controllers in the inner cluster
are the "real implementation". Deliverables: a production-shaped controller, a
two-kind-cluster testbed, a set of formal assumptions and requirements, and a
machine-checked proof.

Does the current Anvil API support this, or do we need enhancements?

## Short answer

**The verification side needs no framework changes. The execution side needs a
small, additive enhancement to the shim layer.**

- **Model / spec / proof:** model both clusters as *one* logical API server
  whose key space is the disjoint union of the two clusters' objects (keys are
  `(kind, namespace, name)`, and `Outer` and `Inner` are different kinds). The
  inner cluster's controllers are modeled as ordinary "other controllers"
  constrained by a rely condition. Nothing in `src/kubernetes_cluster/` changes.
  This is structurally the same setup as the already-verified
  VDeployment → VReplicaSet pair: a controller that creates a child custom
  resource, reads a status that a *different* controller writes, and whose
  liveness depends on that other controller through Welder's
  `liveness_dependency`.
- **Shim layer:** `src/shim_layer/controller_runtime.rs` holds exactly one
  `kube::Client` and sends every `KRequest` to it. We need (1) a second client
  built from an inner-cluster kubeconfig, (2) routing of each request to a
  client by the request's `ApiResource`, and (3) a cross-cluster
  `Controller::watches(...)` trigger so `Inner` status changes wake the
  reconciler promptly. This is a self-contained change of roughly 100 lines,
  additive to the existing entry points.
- **Not recommended:** the existing "external system" hook
  (`ExternalShimLayer` / `ExternalModel`). It is the obvious-looking place for
  "a remote thing the controller talks to", but it is a deterministic,
  request-driven RPC stub with no spontaneous steps and no request drops, so it
  cannot model an inner controller that changes status on its own, and it
  would force us to re-implement the API server semantics (resource versions,
  conflicts, status subresource) inside a custom model, losing the whole proof
  library. Details in "Alternatives considered".

The rest of this note gives the controller design, the mapping onto Anvil, the
required enhancements, draft assumptions and requirements, the testbed, and an
effort estimate.

## 1. Controller design

### 1.1 Resources

Two CRDs in group `anvil.dev`, both namespaced, both with a status
subresource. They share the same `spec` and `status` Rust types so that "same
spec" and "copy status" are literal equalities:

```
kind: Outer            # lives in the outer cluster; users create these
kind: Inner            # lives in the inner cluster; only the sync controller creates these
```

The spec shape is arbitrary for the example; keep it small (two or three
scalar fields) so the CR view types and marshalling lemmas stay short.

### 1.2 Identity and ownership across clusters

- The `Inner` object for `Outer{ns, name}` is `Inner{ns, name}` in the inner
  cluster. Same namespace, same name, by construction.
- **No `ownerReferences` across clusters.** A real inner-cluster garbage
  collector would delete an `Inner` whose owner UID does not exist in *its*
  cluster. The controller must never set an owner reference on `Inner`. This is
  also what makes the single-store model sound (see 2.2). Identity is carried
  by a label `anvil.dev/managed-by: outer-sync` and an annotation
  `anvil.dev/parent-uid: <Outer uid>` instead. Cluster API, KubeFed and
  Karmada all follow this convention for the same reason.
- **Cleanup via a finalizer on `Outer`** (`anvil.dev/inner-sync`). When `Outer`
  gets a deletion timestamp, the controller deletes `Inner`, then removes the
  finalizer.

### 1.3 Reconcile state machine

Each step issues at most one request, in Anvil style. Reads of the `Outer`
object come from the shim layer's quorum read at the start of reconcile; reads
of `Inner` are a quorum `Get` against the inner API server.

```
Init
 ├─ Outer has deletion timestamp
 │    ├─ finalizer absent  → Done
 │    └─ finalizer present → Get Inner → AfterGetInnerForDelete
 │           ├─ NotFound            → Update Outer (remove finalizer, rv from Outer) → AfterRemoveFinalizer → Done
 │           └─ Found               → Delete Inner (precondition: rv, uid)          → AfterDeleteInner → Update Outer (remove finalizer) → ...
 └─ Outer live
      ├─ finalizer absent → Update Outer (add finalizer, rv from Outer) → AfterAddFinalizer → Done   (requeue picks up the rest)
      └─ finalizer present → Get Inner → AfterGetInner
             ├─ NotFound → Create Inner {ns, name, label, parent-uid annotation, spec: Outer.spec} → AfterCreateInner
             ├─ Found, spec == Outer.spec → (skip)
             └─ Found, spec != Outer.spec → Update Inner (fetched object with spec := Outer.spec, label ensured, rv from Get) → AfterUpdateInner
             then → UpdateStatus Outer (status := Inner.status, rv from Outer) → AfterUpdateOuterStatus → Done
Error (any unexpected response) → requeue with short backoff
```

Design notes that matter for both production behavior and the proof:

- `Update Inner` sends the object returned by `Get` with only `spec` (and our
  label/annotation) replaced. This preserves labels or annotations that
  inner-cluster tooling may have added, and gives a well-defined "what the
  update writes" in the model.
- After adding the finalizer the reconcile ends and relies on requeue. This
  avoids carrying a stale `Outer` resource version through the same reconcile
  and is the usual controller-runtime idiom.
- Custom resources do not allow unconditional updates (real API server and
  Anvil's model agree: `allow_unconditional_update` is false for
  `CustomResourceKind`), so every `Update`/`UpdateStatus` carries a resource
  version and can fail with `Conflict`. A conflict ends the reconcile with an
  error and the controller retries on the next round.
- Policy for a pre-existing `Inner{ns,name}` not created by us: v1 takes
  ownership (enforces spec, adds the label). A stricter "refuse to adopt and
  report a condition on `Outer`" variant is easy to implement but changes the
  premise of the liveness requirement; leave it as a follow-up.

### 1.4 Deployment shape

- Runs as a Deployment in the outer cluster, one replica.
- Outer-cluster RBAC: `outers`, `outers/status`, `outers/finalizers` (get,
  list, watch, update, patch) plus the fault-injection ConfigMap if used.
- Inner-cluster credentials: a kubeconfig mounted from a Secret, pointing at a
  ServiceAccount token in the inner cluster bound to a Role that allows only
  `inners` (get, list, watch, create, update, delete). Path passed by env var.
- Watches: `Outer` in the outer cluster (primary), `Inner` in the inner
  cluster mapped to `Outer{ns,name}` (secondary). The watch is a latency
  optimization only. The proof does not depend on it, consistent with Anvil's
  decision not to model the watch cache.

## 2. Mapping onto Anvil's model

### 2.1 One logical API server, two kinds

`ClusterState` has one `api_server.resources: Map<ObjectRef, DynamicObjectView>`.
Install both kinds:

```rust
membership: |cluster: Cluster, id: int| {
    &&& cluster.controller_models.contains_pair(id, outer_sync_controller_model())
    &&& cluster.type_is_installed_in_cluster::<OuterView>()
    &&& cluster.type_is_installed_in_cluster::<InnerView>()
}
```

The reconciler issues plain `KRequest`s for both kinds. `schedule_controller_
reconcile` only fires for `reconcile_model.kind == Outer`, so only `Outer`
objects trigger reconciles. `desired_state_is(outer)` and the
`current_state_matches` predicates all read the same `resources` map, and the
`Inner` key is `ObjectRef { kind: InnerView::kind(), namespace: outer.ns,
name: outer.name }`.

The inner cluster's "real implementation" is any other controller id in
`controller_models`. Our rely condition permits it to send `UpdateStatus` to
`Inner` objects and forbids everything else we care about (2.4).

### 2.2 Why the single-store abstraction is sound here

This is the one trusted argument that a reviewer must accept, so it should be
written down next to the theorem.

1. **Atomicity and interleaving.** Every real request touches exactly one
   API server, each API server executes each request atomically against its
   own store, and the two key spaces are disjoint (different kinds). An
   interleaving of two independent atomic stores is indistinguishable from one
   atomic store over the disjoint union.
2. **Resource versions and UIDs.** The model has one `resource_version_counter`
   and one `uid_counter`; reality has one per cluster. The model therefore
   admits fewer behaviors than reality for cross-object comparisons: in the
   model an `Inner` created after an `Outer` always has a larger rv. The proof
   must treat rv and uid as opaque per-object tokens compared only for
   equality against the same object, which is all the API exposes anyway.
   Anvil already relies on the analogous simplification for uid values. State
   this as an explicit proof-hygiene rule.
3. **Garbage collection.** The model's GC looks up owners in the union store,
   so a cross-cluster owner reference would be treated as valid in the model
   but deleted immediately in reality. Forbidding owner references on `Inner`
   (part of our guarantee condition) removes the divergence: GC never acts on
   `Inner` objects in either world.
4. **Failures.** `drop_req` fails individual requests addressed to the API
   server with an arbitrary `APIError`, and can do so for any finite prefix of
   an execution. That covers "the inner cluster is unreachable for a while" and
   "the outer cluster is unreachable for a while" independently. The liveness
   assumption `disable_req_drop` now means *both* clusters' connectivity
   eventually stabilizes. This is the honest assumption for a multi-cluster
   controller and should be stated as such.
5. **Namespaces.** Anvil does not model Namespace objects; creates never fail
   for a missing namespace. Real inner clusters do fail. Assume the namespace
   exists in the inner cluster (the testbed creates it). Creating it from the
   controller would need cluster-scoped objects, which the model lists as a
   TODO.
6. **CRD installation.** `type_is_installed_in_cluster::<InnerView>()` in the
   membership predicate corresponds to "the `Inner` CRD is applied in the
   inner cluster".

### 2.3 Precedent: VDeployment → VReplicaSet

`src/controllers/vdeployment_controller/model/reconciler.rs` creates and
updates `VReplicaSet` CRs and reads their `status.replicas`, which the
VReplicaSet controller writes. `src/controllers/composition/vdeployment_
reconciler.rs` declares `liveness_dependency: vrs_eventually_stable_
reconciliation()` and `compose_all.rs` discharges it with `compose_dep`. Our
controller is the same shape with two differences that make it *simpler*: it
manages exactly one child per parent (no lists, no pods, no pod monkey) and it
uses no owner references (no GC reasoning).

### 2.4 Rely, guarantee and liveness dependency (draft)

**Guarantee (what our controller promises everyone else).** Every in-flight
API request from our controller id is one of:

- `Get` on an `Outer` or `Inner` key.
- `Create` of an `Inner` with a provided name, no owner references, our
  managed-by label, and `spec` equal to the spec of an `Outer` with the same
  `(namespace, name)`.
- `Update` of an `Inner` with the same constraints, carrying a resource version.
- `Delete` of an `Inner` with a uid and resource-version precondition.
- `Update` of an `Outer` that changes only `metadata.finalizers` (adds or
  removes our finalizer) and carries a resource version.
- `UpdateStatus` of an `Outer`, carrying a resource version.

In particular it never touches Pods or any other kind, so it trivially
satisfies the rely conditions of the existing VReplicaSet, VDeployment,
VStatefulSet and RabbitMQ controllers, and can be composed with them.

**Rely (what we require from every other controller `j`).** For every
in-flight API request from `j`:

- No `Create`, `Update`, `Delete`, `GetThenUpdate`, `GetThenDelete` on any
  `Inner` key. (`UpdateStatus` and `GetThenUpdateStatus` on `Inner` are
  allowed: that is the inner implementation.)
- No `Update`, `UpdateStatus`, `Delete`, `GetThen*` on any `Outer` key.

Users are not modeled as controllers; their influence enters only through
`always(desired_state_is(outer))` in the ESR premise, as for every Anvil
controller.

**Liveness dependency (what we require from the inner implementation).**
Because `Update Inner` carries a resource version and status writes bump the
resource version, an inner controller that changes `Inner.status` forever
could starve our spec update. This is the race described in
`discussion/fairness/fairness-on-controller-race.md`. The natural, defensible
assumption is eventual stability of the inner implementation:

> For every `Inner` object, if its spec stops changing then its status
> eventually stops changing.

Formally this is the inner controller's own ESR with `current_state_matches
(inner) := status == f(spec)` for some function `f`, which is exactly what the
demo's inner controller satisfies and exactly what `compose_dep` consumes.
Note that in Anvil's API server model a status write that does not change the
object is a no-op and does not bump the resource version, so an inner
controller that merely re-writes the same status does not interfere.

A later framework enhancement can remove this dependency for the forward
direction (see 3.3). It cannot be removed for the backward direction, and it
should not be: "copy a status that never settles" has no stable target.

## 3. Required and optional framework enhancements

### 3.1 Required: multi-client routing in the shim layer

`reconcile_with` in `src/shim_layer/controller_runtime.rs` reads `ctx.client`
and builds every `Api::<DynamicObject>::namespaced_with(client, ns, api_
resource)` from it. Change:

- `Data { client }` becomes `Data { client, remote: Option<RemoteTarget> }`
  where `RemoteTarget { group: String, kind: String, client: Client }` (or a
  small `ClientRouter` trait).
- A helper `client_for(&Data, &ApiResource) -> &Client` selects the inner
  client when `api_resource.group == remote.group && kind == remote.kind`, else
  the outer client. Each `match req` arm and the three `transactional_*`
  helpers take the routed client.
- A new entry point `run_controller_with_remote::<K, R, E, O>(fault_injection,
  remote_kubeconfig_path)` that builds the inner client with
  `Kubeconfig::read_from` + `Config::from_custom_kubeconfig` +
  `Client::try_from`, and registers the cross-cluster watch:

  ```rust
  Controller::new(Api::<K>::all(outer.clone()), watcher::Config::default())
      .watches(Api::<O>::all(inner.clone()), watcher::Config::default(), |o| {
          o.namespace().map(|ns| ObjectRef::<K>::new(&o.name_any()).within(&ns))
      })
  ```

`run_controller` and `run_controller_watching_owned` keep working unchanged.
Fault injection (`crash_or_continue`) keeps using the outer client.

Nothing on the verified side sees this: the reconciler still emits
`KubeAPIRequest`s whose view is an `APIRequest` keyed by `(kind, ns, name)`.

### 3.2 Required: the usual per-controller plumbing

Same as for any Anvil controller, all mechanical:

- `src/crds.rs`: `Outer` and `Inner` kube-derived types.
- `trusted/spec_types.rs` and `trusted/exec_types.rs`: `OuterView`,
  `InnerView` and exec wrappers (compare `vreplicaset_controller/trusted/`).
- `model/reconciler.rs`, `model/install.rs`, `exec/reconciler.rs`.
- `src/bin/outer_sync_controller.rs`, `deploy/outer_sync/`, e2e module.

### 3.3 Optional: owner-less transactional update

`GetThenUpdateRequest` / `GetThenUpdateStatusRequest` hard-code the predicate
"current object has `owner_ref`" (both in the model and in the shim's retry
loop; both carry a TODO saying the predicate should come from the client).
Because we cannot use owner references on `Inner`, we cannot use these
transactional requests and fall back to plain `Update` with a resource version.

Generalizing the predicate (for example `owner_ref: Option<OwnerReferenceView>`
with `None` meaning "object exists", i.e. controller-runtime's
`retry.RetryOnConflict`) would let the forward-sync proof drop the liveness
dependency for `Update Inner`. The change is mechanical but touches the message
type, `well_formed()`, the shim, and every existing construction site and
rely clause that reads `req.owner_ref`. Estimate one to three days plus a
full re-verification. Not needed for v1.

### 3.4 Optional: external-system hook improvements (only if someone insists on Option A)

`ExternalShimLayer::external_call` is a synchronous, stateless
`fn(EReq) -> EResp`; a kube client would need a runtime handle. The model's
`ExternalModel` has no spontaneous step and external requests are exempt from
`drop_req`. All three would need to change to make the external hook a
faithful remote cluster. Not recommended; see below.

## 4. Alternatives considered

**A. Inner cluster as the controller's "external system".** Rejected. The
external model is a deterministic function of (request, local state), driven
only by our own requests, so the inner controller's spontaneous status
changes are inexpressible without adding a new `Step` variant to
`Cluster::next` (which every existing proof case-splits on). External requests
cannot be dropped, so transient inner-cluster failures would be unmodeled. And
we would re-implement resource versions, conflicts and the status subresource
in a bespoke `Value`-typed state, losing `req_resp.rs`,
`objects_in_store.rs`, `network_liveness.rs` and the `Cluster::` invariant
library.

**B. Single logical store, route by kind (recommended).** Described above. Zero
model changes, small shim change, trusted argument in 2.2.

**C. First-class multi-API-server model** (`api_servers: Map<ClusterId,
APIServerState>`, `HostId::APIServer(id)`, per-cluster GC and drops). The most
faithful option and the right long-term direction if multi-cluster becomes a
first-class Anvil use case, but it changes `ClusterState`, `HostId`, every
`s.resources()` accessor and every existing proof. Weeks of refactoring for an
example controller, buying only the rv/uid-counter and GC-scope fidelity that
option B handles with two explicit assumptions.

## 5. Draft requirements and assumptions

Written in the style of `trusted/liveness_theorem.rs`. `outer: OuterView`,
`st: StatusView`.

```rust
pub open spec fn inner_key(outer: OuterView) -> ObjectRef {
    ObjectRef { kind: InnerView::kind(), namespace: outer.metadata.namespace->0, name: outer.metadata.name->0 }
}

// Forward sync target: the mirror exists, is live, and carries the parent's spec.
pub open spec fn spec_synced(outer: OuterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[inner_key(outer)];
        &&& s.resources().contains_key(inner_key(outer))
        &&& obj.metadata.deletion_timestamp is None
        &&& InnerView::unmarshal(obj) is Ok
        &&& InnerView::unmarshal(obj)->Ok_0.spec == outer.spec
    }
}

pub open spec fn inner_status_is(outer: OuterView, st: StatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resources().contains_key(inner_key(outer))
        &&& InnerView::unmarshal(s.resources()[inner_key(outer)]) is Ok
        &&& InnerView::unmarshal(s.resources()[inner_key(outer)])->Ok_0.status == st
    }
}

pub open spec fn status_synced(outer: OuterView, st: StatusView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resources().contains_key(outer.object_ref())
        &&& OuterView::unmarshal(s.resources()[outer.object_ref()]) is Ok
        &&& OuterView::unmarshal(s.resources()[outer.object_ref()])->Ok_0.status == st
    }
}
```

**R1 (forward ESR).** For every `outer`:
`always(desired_state_is(outer)) ~> always(spec_synced(outer))`.

**R2 (backward ESR).** For every `outer` and `st`:
`always(desired_state_is(outer) ∧ inner_status_is(outer, st)) ~> always(status_synced(outer, st))`.

R2's premise fixes the inner status rather than assuming the inner controller
is live; this keeps R2 independent of any particular inner implementation.
Combined with R1 and the liveness dependency one gets the end-to-end
corollary "spec stable ⇒ eventually `Outer.status == f(Outer.spec)` forever".

**R3 (cleanup, exec-tested in v1, proof optional).** If `Outer` has a deletion
timestamp and our finalizer, eventually `Inner{ns,name}` is absent and the
`Outer` object is gone. The API server model supports finalizers and
deletion-time semantics, so this is provable, but none of the existing
controllers prove a deletion path yet; budget it separately.

**Assumptions** (all standard for Anvil, restated for two clusters):

1. `cluster.init()` and `always(cluster.next())`.
2. Weak fairness (`next_with_wf`) of: the API server, our controller's steps,
   `schedule_controller_reconcile` for our controller, `disable_crash` for our
   controller, `disable_req_drop`, `disable_pod_monkey`, built-in controllers.
   Interpreted: the outer controller eventually stops crashing, and both
   clusters' API servers eventually stop failing requests.
3. Both CRD types installed; our controller model registered under some id.
4. Rely condition of 2.4 for every other controller id.
5. Liveness dependency of 2.4 (inner status quiesces when inner spec is
   stable). Needed for R1 only; can be discharged by `compose_dep` against a
   verified inner controller, or assumed for an unverified one.
6. Proof hygiene: resource versions and uids are compared only for equality
   against the same object.
7. Out of model: the inner namespace exists; no cross-cluster owner
   references (enforced by our guarantee); no Patch or server-side apply.

## 6. Testbed

Scripts under `tools/` and manifests under `deploy/outer_sync/`, mirroring the
existing `local-test.sh` / `deploy.sh` flow:

1. `kind create cluster --name outer` and `kind create cluster --name inner`
   (single control-plane nodes; the three-worker `deploy/kind.yaml` is not
   needed). Both land on the shared `kind` Docker network.
2. Apply `Inner` CRD, a namespace, a ServiceAccount, Role, RoleBinding and a
   long-lived `kubernetes.io/service-account-token` Secret in `inner`. Render
   a kubeconfig whose server is `https://<inner-control-plane container IP>:6443`
   (from `docker inspect`; kind's API server certificate already includes the
   node IP), whose CA is the cluster CA, and whose user is that token.
3. In `outer`: apply `Outer` CRD, RBAC, the kubeconfig as a Secret, and the
   controller Deployment mounting it. `kind load docker-image` as today.
4. A tiny unverified inner "echo" controller (kube-rs, ~50 lines, its own
   binary in `src/bin/`) deployed in `inner` that sets `Inner.status` from
   `Inner.spec`. This is the stand-in for the real implementation and
   satisfies the liveness dependency by construction.
5. e2e module `e2e/src/outer_sync_e2e.rs` with two `Client`s from contexts
   `kind-outer` and `kind-inner`:
   - create `Outer` → `Inner` appears with equal spec, label and parent-uid;
   - update `Outer.spec` → `Inner.spec` follows;
   - `Inner.status` set by echo controller → `Outer.status` equals it;
   - `docker pause inner-control-plane` for ~30 s during an update, then
     unpause → convergence resumes (exercises the `drop_req` assumption);
   - delete `Outer` → `Inner` removed, finalizer released, `Outer` gone;
   - pre-create a foreign `Inner{ns,name}` → adopted (v1 policy).
6. CI job alongside the existing e2e jobs; two single-node kind clusters fit
   on a standard runner.

For a live demo, the same scripts plus `kubectl --context kind-outer` /
`kubectl --context kind-inner` side by side are sufficient. Running the
controller out-of-cluster with two kubeconfig contexts also works and is
convenient for development, but the in-cluster deployment is what the
"production-shaped" goal calls for.

## 7. Effort and phasing (rough)

| Phase | Work | Estimate |
|---|---|---|
| 1 | Shim routing + remote watch; CRDs, views, exec reconciler; deploy manifests | ~1 week |
| 2 | Two-cluster testbed, echo controller, e2e tests, CI job | ~3–5 days |
| 3 | Model reconciler, install, trusted spec (R1, R2, rely/guarantee, dependency) | ~3 days |
| 4 | Liveness proof of R1 and R2 | ~3–6 weeks |
| 5 | Guarantee proof, `ControllerSpec` and CORE instance, composition with existing controllers | ~1 week |
| 6 (optional) | R3 deletion proof; owner-less transactional update (3.3) | 1–3 weeks |

Phase 4 dominates. For calibration, the VReplicaSet liveness proof is about
10k lines of Verus; this controller has fewer moving parts (one child, no
lists, no GC, no pod monkey) but two new ingredients: a two-kind
rely/guarantee and the leads-to argument that threads the liveness dependency
through the `Update Inner` conflict case. Expect the proof to be shorter than
VReplicaSet's, not trivially so.

## 8. Risks and open points

- **The conflict/dependency argument (2.4)** is the only genuinely new proof
  idea. If it proves awkward, 3.3 is the escape hatch: with an owner-less
  transactional update the shim's retry loop absorbs the race and R1 needs no
  dependency.
- **Adoption policy** for a pre-existing `Inner` (1.3) changes the R1 premise
  if we choose "refuse". Decide before writing the trusted spec.
- **Model fidelity caveats** in 2.2 items 2 and 5 must appear next to the
  theorem so a reader does not over-read what was proved.
- **Kind networking**: the in-cluster controller reaches the inner API server
  by container IP on the `kind` Docker network. This is stable on Linux CI
  runners; on Docker Desktop it needs the same network but has worked for
  Cluster API's docker provider for years.
