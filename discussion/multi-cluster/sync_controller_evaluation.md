# Two-cluster "Outer → Inner" sync controller: evaluation and design

**Revision 2.** Revision 1 proposed a single reconciler with a finalizer on
`Outer`, literal spec/status equality, and adoption of pre-existing `Inner`
objects, and claimed no framework changes. An adversarial review found that
the finalizer made cleanup irreversible under the model's fault injection,
that adoption was a cross-cluster privilege escalation, that the soundness
argument was stated in the unsound direction, and that the composition
precedent did not apply. This revision replaces the finalizer with a
garbage-collecting janitor reconciler, defines convergence on a projection
rather than whole-object equality, refuses to adopt, rewrites the soundness
argument as a simulation, and adds one required framework change: modeling
`metadata.generation`, without which no Anvil controller can set
`status.observedGeneration` at all.

**Revision 3.** The mirrored objects may be the *same kind* in both clusters
(the natural case: one CRD installed in both, a real controller for it in the
inner cluster, the sync controller for it in the outer cluster). Revision 2
relied on the two kinds differing to keep model keys distinct. This revision
folds the cluster into the model's kind at the trusted wrapper boundary, so
the model sees distinct keys whether or not the real kinds differ, and adds
the rely clause and testbed cases that the same-kind case needs.

## 0. The question and the short answer

We want an example controller that runs in an *outer* cluster, reconciles a
custom resource (the *Outer* copy) by ensuring a custom resource with the
same namespace, name and spec (the *Inner* copy) exists in a separate *inner*
cluster, and copies the Inner copy's status back into the Outer copy's
status. Controllers in the inner cluster are the real implementation. In the
natural case the two copies are the same kind, from one CRD installed in both
clusters; the design must not rely on the kinds differing. `metadata.
generation` and `status.observedGeneration` must behave conventionally for
an observer of either cluster. Deliverables: a production-shaped controller,
a two-kind-cluster testbed, formal assumptions and requirements, and a
machine-checked proof.

Throughout, "Outer" and "Inner" name *roles* (the copy in the outer cluster,
the copy in the inner cluster), not necessarily distinct kinds. The example
uses one kind, `Widget`, in both clusters.

**Does the current Anvil API support this?**

- **Model and proof framework:** yes, with one required enhancement. Both
  clusters are modeled as one logical API server whose key space is the
  disjoint union of the two clusters' objects. Keys are
  `(kind, namespace, name)`; the cluster is folded into the model's kind at
  the trusted exec/model boundary (the Outer copy has model kind `widget`,
  the Inner copy `widget@inner`), so keys are distinct whether or not the
  real kinds are. The inner cluster's controllers are ordinary "other
  controllers" bounded by a rely condition. The required enhancement is
  `metadata.generation` in `ObjectMetaView` and the API server model. Nothing
  else in `src/kubernetes_cluster/` changes.
- **Trusted wrappers and shim layer:** the exec `ApiResource` and
  `DynamicObject` wrappers gain a cluster tag that determines their view kind;
  the shim routes requests by that tag, takes an explicit primary client, and
  runs two reconcilers in one process. Additive, roughly 200 lines, all in
  already-trusted code.
- **Not the right vehicle:** the external-system hook (`ExternalShimLayer`,
  `ExternalModel`). It is a deterministic request-driven stub with no
  spontaneous steps and no request drops, so it cannot model an inner
  controller acting on its own, and it would force re-implementing API server
  semantics in a bespoke model.
- **Optional:** an owner-less transactional update (section 4.3). Needed only
  to compose against a *verified* inner implementation, or to remove the
  liveness dependency from the forward-sync proof.

## 1. Design

### 1.1 Resources

One CRD, `Widget` in group `anvil.dev`, namespaced, with the status
subresource, installed identically in both clusters:

```
kind: Widget
  # outer cluster: users create these; the sync controller is their controller
  # inner cluster: only the sync controller creates the mirrors; the real Widget
  #                controller lives here and acts on all Widgets
status:
  observedGeneration: int64        # conventional meaning on each object
  <mirrored fields>                # written by the inner Widget controller,
                                   # copied to the Outer copy by the sync controller
```

Keep the spec to two or three scalar fields so the view types and
marshalling lemmas stay short. The example's inner implementation is a small
unverified "echo" `Widget` controller that sets the mirrored fields from the
spec and sets `status.observedGeneration = metadata.generation`. Nothing
below depends on the kinds being equal; two different CRDs with a shared
spec/status shape work identically.

### 1.2 Identity, ownership, and lifecycle

- `Inner{ns, name}` mirrors `Outer{ns, name}`. Names match by construction.
- **No `ownerReferences` across clusters.** The inner cluster's garbage
  collector would delete an `Inner` whose owner uid does not exist there, and
  forbidding them is also what keeps the single-store model sound (3.2).
- **No finalizers, on either object, by either of our controllers.** The
  controller therefore has no irreversible action; every fault is
  re-convergent, and `Outer` deletion is never blocked by a partition.
- Identity is carried by a label `anvil.dev/managed-by: outer-sync` and an
  annotation `anvil.dev/parent-uid: <Outer uid>`. The annotation is
  load-bearing: it is how the janitor distinguishes a live mirror from a
  stale one, and how the sync controller refuses to write to an `Inner` it
  does not own.
- **Refuse to adopt.** The sync controller writes to an existing `Inner` only
  if it carries the label and its `parent-uid` equals the current `Outer`
  uid. Anything else is left alone: a stale-uid mirror is removed by the
  janitor and then recreated; a foreign object is never touched. Adoption
  would let anyone who can create `Outer{ns,name}` in the outer cluster
  overwrite `Inner{ns,name}` in the inner cluster. With one kind in both
  clusters, foreign objects are the normal case rather than a corner: anyone
  using the inner cluster natively can create `Widget{ns,name}` there.
- **Chains compose; cycles are inert.** A second sync controller in the inner
  cluster, pointed at a third cluster, sees our mirror as its Outer copy and
  propagates it onward. A cycle back to the outer cluster finds an unlabeled
  object there and refuses, so nothing loops.
- **Cleanup is background garbage collection**, the same semantics Kubernetes
  itself gives cascading deletion: a janitor reconciler removes any labeled
  `Inner` whose `Outer` is absent or has a different uid.

### 1.3 The sync reconciler (primary kind `Outer`, runs against a snapshot with generation `g`, resource version `r`, spec `σ`, uid `u`)

```
Init
 └─ Get Inner{ns,name}                                   (inner cluster, quorum read)
      ├─ NotFound → Create Inner{ns,name; label; parent-uid=u; spec=σ; no ownerRefs; no finalizers}
      │              → AfterCreateInner → Done            (no status write yet)
      ├─ Found, not ours (label missing or parent-uid ≠ u) → Done (no writes)
      ├─ Found, ours, deletionTimestamp set → Done         (treat as absent-in-progress; requeue)
      ├─ Found, ours, spec ≠ σ → Update Inner (fetched object; spec := σ; label/annotation ensured; rv from Get)
      │              → AfterUpdateInner → Done            (inner cannot be caught up yet)
      └─ Found, ours, spec == σ
           ├─ Inner.status.observedGeneration ≠ Inner.metadata.generation → Done   (inner still converging)
           └─ caught up
                ├─ π(Outer.status) == π(Inner.status) ∧ Outer.status.observedGeneration == g → Done
                └─ else UpdateStatus Outer{status := π(Inner.status) with observedGeneration := g; rv r}
                       → AfterUpdateOuterStatus → Done
Error (any unexpected response) → requeue with backoff
```

`π` is the projection onto the mirrored fields. The controller never writes
`Outer` spec or metadata, never writes `Inner` status, never deletes
anything, and every write carries a resource version (custom resources do not
permit unconditional updates, in the real API server or the model). The
"skip when already equal" branch matters: it removes conflicts in steady
state without relying on server-side no-op detection.

### 1.4 The janitor reconciler (primary kind `Inner`, runs in the same binary)

```
Init
 ├─ label missing → Done                                  (not ours)
 └─ Get Outer{ns,name}                                    (outer cluster, quorum read)
      ├─ Found, uid == parent-uid → Done
      └─ NotFound, or uid ≠ parent-uid → Delete Inner{ns,name; precondition uid = Inner.uid} → Done
```

The uid precondition is what garbage collectors use; a resource-version
precondition would only import the status-write race into deletion.

### 1.5 Generation semantics, as seen from each cluster

Kubernetes increments `metadata.generation` of a custom resource with a status
subresource exactly when its spec changes, and never on status writes.
Observers (kstatus-style tooling, `kubectl wait`, operators reading YAML)
read `status.observedGeneration == metadata.generation` as "the status
reflects the current spec".

**Inner, seen from the inner cluster.** `Inner` is an ordinary CR. The sync
controller writes its spec (which bumps `Inner.generation`, as an observer
expects) and never its status. The inner implementation sets
`Inner.status.observedGeneration` from `Inner.metadata.generation`. Nothing
unusual is visible.

**Outer, seen from the outer cluster.** The sync controller sets
`Outer.status.observedGeneration := g` only in the branch where it has
verified, in one reconcile, that `Inner.spec == σ` and the inner
implementation reports `Inner.status.observedGeneration ==
Inner.metadata.generation`, and it writes that status with `Outer`'s
resource version `r` from the same snapshot. Because a generation bump
implies a resource-version bump, the write succeeds only while `Outer` is
still at generation `g` with spec `σ`. So:

> `Outer.status.observedGeneration == Outer.metadata.generation` holds
> exactly when the current `Outer` spec has been propagated to `Inner` and
> the mirrored status is the inner implementation's status for that spec.

While a spec change is propagating anywhere in the chain, `observedGeneration`
lags and an observer sees "in progress". No bookkeeping of which `Inner`
generation corresponds to which `Outer` generation is needed, because names
match and the snapshot's resource version pins the correspondence. The
`Inner`'s own `observedGeneration` is never copied to `Outer` (it is an
inner-cluster number); `π` excludes it.

If an inner implementation never sets `observedGeneration`, `Outer` never
reports caught-up. That is the honest outcome for a non-conforming inner
controller; a per-deployment switch to treat a missing field as caught-up is
an exec-level option outside the proof.

### 1.6 Deployment shape

- One Deployment in the outer cluster, `replicas: 1`, `strategy: Recreate`.
  kube-runtime has no leader election, and two live instances would violate
  our own rely condition (safe under resource-version preconditions, but
  outside the proof).
- Outer-cluster RBAC: `outers` (get, list, watch), `outers/status` (update,
  patch). If fault injection is used, `configmaps` (get, update) in the
  `default` namespace, which is where `crash_or_continue` reads its
  configuration.
- Inner-cluster credential: a kubeconfig mounted from a Secret, pointing at a
  ServiceAccount token in the inner cluster bound to a **ClusterRole** on
  `inners` (get, list, watch, create, update, delete). `Outer` can live in any
  outer namespace, so a namespaced Role is insufficient.
- Watches: `Outer` in the outer cluster (sync primary), `Inner` in the inner
  cluster (janitor primary and sync secondary, mapped to `Outer{ns,name}`).
  Watches are a latency optimization; the proof relies only on requeue.
- Client timeouts: kube-rs defaults to a 295-second read timeout. Lower it for
  the inner client so a partition surfaces as an error within a reconcile
  rather than a five-minute stall.
- Requeue: 60 seconds after `Done`, 10 seconds after an error, both fixed
  (the shim's `error_policy`). Exponential backoff is a shim improvement, not
  a proof concern.

## 2. Alternatives considered

**External-system hook.** Rejected for the reasons in section 0.

**First-class multi-API-server model** (`api_servers: Map<ClusterId, _>`,
`HostId::APIServer(id)`, per-cluster GC and drops). Most faithful, and the
right long-term direction if multi-cluster becomes a first-class Anvil use
case. It changes `ClusterState`, `HostId`, every `s.resources()` accessor and
every existing proof. Not justified for an example controller when the
single-store simulation (3.2) handles the differences with stated
obligations.

**Finalizer on `Outer`** (revision 1). Rejected: under the model's fault
injection a `Get` can spuriously return `NotFound`, and "remove finalizer on
NotFound" is irreversible, so cleanup was unprovable and, in reality, the
same path fires when the inner CRD is uninstalled. Deletion also blocked on
partitions. The janitor has the same exposure to a spurious `NotFound` but as
a transient (it may delete a live mirror, which the sync controller then
recreates) rather than a permanent leak.

**Uid-suffixed `Inner` names.** Would make cleanup of a delayed `Create`
trivially provable but violates the same-name requirement. Not taken.

## 3. Mapping onto Anvil's model

### 3.1 One logical store, two model kinds, two controllers

The model keys objects by `(kind, namespace, name)`. Since the two copies may
share a real kind, namespace and name, the cluster must enter the key. The
model already admits arbitrary custom-resource kind strings, so the cluster
is folded into the *model* kind: `OuterView::kind() ==
CustomResourceKind("widget")`, `InnerView::kind() ==
CustomResourceKind("widget@inner")`. `OuterView` and `InnerView` are two
view types with identical spec and status views, differing only in kind; on
the exec side they are two wrappers, `OuterWidget` and `InnerWidget`, over
the same `crds::Widget` Rust type. The tag is attached at the trusted
boundary (4.2), never seen by real API servers, and never read by the
proofs except through `kind()`.

Both model kinds are installed in one `Cluster`; the sync and janitor
reconcilers are two controller ids in `controller_models`:

```rust
membership_sync:    |c, id| c.controller_models.contains_pair(id, sync_controller_model())
                          && c.type_is_installed_in_cluster::<OuterView>()
                          && c.type_is_installed_in_cluster::<InnerView>()
membership_janitor: |c, id| c.controller_models.contains_pair(id, janitor_controller_model()) && ...
```

`schedule_controller_reconcile` fires for the reconciler's own model kind
only, so Outer copies schedule the sync controller and Inner copies schedule
the janitor, even though both are `Widget` objects in reality. All
predicates read the single `resources` map; the mirror key is
`ObjectRef { kind: InnerView::kind(), namespace: outer.ns, name: outer.name }`.

This is structurally the verified VDeployment → VReplicaSet pair (a parent
creating a child CR whose status another controller writes, with a
`liveness_dependency` discharged by `compose_dep`), with one important
difference explained in 3.3: VDeployment uses owner references and the
transactional `GetThenUpdate`; we cannot.

### 3.2 Why the single-store model is sound for two real clusters

This is the trusted argument, to be placed next to the theorem. It is a
simulation, and it imposes obligations on the *implementation*, not on the
proof.

**Claim.** Every execution of the real system (two API servers with
independent resource-version and uid counters, our two controllers, the
network) maps to an execution of the model.

**Map.** Union the two stores. Choose any linearization of write events
consistent with each cluster's own order (each server serializes its own
writes) and relabel resource versions and uids by their position in that
order; the map is injective and order-preserving per cluster. Every real
step then corresponds to a model step: a real create is a model create with
the next counter value, and so on.

**Obligation 1 (exec hygiene).** The relabeling changes rv and uid *values*
but preserves equality between an object and a precondition or request that
copied them from that object. The simulation therefore holds only for code
whose behavior depends on rv and uid solely through such equality. Our two
controllers must never read `resource_version()` or `uid()` values (they use
`resource_version_eq`, `uid_eq`, and whole-object copy). The proof itself
will use global-counter lemmas such as
`object_in_ok_get_resp_is_same_as_etcd_with_same_rv` in `proof/req_resp.rs`
and the `rv < resource_version_counter` clauses of the well-formedness
invariants in `proof/objects_in_store.rs`; that is fine, because those lemmas
are applied to compare a request with the store object of the same key,
which the relabeling preserves.

**Obligation 2 (composition).** Any other controller sharing the composition
that reads rv values (VDeployment uses the rv as a pod-template hash; the
RabbitMQ controller stores an rv string in an annotation) must live entirely
in one cluster. All existing controllers do.

**Obligation 3 (cluster tagging).** The map from (cluster, real kind) to
model kind is injective, and every exec value's view kind reflects the
cluster it came from or is bound for. Concretely: an `ApiResource` wrapper's
view kind is the tagged kind of its cluster field; a `DynamicObject`
returned by the shim carries the tag of the client that produced it; the
`OuterWidget` and `InnerWidget` wrappers marshal to and unmarshal from
tagged dynamic objects only. All of this is `external_body` code whose views
are already `uninterp`; the shim is already trusted to return response
objects whose kind matches the request key, and the tag extends that trust
by one field. Without the tag the simulation map is not injective and the
model has one slot for two real objects.

**TCB notes.** Two trusted statements in the repository are literally false
for a two-cluster deployment and must be documented as such: the
`external_body` ensures in `kubernetes_api_objects/exec/object_meta.rs` that
equates the real rv string with the model's global counter (unsatisfiable
jointly for two counters; our controllers never call that accessor), and the
axiom `generated_name_spec` in `spec/api_server/state_machine.rs`, which
asserts generated-name uniqueness against every key regardless of kind (we
never use `generateName`; the axiom's own TODO proposes the per-kind form).

**Other divergences and how they are closed.**

- *Garbage collection.* The model's GC looks up owners in the union store,
  so a cross-cluster owner reference would be valid in the model and deleted
  immediately in reality. Our guarantee forbids owner references on `Inner`,
  so GC never acts on it in either world.
- *Failures.* `drop_req` fails any individual request to the API server with
  any `APIError`, for any finite prefix of an execution, independently per
  request. That covers "the inner cluster is unreachable for a while" and
  "the outer cluster is unreachable for a while". The fairness assumption
  `disable_req_drop` now reads: both clusters' connectivity eventually
  stabilizes.
- *Executed-but-lost writes.* The model has no transition "server executed
  the request, client received an error" (the network never loses messages).
  The real case is simulated by "request executed, response left in flight,
  controller crashes before reading it" via `restart_controller`. This is a
  projection, not a refinement: a real lost response affects one key while
  `restart_controller` wipes every key's ongoing reconcile. It is acceptable
  here because reconciles for distinct `Outer` keys touch disjoint objects and
  all our properties are per key. Consequences: the assumption "crashes
  eventually stop" also covers "lost responses eventually stop", and a stale
  request may still execute later, so every write must be safe to replay.
  Updates and status updates carry resource versions, deletes carry uids.
  `Create` has no precondition, and a delayed `Create Inner` can land after
  its `Outer` is gone; the janitor collects it (5, R3).
- *Namespaces.* Not modeled; creates never fail for a missing namespace.
  Assume the inner namespace exists. Deleting the inner namespace deletes
  `Inner` out of band and makes creates fail; R1 does not hold in reality
  while that persists. Deleting the outer namespace proceeds without
  blocking; the janitor cleans up.
- *CRD installation and schema.* `type_is_installed_in_cluster::<InnerView>()`
  corresponds to "the CRD is applied in the inner cluster". Schema
  parity, including OpenAPI defaults, is assumed; a default applied on one
  side only makes the projected specs never equal.
- *Spurious `NotFound`.* The model's fault injection may answer a `Get` of an
  existing object with `ObjectNotFound`. Reality does the same when a CRD is
  uninstalled or a kubeconfig points at the wrong cluster; the shim maps every
  404 to `ObjectNotFound`. Before drops stop, the janitor may therefore delete
  a live mirror, and the sync controller recreates it afterwards. The
  operational assumption to state: the CRD is installed in the outer cluster
  whenever the outer API server answers.
- *Admission and Patch.* Not modeled. Mutating admission on `Inner` spec is
  out of scope. The inner implementation may use Patch or server-side apply
  for status; for our purposes that is an `UpdateStatus`.

### 3.3 Rely, guarantee, and dependencies

**Sync guarantee.** Every in-flight API request from the sync controller is
one of: `Get` on an `Outer` or `Inner` key; `Create` of an `Inner` with a
provided name, no owner references, no finalizers, our label, `parent-uid`
equal to the triggering `Outer`'s uid, and spec equal to that `Outer`'s spec;
`Update` of an `Inner` carrying a resource version, whose object equals the
stored object at that resource version with spec replaced and our
label/annotation ensured (stated rv-conditionally against the store, in the
style of `vd_rely_update_req`); `UpdateStatus` of an `Outer` carrying a
resource version, with `status.observedGeneration == metadata.generation` of
the sent object. Never a delete, never `Outer` spec or metadata, never `Inner`
status, never any other kind.

**Janitor guarantee.** Only `Get` on `Outer` keys and `Delete` on labeled
`Inner` keys with a uid precondition.

Both guarantees trivially satisfy the rely conditions of the four existing
verified controllers, which constrain only Pods, PVCs, VReplicaSets and
RabbitMQ-managed kinds.

**Rely on every other controller `j`** (the janitor and sync are composed
with each other, so "other" excludes them):

- On `Inner` keys: no `Create`, no `Delete`, no `GetThenDelete`, no spec
  change; `UpdateStatus` and `GetThenUpdateStatus` allowed; `Update` allowed
  only if it changes metadata alone, adds neither finalizers nor owner
  references, and preserves our label and `parent-uid` annotation. This
  admits real inner implementations that label or annotate their objects and
  write status by Patch. The preservation clause matters most in the
  same-kind case, where the inner cluster's real `Widget` controller has
  opinions about the object's metadata: a controller that replaced metadata
  wholesale would make the janitor lose track of the mirror and the sync
  controller refuse it forever. Merge-patch style controllers satisfy it.
- On `Outer` keys: no `Update`, `UpdateStatus`, `Delete`, `GetThen*`.

Users are not modeled; their influence enters through
`always(desired_state_is(outer))`.

**D1, liveness dependency on the inner implementation (an axiom in v1).**
For every `Inner`: if its spec stops changing, its status and metadata
eventually stop changing and `status.observedGeneration == metadata.generation`.
This is eventual stability of the inner controller, the premise of ESR
itself. It is needed because `Update Inner` carries a resource version and
every inner-side write bumps it; the R1 argument is "either our update
eventually succeeds, or the inner spec is stable forever, in which case D1
gives quiescence and the next Get/Update pair succeeds after drops stop". In
the model a status write that changes nothing does not bump the resource
version, so an inner controller that merely rewrites the same status does not
interfere. Revision 1 claimed D1 could be discharged against the verified
controllers in this repository; it cannot, because all of them require their
CR to carry a controller owner reference (their status writes go through
`GetThenUpdateStatus`, whose `well_formed` demands one) and our `Inner` has
none. Discharging D1 against a verified inner implementation requires 4.3.

**D2, liveness dependency of the sync controller on the janitor.** A
stale-uid `Inner` (from a deleted and recreated `Outer`) must be removed
before the sync controller, which refuses to adopt, can create the new
mirror. D2 is the janitor's own liveness property R3 and *is* dischargeable
with `compose_dep`: the janitor is ours, verified, uses no owner references
and no transactional requests. This gives the proposal a genuine
composition instance.

## 4. Framework enhancements

### 4.1 Required: model `metadata.generation`

Without it no controller can set `status.observedGeneration` (the exec
reconciler must conform to the model, and the model cannot see the field).
The VStatefulSet CRD already declares `observedGeneration` in its status
schema and the controller never populates it, for exactly this reason.

Scope:

- `ObjectMetaView`: add `generation: Option<int>`. Exec `ObjectMeta`: an
  `external_body` getter `generation()` tied to the view, like
  `resource_version()`.
- API server model, custom resources only (the model's CRs all have the
  status subresource, since `UpdateStatus` exists for them): `Create` sets
  `Some(1)`; `Update` sets `old + 1` iff the spec changed, else unchanged, and
  ignores any client-supplied value (server-owned, like rv and uid); `Update
  Status` leaves it unchanged (already the case, since
  `status_updated_object` keeps old metadata); setting a deletion timestamp
  bumps it, as `rest.BeforeDelete` does. Built-in kinds have per-kind rules
  in Kubernetes; leave them unmodeled (`None`, never read) rather than model
  them wrong.
- `src/executable_model/api_server.rs` and the conformance tests follow the
  same rules.
- Blast radius measured on the current tree: 107 `ObjectMetaView { .. }`
  literals without a rest pattern that need the field, 38 whole-metadata
  equality sites in existing proofs that need inspection, plus a full
  re-verification. Estimate one to two weeks.

### 4.2 Required: cluster-tagged wrappers and shim layer

Trusted wrappers in `src/kubernetes_api_objects/exec/`:

- `ApiResource` gains a `cluster: ClusterId` field. Its view kind becomes the
  tagged kind; the CR wrapper's `api_resource()` postcondition ties it to the
  wrapper's `kind()`.
- `DynamicObject` gains the same field, set by the shim from the client that
  produced the object (`from_kube_in(obj, cluster)`); `into_kube` drops it.
- The CR wrapper macro takes a cluster parameter so that `OuterWidget` and
  `InnerWidget` wrap the same kube type with different view kinds, and their
  `unmarshal` accepts only matching tags.

`reconcile_with` in `src/shim_layer/controller_runtime.rs` reads one
`ctx.client`. Change:

- `Data` carries one `Client` per `ClusterId`; `client_for(&ApiResource) ->
  &Client` picks by the request's cluster tag. Every request arm and the
  three `transactional_*` helpers take the routed client and tag the objects
  they return.
- An entry point that takes an explicit primary `Client` and `ClusterId`
  (today `run_controller` calls `Client::try_default()`), so the janitor's
  primary watch and quorum read target the inner cluster and its triggering
  object is wrapped with the inner tag.
- A helper to run two controllers in one process (`tokio::join!` on two
  `Controller::run` streams) and to register a secondary
  `watches(Api::<Inner>::all(inner), cfg, mapper)` on the sync controller.
- Client construction from a kubeconfig path with an explicit read timeout.

Verified against kube-rs 0.91.0 source: `Controller::watches` has the needed
signature; watcher errors surface as `Err` items behind a default backoff and
the controller keeps running; single-object `Api::get` without a resource
version is a quorum read; non-API errors (connection refused, timeouts) map
to `APIError::Other`, which the reconciler treats as a generic retry.

### 4.3 Optional: owner-less transactional update

`GetThenUpdate*` hard-codes the predicate "current object carries
`owner_ref`" in the model and in the shim's retry loop, both with TODOs. An
owner-less form (controller-runtime's `RetryOnConflict`) would let the
forward-sync proof drop D1 for the `Update Inner` step, and would let a
verified inner implementation write its own status without an owner, which is
what makes D1 dischargeable by composition. Mechanical but touches the
message type, `well_formed()`, the shim, and every existing construction site
and rely clause that reads `req.owner_ref`. One to three days plus
re-verification. Not required for v1.

## 5. Requirements and assumptions

Notation as in `trusted/liveness_theorem.rs`. `π` projects a status onto the
mirrored fields.

```rust
pub open spec fn inner_key(outer: OuterView) -> ObjectRef { /* kind Inner, same ns and name */ }

pub open spec fn owned_inner(outer: OuterView, obj: DynamicObjectView) -> bool {
    &&& obj.metadata.labels->0["anvil.dev/managed-by"] == "outer-sync"
    &&& obj.metadata.annotations->0["anvil.dev/parent-uid"] == uid_string(outer.metadata.uid->0)
}

// R1 target.
pub open spec fn spec_synced(outer: OuterView) -> StatePred<ClusterState> {
    |s| { let obj = s.resources()[inner_key(outer)];
          &&& s.resources().contains_key(inner_key(outer))
          &&& obj.metadata.deletion_timestamp is None
          &&& owned_inner(outer, obj)
          &&& InnerView::unmarshal(obj) is Ok
          &&& InnerView::unmarshal(obj)->Ok_0.spec == outer.spec }
}

// R2 premise: the inner implementation has settled on status st for this spec.
pub open spec fn inner_settled(outer: OuterView, st: StatusView) -> StatePred<ClusterState> {
    |s| { let inner = InnerView::unmarshal(s.resources()[inner_key(outer)])->Ok_0;
          &&& spec_synced(outer)(s)
          &&& inner.status.observed_generation == inner.metadata.generation
          &&& π(inner.status) == st }
}

// R2 target.
pub open spec fn status_synced(outer: OuterView, st: StatusView) -> StatePred<ClusterState> {
    |s| { let o = OuterView::unmarshal(s.resources()[outer.object_ref()])->Ok_0;
          &&& π(o.status) == st
          &&& o.status.observed_generation == o.metadata.generation }
}

// R3: per mirror key k and parent uid a.
pub open spec fn parent_absent(k: ObjectRef, a: Uid) -> StatePred<ClusterState> {
    |s| !(s.resources().contains_key(outer_key_of(k)) && s.resources()[outer_key_of(k)].metadata.uid == Some(a))
}
pub open spec fn mirror_collected(k: ObjectRef, a: Uid) -> StatePred<ClusterState> {
    |s| !(s.resources().contains_key(k) && labeled_with_parent(s.resources()[k], a))
}
```

**R1 (forward ESR).** For every `outer`:
`always(desired_state_is(outer)) ~> always(spec_synced(outer))`.

**R2 (backward ESR with generation).** For every `outer` and `st`:
`always(desired_state_is(outer) ∧ inner_settled(outer, st)) ~> always(status_synced(outer, st))`.
The premise fixes the inner status rather than assuming the inner controller
is live, so R2 is independent of any particular inner implementation. Under
`always(desired_state_is(outer))` the `Outer` generation is constant (a
generation bump implies a spec change), which is what makes the target's
`observed_generation == generation` conjunct stable.

**R3 (cleanup, the janitor's liveness property).** For every mirror key `k`
and uid `a`: `always(parent_absent(k, a)) ~> always(mirror_collected(k, a))`.
Its premise is an absence, unlike every existing Anvil proof; the mechanics
are the same (weak fairness of `schedule_controller_reconcile` for the
janitor on key `k`, which is enabled while the `Inner` exists). Delayed
creates for uid `a` are finitely many, because a `Create` is only sent by a
reconcile scheduled while an `Outer` with uid `a` existed.

**G-gen (safety invariant, part of the sync guarantee).** Every
`UpdateStatus Outer` sent by the sync controller has
`obj.status.observed_generation == obj.metadata.generation`, and was formed
from an `Inner` that satisfied `inner_settled` for that `obj`'s spec. Combined
with the resource-version precondition this yields the observer property in
1.5.

**Corollary.** R1, D1 and R2 together give: if the `Outer` spec is stable,
then eventually and stably `π(Outer.status) == f(spec)` and
`observedGeneration == generation`, where `f` is the inner implementation's
function.

**Assumptions**, all standard for Anvil and restated for two clusters:

1. `cluster.init()` and `always(cluster.next())`.
2. Weak fairness of the API server, of both our controllers' steps and
   `schedule_controller_reconcile`, of `disable_crash` for both, of
   `disable_req_drop`, `disable_pod_monkey`, and the built-in controllers.
   Interpreted: our process eventually stops crashing, lost responses
   eventually stop, and both clusters' API servers eventually stop failing
   requests.
3. Both model kinds installed (the CRD applied in both clusters); both
   controller models registered.
4. The rely condition of 3.3 for every other controller id.
5. D1 for the inner implementation (axiom in v1).
6. The generation semantics of 4.1 hold for both real API servers (they do
   for CRDs with the status subresource).
7. Exec hygiene: our controllers never read rv or uid values (3.2,
   obligation 1).
8. Out of model, operational: the inner namespace exists; CRD schema parity;
   the CRD is installed in the outer cluster whenever its API server answers; one
   active replica; no mutating admission on `Inner` spec.

## 6. What the model does and does not cover

Stated so that a reader does not over-read the theorem.

| Real-world situation | In the model? | How |
|---|---|---|
| Outer controller live, inner cluster unreachable for a finite time | yes | `drop_req` on inner-bound requests |
| Same for the outer cluster | yes | `drop_req` on outer-bound requests |
| Permanent partition | excluded by fairness | correct: no liveness holds under it |
| Write executed, client sees timeout | by projection | executed + `restart_controller`; all writes replay-safe; delayed `Create` collected by janitor |
| Late delivery of a stale request after retry | yes | network reorders; preconditions reject stale writes |
| Spurious/real `NotFound` (CRD missing, wrong kubeconfig) | yes, as a fault | janitor may transiently delete a live mirror; recreated after drops stop |
| Inner implementation changing status on its own | yes | other controller under rely |
| Inner implementation adding labels/annotations | yes | metadata-only `Update` allowed by rely |
| Inner implementation adding finalizers to `Inner` | no (rely forbids) | relaxing it adds a dependency "inner side releases finalizers" to R3 |
| User deletes or edits `Inner` out of band; inner cluster rebuilt | no | controller recovers in exec (NotFound → Create; uid mismatch → janitor); modeling it needs an "inner monkey" step in `src/kubernetes_cluster/`, priced like `pod_monkey` |
| Inner namespace deleted | no | R1 false in reality while it persists; operational assumption |
| Outer deleted and recreated with new uid while old mirror exists | yes | janitor removes stale mirror (D2), sync recreates |
| Pre-existing foreign `Inner{ns,name}` (routine when both clusters share the kind) | vacuous in model (only our controllers create objects of the inner model kind) | exec refuses to adopt; observable only via logs and a lagging `observedGeneration` in v1 |
| Inner cluster's real controller rewriting metadata | partly | rely requires our label and annotation to be preserved |
| Two sync controllers forming a cycle across clusters | no | refuse-to-adopt makes the cycle inert (1.2) |
| Two controller replicas | no | `replicas: 1`, `strategy: Recreate` |
| Time-based behavior (staleness after N seconds) | no | no clock in the model |
| Generation bumps on spec change, not on status | yes, after 4.1 | API server model |

## 7. Testbed

Scripts under `tools/`, manifests under `deploy/outer_sync/`, mirroring
`local-test.sh` and `deploy.sh`:

1. `kind create cluster --name outer` and `--name inner`, single control-plane
   nodes on the shared `kind` Docker network.
2. In `inner`: the `Widget` CRD (the same manifest as in `outer`), a
   namespace, ServiceAccount, ClusterRole, ClusterRoleBinding, a long-lived
   `kubernetes.io/service-account-token` Secret, and the echo `Widget`
   controller. Render a kubeconfig whose server is the
   inner control-plane container's IP on port 6443 (from `docker inspect`;
   pin the IP with `--ip` if the network is ever disconnected and reconnected
   during tests; whether kind's API server certificate includes that IP is
   not verifiable from this repository and must be checked once), CA from the
   cluster, user from the token.
3. In `outer`: the same `Widget` CRD, RBAC, the kubeconfig Secret, the
   controller Deployment (`replicas: 1`, `strategy: Recreate`), image loaded
   with `kind load docker-image`. No `Widget` controller other than the sync
   controller runs in `outer`.
4. e2e module `e2e/src/outer_sync_e2e.rs` with two `Client`s from contexts
   `kind-outer` and `kind-inner`:
   - create `Outer` → `Inner` appears with equal spec, label, parent-uid;
   - update `Outer.spec` → `Inner.spec` follows; `Inner.generation` increases
     by exactly one per spec change and not on status copies;
   - echo controller settles → `Outer.status` mirrors it and
     `Outer.status.observedGeneration == Outer.metadata.generation`; before
     it settles, `observedGeneration` lags (assert with a watch log);
   - partition: `docker network disconnect kind inner-control-plane` during an
     update (this fails fast; a `docker pause` shorter than the client read
     timeout never reaches the error path), then reconnect with the same IP →
     convergence resumes;
   - delete `Outer` → the janitor removes `Inner`; delete `Outer` while
     partitioned → deletion completes immediately, `Inner` removed after heal;
   - delete and recreate `Outer` with the same name → old mirror removed, new
     one created, no adoption;
   - pre-create a native `Widget{ns,name}` in `inner` (no label), then create
     `Widget{ns,name}` in `outer` → the inner object is never modified, the
     echo controller keeps serving it, the outer object never reports
     caught-up;
   - have the echo controller add its own label and annotation to mirrors →
     ours survive, sync and janitor unaffected;
   - `kubectl get widget -A` in both contexts as the demo view: same names,
     same specs, statuses flowing inward-to-outward;
   - crash mode of the shim during each write step.
5. CI job alongside the existing e2e jobs; two single-node clusters fit on a
   standard runner.

## 8. Effort and phasing (rough)

| Phase | Work | Estimate |
|---|---|---|
| 0 | `metadata.generation` in view, API server model, executable model, exec getter; re-verify all controllers | 1–2 weeks |
| 1 | Cluster-tagged `ApiResource`/`DynamicObject`/CR wrappers; shim routing by tag, explicit-client entry point, dual-controller runner; CRD, views, both exec reconcilers; manifests | ~1.5 weeks |
| 2 | Two-cluster testbed, echo controller, e2e tests, CI job | ~1 week |
| 3 | Model reconcilers, install, trusted spec (R1–R3, G-gen, rely/guarantee, D1, D2) | ~1 week |
| 4 | Liveness proofs: sync R1 (new lemma family for conflict-under-dependency, stale-snapshot status write), R2, janitor R3 (absence premise, no precedent) | 4–8 weeks |
| 5 | Guarantee proofs, `ControllerSpec`s, `compose_dep` (sync on janitor) and composition with the four existing controllers | 1–2 weeks |
| optional | Owner-less transactional update (4.3); inner-monkey model step; readiness conditions on `Outer` | 1–3 weeks |

For calibration, the existing `proof/` directories are 8.7k lines
(VReplicaSet), 11.7k (VDeployment), 13.8k (VStatefulSet) and 9k (RabbitMQ).
Both our reconcilers are smaller than any of those, but three ingredients
have no precedent: plain `Update`/`UpdateStatus` with resource versions (all
existing controllers use `GetThenUpdate*`), a leads-to that threads a
liveness dependency through a conflict loop, and a deletion-side liveness
property. Phase 4 dominates and is the least certain number.

## 9. Open decisions

- **Rely on inner-side finalizers.** v1 forbids them. If real inner
  implementations need them, R3 acquires a dependency on their release and
  the sync controller must treat terminating mirrors as absent-in-progress
  (already in the state machine).
- **Conditions on `Outer` status.** A `Ready`/`InnerReachable` condition is
  cheap to add to the projection but adds no provable content without time in
  the model. Recommended as an exec-visible follow-up once R1–R3 are proved.
- **Transient deletion by the janitor on spurious `NotFound`.** Accepted in
  v1 as the price of never blocking deletion. If the inner workload is
  expensive to tear down, a second confirming `Get` before `Delete` reduces
  the real-world exposure at no cost to the proof.
- **Naming.** `Widget` is a placeholder for the shared kind; the model tag
  string (`@inner`) and the `ClusterId` enum are likewise placeholders.
- **Surfacing refusal.** In the same-kind case a refused native object is a
  routine conflict, and a condition on the outer object saying so is worth
  more than in revision 2. Still recommended as a follow-up after R1–R3.
