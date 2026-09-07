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

**Decisions closed after revision 3.** The inner cluster's real controller
may put finalizers on mirrors (rely relaxed; cleanup gains dependency D3).
The shared kind is `Widget`, the inner model kind is `widget@inner`, and
the cluster enum is `ClusterId { Primary, Remote }` (the outer copy lives in
the primary cluster, the inner copy in the remote one).

**Revision 4, after a second design review against real controller
practice.** Four decisions changed: (1) spec and status writes use a
JSON-patch primitive whose `test` operations pin `metadata.uid` and
`metadata.generation`, instead of a full-object replace pinned to
`resourceVersion`; this removes the inner-quiescence dependency from the
forward-sync proof and makes the controller tolerant of an inner controller
that writes timestamps or heartbeats. (2) `status.observedGeneration` on the
outer copy is stamped on every status write, as Deployment and StatefulSet
do, and a `Synced` condition carrying its own `observedGeneration` says
whether the mirror has caught up. (3) The janitor establishes that a parent
is absent by a *successful* `List` of outer copies that contains no object
with the mirror's parent uid, never by a `Get` returning `NotFound`, so a
type-level 404 (CRD reinstall, misrouted kubeconfig) is an error rather than
mass deletion. (4) Exactly one outer cluster per inner cluster is an
explicit assumption; a parent-cluster identity and a `keep` annotation that
freezes collection are deferred features.

**Revision 5, after building and verifying it.** The controller, the
two-cluster testbed and the proofs of R1, R2 and R3 exist and pass; both
reconcilers are packaged as Welder controller specs and composed. Writing the
proofs changed the specification in five places, all recorded in section 5:
(1) *fat-finger tolerance*: the rely no longer forbids other actors from
changing a mirror's spec (a mistaken `kubectl edit` in the inner cluster is
not malicious and a controller must survive it); the sync reconciler
overwrites such an edit and never copies a status the inner side computed
for it, and R1 and R2 promise convergence for the time after such edits stop,
exactly as they do for the time after the outer spec stops changing. (2) The
premise of R1 and R2 fixes the outer copy's *generation* along with its spec,
which is the same statement made precise, and is what pins
`observedGeneration` in R2's target. (3) Mirrored status fields are copied
only when the inner status observes the mirror's current generation;
otherwise the previously reported fields are kept and `Synced=False/
InnerConverging` is written. (4) R3 is stated per mirror *object* (key,
parent uid, object uid) with the target "that object is gone", and D1 (inner
liveness) is no longer a named assumption: R2's premise fixes the inner
status, so D3 is the only liveness assumption about the inner side. (5) The
sync reconciler's Welder spec names the janitor: its partial rely on the
janitor is the janitor's guarantee, not the anonymous rely. A claim about
Kubernetes raised in review, that a PATCH response carries the object's
status at the instant of the write, was verified and found to be already
modeled; using it would not change any property and was not adopted (4.1c).

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

- **Model and proof framework:** yes, with two enhancements, both on this
  branch and verified, and nothing else: the proofs of R1, R2 and R3 and the
  Welder composition went through with the framework's existing lemma
  library. Both clusters are modeled as one logical API
  server whose key space is the disjoint union of the two clusters' objects.
  Keys are `(kind, namespace, name)`; the cluster is folded into the model's
  kind at the trusted exec/model boundary (the Outer copy has model kind
  `widget`, the Inner copy `widget@inner`), so keys are distinct whether or
  not the real kinds are. The inner cluster's controllers are ordinary "other
  controllers" bounded by a rely condition. The enhancements are
  `metadata.generation` in `ObjectMetaView` and the API server model, and a
  JSON-patch primitive (`PatchRequest`, `PatchStatusRequest`) with `test`
  operations on uid and generation. Nothing else in
  `src/kubernetes_cluster/` changes.
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
  to compose against a *verified* inner implementation.
- **Status:** everything below the line "proposed" in earlier revisions is
  built and verified; section 8 has the inventory.

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
- **No finalizers by either of our controllers, on either object.** The
  controller therefore has no irreversible action; every fault is
  re-convergent, and `Outer` deletion is never blocked by a partition. The
  inner cluster's real `Widget` controller *may* put its own finalizers on
  mirrors (it is a normal `Widget` controller and does not know they are
  mirrors). A janitor `Delete` then only stamps a deletion timestamp; the
  mirror lingers until the inner side releases its finalizer, which is the
  inner controller's own liveness obligation (D3 in 3.3).
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

### 1.3 The sync reconciler (primary kind `Outer`, runs against a snapshot with generation `g`, spec `σ`, uid `u`)

```
Init
 └─ Get Inner{ns,name}                                   (inner cluster, quorum read)
      ├─ NotFound → Create Inner{ns,name; label; parent-uid=u; spec=σ; no ownerRefs; no finalizers}
      │              → AfterCreateInner → Done           (the watch on the mirror triggers the next reconcile)
      ├─ Found, deletionTimestamp set (ours or not) → status Synced=False/InnerTerminating → Done
      │                                                  (absent-in-progress: wait for the inner side to release it)
      ├─ Found, not ours (label missing or parent-uid ≠ u) → status Synced=False/ForeignObject → Done
      ├─ Found, ours, spec ≠ σ → Patch Inner {test uid=Inner.uid, test generation=Inner.generation; add /spec := σ}
      │              → AfterPatchInner → Done             (covers a fat-finger edit of the mirror's spec)
      ├─ Found, ours, spec == σ, Inner.status.observedGeneration == Inner.metadata.generation
      │     → status { observedGeneration: g, mirrored fields: π(Inner.status),
      │                Synced: True (reason Synced, condition.observedGeneration = g) }
      └─ Found, ours, spec == σ, inner not caught up
            → status { observedGeneration: g, mirrored fields: as previously reported,
                       Synced: False/InnerConverging (condition.observedGeneration = g) }
      where "status X" means: Outer.status == X → Done,
                              else PatchStatus Outer {test uid=u, test generation=g; add /status := X}
                                   → AfterPatchOuterStatus → Done
Error (any unexpected response) → requeue with backoff
```

`π` is the projection onto the mirrored fields (everything in the shared
status type except `observedGeneration` and `conditions`). The controller
never writes `Outer` spec or metadata, never writes `Inner` status or
metadata, and never deletes anything.

The last two branches are the status-copy rule. Mirrored fields are copied
*only* from an inner status that observes the mirror's current generation.
If the inner side reconciled an earlier generation of the mirror, including a
generation produced by a mistaken edit that the reconciler has since
overwritten, its status is for a spec the outer copy never asked for and is
never reported; the outer copy keeps the last fields it did report and says
`InnerConverging`. This is what makes "the outer status is the inner
implementation's status for the outer spec" a theorem (R2) rather than a
hope.

Writes are JSON patches, not replaces. A patch carries no
`resourceVersion`; the API server applies it to the latest object, so writes
by other actors to fields the patch does not test (the inner controller's
status, labels, annotations, finalizers; a user's labels on the outer copy)
never make it fail. What the patch tests is exactly what the decision
depended on: `metadata.uid` (same incarnation of the object) and
`metadata.generation` (same spec as was read, since generation changes iff
the spec does). A stale or replayed patch therefore fails its `test` and is
rejected. This is controller-runtime's optimistic-concurrency idiom with the
token chosen so that only spec changes invalidate it. The "skip when already
equal" branch avoids a write per reconcile in steady state.

### 1.4 The janitor reconciler (primary kind `Inner`, runs in the same binary)

```
Init
 ├─ label or parent-uid annotation missing → Done         (not ours)
 └─ List Outer in namespace ns                            (outer cluster, quorum read)
      ├─ error (including a type-level 404: CRD absent, misrouted kubeconfig) → Error (requeue; never delete)
      ├─ Ok, some listed Outer has uid == parent-uid → Done
      └─ Ok, no listed Outer has uid == parent-uid → Delete Inner{ns,name; precondition uid = Inner.uid} → Done
```

Absence is established only by a *successful* read that does not contain
the parent, matched on uid rather than name. Two consequences. A `Get`
returning `NotFound` is never treated as absence: the model's fault
injection can fake that answer, and in reality a CRD reinstall window or a
kubeconfig pointing at the wrong cluster answers `NotFound` for every key at
once, which would otherwise delete every mirror within one requeue period.
And a same-named parent with a different uid (the outer copy was deleted
and recreated) counts as absent, so the stale mirror is collected and the
sync controller creates a fresh one; the two controllers agree on what a
uid mismatch means.

The uid precondition on `Delete` is what garbage collectors use; a
resource-version precondition would only import the status-write race into
deletion. If the mirror carries an inner-side finalizer, `Delete` stamps a
deletion timestamp and returns Ok; the mirror stays scheduled while it
exists, so the janitor re-runs, re-issues `Delete` (a no-op on an
already-terminating object), and the object disappears when the inner side
removes its finalizer. The janitor never touches finalizers itself.

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

**Outer, seen from the outer cluster.** The sync controller follows the
convention of the built-in workload controllers: every status write it makes
sets `Outer.status.observedGeneration := g`, the generation of the snapshot
it reconciled, meaning "the controller has processed this generation", and
progress is reported in a condition. The status patch tests `uid == u` and
`generation == g`, so it lands only while `Outer` is still at generation `g`
with spec `σ`; a user spec change in between makes the patch fail and the
next reconcile stamps the new generation. The condition `Synced` is `True`,
with `condition.observedGeneration == g`, exactly when the controller
verified in that reconcile that `Inner.spec == σ` and the inner
implementation reports `Inner.status.observedGeneration ==
Inner.metadata.generation`; the mirrored fields are copied from
`Inner.status` in exactly that case (1.3). Otherwise `Synced` is `False`
with a reason (`InnerConverging`, `InnerTerminating`, `ForeignObject`) and
the previously reported fields are kept. So:

> `Outer.status.observedGeneration == Outer.metadata.generation` means the
> sync controller has acted on the current spec; `Synced == True` with the
> same `observedGeneration` means that spec is in the inner cluster and the
> mirrored status is the inner implementation's status for it.

kstatus-style tooling reads the first as "not in progress at the controller
level" and the second as readiness, which is how Deployment's
`observedGeneration` and `Progressing`/`Available` conditions are read. A
controller that is down, an unreachable inner cluster and a foreign object
are now distinguishable: the first leaves `observedGeneration` behind
`generation`, the second and third show `Synced=False` with a reason. No
bookkeeping of which `Inner` generation corresponds to which `Outer`
generation is needed, because names match and the status patch's generation
test pins the correspondence. The `Inner`'s own `observedGeneration` is never
copied to `Outer`; `π` excludes it.

If an inner implementation never sets `observedGeneration`, `Synced` never
becomes `True`. That is the honest outcome for a non-conforming inner
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
  The spec and status patches test uid and generation, so a replayed patch
  either lands on the same generation it was formed for (a no-op) or is
  rejected; deletes carry uids. `Create` has no precondition, and a delayed
  `Create Inner` can land after its `Outer` is gone; the janitor collects it
  (5, R3).
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

As written in `trusted/rely_guarantee.rs`. Every condition quantifies over
the API requests a controller has in flight.

**Sync guarantee** (`widget_sync_guarantee`). A request sent while
reconciling the outer copy at `outer_key` is one of: `Get` of
`inner_key_of(outer_key)`; `Create` in `outer_key`'s namespace of exactly
`make_inner(outer)` for an outer copy `outer` at that key whose uid has been
issued and is bound to that key (label, `parent-uid` annotation, spec `σ`, no
owner references, no finalizers, no status); `Patch` of kind `Inner` at
`outer_key`'s namespace and name (the spec patch); `PatchStatus` of kind
`Outer` at that namespace and name with `test` on uid and generation and a
status whose `observedGeneration`, and whose `Synced` condition's
`observedGeneration`, equal the tested generation (G-gen). Nothing else: no
`Update`, no `Delete`, no `List`, no writes to any other key.

**Janitor guarantee** (`widget_janitor_guarantee`). A request sent while
reconciling the mirror at `inner_key` is a `List` of kind `Outer` in
`inner_key`'s namespace, or a `Delete` of `inner_key` (kind `Inner`) with a
uid precondition.

**Sync rely on an anonymous other controller** (`widget_sync_rely`): no
`Create` of kind `Inner`; an `Update` or `GetThenUpdate` of a mirror that is
going to land (its resource version matches the store) changes neither the
owner references nor the mirror's identity (`managed-by` label and
`parent-uid` annotation), and is otherwise *free*, spec included; `Patch` of
anything (a spec patch of a mirror is a fat-finger edit, a status patch is how
the inner side reports); no `UpdateStatus`, `GetThenUpdateStatus` or
`PatchStatus` of kind `Outer`; no `Delete` or `GetThenDelete` of kind
`Inner`. Adding and removing the inner side's own finalizers, labels and
annotations is allowed, which admits real inner implementations that
finalize, label and annotate what they reconcile, as long as they do not
replace metadata wholesale (merge-patch style controllers satisfy this).

**Janitor rely on an anonymous other controller** (`widget_janitor_rely`): a
`Create` of kind `Inner` at namespace `ns` and name `n` is `make_inner(outer)`
for an outer copy at `Outer{ns, n}` whose uid is bound to that key (the sync
reconciler's way; this is what makes every mirror's `parent-uid` a real,
issued uid that only its parent can carry); `Update` and `GetThenUpdate` as
in the sync rely.

**The sync reconciler's rely on the janitor is the janitor's guarantee**,
not the anonymous rely: the janitor does delete mirrors, and the sync
reconciler's proof needs to know *which* (only mirrors whose parent is gone,
established from a successful `List`). The Welder `safety_partial_rely` is a
function of the other controller's id, so the sync spec says "for the janitor
id, the janitor's guarantee; for anyone else, `widget_sync_rely`". The
janitor's model, not just its messages, is then in scope of the sync proof:
the message invariant `janitor_deletes_are_sound` (a janitor `Delete` in
flight targets an object whose parent is absent forever) is proved from the
janitor's state machine and is what shows a janitor `Delete` never removes a
mirror R1 is about to rely on.

The two guarantees discharge each other's relies (`compatible` in
`composition/widget_sync_reconciler.rs`): the janitor's guarantee is the sync
reconciler's rely on it by definition, and the sync guarantee's `Create` is
`make_inner(outer)` at the outer copy's own namespace and name, which is the
janitor's rely. Whether both guarantees also satisfy the rely conditions of
the four existing verified controllers (which constrain Pods, PVCs,
VReplicaSets and RabbitMQ-managed kinds) is expected but has *not* been
mechanically checked; composing the pair into `compose_all.rs` is future
work (section 8).

Users are not modeled; their influence enters through the premises of R1
and R2 (`outer_stable`, section 5).

**D1 is gone.** Earlier revisions named a liveness dependency on the inner
implementation ("if the mirror's spec stops changing, the inner status
eventually settles with `observedGeneration == generation`"). It was only
ever needed to *state* R2 with a live inner side. R2 is instead stated with
the inner status fixed in its premise (`inner_settled`), so it holds for any
inner implementation, live or not, and the only liveness assumption about
the inner side is D3. Discharging "the outer status eventually equals
`f(spec)`" for a particular inner implementation is then that
implementation's own ESR composed with R2.

**D2, the sync reconciler's liveness dependency on the janitor, is R3 and is
discharged by composition.** A stale-uid mirror (from a deleted and recreated
`Outer`), or a delayed `Create` that landed after its parent was gone, must be
removed before the sync reconciler, which refuses to adopt, can create the
new mirror. R3 is the janitor's ESR; `compose_dep` consumes it as the sync
spec's `liveness_dependency`. This is the repository's second genuine
`compose_dep` instance after VDeployment on VReplicaSet.

**D3, the environment rely, unchanged.** For every terminating mirror object
(kind `Inner`, uid `u`, deletion timestamp set): the object with uid `u` is
eventually gone. Interpreted: the inner side removes every finalizer it owns
from an object it sees terminating, after which the API server removes the
object (the model rejects new finalizers on terminating objects). R3 depends
on it directly; R1 and R2 through R3. It is the `environment_rely` of both
Welder specs and remains an axiom in this version; an inner implementation
verified in Anvil would discharge it in its own guarantee.

### 3.4 Packaging as Welder controller specs

Welder (`kubernetes_cluster/proof/core.rs`, `composition.rs`) adds no
verification power: `sync_eventually_synced` and
`sync_eventually_mirrors_status` are ordinary theorems with explicit
hypotheses (fairness, the janitor's guarantee, D3, R3). What Welder adds is
the closed statement about the cluster running both controllers, and a
mechanical check of the bookkeeping:

- `compose_dep` consumes the janitor's *proved* ESR to discharge the sync
  spec's liveness dependency, so `core(widget_core_cluster, {janitor, sync})`
  assumes nothing about the janitor beyond its model. Only D3 remains an
  assumption about the environment.
- `compatible` forces each guarantee to be proved to imply the other's rely,
  so a mismatch between what one reconciler promises and what the other
  assumes is a verification failure, not a gap in a prose argument.
- The `ControllerSpec` shape (ESR, guarantee, partial rely, environment rely,
  liveness dependency, fairness, membership) is the same for every Anvil
  controller, which is what will let the pair be composed with the existing
  four without reopening any proof.

The concrete instance is `widget_core_cluster()` (janitor id 1, sync id 2,
both Widget kinds installed) and `widget_core_holds()`.

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
- Blast radius, measured by making the change: the struct and its
  `default()`, the create and update literals in the API server model, the
  delete-with-finalizers branch, three proof sites that replicate the create
  literal (VReplicaSet and VDeployment helper invariants), the executable
  model's create/update/delete paths, one exec getter, and one unit test.
  Whole-metadata equalities in existing proofs compare objects that are both
  constructed with `generation: None`, so they are unaffected. Plus a full
  re-verification. (An earlier draft estimated 107 literal sites; that count
  was an artifact of line-based grep over multi-line `..self` helpers.)
- **Status: done on this branch.** Re-verifying the existing controllers
  surfaced three kinds of fallout, all mechanical, all now fixed:
  1. *Proof-side replicas of the create literal* (six sites across
     VReplicaSet, VDeployment and VStatefulSet) needed the new field so they
     stay syntactically identical to the model's created object.
  2. *Identity-modulo-server-churn comparisons* in VDeployment and RabbitMQ
     used `metadata.without_resource_version()`. Both controllers update a
     custom resource (VReplicaSet, VStatefulSet) whose spec change now also
     bumps generation, so those comparisons became false after an update.
     They now use `without_resource_version_and_generation()`. This is the
     same lesson the sync controller must apply: the identity of an object
     across its own updates excludes every server-owned counter.
  3. *Solver budgets*: four large lemmas crossed the default rlimit with the
     slightly larger metadata term and needed an explicit `rlimit`; one
     framework lemma (at-most-one-controller-owner) was restructured with a
     per-key case split instead.
  The well-formedness invariant `etcd_object_is_well_formed` now also
  records that custom resources always carry a generation and built-in
  kinds never do; RabbitMQ's no-op ConfigMap update needed exactly that
  fact. Staged verification of `kubernetes_cluster` and all four controllers
  plus `composition` passes, and the full `cargo verus verify --lib` passes
  (944 verified, 0 errors, about 25 minutes on Verus `main` built for this
  branch).

### 4.1b Required: a JSON-patch primitive (done on this branch)

The model had only whole-object `Update`/`UpdateStatus` (kube `replace`)
pinned to `resourceVersion`, and transactional `GetThen*` forms whose
predicate is a hard-coded owner reference. Neither fits a controller that
shares an object with another controller: replace-with-rv fails on every
unrelated write, and the transactional forms overwrite the whole object on
retry. `PatchRequest` and `PatchStatusRequest` model the idiomatic
alternative: a JSON patch of `test` operations on `metadata.uid` and
`metadata.generation` followed by an `add` of `/spec` (or `/status`),
applied by the API server atomically to the stored object. In the model a
failed test returns `Invalid` (the API server answers 422 for a failed JSON
patch `test`); a passing patch reuses the existing update pipeline
(`handle_update_request` / `handle_update_status_request` on the stored
object with the new spec or status), so validity, the no-op rule, the
resource-version bump and the generation rule are unchanged. The shim
realizes it with kube's `Api::patch` / `patch_status` and `Patch::Json`. The
four existing controllers' rely conditions forbid other controllers from
patching the kinds they manage, which no composed controller does, so their
proofs and guarantees are unaffected. Merge patch, server-side apply and
`managedFields` remain unmodeled.

### 4.1c Investigated, not adopted: reading status from the PATCH response

A review question asked whether a Kubernetes PATCH returns the object,
status included, as of the instant of the write, and whether the sync
reconciler should use that instead of re-reading. It does: the API server
answers a PATCH on the main endpoint with the persisted object at the
write's linearization point, `.status` included, and kube-rs's
`Api::patch` returns it. The model already says so: `PatchResponse` carries
`Result<DynamicObjectView, APIError>` and the API server model answers with
the stored object after the update, so no framework change is involved.

The sync reconciler does not use it, for a reason that follows from the
status-copy rule. The response to the spec patch is the mirror with the
*new* generation and the *old* status, whose `observedGeneration` is the
old generation; the copy rule (rightly) refuses that status. The only line
it could write from the response is `Synced=False/InnerConverging` at the
outer generation, one reconcile earlier than the watch-triggered reconcile
writes the same line; `Synced=True` cannot come sooner, because it waits on
the inner implementation. Against that, the extra branch would add a state
to both reconcilers and to the proof for no change in any of R1, R2 or R3.
The response to the *status* patch on the outer copy is likewise not read:
the reconcile ends, and the next one compares the store with the desired
status. The reason `Propagating` reserved for such an early line is defined
and unused.

### 4.2 Required: cluster-tagged wrappers and shim layer (done on this branch)

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
owner-less form (controller-runtime's `RetryOnConflict`) would let a
verified inner implementation write its own status without an owner
reference, which is what composing against a verified inner implementation
(and discharging D3 from its guarantee) needs. Mechanical but touches the
message type, `well_formed()`, the shim, and every existing construction site
and rely clause that reads `req.owner_ref`. One to three days plus
re-verification. Not required for v1.

## 5. Requirements and assumptions

As in `trusted/liveness_theorem.rs` (the file is the authority; this is a
readable transcription). `π` is `WidgetStatusView::mirrored()`, the status
with `observedGeneration` and `conditions` cleared. Both clusters are one
logical store: the outer copy has kind `widget`, the mirror `widget@inner`,
at the same namespace and name.

```rust
// Premise of R1 and R2: the outer copy `outer` (with its uid) is present, not
// terminating, has spec outer.spec at generation outer.metadata.generation, and
// nobody is writing anything but that spec to the mirror any more.
outer_stable(outer)(s) :=
    desired_state_is(outer)(s)
 && s.resources()[outer.object_ref()].metadata.generation == outer.metadata.generation
 && mirror_spec_undisturbed(outer)(s)

// Every in-flight Update / GetThenUpdate / Patch of the mirror writes outer.spec
// (the sync reconciler's own patches included). Other writes are unconstrained.
mirror_spec_undisturbed(outer)(s) :=
    forall msg in flight, msg is an API request:
        Update(req)        with req.key() == inner_key(outer) ==> unmarshal_spec(req.obj.spec) == Ok(outer.spec)
        GetThenUpdate(req) with req.key() == inner_key(outer) ==> same
        Patch(req)         with req.key() == inner_key(outer) ==> unmarshal_spec(req.spec) == Ok(outer.spec)

// R1 target.
spec_synced(outer)(s) :=
    let obj = s.resources()[inner_key(outer)];
    contains_key && obj.metadata.deletion_timestamp is None
 && unmarshal(obj) is Ok && is_mirror_of(unmarshal(obj), outer) && unmarshal(obj).spec == outer.spec

// R2 premise (with outer_stable): the inner side has processed the mirror's
// current spec and reports `mirrored` for it.
inner_settled(outer, mirrored)(s) :=
    spec_synced(outer)(s) && inner_caught_up(inner) && π(inner.status) == mirrored
    where inner = unmarshal(s.resources()[inner_key(outer)]),
          inner_caught_up(inner) := inner.status is Some
                                 && inner.status.observed_generation == inner.metadata.generation

// R2 target.
status_synced(outer, mirrored)(s) :=
    let stored = unmarshal(s.resources()[outer.object_ref()]);  // must be Ok, status Some
    π(stored.status) == mirrored
 && stored.status.observed_generation == stored.metadata.generation
 && stored.status.synced_condition() == Some { status: True, observed_generation: stored.metadata.generation, .. }

// R3 (per mirror object): key k of kind Inner, parent uid a, object uid u.
mirror_object_is(k, a, u)(s) := contains_key(k) && s.resources()[k].metadata.uid == Some(u)
                               && mirror_of_parent(s.resources()[k], a)   // label + parent-uid annotation == a
object_is_gone(k, u)(s)      := !(contains_key(k) && s.resources()[k].metadata.uid == Some(u))
parent_absent(k, a)(s)       := !(contains_key(outer_key_of(k)) && s.resources()[outer_key_of(k)].metadata.uid == Some(a))

// D3 (environment rely): a terminating mirror object is eventually gone.
inner_terminating_object(k, u)(s) := k.kind == Inner && contains_key(k)
                                   && s.resources()[k].metadata.uid == Some(u)
                                   && s.resources()[k].metadata.deletion_timestamp is Some
inner_releases_terminating_objects := forall (k, u): inner_terminating_object(k, u) ~> object_is_gone(k, u)
```

**R1 (forward ESR).** For every `outer`:
`□ outer_stable(outer) ~> □ spec_synced(outer)`.

**R2 (backward ESR with generation).** For every `outer` and `mirrored`:
`□ (outer_stable(outer) ∧ inner_settled(outer, mirrored)) ~> □ status_synced(outer, mirrored)`.

**R3 (cleanup, the janitor's ESR).** For every `(k, a, u)`:
`□ parent_absent(k, a) ∧ mirror_object_is(k, a, u) ~> object_is_gone(k, u)`.

**G-gen (part of the sync guarantee, section 3.3).** Every `PatchStatus`
of an outer copy the sync reconciler has in flight tests the copy's uid and
generation and writes a status whose `observedGeneration`, and whose `Synced`
condition's `observedGeneration`, equal the tested generation. With the
generation test, this yields the observer property of 1.5.

*Reading the premises.* `outer_stable` says three things an operator would
recognize: the user has stopped editing the outer copy (spec, hence
generation, constant; not being deleted; same object, not a recreated one),
and whoever was fat-fingering the mirror's spec in the inner cluster has
stopped. The premise is about the *future* from some point on, which is what
`□ ... ~>` means: convergence is promised after the disturbances stop, not
during them. During them the reconciler still behaves (guarantee, G-gen,
"never copy a status for a spec we did not ask for"), it just cannot be
promised to *finish*. `inner_settled` fixes the inner implementation's
answer instead of assuming the inner implementation is live; that is the
reason R2 needs no D1.

*Reading the targets.* R1's target includes "is a mirror of `outer`", which
carries the *current* outer uid, so a stale mirror from a recreated outer copy
does not count; and "not terminating", so a mirror the janitor has marked for
deletion does not count either. R2's target is exactly what kstatus-style
tooling reads. R3's target is that the specific object is gone; uids are
never reused, so nothing can bring it back. Whether another mirror with the
same parent uid appears later depends on who creates mirrors, and R1's proof
handles that for the parent uids it cares about (reconciles triggered by an
old copy of the outer object drain in finite time).

**Assumptions**, all standard for Anvil and restated for two clusters:

1. `cluster.init()` and `always(cluster.next())`.
2. Weak fairness of the API server, of both our controllers' steps and
   `schedule_controller_reconcile`, of `disable_crash` for both, of
   `disable_req_drop`, `disable_pod_monkey`, and the built-in controllers.
   Interpreted: our process eventually stops crashing, lost responses
   eventually stop, and both clusters' API servers eventually stop failing
   requests.
3. Both model kinds installed (the CRD applied in both clusters); both
   controller models registered under distinct ids.
4. The rely conditions of 3.3 for every other controller id (and, for the
   sync reconciler, that the controller at the janitor id is the janitor).
5. D3 for the inner implementation (an axiom in this version). Nothing else
   about the inner implementation: it may be down, slow, or wrong, and R1
   and R3 still hold; R2 holds for whatever status it settles on.
6. The generation semantics of 4.1 hold for both real API servers (they do
   for CRDs with the status subresource).
7. Exec hygiene: our controllers never read rv or uid values (3.2,
   obligation 1).
8. Out of model, operational: the inner namespace exists; CRD schema parity;
   the CRD is installed in the outer cluster whenever its API server answers;
   one active replica; no mutating admission on `Inner` spec.

## 6. What the model does and does not cover

Stated so that a reader does not over-read the theorem.

| Real-world situation | In the model? | How |
|---|---|---|
| Outer controller live, inner cluster unreachable for a finite time | yes | `drop_req` on inner-bound requests |
| Same for the outer cluster | yes | `drop_req` on outer-bound requests |
| Permanent partition | excluded by fairness | correct: no liveness holds under it |
| Write executed, client sees timeout | by projection | executed + `restart_controller`; all writes replay-safe; delayed `Create` collected by janitor |
| Late delivery of a stale request after retry | yes | network reorders; preconditions reject stale writes |
| Spurious/real `NotFound` (CRD missing, wrong kubeconfig) | yes, as a fault | harmless: the janitor deletes only on a *successful* `List` lacking the parent uid, and fault injection can only fail a request, never fabricate a successful list; a type-level 404 is a request error and the janitor requeues |
| Inner controller writing status, timestamps or heartbeat annotations on every reconcile | yes | spec patch tests generation, not rv, so such writes cannot starve it |
| Two outer clusters feeding one inner cluster | no (assumed away) | a parent-cluster identity is a deferred feature; until then exactly one outer cluster per inner cluster |
| Inner implementation changing status on its own | yes | other controller under rely |
| Inner implementation adding labels/annotations | yes | identity-preserving `Update` allowed by rely |
| Mistaken (fat-finger) edit of a mirror's spec in the inner cluster; the inner controller reconciles it before we overwrite it | yes | the rely permits the edit; the reconciler overwrites it and never copies a status whose `observedGeneration` is not the mirror's current generation; R1/R2 promise convergence once such edits stop (`mirror_spec_undisturbed`) |
| Inner implementation adding finalizers to `Inner` | yes | rely allows it; R3 (and R1 via D2) depend on D3, "the inner side releases finalizers on terminating objects" |
| User deletes `Inner` out of band; inner cluster rebuilt | no | controller recovers in exec (NotFound → Create; uid mismatch → janitor); modeling it needs an "inner monkey" step in `src/kubernetes_cluster/`, priced like `pod_monkey` (spec edits are covered by the row above) |
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
   - have the echo controller add its own label, annotation and a finalizer
     to every `Widget` it reconciles, releasing the finalizer on deletion →
     ours survive; deleting the outer copy leaves the mirror terminating
     until the echo controller releases it, then it disappears; deleting and
     recreating the outer copy waits for the old mirror to finish
     terminating before the new one is created;
   - `kubectl get widget -A` in both contexts as the demo view: same names,
     same specs, statuses flowing inward-to-outward;
   - crash mode of the shim during each write step.
5. CI job alongside the existing e2e jobs; two single-node clusters fit on a
   standard runner.

## 8. What exists, and what it cost

Everything in the plan's phases 0 through 4 is done and verified on this
branch; phase 5 is done for the pair and not for the union with the existing
controllers. The full `cargo verus verify --lib` passes (1141 verified, 0
errors, about an hour on the development machine; the same command was 944
verified before the Widget example was added).

| Piece | Where | Size / status |
|---|---|---|
| `metadata.generation`, Patch primitive, cluster-tagged wrappers, shim routing | `kubernetes_api_objects/`, `kubernetes_cluster/`, `shim_layer/` | verified; all existing controllers re-verified |
| Model reconcilers (sync, janitor), install | `widget_sync_controller/model/` | ~400 lines |
| Exec reconcilers, binaries, echo controller | `widget_sync_controller/exec/`, `src/bin/` | ~500 lines; exec-model conformance verified |
| Trusted spec: types, rely/guarantee, R1/R2/R3, D3 | `widget_sync_controller/trusted/` | ~1000 lines (the TCB of the example) |
| Safety: guarantees, bound parent uids, janitor decision soundness, sync request invariants | `proof/guarantee.rs`, `helper_invariants.rs`, `janitor_invariants.rs`, `sync_invariants.rs` | ~2300 lines |
| Termination of both reconcilers | `proof/liveness/terminate.rs` | ~350 lines |
| R3 (janitor liveness) | `proof/liveness/janitor_proof.rs` | ~2000 lines, 29 lemmas |
| R1 (forward sync) | `proof/liveness/sync_proof.rs` | ~2900 lines, 33 lemmas |
| R2 (status mirroring) | `proof/liveness/sync_status_proof.rs` | ~1550 lines, 24 lemmas |
| Welder specs, pair composition, concrete two-controller cluster | `composition/widget_janitor_reconciler.rs`, `widget_sync_reconciler.rs` | ~460 lines |
| Testbed, manifests, e2e | `tools/two-cluster-test.sh`, `deploy/widget_sync/`, `e2e/src/widget_sync_e2e.rs` | runs on two kind clusters |

For calibration, the existing `proof/` directories are 8.7k lines
(VReplicaSet), 11.7k (VDeployment), 13.8k (VStatefulSet) and 9k (RabbitMQ);
the Widget pair is about 9k for two reconcilers and three properties. The
three ingredients without precedent each turned out to have a workable
shape:

- *A liveness dependency threaded through a conflict loop* (R1 needing the
  janitor to remove a stale mirror first). Handled by proving, as a message
  invariant, that a janitor `Delete` in flight targets an object whose
  parent is absent forever, so the janitor's deletes can never race the
  sync reconciler's creates for a live parent; R3 is then consumed as a
  black box per object.
- *A liveness property with an absence premise* (R3). The same WF1 mechanics
  as every other Anvil proof, with `schedule_controller_reconcile` enabled
  by the mirror's existence rather than the parent's; the novelty was the
  phase structure (drops and crashes off, then per-object facts about the
  scheduled snapshot and the janitor's `List` responses being fresh).
- *A status target pinned to the generation* (R2). Once the premise fixes
  the generation and the status patch tests it, the proof is a chain of
  "every snapshot, response and in-flight status write for this key is
  current" invariants followed by one reconcile.

Not done, and known:

- **Composition with the four existing controllers** (`compose_all.rs`).
  Needs eight cross implications (each Widget guarantee against each of
  `vrs_rely`, `vd_rely`, `vsts_rely`, `rmq_rely`, and each of the four
  guarantees against the two Widget relies). All should follow from kind
  disjointness, but the VRS/VSTS precedent shows some need hand-written
  string lemmas. Estimated one to two days.
- **D3 discharged by a verified inner implementation** rather than assumed.
  Needs an inner controller that writes status without an owner reference,
  which the Patch primitive now permits.
- **The full-repository `cargo verus verify --lib` time** has grown from
  about 25 minutes to about an hour with the new modules; staged per-module
  verification is what the branch was developed with.

## 9. Decisions and follow-ups

Decided:

- **Inner-side finalizers on mirrors: allowed.** Rely permits them; D3
  covers their release; the sync controller treats terminating mirrors as
  absent-in-progress; the janitor re-issues `Delete` until the object is gone.
- **Writes are JSON patches testing uid and generation** (revision 4), for
  both the inner spec and the outer status. The Patch primitive is in the
  model and shim.
- **`observedGeneration` stamped on every outer status write; readiness in a
  `Synced` condition** (revision 4). Conditions are therefore part of v1
  status.
- **Janitor establishes absence by a successful `List` matched on parent
  uid** (revision 4); a `NotFound` is never absence.
- **Exactly one outer cluster per inner cluster** is an explicit assumption
  (revision 4).
- **Naming.** Kind `Widget` in group `anvil.dev`; inner model kind
  `widget@inner`; `ClusterId { Primary, Remote }`.
- **Fat-finger edits of a mirror's spec are tolerated, not forbidden**
  (revision 5). The rely leaves the spec free; the reconciler overwrites and
  never copies a status for a generation it did not ask for; R1/R2 hold
  once the edits stop.
- **The R1/R2 premise fixes the outer generation** along with the spec
  (revision 5); that is the same premise stated precisely, and what pins
  `observedGeneration` in R2's target.
- **Mirrored fields are copied only from a caught-up inner status**
  (revision 5); otherwise the last reported fields are kept with
  `Synced=False/InnerConverging`.
- **D1 is not an assumption** (revision 5); R2's premise fixes the inner
  status. D3 is the only inner-side liveness assumption.
- **The PATCH response's status is not used** (revision 5, 4.1c).

Deferred features:

- **Parent-cluster identity** on mirrors, to allow several outer clusters to
  target one inner cluster and to decide between re-parenting in place and
  delete-and-recreate on an outer uid change.
- **A `keep` annotation** that freezes collection of a mirror, in the spirit
  of orphan semantics; its motivation (operator-controlled migrations) is
  noted but not yet needed.
- **A validating admission policy in the inner cluster** restricting the
  sync ServiceAccount to objects that carry the managed-by label, turning
  refuse-to-adopt from a code guard into an enforced invariant; and Warning
  events from the shim on the refusal branch.
- **Spec projection `π_spec`** for inner implementations that write their
  own spec fields; for `Widget` the whole spec is outer-owned.
- **Owner-less transactional update** (4.3) is no longer needed for the
  forward-sync proof (the patch primitive replaced it); it remains the way
  to compose against a verified inner implementation that writes status
  through `GetThenUpdateStatus`.
- **Inner-monkey model step**, if out-of-band mutation of mirrors is to be
  brought inside the proved envelope.
