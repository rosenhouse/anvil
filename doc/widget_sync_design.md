# Widget sync controller: design and verification

A controller in an *outer* cluster mirrors every `Widget` created there into an
*inner* cluster, where a real `Widget` implementation acts on it, and copies the
inner copy's status back. Both clusters install the same CRD. The controller is
verified in Anvil. This document states the design, what is proved, and what is
assumed. `deploy/widget_sync/README.md` says how to run the demo.

## 0. Summary

- Two reconcilers run in one process in the outer cluster: the **sync**
  reconciler (primary: outer `Widget`s) creates and updates mirrors and writes
  outer status; the **janitor** (primary: inner `Widget`s) deletes mirrors
  whose parent is gone.
- Writes are JSON patches whose `test` operations pin `metadata.uid` and
  `metadata.generation`. No owner references cross clusters; neither reconciler
  uses finalizers.
- Proved (section 3): R1, the mirror eventually and stably carries the outer
  spec; R2, the outer status eventually and stably carries the inner status for
  that spec, stamped with the outer generation; R3, a mirror whose parent is
  gone is eventually removed; R3s, no mirror pointing at a departed parent
  persists. All four are ESR-style properties in the sense of the Anvil paper.
- Assumed: D3, the inner side eventually releases terminating objects; exactly
  one outer cluster per inner cluster; the operational items in section 3.5.
- Framework additions (section 5): `metadata.generation` in the model, a JSON
  patch primitive, and a cluster tag on the exec wrappers with routing in the
  shim.
- What is mechanized about "two clusters" (section 2): a two-store model,
  `TwoCluster`, with a proof that every execution of it is, under an injective
  relabeling of uids and resource versions, an execution of the one-store
  model. R1, R2, R3 and R3s are then stated on two-store executions
  (`widget_two_cluster_theorem`).

## 1. Design

### 1.1 Resources and identity

One CRD, `Widget` in group `anvil.dev`, namespaced, with the status
subresource, installed in both clusters. `Inner{ns, name}` mirrors
`Outer{ns, name}`; names match by construction.

A mirror carries the label `anvil.dev/managed-by: widget-sync` and the
annotation `anvil.dev/parent-uid: <uid of the outer copy>`. The annotation is
how the janitor tells a live mirror from a stale one and how the sync
reconciler refuses to write an inner object it does not own.

- No owner references across clusters: the inner garbage collector would
  delete an object whose owner does not exist there.
- No finalizers by either reconciler. Every action is re-convergent and outer
  deletion never blocks on a partition. The inner implementation may put its
  own finalizers on mirrors; the janitor's Delete then stamps a deletion
  timestamp and the object lingers until the inner side releases it (D3).
- Refuse to adopt. The sync reconciler writes an existing inner object only if
  it carries the label and its `parent-uid` equals the current outer uid.
  Anything else is reported as `ForeignObject` and never touched. Adoption
  would let anyone who can create `Outer{ns,name}` overwrite `Inner{ns,name}`.
- Chains compose, cycles are inert: a second sync controller in the inner
  cluster sees our mirror as its outer copy; a cycle back finds an unlabeled
  object and refuses.

### 1.2 The sync reconciler

Triggered by an outer `Widget` with generation `g`, spec `σ`, uid `u`, and by
same-named inner `Widget`s (a latency optimization; liveness rests on requeue).

```
Init
 └─ Get Inner{ns,name}                                   (inner cluster, quorum read)
      ├─ NotFound → Create Inner{ns,name; label; parent-uid=u; spec=σ} → Done
      ├─ Found, deletionTimestamp set → status Synced=False/InnerTerminating → Done
      ├─ Found, not ours (label missing or parent-uid ≠ u) → status Synced=False/ForeignObject → Done
      ├─ Found, ours, spec ≠ σ → Patch Inner {test uid, test generation; add /spec := σ} → Done
      ├─ Found, ours, spec == σ, Inner.status.observedGeneration == Inner.metadata.generation
      │     → status { observedGeneration: g, mirrored fields: π(Inner.status),
      │                Synced: True, condition.observedGeneration: g }
      └─ Found, ours, spec == σ, inner not caught up
            → status { observedGeneration: g, mirrored fields: as previously reported,
                       Synced: False/InnerConverging, condition.observedGeneration: g }
      "status X" means: Outer.status == X → Done,
                        else PatchStatus Outer {test uid=u, test generation=g; add /status := X} → Done
Error (any unexpected response) → requeue
```

`π` projects a status onto the mirrored fields (everything except
`observedGeneration` and `conditions`). The reconciler never writes outer spec
or metadata, never writes inner status or metadata, never deletes.

**Patches test uid and generation.** A patch carries no `resourceVersion`, so
writes by other actors to fields the patch does not test (inner status, labels,
annotations, finalizers) cannot make it fail. What it tests is what the
decision depended on: the same incarnation of the object and the same spec as
read. A stale or replayed patch fails its test and is rejected. Generation, not
resource version, is the token because generation changes only with the spec.

**Status is copied only from a caught-up inner status.** If the inner status
observes an older generation of the mirror, including one produced by an
out-of-band edit the reconciler has since overwritten, it is a status for a
spec the outer copy never asked for. It is never reported; the outer copy keeps
the last fields it did report and says `InnerConverging`. R2 depends on this
rule.

### 1.3 The janitor

Triggered by an inner `Widget`.

```
Init
 ├─ label or parent-uid annotation missing → Done
 └─ List Outer in namespace ns                            (outer cluster, quorum read)
      ├─ error (including a type-level 404) → Error (requeue; never delete)
      ├─ Ok, some listed Outer has uid == parent-uid → Done
      └─ Ok, none has → Delete Inner{ns,name; precondition uid = Inner.uid} → Done
```

Absence is established only by a successful read that lacks the parent,
matched on uid. A `Get` returning `NotFound` is never treated as absence: the
model's fault injection can fake it, and a CRD reinstall window or a kubeconfig
pointing at the wrong cluster answers `NotFound` for every key. A same-named
parent with another uid counts as absent, so a recreated outer copy gets a
fresh mirror. The uid precondition is what garbage collectors use.

### 1.4 Generation and status, as an observer reads them

Kubernetes bumps `metadata.generation` of a custom resource with a status
subresource exactly when its spec changes. On the **inner** copy nothing is
unusual: the sync reconciler writes the spec, the inner implementation writes
the status with its own `observedGeneration`.

On the **outer** copy every status write by the sync reconciler sets
`status.observedGeneration := g`, the generation of the snapshot it reconciled,
and the patch's generation test makes it land only while the copy is still at
`g`. The condition `Synced` is `True` with `condition.observedGeneration == g`
exactly when the reconcile verified `Inner.spec == σ` and the inner status
observes the mirror's current generation.

> `status.observedGeneration == metadata.generation` means the sync controller
> has acted on the current spec. `Synced == True` at that generation means the
> spec is in the inner cluster and the mirrored fields are the inner
> implementation's status for it.

Otherwise `Synced` is `False` with reason `InnerConverging`,
`InnerTerminating` or `ForeignObject`. An inner implementation that never sets
`observedGeneration` never reaches `Synced=True`.

## 2. The model

### 2.1 One store, two kinds, two controllers

Anvil's model has one API server whose store is keyed by `(kind, namespace,
name)`. The cluster is folded into the *model* kind at the exec boundary: the
outer copy has kind `widget`, the mirror `widget@inner`. `OuterWidgetView` and
`InnerWidgetView` are two view types with the same spec and status, differing
only in `kind()`; on the exec side `OuterWidget` and `InnerWidget` wrap the
same kube type and are bound to `ClusterId::Primary` and `ClusterId::Remote`.
Both kinds are installed in one `Cluster`; the two reconcilers are two
controller ids. `schedule_controller_reconcile` fires for a reconciler's own
kind, so outer copies schedule the sync reconciler and inner copies the
janitor. The inner implementation is an ordinary other controller under a rely
condition.

### 2.2 Two stores, and the refinement into one

`kubernetes_cluster/spec/two_cluster.rs` defines `TwoCluster`: a cluster whose
kinds are split between a primary and a remote API server, each with its own
store, uid counter and resource-version counter, while controllers, network
and failures are shared. Every step is a step of the one-store model taken on
one of the two projections. A request is handled by the API server of its
kind, the garbage collector of a side reads only that side's store, and a
reconcile is scheduled from the store of the controller's kind. For the Widget
pair the remote kinds are `{widget@inner}`.

`kubernetes_cluster/proof/two_cluster/` proves that every execution of
`TwoCluster` maps to an execution of `Cluster`. The map unions the two stores
and relabels uids and resource versions injectively, per side, by an
assignment read off the execution: the k-th value a store's counter allocates
goes to the number of values both stores had allocated by then, so the
one-store counters count every allocation once. Annotation values follow the
uids through a per-controller hook; for the Widget pair the hook covers the
`parent-uid` annotation. The proof (`relabel`, `api_server`, `steps`,
`execution`, `fairness`) covers the initial state, every step, and weak
fairness of every action the liveness proofs assume. Fairness needs the
two-store message behind a one-store message to stay the same while a wait
lasts, which follows from the one-store invariants that no message is in
flight twice and that in-flight ids are below the allocator.

`widget_sync_controller/proof/two_cluster.rs` instantiates the refinement.
Both reconcilers commute with the relabeling, and `widget_two_cluster_theorem`
states R1, R2, R3 and R3s of every execution of the two-store model that runs
exactly the pair under its fairness assumptions and D3, each property read on
the store its objects live in.

The refinement holds under hypotheses, all met by the Widget pair:

1. Controllers write only objects of known kinds, name what they create, put
   owner references only on kinds of the object's own side (`request_ok`), and
   have no external system.
2. Installed types validate objects without reading metadata, and their
   default status unmarshals (true of every type installed through
   `Cluster::installed_type`).
3. Every reconciler commutes with the relabeling: run on the relabeled object
   and response it reaches the same local state and sends the relabeled
   request. A reconciler that copies a uid or resource version into data other
   than through the hook, or whose local state holds one, does not. The
   `UidToken` boundary (section 5.3) and `tools/check-widget-exec-hygiene.sh`
   hold the exec code to the same discipline as the model.
4. The pod monkey of the two-store model writes named pods without
   server-assigned fields or owner references.

What remains trusted is the usual Anvil boundary, per store: that each real API
server behaves as the model's API server, with its uids and resource versions
read as that store's counter values. A controller that reads counter values
into data (VDeployment uses a resource version as a hash; RabbitMQ stores one
in an annotation) is outside hypothesis 3 and must live in one cluster. The
axiom `generated_name_spec` and the `external_body` ensures equating a real
resource-version string with the model counter are not used by these
reconcilers.

### 2.3 What the model covers

| Situation | Modeled | How |
|---|---|---|
| Two API servers with independent uid and resource-version counters | yes | the two-store model and its refinement (section 2.2) |
| Either cluster unreachable for a finite time | yes | `drop_req` |
| Permanent partition | excluded | fairness (`disable_req_drop`) |
| Write executed, client sees a timeout | by projection | executed plus `restart_controller`; every write is replay-safe (patches test uid and generation, deletes carry uids); a delayed `Create` is collected by the janitor |
| Late delivery of a stale request | yes | the network reorders; the tests reject it |
| Spurious `NotFound` (CRD missing, wrong kubeconfig) | yes, as a fault | the janitor deletes only after a successful `List` lacking the parent |
| Inner implementation writing status, timestamps or annotations on every reconcile | yes | the spec patch tests generation, not resource version |
| Inner implementation adding finalizers | yes | rely allows it; R3 needs D3 |
| Out-of-band edit of a mirror's spec (a `kubectl edit` in the inner cluster) | yes, as another controller's write | the rely permits it; the reconciler overwrites it and never copies a status computed for it; R1 and R2 hold once such edits stop |
| Out-of-band delete of a mirror; inner cluster rebuilt | no | the exec code recovers (NotFound → Create); modeling it needs a monkey step (issue #13) |
| Foreign `Widget{ns,name}` pre-existing in the inner cluster | vacuous | only the sync reconciler creates inner-kind objects in the model; the exec code refuses to adopt |
| Two outer clusters feeding one inner cluster | no | assumed away; parent-cluster identity is future work (issue #10) |
| Namespaces, admission, schema drift | no | operational assumptions, section 3.5 |
| Two replicas of the controller | no | one replica; a second would violate the rely |

## 3. Specification

The trusted specification is `src/controllers/widget_sync_controller/trusted/`:
`spec_types.rs` (views and the mirror relation), `rely_guarantee.rs`,
`liveness_theorem.rs` (R1, R2, R3, R3s, D3). `π` is
`WidgetStatusView::mirrored()`.

### 3.1 Guarantees

**Sync** (`widget_sync_guarantee`). A request sent while reconciling the outer
copy at `outer_key` is one of: `Get` of the mirror key; `Create`, in that
namespace, of exactly `make_inner(outer)` for an outer copy at `outer_key`
whose uid is issued and bound to that key; `Patch` of the mirror's spec;
`PatchStatus` of the outer copy testing uid and generation, whose status and
`Synced` condition carry the tested generation as `observedGeneration`
(G-gen). Nothing else.

**Janitor** (`widget_janitor_guarantee`). A `List` of outer copies in the
mirror's namespace, or a `Delete` of the mirror with a uid precondition.

### 3.2 Relies

**Sync, on an anonymous other controller** (`widget_sync_rely`): no `Create`
of the inner kind; an `Update` of a mirror that is going to land keeps its
owner references and its identity (label and `parent-uid` annotation) and is
otherwise free, spec included; any `Patch`; no status write to the outer kind;
no `Delete` of the inner kind.

**Janitor, on an anonymous other controller** (`widget_janitor_rely`): a
`Create` of the inner kind at `ns/n` is `make_inner(outer)` for an outer copy
at `Outer{ns,n}` with a bound uid; updates keep identity.

**Sync, on the janitor.** The janitor's guarantee, not the anonymous rely. The
sync spec's `safety_partial_rely` is a function of the other controller's id
and names the janitor's id. What the sync proof needs beyond the guarantee, that
a janitor `Delete` in flight targets an object whose parent is absent for good,
holds only under the janitor's rely and is therefore part of the janitor's ESR
(`widget_janitor_esr`), which the sync spec takes as its liveness dependency.

### 3.3 Properties

```
outer_stable(outer)(s) :=
    desired_state_is(outer)(s)
 && s.resources()[outer.object_ref()].metadata.generation == outer.metadata.generation
 && mirror_spec_undisturbed(outer)(s)
        // every in-flight Update / GetThenUpdate / Patch of the mirror writes outer.spec

spec_synced(outer)(s)            := the mirror exists, is not terminating, is a mirror of outer, has spec outer.spec
inner_settled(outer, mirrored)(s) := spec_synced(outer)(s) && inner_caught_up(inner) && π(inner.status) == mirrored
status_synced(outer, mirrored)(s) := the outer copy's status has π == mirrored,
                                     observedGeneration == its generation,
                                     Synced == True with observedGeneration == its generation

mirror_object_is(k, a, u)(s) := an object with uid u at k is a mirror pointing at a
object_is_gone(k, u)(s)      := no object with uid u is at k
parent_absent(k, a)(s)       := no object with uid a is at outer_key_of(k)
mirror_collected(k, a)(s)    := no mirror pointing at a is at k
```

| | Statement | Proved in |
|---|---|---|
| R1 | `∀outer. □outer_stable(outer) ~> □spec_synced(outer)` | `proof/liveness/sync_proof.rs` |
| R2 | `∀outer, mirrored. □(outer_stable(outer) ∧ inner_settled(outer, mirrored)) ~> □status_synced(outer, mirrored)` | `proof/liveness/sync_status_proof.rs` |
| R3 | `∀k, a, u. □parent_absent(k, a) ∧ mirror_object_is(k, a, u) ~> object_is_gone(k, u)` | `proof/liveness/janitor_proof.rs` |
| R3s | `∀k, a. □parent_absent(k, a) ~> □mirror_collected(k, a)` | `proof/liveness/cleanup_proof.rs` |
| D3 | `∀k, u. inner_terminating_object(k, u) ~> object_is_gone(k, u)` | assumed |

The premise of R1 and R2 says: the user has stopped editing the outer copy
(spec and generation constant, not being deleted, same uid), and whoever was
editing the mirror's spec out of band has stopped. Convergence is promised for
the time after the disturbances stop; during them the guarantees still hold.
R2's premise fixes the inner status instead of assuming the inner
implementation is live, so R2 holds for any inner implementation. R3 is per
object; R3s is the stable form and is the sync reconciler's promise given R3.

### 3.4 Composition

Both reconcilers are Welder controller specs
(`src/controllers/composition/widget_janitor_reconciler.rs`,
`widget_sync_reconciler.rs`). The janitor's ESR is R3 together with
`□janitor_deletes_are_sound`; its environment rely is D3. The sync
reconciler's ESR is R1, R2 and R3s; its liveness dependency is the janitor's
ESR; its partial rely names the janitor; its environment rely is D3.
`compose_dep` composes the pair, and `widget_core_holds` proves `core` for a
concrete cluster with the two controllers.

Welder proves nothing new here. It gives the closed statement about the
cluster running both controllers, with the janitor's ESR consumed rather than
assumed, and a mechanical check that each guarantee implies the other's rely.

The concrete two-controller instance exercises neither R2's premise nor D3:
nothing in it writes inner status or finalizers. Verifying the echo controller
as a third member would discharge both (issue #3).

### 3.5 Assumptions

1. `cluster.init()` and `□cluster.next()`.
2. Weak fairness of the API server, both reconcilers, `schedule_controller_reconcile`, `disable_crash`, `disable_req_drop`, `disable_pod_monkey` and the built-in controllers. Read: the process stops crashing, lost responses stop, both API servers stop failing requests.
3. Both kinds installed; both controller models registered under distinct ids.
4. The relies of 3.2 for every other controller id.
5. D3.
6. Generation semantics as in section 5.1 on both real API servers (true for CRDs with the status subresource).
7. The hypotheses of the refinement in 2.2, and one outer cluster per inner cluster.
8. Operational: the inner namespace exists; CRD schema parity; the CRD is installed in the outer cluster whenever its API server answers; one replica; no mutating admission on the inner spec.

## 4. Deployment shape

- One Deployment in the outer cluster, `replicas: 1`, `strategy: Recreate`.
- Outer RBAC: `widgets` get, list, watch; `widgets/status` patch. Inner: a
  ClusterRole on `widgets` with get, list, watch, create, patch, delete, bound
  to a service account whose kubeconfig is mounted from a Secret.
- Watches: outer `Widget`s (sync primary), inner `Widget`s (janitor primary and
  sync secondary, mapped by name).
- Requeue: fixed intervals after `Done` and after an error; the remote client
  has a short request timeout so a partition surfaces as a failed reconcile.

Issues #9 and #10 on the fork list the operability and hardening work a
production deployment needs: error reasons in the `Synced` condition, Events,
per-object backoff, KEP-1623 condition fields, a name selector on the janitor's
List, token rotation, leader election, and a cluster identity on mirrors.

## 5. Framework additions

### 5.1 `metadata.generation`

`ObjectMetaView` has `generation: Option<int>`. For custom resources the API
server model sets `Some(1)` on create, increments it on an update that changes
the spec, leaves it on status writes, and increments it when a deletion
timestamp is stamped. Built-in kinds keep `None`. `etcd_object_is_well_formed`
records that custom resources carry a generation and built-in kinds do not. The
executable model, the exec getter and the conformance tests follow the same
rules.

### 5.2 JSON patch

`PatchRequest` and `PatchStatusRequest` carry `test` operations on uid and
generation and a new spec or status. The API server model answers a failed
test with `Invalid` (a failed JSON patch `test` is a 422) and otherwise applies
the existing update pipeline to the stored object with the spec or status
replaced, so validity, the no-op rule, the resource-version bump and the
generation rule are unchanged. The shim uses `Api::patch` and `patch_status`
with `Patch::Json`. Merge patch, server-side apply and `managedFields` are not
modeled. The executable model does not implement Patch yet (issue #12).

### 5.3 Cluster tag and routing

`ApiResource` and `DynamicObject` carry a `ClusterId`; a wrapper type is bound
to one cluster (`ClusterBound`) and its view kind is the tagged kind. The shim
holds one client per cluster, routes each request by the tag of its
`ApiResource`, tags the objects it returns, and derives a controller's primary
watch cluster from its wrapper type. Two controllers can run in one process.

### 5.4 Not done

An owner-less transactional update (`GetThenUpdate` without the hard-coded
owner-reference check) would let a verified inner implementation write its
status without an owner reference, which composing against one requires.

## 6. Alternatives rejected

| Alternative | Why not |
|---|---|
| Finalizer on the outer copy for cleanup | "remove finalizer on NotFound" is irreversible under fault injection and under a CRD uninstall; deletion blocks on partitions |
| Native multi-store `ClusterState` | changes every `s.resources()` use and every `APIServerStep` case split in the repository; the two-store model and refinement (section 2.2) give the same theorem without that |
| The external-system hook for the inner cluster | a deterministic request-driven stub; cannot model an inner controller acting on its own |
| Uid-suffixed mirror names | trivially provable cleanup, but names must match |
| Reading status from the PATCH response | already modeled (`PatchResponse` carries the object); the copy rule refuses that status anyway, since it is for the previous generation; adds a state for no change in R1 to R3 |
| A token minted on the outer copy instead of its uid | requires writing outer metadata and does not survive recreation |

## 7. Inventory

| Piece | Where |
|---|---|
| Trusted spec: types, mirror relation, rely and guarantee, R1 to R3s, D3 | `widget_sync_controller/trusted/` |
| Model reconcilers | `widget_sync_controller/model/` |
| Exec reconcilers (proved to conform to the model) | `widget_sync_controller/exec/` |
| Guarantees, store and message invariants | `widget_sync_controller/proof/{guarantee,helper_invariants,janitor_invariants,sync_invariants}.rs` |
| Termination, R3, R1, R2, R3s | `widget_sync_controller/proof/liveness/` |
| Welder specs and composition | `composition/widget_{janitor,sync}_reconciler.rs` |
| Two-store model | `kubernetes_cluster/spec/two_cluster.rs` |
| Refinement into the one-store model | `kubernetes_cluster/proof/two_cluster/` |
| R1 to R3s on two clusters | `widget_sync_controller/proof/two_cluster.rs` |
| Binaries, manifests, testbed, e2e | `src/bin/`, `deploy/widget_sync/`, `tools/two-cluster-test.sh`, `e2e/src/widget_sync_e2e.rs` |

Full-repository verification (`cargo verus verify --lib`) passes.

## 8. Future work

Tracked as issues on the fork: verified echo controller discharging D3 (#3); operability (#9) and hardening (#10);
proof layout and solver budgets (#11); composition with the other four
controllers and Patch in the executable model (#12); modeling out-of-band
mirror edits and deletes (#13); parent-cluster identity, a `keep` annotation,
an admission policy in the inner cluster, and a spec projection for
inner-owned fields (#10).
