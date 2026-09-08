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
  relabeling of uids and resource versions (and of the `parent-uid`
  annotation through it), an execution of the one-store model. R1, R2, R3,
  R3s and the janitor's delete soundness are then stated on two-store
  executions (`widget_two_cluster_theorem`; `widget_instance_two_cluster_theorem`
  for the concrete cluster of the pair).

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
states R1, R2, R3, R3s and the janitor's delete soundness of every execution
of the two-store model that runs the pair under its fairness assumptions and
D3, each property read on the store its objects live in. The cluster may run
other controllers beside the pair (`widget_cluster_with_others`): each must
meet hypotheses 1 and 3 below for its own model (`other_model_ok`,
`other_model_commutes`), and the pair's relies of section 3.2 must hold of it
as invariants of the one-store model from init and next
(`widget_relies_hold_of`), which is what a Welder composition of that
controller with the pair establishes from its guarantee. No fairness of the
other controllers is assumed. `widget_instance_two_cluster_theorem` discharges
the hypotheses for the concrete cluster of the pair, the case with no other
controller (`widget_pair_cluster`), and `widget_disturbed_two_cluster_theorem`
for the cluster of the pair with the disturber (section 2.4).

The two-store statement thus quantifies over other controllers as the
one-store theorems do, with hypotheses 1 and 3 added per controller:
composing the pair with a verified inner implementation on two stores needs
that implementation's own commutation lemma and its guarantee proved as an
invariant. What remains narrower is the kind partition. A kind lives on
exactly one side; with `{widget@inner}` remote, every built-in kind is
primary, so an inner implementation that creates Pods or ConfigMaps in the
inner cluster is not expressible in this two-store cluster.

The refinement holds under hypotheses, all met by the Widget pair:

1. Controllers write only objects of known kinds, name what they create, put
   owner references only on kinds of the object's own side (`request_ok`), and
   have no external system.
2. Installed types validate objects and transitions without reading
   metadata, and their default status unmarshals. The second follows from
   `marshal_status_preserves_integrity` for every type installed through
   `Cluster::installed_type`; the first is a per-type fact (`CustomResourceView`
   promises it for state validation only), checked for both Widget types in
   `lemma_widget_instance_is_pair_cluster`.
3. Every reconciler commutes with the relabeling: run on the relabeled object
   and response it reaches the same local state and sends the relabeled
   request. A reconciler that copies a uid or resource version into data other
   than through the hook, or whose local state holds one, does not. The
   `UidToken` boundary (section 5.3) and `tools/check-widget-exec-hygiene.sh`
   hold the exec code to the same discipline as the model.
4. The pod monkey of the two-store model writes named pods without
   server-assigned fields, owner references or annotations. This drops the
   monkey behaviours that exercise stale-write conflicts and garbage
   collection of owned pods; irrelevant to the Widget pair, but a
   pod-managing controller verified on `TwoCluster` would lose that fault
   coverage. The restriction exists because which monkey action runs is a
   `choose` over the input, which Verus does not equate across an input and
   its relabeling.

What remains trusted is the usual Anvil boundary, per store: that each real API
server behaves as the model's API server, with its uids and resource versions
read as that store's counter values; that the shim routes each model kind to
the cluster the model assigns it (section 5.3), which the model cannot check;
and the injectivity of `int_to_string_view` (an `external_body` fact over all
integers), which the hook's injectivity now rests on. A controller that reads counter values
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
| Inner implementation writing status, timestamps or annotations on every reconcile | yes, as another controller under the rely | the spec patch tests generation, not resource version; on two stores the implementation must also meet hypotheses 1 and 3 of 2.2 |
| Inner implementation adding finalizers | yes, as another controller under the rely | rely allows it; R3 needs D3; on two stores also hypotheses 1 and 3 of 2.2 |
| Out-of-band edit of a mirror's spec, or of its other labels and annotations (a `kubectl edit` in the inner cluster) | yes, as another controller's write | the rely permits it; the reconciler overwrites a spec edit and never copies a status computed for it; R1 and R2 hold once such edits stop (`mirror_spec_undisturbed`). The disturber (section 2.4) is a controller model doing this, on one store and on two |
| Out-of-band delete of a mirror; inner cluster rebuilt | yes, as another controller's delete | the rely permits any Delete; the reconciler recovers (NotFound → Create); R1 and R2 hold once such deletes stop landing on the live mirror (`mirror_undeleted`); R3 and R3s hold throughout. The disturber (section 2.4) is a controller model doing exactly this, on one store and on two |
| Out-of-band edit that removes the mirror's label or `parent-uid` annotation | excluded by the rely | the object becomes foreign to both reconcilers, which refuse to adopt; no recovery is possible without adoption (section 1.1) |
| A kind present in both clusters (Pods, ConfigMaps) | no | the two-store model assigns each kind to one side |
| Foreign `Widget{ns,name}` pre-existing in the inner cluster | vacuous | only the sync reconciler creates inner-kind objects in the model; the exec code refuses to adopt |
| Two outer clusters feeding one inner cluster; many outer namespaces each with its own inner cluster | no | assumed away for the single pair; the fan-out and parent-cluster identity are follow-up work (issue #15) |
| Namespaces, admission, schema drift | no | operational assumptions, section 3.5 |
| Two replicas of the controller | no | one replica; a second would violate the rely |

### 2.4 The disturber

An out-of-band actor in the inner cluster is not a fault of the cluster model
but another controller, so it is modeled as one, in the way Anvil treats every
other controller: through a rely. `model/disturber_reconciler.rs` is a
controller model triggered by inner `Widget`s that, on each reconcile, patches
the mirror's spec testing nothing and then deletes the mirror with no
precondition, ignoring every response. No fairness is assumed for it, so it may
act at any moment and stop at any moment, which is what a `kubectl delete` or a
rebuilt inner cluster looks like from the pair's side. Its guarantee
(`proof/disturber.rs`: every request it has in flight is such a Patch or Delete
of its own key) implies both reconcilers' relies, and
`composition/widget_disturber_reconciler.rs` composes it with the pair through
Welder: `widget_disturbed_core_holds` is the closed statement for a cluster
running the janitor, the sync reconciler and the disturber.
`widget_disturbed_two_cluster_theorem` (`proof/two_cluster.rs`) is the same
statement on two stores, with the disturber acting in the remote store: its
model reads only the namespace, name and spec of its object and tests nothing,
so it commutes with the relabeling by computation, and its guarantee gives the
pair's relies in the form the two-store theorem asks for (section 2.2).

The disturber adds no assumption. What it buys is a witness that the relaxed
sync rely (any Delete, any Patch) is satisfiable by something that deletes and
edits mirrors, and that the premises of R1 and R2 are the only place where "the
disturbance has stopped" is said. A cluster-model step in the style of the pod
monkey was not needed: it would have touched every `next_step` case split in the
repository and the two-store simulation, for a behaviour the rely already
expresses.

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
any `Delete` and any `GetThenDelete`, mirrors included. A transactional delete
never removes a mirror, which has no owner references; a plain delete may, and
R1 and R2 are stated for the time after such deletes stop landing on the live
mirror.

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
outer_spec_stable(outer)(s) :=
    desired_state_is(outer)(s)
 && mirror_spec_undisturbed(outer)(s)
        // every in-flight Update / GetThenUpdate / Patch of the mirror writes outer.spec
 && mirror_undeleted(outer)(s)
        // while a mirror of outer is at the mirror key, every in-flight Delete of that key
        // names, by uid precondition, an object other than that mirror
outer_stable(outer)(s) :=
    outer_spec_stable(outer)(s)
 && s.resources()[outer.object_ref()].metadata.generation == outer.metadata.generation

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
| R1 | `∀outer. □outer_spec_stable(outer) ~> □spec_synced(outer)` | `proof/liveness/sync_spec_proof.rs` |
| R2 | `∀outer, mirrored. □(outer_stable(outer) ∧ inner_settled(outer, mirrored)) ~> □status_synced(outer, mirrored)` | `proof/liveness/sync_status_proof.rs` |
| R3 | `∀k, a, u. □parent_absent(k, a) ∧ mirror_object_is(k, a, u) ~> object_is_gone(k, u)` | `proof/liveness/janitor_proof.rs` |
| R3s | `∀k, a. □parent_absent(k, a) ~> □mirror_collected(k, a)` | `proof/liveness/cleanup_proof.rs` |
| D3 | `∀k, u. inner_terminating_object(k, u) ~> object_is_gone(k, u)` | assumed |

The premise of R1 and R2 says: the user has stopped editing the outer copy
(spec constant, not being deleted, same uid), and whoever was editing the
mirror's spec or deleting the mirror out of band has stopped. R2 also fixes the
outer copy's generation, which the status it promises is stamped with; R1 says
nothing about status and does not need it.
Convergence is promised for the time after the disturbances stop; during them
the guarantees still hold. The delete clause is stated so that it costs
nothing in the undisturbed case: a Delete the janitor sends satisfies it
whenever the outer copy exists (`janitor_deletes_are_sound`), a stale Delete of
an earlier mirror misses by uid, and a Delete that arrives while no mirror of
`outer` is at the key is free. Only a Delete that would remove the live mirror
is excluded, and one that keeps arriving forever falsifies the premise rather
than the conclusion. R2's premise fixes the inner status instead of assuming
the inner implementation is live, so R2 holds for any inner implementation. R3
is per object; R3s is the stable form and is the sync reconciler's promise
given R3. Neither R3 nor R3s needs a premise about deletes: the janitor's rely
already admits any Delete, and an extra delete of a mirror only helps them.

On two stores (`two_cluster_outer_spec_stable`, `two_cluster_outer_stable`) the
premises read the outer copy and the in-flight writes on the primary side and
the delete clause on the remote side, where the mirror lives.

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

The whole-repository composition (`src/controllers/composition/compose_all.rs`)
adds the pair to the cluster running the VReplicaSet, VDeployment,
VStatefulSet and RabbitMQ controllers: `core_holds` proves `core` for the
six-controller cluster. The pair is composed first (`widget_pair_core_holds`),
so its liveness dependency is discharged internally and the outer step is a
plain `compose`. The cross compatibilities are kind disjointness: the pair
only sends requests to the two Widget kinds (for the sync reconciler this is
read off `mirror_create_req`, whose Create is `make_inner(outer).marshal()`),
and the other four controllers only send requests to Pods, PVCs,
VReplicaSets and the RabbitMQ-managed kinds. The one fact Verus does not find
on its own is that the custom kind names differ (`kind_strings_distinct`).

The concrete instances exercise neither R2's premise nor D3: nothing in them
writes inner status or finalizers. That is by decision: the inner controller is
whatever the workload cluster runs, the sync controller stays agnostic to it,
and D3 is an assumption about it, not a proof obligation. The echo controller
in the testbed is an unverified stand-in. A separate concrete instance adds the
disturber (section 2.4) as a third member with an empty ESR and no rely;
`widget_disturbed_core_holds` composes it with the pair.

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

### 5.4 Footprint

Against upstream, `src/kubernetes_cluster` differs in 19 files, 4964 lines
added and 13 removed. 4189 of the added lines are the two-store model and its
refinement (`spec/two_cluster.rs` and the five files of `proof/two_cluster/`),
423 are `proof/api_server.rs` (the `keeps_identity` family: what each request
leaves alone, and the uid facts: the store only grows by fresh uids), 29 are
`proof/temporal_rules.rs` (two rules of temporal logic that
`verus_temporal_logic` lacks), 112 lines of `spec/api_server/state_machine.rs`
are the generation rules and the JSON-patch handlers of 5.1 and 5.2, and 96 of
`spec/message.rs` are the Patch plumbing. The remaining proof files gain the
`Patch` and `PatchStatus` arms of their case splits. One invariant is
strengthened: `etcd_object_is_well_formed` now records that a custom resource
carries a generation and a built-in kind does not, which the no-op rule for an
update carrying the stored object needs. Three framework lemmas gained a
budget with the new request arms: `lemma_xor_preserves_during_api_server_step`
(rlimit 100, spun off), `lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id`
(rlimit 50) and `lemma_always_each_object_in_etcd_has_at_most_one_controller_owner`
(rlimit 200, spun off, its inductive step restated per key). In the four
existing controllers the same arms added eight budgets (`rlimit(100)` on two
VReplicaSet and two VDeployment lemmas and on two VStatefulSet lemmas,
`rlimit(400)` on two VStatefulSet store invariants) and raised one from 20 to
60 (`lemma_from_after_send_list_vrs_req_to_receive_list_vrs_resp_with_nv`).
The Widget pair's own proofs carry no budget annotation.

### 5.5 Not done

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
| Assumptions, invariant bundles, stable specs, phase I, the sync reconciler's layers | `widget_sync_controller/proof/liveness/spec.rs` |
| One step of the cluster at the mirror key and the outer copy | `widget_sync_controller/proof/liveness/api_actions.rs` |
| Termination of both reconcilers | `widget_sync_controller/proof/liveness/terminate.rs` |
| R1, R2, R3, R3s | `widget_sync_controller/proof/liveness/{sync_spec_proof,sync_status_proof,janitor_proof,cleanup_proof}.rs` |
| Store facts (uids, what each request leaves alone) and temporal rules the pair uses | `kubernetes_cluster/proof/{api_server,temporal_rules}.rs` |
| The disturber: model, guarantee, composition with the pair | `widget_sync_controller/model/disturber_reconciler.rs`, `proof/disturber.rs`, `composition/widget_disturber_reconciler.rs` |
| Welder specs and composition | `composition/widget_{janitor,sync,disturber}_reconciler.rs`, `composition/compose_all.rs` |
| Two-store model | `kubernetes_cluster/spec/two_cluster.rs` |
| Refinement into the one-store model | `kubernetes_cluster/proof/two_cluster/` |
| R1 to R3s on two clusters, for the pair beside admitted other controllers; the instances of the pair and of the pair with the disturber | `widget_sync_controller/proof/two_cluster.rs` |
| Binaries, manifests, testbed, e2e | `src/bin/`, `deploy/widget_sync/`, `tools/two-cluster-test.sh`, `e2e/src/widget_sync_e2e.rs` |

Full-repository verification (`cargo verus verify --lib`) passes.

## 8. Future work

Tracked as issues on the fork: repository hygiene, now the e2e checks that
need the kind testbed (#14). Operability (#9), hardening (#10) and the proof
layout and solver-budget pass (#11) are done in the scope their issues record. Out-of-band edits and deletes of mirrors (#13) are modeled (sections
2.3 and 2.4); what remains excluded is an edit that strips a mirror's
identity, which the design refuses to recover from.

Decided against, for this branch: a verified inner controller (the sync
controller stays agnostic to the inner side; D3 is an assumption, #3), a spec
projection for inner-owned fields (no spec field is owned by the inner side),
and parent-cluster identity on mirrors for the single pair.

Follow-ups after this branch: the fan-out to many outer namespaces, each with
its own inner cluster, in the Cluster API shape of a management cluster and
its workload clusters, together with parent identity on mirrors and tenancy
(#15); and the pass that makes the branch reviewable for an upstream
contribution (#16).
