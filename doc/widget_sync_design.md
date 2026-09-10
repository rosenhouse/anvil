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
  spec; R2, the outer status eventually and stably is the one derived from the
  inner status for that spec (its fields mirrored, its conditions merged),
  stamped with the outer generation; R3, a mirror whose parent is
  gone is eventually removed; R3s, no mirror pointing at a departed parent
  persists. All four are ESR-style properties in the sense of the Anvil paper.
- Also proved: the **round trip**, R1 and R2 chained -- once an outer copy stops
  changing, it eventually and stably carries the status derived from one its
  mirror is itself stably holding, for a mirror that carries the copy's spec.
  R1's conclusion does not reach R2's premise, so the chain needs D4 (below). It
  is proved for a cluster that runs a modelled inner implementation, not for the
  one section 3.4 closes over, and it is not part of the sync controller's ESR:
  it does not travel through composition or into the multi-store theorems.
- Assumed: D3, the inner side eventually releases terminating objects; D4, the
  inner implementation eventually settles on a status for the spec it was given;
  exactly one outer cluster per inner cluster; the operational items in
  section 3.5.
- Framework additions (section 5): `metadata.generation` in the model, a JSON
  patch primitive, and a cluster tag on the exec wrappers with routing in the
  shim.
- What is mechanized about "many clusters" (section 2): a multi-store model,
  `MultiCluster<S>`, one API server per cluster, with a proof that every
  execution of it is, under an injective relabeling of uids and resource
  versions (and of the `parent-uid` annotation through it), an execution of the
  one-store model. R1, R2, R3, R3s and the janitor's delete soundness (less the
  clause that no uid the primary counter may still issue names the parent) are
  then stated on multi-store executions (`widget_multi_cluster_theorem`, for any
  cluster meeting the refinement's hypotheses, and closed for the cluster of any
  configuration that runs one binding's janitor, with and without the disturber:
  `widget_instance_multi_cluster_theorem`,
  `widget_disturbed_multi_cluster_theorem`).
  `widget_kinds_multi_cluster_theorem` states them for a whole deployment: every
  configured kind's sync controller, every binding's janitor, one store per
  binding (`doc/widget_sync_fanout_design.md`, section 5.3).
- Which CRDs: any with the shape of section 2.2 of the fanout design. The
  controller checks it at boot, in the management cluster only, and refuses to
  start without it.
- The theorems are parameterized by the API server's schema validation and hold
  for any. Every closed instance is read at the trivial one, so none of them
  exercises a server that refuses a spec (fanout design, section 5.3).

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
  it carries the label and its `parent-uid` equals the current outer uid. An
  object with the label and a `parent-uid` annotation naming another uid is a
  mirror of a previous incarnation: it is reported as `StaleMirror` and left
  to the janitor. Anything else is reported as `ForeignObject`. Neither is
  ever touched. Adoption would let anyone who can create `Outer{ns,name}`
  overwrite `Inner{ns,name}`.
- Chains compose and cycles are inert, by the adoption rule rather than by
  proof: a second sync controller in the inner
  cluster sees our mirror as its outer copy; a cycle back finds an unlabeled
  object and refuses.

### 1.2 The sync reconciler

Triggered by an outer `Widget` with generation `g`, spec `σ`, uid `u`, and by
same-named inner `Widget`s (a latency optimization; liveness rests on requeue).

```
Init
 └─ Get Inner{ns,name}                                   (inner cluster, quorum read)
      ├─ NotFound → Create Inner{ns,name; label; parent-uid=u; spec=σ}
      │     ├─ Ok → Done
      │     └─ error e → report Failed(e)
      ├─ error e → report Failed(e)
      ├─ Found, deletionTimestamp set → status InnerTerminating → Done
      ├─ Found, label and parent-uid present, parent-uid ≠ u → status StaleMirror → Done
      ├─ Found, label or parent-uid missing → status ForeignObject → Done
      ├─ Found, ours, spec ≠ σ → Patch Inner {test uid, test generation; add /spec := σ}
      │     ├─ Ok → Done
      │     └─ error e → report Failed(e)
      ├─ Found, ours, spec == σ, Inner.status.observedGeneration == Inner.metadata.generation
      │     → status Synced, from Inner.status → Done
      └─ Found, ours, spec == σ, inner not caught up → status InnerConverging → Done
      "status c[, from S]" means: X := outer_status_for(g, S or Outer.status, c) (section 3.3);
                                  Outer.status == X → Done,
                                  else PatchStatus Outer {test uid=u, test generation=g; add /status := X} → Done
      "report Failed(e)" means:   X := outer_status_for(g, Outer.status, Failed(reason(e)));
                                  Outer.status == X → Error,
                                  else PatchStatus Outer {test uid=u, test generation=g; add /status := X}
                                       → Error, whatever the answer (the write is not retried)
Error (any other unexpected response, and after every report) → requeue
```

`π` projects a status onto the mirrored fields (everything except
`observedGeneration` and `conditions`); `outer_status_for` (section 3.3)
builds the outer status from the generation, a source status and the
outcome. The reconciler never writes outer spec or metadata, never writes
inner status or metadata, never deletes.

**Error reasons.** `reason(e)` maps the model's API errors to the reason of
the `Synced` condition: `Forbidden` for an authorization error;
`InnerUnreachable` for `Timeout`, `ServerTimeout` and `InternalError`;
`CreateFailed` for a `NotFound` answering the Create (the inner namespace is
missing); `Rejected` for `Invalid`, `BadRequest` and `NotSupported`;
`RequestFailed` otherwise (a `NotFound` answering the Patch, an
`AlreadyExists`, a `Conflict`). In the model a failed JSON patch `test` is
also answered `Invalid`; on a real API server the two share the 422 status
and differ only in the message, and the shim hands a failed test to the
reconciler as `Conflict`, so a race on the mirror reads `RequestFailed` and
is retried, while `Rejected` is reserved for a schema or webhook rejection.
The shim also maps a connection failure or a client-side request timeout to
`Timeout`, so a partition from the inner cluster reads `InnerUnreachable`. `ForeignObject`, `Forbidden` and `Rejected` are the
permanent cases: nothing the reconciler does again changes the answer, and
`Stalled` is `True` for them (section 1.4).

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

Because absence is matched on uid, a restore of the outer cluster that
issues new uids makes every mirror stale at once; for that event the shim
carries an operator gate that withholds the janitor's Delete requests while a
mounted file exists, answering the reconciler with `Timeout` instead
(`controller_runtime::deletes_withheld`; the deployment in section 4). The
gate is safe without any change to the model or the proofs: to the verified
reconciler a withheld delete is a failed request, which the model covers as
the `drop_req` fault, and withholding a delete can only defer R3 and R3s,
which resume when the gate is cleared, never violate the janitor's soundness
fact, which is about the deletes that are sent.

### 1.4 Generation and status, as an observer reads them

Kubernetes bumps `metadata.generation` of a custom resource with a status
subresource when its spec changes and when a deletion timestamp is stamped
(section 5.1), never on a status write. On the **inner** copy nothing is
unusual: the sync reconciler writes the spec, the inner implementation writes
the status with its own `observedGeneration`.

On the **outer** copy every status write by the sync reconciler, the ones
that report a failure included, sets `status.observedGeneration := g`, the
generation of the snapshot it reconciled, and the patch's generation test
makes it land only while the copy is still at `g`. The status carries three
conditions, `Synced`, `Ready` and `Stalled`, all with
`condition.observedGeneration == g` (G-gen, section 3.1). `Synced` is `True`
exactly when the reconcile verified `Inner.spec == σ` for the snapshot's `σ`
and the inner status observes the mirror's current generation; the patch's
generation test is what keeps a snapshot the outer copy has moved past from
landing.

> `status.observedGeneration == metadata.generation` means the sync controller
> has acted on the current spec, whether or not it succeeded. `Synced == True`
> at that generation means the spec is in the inner cluster and the mirrored
> fields are the inner implementation's status for it.

Otherwise `Synced` is `False` with reason `InnerConverging`,
`InnerTerminating`, `StaleMirror`, `ForeignObject`, or, after a failed
request, `Forbidden`, `InnerUnreachable`, `CreateFailed`, `Rejected` or
`RequestFailed` (section 1.2); the mirrored fields keep their last reported
values. An inner implementation that never sets `observedGeneration` never
reaches `Synced=True`.

`Ready` and `Stalled` combine the sync reconciler's own outcome with the inner
copy's conditions of the same type, which are consulted only when the inner
status is, that is when `Synced` is `True`:

- `Ready` is `True` exactly when `Synced` is `True`, the inner `Ready`
  condition, if present, is `True`, and the inner `Stalled` condition, if
  present, is not `True`. Otherwise it is `False`: with reason `NotSynced`
  when not synced, else with the reason and message of the inner condition
  that denies it. When synced with no inner `Ready` condition it is `True`
  with reason `Synced`.
- `Stalled` is `True` when the outcome is permanent (`ForeignObject`,
  `Forbidden`, `Rejected`), with that reason, or when the inner `Stalled`
  condition is `True`, with that condition's reason and message. Otherwise it
  is `False`, with the inner `Stalled` condition's reason and message when
  synced and present, else with the outcome's reason.
- `Ready` and `Stalled` are never both `True`
  (`lemma_ready_and_stalled_exclusive`), which (G-shape) carries to a reader of
  the patch. It is still not lifted to the stored outer copy.

The rest of this section describes `reconcile_core`, not a theorem. What the
guarantee proves of a status write is (G-shape) and (G-gen) (section 3.1), which
relate the reported conditions to each other and to the tested generation, never
to the inner cluster. So `Synced == True` meaning the spec is in the inner
cluster is a property of the code. No theorem carries that direction to a reader
of the outer copy. R2 carries its converse -- a settled inner status is
eventually reported -- under premises that findings 1 and 3 of issue #49 record
as unchained and unmodelled.

## 2. The model

### 2.1 One store, two kinds, two controllers

Anvil's model has one API server whose store is keyed by `(kind, namespace,
name)`. The cluster is folded into the *model* kind at the exec boundary:
`model_kind(name, cluster)` names the copies of the CRD `name` in `cluster`,
so the outer copy has kind `model_kind(name, Primary)` and the mirror in the
binding `b` has kind `model_kind(name, Remote(b))`, written `name@ns/cluster`.
Objects are `SyncedObjectView`, one view type whose `kind` is data
(doc/widget_sync_fanout_design.md, section 2.3); a configured kind is a
`SyncKind { outer_kind, name, selector }` and a binding is a `ClusterRefView`.
The pair is parameterized by them: `k.outer_kind` is the outer kind and
`inner_kind(k, b)` the mirror kind of the binding `b`. On the exec side one
`SyncedObject` wrapper carries the kind it was unmarshalled with, and
`SyncKindExec` (the registry entry plus the selector) is what ties a runtime
kind and a cluster to a model kind.

The outer kind and every inner kind are installed in one `Cluster`; the sync
reconciler is one controller id per kind and the janitor one controller id per
(kind, binding). `schedule_controller_reconcile` fires for a reconciler's own
kind, so outer copies schedule the sync reconciler and the mirrors of a
binding schedule that binding's janitor. The inner implementation is an
ordinary other controller under a rely condition.

### 2.2 Many stores, and the refinement into one

`kubernetes_cluster/spec/multi_cluster.rs` defines `MultiCluster<S>`: a cluster
whose kinds are split between a family of API servers indexed by a side `S`,
each with its own store, uid counter and resource-version counter, while
controllers, network and failures are shared. `side_of` routes a kind to its
side, `home` is the side a step that touches no store is taken on, and `wf()`
asks that the routing be total and that `home` be a side. Every step is a step
of the one-store model taken on one of the projections, every other store
unchanged. A request is handled by the API server of its kind, the garbage
collector of a side reads only that side's store, and a reconcile is scheduled
from the store of the controller's kind. For the Widget controllers the sides
are the primary cluster and the inner cluster of each binding
(doc/widget_sync_fanout_design.md, section 5.2).

`kubernetes_cluster/proof/multi_cluster/` proves that every execution of
`MultiCluster<S>` maps to an execution of `Cluster`. The map unions the stores
and relabels uids and resource versions injectively, per side, by an
assignment read off the execution: the k-th value a store's counter allocates
goes to the number of values all the stores had allocated by then, so the
one-store counters count every allocation once. A value no counter reaches
relabels to a negative value, distinct for every side and every counter value:
the sides are numbered by their rank in the set of sides. Annotation values
follow the uids through a per-controller *hook* (`Hook`: a function from the uid
relabeling to a relabeling of annotation values); for the Widget controllers the
hook covers the `parent-uid` annotation. The proof (`finite`, the sums and ranks
over that set; `relabel`, `api_server`, `steps`, `execution`, `fairness`) covers
the initial state, every step, and weak fairness of every action the liveness
proofs assume. Fairness needs the multi-store message behind a one-store message
to stay the same while a wait lasts, which follows from the one-store invariants
that no message is in flight twice and that in-flight ids are below the allocator
(`every_in_flight_msg_has_no_replicas_and_has_unique_id`,
`every_in_flight_msg_has_lower_id_than_allocator`, proved on the mapped
execution from init and next, so the transfer is not circular).

`widget_sync_controller/proof/multi_cluster.rs` instantiates the refinement.
Both reconcilers commute with the relabeling. `widget_multi_cluster_theorem`
states R1, R2, R3 and R3s of every execution of the multi-store model that runs
the pair under its fairness assumptions and D3, each property read on the
store its objects live in. It also states the janitor's delete soundness: a
janitor Delete in flight names a uid below the uid counter of the store of its
kind, and no outer copy of `k` in the primary store *whose selector names the
binding's cluster* carries the parent uid of a mirror the Delete would remove.
The counter clause is an invariant of the multi-store
model itself (the janitor deletes by the uid of a stored mirror), not a
pull-back: a uid a store's counter never reaches relabels to a negative value,
about which no one-store fact says anything, so the "never will" half of the
one-store fact, that no uid at or above the counter names the parent, does not
survive the relabeling.

The cluster conjunct narrows the second clause from every stored outer copy to
the outer copies of the binding the janitor serves, and it is what the janitor's
own decision checks (`doc/widget_sync_fanout_design.md`, section 3.3): the
janitor lists the outer copies of the mirror's namespace and keeps the mirror
only if one of them has its parent uid *and* selects its cluster. The clause
therefore says exactly what the janitor looked at before deleting, which is what
makes it provable at all once a parent may name a cluster other than the
janitor's. What it costs is the case the CEL immutability rule rules out: if a
parent could move from cluster `c1` to `c2` while keeping its uid, an outer copy
carrying that parent uid would still be stored, selecting `c2`, and the statement
would not forbid `c1`'s janitor from collecting the mirror it left behind. Under
the rule that case does not arise, because `cluster_of` is preserved across every
update of an installed object
(`lemma_api_server_step_preserves_cluster_of`); without the rule the
mirror `c1`'s janitor collects is one no parent points at any more, which is the
right outcome operationally but is not the clause as stated.

The cluster may run other controllers beside the pair
(`widget_cluster_with_others`). Each other controller must meet hypotheses 1
and 3 below for its own model (`other_model_ok`, `other_model_commutes`), and
every installed type, including any the other controller brings, must meet
hypothesis 2. For the six-controller cluster of section 3.4 that would mean
the state validation of the four other controllers' types as well as their
commutation lemmas, which is why that cluster is not pulled back. The pair's relies of section 3.2 must hold of the other
controller as invariants of the one-store model under the pair's own spec,
init, next, the pair's fairness and D3 (`widget_relies_hold_of`);
`lemma_relies_hold_of_from_welder` derives that from what a Welder composition
of the controller with the pair establishes, the controller's guarantee as an
invariant under `cluster_model`, given that the guarantee implies the relies
and that the pair's spec provides every fairness the Welder registry declares.
No fairness of the other controllers is assumed. `widget_pair_cluster` names the
case with no other controller and `lemma_disturber_is_other_controller_ok`
admits the disturber (section 2.4) as one. `widget_instance_multi_cluster_theorem`
and `widget_disturbed_multi_cluster_theorem` close the statement for the clusters
`composition/widget_sync_reconciler.rs` and
`composition/widget_disturber_reconciler.rs` build from a configuration, for any
configuration meeting `sync_kind_ok` and `bindings_ok`; the demo
applies them in one line. Those instances are the witness that the hypotheses are
satisfiable, because the sync reconciler serves a finite set of bindings
(doc/widget_sync_fanout_design.md, sections 3.2 and 5.2).

Those clusters register one janitor, the janitor of the binding the theorem is
read for. `widget_kinds_multi_cluster_theorem`
(`widget_sync_controller/proof/multi_cluster_kinds.rs`) covers a whole
deployment instead, discharging `widget_other_controller_ok` for each other
controller from that controller's model and from its guarantee under init and
next (doc/widget_sync_fanout_design.md, section 5.3).

The multi-store statement thus quantifies over other controllers as the
one-store theorems do, with hypotheses 1 to 3 added per controller: composing
the pair with a verified inner implementation on many stores needs that
implementation's own commutation lemma and its guarantee proved as an
invariant. What remains narrower is the kind partition. A kind lives on
exactly one side, and every built-in kind is routed to the primary side, so an
inner implementation that creates Pods or ConfigMaps in an inner cluster is not
expressible in this multi-store cluster.

The refinement holds under three hypotheses, all met by the Widget pair, and
two restrictions of the multi-store model:

1. Controllers write only objects of known kinds, name what they create, put
   owner references only on kinds of the object's own side (`request_ok`), and
   have no external system.
2. Installed types validate objects and transitions without reading
   metadata, and their default status unmarshals. The second follows from
   `marshal_status_preserves_integrity` for every type installed through
   `Cluster::installed_type`; the first is a per-type fact (`CustomResourceView`
   promises it for state validation only), checked for both Widget types in
   `lemma_widget_instance_types`.
3. Every reconciler commutes with the relabeling: run on the relabeled object
   and response it reaches the same local state and sends the relabeled
   request. A reconciler that copies a uid or resource version into data other
   than through the hook, or whose local state holds one, does not. The
   `UidToken` boundary (section 5.3) and `tools/check-widget-exec-hygiene.sh`
   hold the exec code to the same discipline as the model.
4. (Restriction.) The pod monkey of the multi-store model writes named pods
   without server-assigned fields, owner references or annotations. This drops
   the monkey behaviours that exercise stale-write conflicts and garbage
   collection of owned pods; irrelevant to the Widget pair, but a
   pod-managing controller verified on `MultiCluster` would lose that fault
   coverage. The restriction exists because which monkey action runs is a
   `choose` over the input, which the proof cannot equate between an input
   and its relabeling. The monkey also acts on the home store only, so a
   multi-store theorem gives no monkey coverage in the other stores at all.
5. (Restriction.) Every store starts empty with its counters at zero
   (`MultiCluster::init`). The refinement rests on it: a value a counter has
   allocated is non-negative, which is what keeps it apart from the negative
   value an unallocated one relabels to. An inner cluster that already holds
   objects is therefore not an execution of this model, so the theorems say
   nothing about a mirror key already taken in a cluster the controller has not
   written to. What the reconcilers do there -- refuse to adopt, report
   `ForeignObject` -- is pinned by the exec code's conformance to the model,
   not by a theorem.

What remains trusted is the usual Anvil boundary, per store: that each real API
server behaves as the model's API server, with its uids and resource versions
read as that store's counter values; that the shim routes each model kind to
the cluster the model assigns it (section 5.3), which the model cannot check,
and that the wrappers' `unmarshal` and `has_kind` postconditions read the
model kind off the cluster tag and the kube kind (`DynamicObject::kind()`,
which reports the API server's kind string, is not used by the pair);
and the injectivity of `int_to_string_view` (an `external_body` fact over all
integers), which the hook's injectivity rests on. A controller that reads counter values
into data (VDeployment uses a resource version as a hash; RabbitMQ stores one
in an annotation) is outside hypothesis 3 and must live in one cluster. The
axiom `generated_name_spec` and the `external_body` ensures equating a real
resource-version string with the model counter are not used by these
reconcilers.

### 2.3 What the model covers

| Situation | Modeled | How |
|---|---|---|
| An API server per cluster, with independent uid and resource-version counters | yes | the multi-store model and its refinement (section 2.2) |
| Either cluster unreachable for a finite time | yes | `drop_req` |
| Permanent partition | excluded | fairness (`disable_req_drop`) |
| Write executed, client sees a timeout | yes | covered by an executed write plus `restart_controller`; every write is replay-safe (patches test uid and generation, deletes carry uids); a delayed `Create` is collected by the janitor |
| Late delivery of a stale request | yes | the network reorders; the tests reject it |
| Spurious `NotFound` (CRD missing, wrong kubeconfig) | yes, as a fault | the janitor deletes only after a successful `List` lacking the parent |
| Inner implementation writing status, timestamps or annotations on every reconcile | yes, as another controller under the rely, and modeled as one (2.5) | the spec patch tests generation, not resource version; on many stores the implementation must also meet hypotheses 1 to 3 of 2.2; an annotation write is an `Update` carrying a resource version (3.2) |
| Inner implementation adding finalizers | yes, as another controller under the rely | rely allows it; R3 needs D3; on many stores also hypotheses 1 to 3 of 2.2 |
| Out-of-band edit of a mirror's spec, or of its other labels and annotations (a `kubectl edit` in the inner cluster) | yes, as another controller's write | the rely permits it; the reconciler overwrites a spec edit and never copies a status computed for it; R1 and R2 hold once such edits stop (`mirror_spec_undisturbed`). The disturber (section 2.4) is a controller model doing the spec edit, on one store and on two |
| Out-of-band delete of a mirror; inner cluster rebuilt | yes, as another controller's delete | the rely permits any Delete; the reconciler recovers (NotFound → Create); R1 and R2 hold once such deletes stop landing on the live mirror (`mirror_undeleted`); R3 and R3s hold throughout. The disturber (section 2.4) is a controller model doing exactly this, on one store and on two |
| Out-of-band edit that removes the mirror's label or `parent-uid` annotation | excluded by the rely | the object becomes foreign to both reconcilers, which refuse to adopt; no recovery is possible without adoption (section 1.1) |
| Outer cluster restored with new uids | operational | the janitor pause gate (shim) withholds deletes; the model sees a failed request (`drop_req`); cleanup under R3 and R3s resumes when the gate is cleared (section 1.3) |
| A kind present in more than one cluster (Pods, ConfigMaps) | no | the multi-store model assigns each kind to one side |
| Foreign `Widget{ns,name}` pre-existing in the inner cluster | vacuous | only the sync reconciler creates inner-kind objects in the model; the exec code refuses to adopt and reports `ForeignObject` with `Stalled=True` |
| Stale mirror of an earlier incarnation of the outer copy | yes | reported as `StaleMirror` until the janitor removes it (R3); R1's settling argument covers the wait |
| Error responses to the reconcile's requests | yes | `drop_req` answers any request with any `APIError`; the reconcile reports the mapped reason once and requeues; the report is one more step of the reconcile in the liveness proofs |
| Two outer clusters feeding one inner cluster | no | assumed away, and enforced operationally by the claim (`doc/widget_sync_fanout_design.md`, section 1.3) |
| Many outer namespaces, each with its own inner cluster | yes | a kind and a binding are data in the model, and the theorems are stated for both (`doc/widget_sync_fanout_design.md`, sections 3 and 5) |
| Namespaces, admission, schema drift | no | operational assumptions, section 3.5 |
| Two replicas of the controller | no | one replica assumed; a second is benign for safety (every write tests uid and generation or carries a uid precondition) but is outside the model, and costs status flapping and `AlreadyExists` noise |

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
Welder: `widget_disturbed_core_holds_for` is the closed statement for a cluster
running the janitor, the sync reconciler and the disturber, for any one-binding
configuration, and `widget_disturbed_core_holds` is the demo's instance of it.
`lemma_disturber_is_other_controller_ok` (`proof/multi_cluster.rs`) admits it
into the multi-store statement, acting in the binding's store: its
model reads only the namespace, name and spec of its object and tests nothing,
so it commutes with the relabeling by computation, and its guarantee gives the
pair's relies in the form the multi-store theorem asks for (section 2.2).

The value it writes over the spec, `disturbed_spec`, is a closed definition
(`model/disturber_reconciler.rs`): it appends one character to the value it
found, so `disturbed_spec(v) != v` for every `v`
(`disturbed_spec_changes_the_spec`, proved by length). Nothing the pair proves
depends on which value it is beyond that; what the inequality rules out is a
disturber that writes the spec back unchanged, which would be no disturbance at
all -- the premise of R1 and R2, "no edit of the mirror's spec is in flight",
would be met by a Patch that changes nothing. The disturber stands for a
`kubectl edit` and has no exec twin.

The disturber adds no assumption. What it buys is a witness that the relaxed
sync rely (any Delete, any Patch) is satisfiable by something that deletes and
edits mirrors, and that the premises of R1 and R2 are the only place where "the
disturbance has stopped" is said. A cluster-model step in the style of the pod
monkey was not needed: it would have touched every `next_step` case split in the
repository and the multi-store simulation, for a behaviour the rely already
expresses.

### 2.5 The inner implementation

The controller a workload cluster runs for a mirrored kind is what the return
path exists for: the sync controller copies a spec in, something acts on it and
writes a status, and the sync controller carries that status back out. It is
another controller under the rely, like the disturber, and
`model/inner_impl_reconciler.rs` models one. On each reconcile it patches the
status of the mirror it was triggered by, stamping `observedGeneration` with the
generation it observed and reporting `Ready`. The patch tests the mirror's uid and generation. The uid test is the safety
one: generations restart at 1 with each incarnation, so without it a patch
delayed past a delete and a recreate would make `inner_caught_up` hold of a
status computed for the previous incarnation's spec. The generation test keeps a
late patch from overwriting a settled status with an older one, which
`always(inner_settled)` needs. What a real
implementation computes is its own business; the pair's properties are stated
over whatever status it writes, so the model writes the cheapest one that has
the shape.

Its guarantee (`proof/inner_impl.rs`: every request it has in flight is a status
Patch of its own mirror, of its own kind) implies both reconcilers' relies. The
sync reconciler's rely asks only that a status Patch not name the outer kind,
and the janitor's constrains Creates and Updates, of which it sends neither.
`composition/widget_inner_impl_reconciler.rs` composes it with the pair through
Welder, as the disturber is composed: `widget_implemented_core_holds_for` is the
closed statement for any one-binding configuration, and
`widget_implemented_core_holds` the demo's instance. Both are one-store
readings; the multi-store one needs the implementation's commutation lemma and
`widget_other_controller_ok`, which the disturber has and this does not.

The status it writes carries the empty remainder: `empty_status_rest()` is the
cheapest remainder a model can supply, and nothing the pair proves depends on
which one it is. The testbed's echo controller writes a populated one:
`observedCount` for a Widget, `observedSize` for a Gadget. So the modelled execution exercises the conditions half of the
return path and not the payload half: `settled.rest` is the default remainder
there, and `status_synced` cannot tell a mirrored remainder from a defaulted
one. The echo controller also tests nothing on its patch, where the model tests
uid and generation, so the model is neither an over- nor an under-approximation
of it.

R2's premise is producible in this cluster: the status the model writes reports
the mirror as caught up with the generation it tested
(`lemma_inner_impl_status_is_caught_up`), and a status write keeps the metadata
and the spec (`status_updated_object`), so `spec_synced` survives it. No
fairness is assumed for the implementation, so nothing here says when the inner
side settles.

## 3. Specification

The trusted specification is `src/controllers/widget_sync_controller/trusted/`:
`spec_types.rs` (`SyncKind`, `Binding`, `inner_kind`, `inner_key`, the mirror
relation and the status builders), `rely_guarantee.rs`, `liveness_theorem.rs`
(R1, R2, R3, R3s, D3), `step.rs` (the reconcilers' step types) and
`exec_types.rs` (`SyncKindExec` and the outcome types). Every one of them is
stated for a kind `k` and, where the mirrors are concerned, a binding `b`; the
routing the model trusts (section 5.3) is `RegistryEntry::api_resource`,
which names the model kind of a configured kind in a cluster. `π` is
`SyncedStatusView::mirrored()`.

Trusted beyond the specification, under `widget_sync_controller/`: one
`external_body` function in `trusted/exec_types.rs` — `outer_status_for`,
which builds the outer status, its three conditions included, by hand to match
the spec's definition — four `external_body` items in `model/install.rs`, the
`Marshallable` instances of the reconcile states, whose `marshal` and
`unmarshal` are the eight uninterpreted spec functions the hygiene script pins
there. Each modelled controller costs one round-trip axiom and two
uninterpreted functions, which is the price of the disturber (section 2.4) and
of the inner implementation (section 2.5). Nothing else under the controller is uninterpreted: the mirrored
remainder of a status that was never written is the shape's empty remainder,
`empty_status_rest()`.

Everything the pair used to trust about its own wrappers is now the shape's,
and lives in `kubernetes_api_objects`, where anything else generic over kinds
shares it. That inventory, which
`tools/check-widget-exec-hygiene.sh` pins file by file:

| File | What is trusted there |
|---|---|
| `exec/synced_object.rs` | the wrappers of the shape: `SyncedObject`'s `unmarshal`, `marshal`, `has_kind`, `new` and accessors; `SyncedStatus`'s and `SyncedCondition`'s constructors and accessors, `SyncedStatus::rest` and `RawValue::empty_rest` (whose values satisfy `status_rest_ok`, the precondition of `SyncedStatus::new`); the free `marshal_status` and `cluster_of_dynamic`, the latter being the selector read off a stored object that a `List` response gives; and the two equalities `RawValue::eq` and `SyncedStatus::eq`, whose postconditions are *iffs* — `b == (self@ == other@)` — so each is trusted to decide equality of the view in both directions, which is what makes "the specs differ" and "the status differs" decisions of the reconcilers rather than approximations |
| `exec/registry.rs` | `RegistryEntry::crd_name` and `RegistryEntry::api_resource`, the routing the model trusts (section 5.3): the model kind of a configured kind in a cluster |
| `spec/synced_object.rs` | the uninterpreted `unmarshal_status`, `marshal_status`, `spec_field`, `status_rest_ok` and `empty_status_rest`, and three axioms over them: `marshal_status_preserves_integrity` (`unmarshal_status(marshal_status(s)) == Ok(s)`, **for a representable `s`** — a status whose remainder carries an `observedGeneration` or `conditions` of its own is not representable, so an unguarded round trip would be a contract no implementation can keep), `unmarshal_status_is_representable` (a status read out of a value is one) and `empty_status_rest_ok` (the empty remainder is one). Representability is a *precondition* of `DynReconciler::reconcile_core`, beside the two the trait already carries, discharged by the shim's unmarshal -- not a property asserted of every `SyncedObject`, which would let any holder of one conclude that an arbitrary status is representable. `unmarshal`, `marshal` and their lemmas are proved over these, not assumed |
| `spec/model_kind.rs` | nothing: `model_kind` and its injectivity are proved. The hypotheses that injectivity rests on — no `@` in a kind name, none in a binding's parts and no `/` in its namespace — are checked on the exec side at boot (`crd_shape::check_kind_name`) and when a Secret is read (`bindings::binding_of_secret`) |

From the framework the pair also relies on `UidToken`, on the `PatchTests` and
`Preconditions` setters, and on the shim's construction of the JSON `test`
operations, which is where "patches test uid and generation" becomes real.
`tools/check-widget-exec-hygiene.sh` fails when an `external_body` appears
anywhere else under `widget_sync_controller/`, and when the counts of the four
files above change.

### 3.1 Guarantees

**Sync** (`widget_sync_guarantee`). A request sent while reconciling the outer
copy at `outer_key` is one of: `Get` of the mirror key; `Create`, in that
namespace, of exactly `make_inner(outer)` for an outer copy at `outer_key`
whose uid is issued and bound to that key; `Patch` of the mirror's spec;
`PatchStatus` of the outer copy testing uid and generation, whose status and
`Synced`, `Ready` and `Stalled` conditions carry the tested generation as
`observedGeneration` (G-gen), and whose condition list is those three and
nothing else, in that order (G-shape). Nothing else.

(G-shape) also relates the three to each other. Each is `True` or `False`.
`Ready` is `True` only when `Synced` is, and never at the same time as
`Stalled`. `Synced` is `True` exactly when its reason is `Synced`, and it
carries no message. A `False` `Synced` means no inner status was read, and the
other two say so rather than reporting one: `Ready` denies with `NotSynced`,
`Stalled` repeats `Synced`'s reason, and neither carries a message.

What (G-shape) never does is relate a reported condition to the inner cluster.
The mirrored remainder is unconstrained, and so are the `Ready` and `Stalled`
text where `Synced` is `True` -- the path that carries the inner status, and so
the path that matters. Tying either to the status the mirror held needs the
`Get` response that produced it, which no state keeps, so a reconciler reporting
`Synced` and `Ready` over invented mirrored fields still satisfies the
guarantee. Issue #49 finding 2 is open.

Each condition being two-valued is `outer_status_for`'s merge, which issue #49
finding 16 disputes: a workload reporting `Ready=Unknown` is reported `False`.
(G-shape) states that merge rather than endorsing it, so changing it changes the
guarantee.

**Janitor** (`widget_janitor_guarantee`). A `List` of outer copies in the
mirror's namespace, or a `Delete` of the mirror with a uid precondition.

### 3.2 Relies

**Sync, on an anonymous other controller** (`widget_sync_rely`): no `Create`
of the inner kind; an `Update` of the inner kind carries a resource version
and, if it is going to land, keeps the mirror's owner references and its
identity (label and `parent-uid` annotation), and is otherwise free, spec
included; any `Patch`; no status write to the outer kind;
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
holds only under the janitor's rely and is therefore carried in the janitor's
ESR slot (`widget_janitor_esr`: R3 together with this safety fact), which the
sync spec takes as its liveness dependency.

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
inner_settled(outer, settled)(s)  := spec_synced(outer)(s) && inner_caught_up(inner)
                                  && π(inner.status) == π(settled) && inner.status.conditions == settled.conditions
status_synced(outer, settled)(s)  := the outer copy's status == outer_status_for(its generation, settled, Synced)

outer_status_for(g, src, c) := { observedGeneration: g, π: π(src),
                                 conditions: [Synced(g, c), Ready(g, src, c), Stalled(g, src, c)] }
    // src is the inner status when c is Synced (its conditions are read), else the previous outer status;
    // the three conditions are defined in section 1.4; every one carries observedGeneration g

mirror_object_is(k, a, u)(s) := an object with uid u at k is a mirror pointing at a
object_is_gone(k, u)(s)      := no object with uid u is at k
parent_absent(k, a)(s)       := no object with uid a is at outer_key_of(k)
mirror_collected(k, a)(s)    := no mirror pointing at a is at k
```

| | Statement | Proved in |
|---|---|---|
| R1 | `∀outer. □outer_spec_stable(outer) ~> □spec_synced(outer)` | `proof/liveness/sync_spec_proof.rs` |
| R2 | `∀outer, settled. □(outer_stable(outer) ∧ inner_settled(outer, settled)) ~> □status_synced(outer, settled)` | `proof/liveness/sync_status_proof.rs` |
| R3 | `∀k, a, u. (□parent_absent(k, a) ∧ mirror_object_is(k, a, u)) ~> object_is_gone(k, u)` | `proof/liveness/janitor_proof.rs` |
| R3s | `∀k, a. □parent_absent(k, a) ~> □mirror_collected(k, a)` | `proof/liveness/cleanup_proof.rs` |
| D3 | `∀key, u. inner_terminating_object(k, b, key, u) ~> object_is_gone(key, u)`, per binding `b` (the premise fixes `key.kind == inner_kind(k, b)`) | assumed |
| D4 | `∀outer. □(outer_stable(outer) ∧ spec_synced(outer)) ~> ∃settled. □(outer_stable(outer) ∧ inner_settled(outer, settled))` | assumed |
| RT | `∀outer. □outer_stable(outer) ~> ∃settled. □(status_synced(outer, settled) ∧ inner_settled(outer, settled))` | `proof/liveness/round_trip.rs` |

RT is R1 and R2 chained; D4 is the step between them. R2's premise,
`inner_settled`, is R1's conclusion plus two facts R1 does not supply: that the
inner status observes the mirror's current generation, and that it is the
particular `settled` R2 is stated for. Both are about the implementation running
in the inner cluster, which Anvil does not model.

RT's conclusion keeps `inner_settled` beside `status_synced`. That is what makes
it a round trip. `status_synced` alone, with `settled` existentially quantified
and unconstrained, says only that the outer copy holds some status of the merge's
shape -- which (G-shape) already gives. The two together say the reported status
is the merge of one the mirror is holding.

RT's conclusion is weaker than R2's: it does not name the status the user will
see. Its premise is the one a user can establish, by not editing the object.

`widget_round_trip_holds` (`composition/widget_inner_impl_reconciler.rs`) states
RT for a cluster running the pair and the inner implementation of section 2.5.
No member of the cluster of section 3.4 writes a mirror status, so RT is stated
over the cluster that runs the modelled implementation. RT is not a conjunct of `widget_sync_esr`, so it does not travel
through Welder composition and is in none of the multi-store theorems.

The premise of R1 and R2 says: the user has stopped editing the outer copy
(spec constant, not being deleted, same uid), and whoever was editing the
mirror's spec or deleting the mirror out of band has stopped. R2 also fixes the
outer copy's generation, which the status it promises is stamped with; R1 says
nothing about status and does not need it.
Convergence is promised for the time after the disturbances stop; during them
the guarantees still hold. The delete clause is stated so that it costs
nothing in the undisturbed case:

- a Delete the janitor sends satisfies it whenever the outer copy exists
  (`janitor_deletes_are_sound`);
- a stale Delete of an earlier mirror misses by uid;
- a Delete that arrives while no mirror of `outer` is at the key is free.

Only a Delete that would remove the live mirror is excluded, and one that
keeps arriving forever falsifies the premise rather than the conclusion.

These clauses are premises rather than clauses of `widget_sync_rely` on
purpose. A rely is unconditional and is discharged once, by Welder's
compatibility check, from the other controller's guarantee; a rely that
forbade spec edits or deletes of mirrors would exclude the very actor the
design wants to tolerate. The model has no users, so the clauses do constrain
other controllers, which is what a rely does; the temporal premise of R1 and
R2 is the only form in which "that actor has stopped" can be said. The
disturber (section 2.4) shows the premise is satisfiable and not vacuous
under the relaxed rely, and `janitor_deletes_are_sound` shows the janitor's
own Deletes satisfy it. R2's premise fixes the inner status instead of assuming
the inner implementation is live, so R2 holds for any inner implementation;
it fixes the inner conditions beside the mirrored fields because the outer
status is a function of both, and R2 promises the whole status. R3
is per object; R3s is the stable form and is the sync reconciler's promise
given R3. Neither R3 nor R3s needs a premise about deletes: the janitor's rely
already admits any Delete, and an extra delete of a mirror only helps them.

On many stores (`multi_cluster_outer_spec_stable`, `multi_cluster_outer_stable`)
the premise is read whole on the primary projection, where its delete clause is
vacuous because no mirror lives there, and the delete clause is read again on
the projection of the binding's cluster, where the mirror lives.

### 3.4 Composition

Both reconcilers are Welder controller specs
(`src/controllers/composition/widget_janitor_reconciler.rs`,
`widget_sync_reconciler.rs`). The janitor's ESR slot carries R3 together with
the safety fact `□janitor_deletes_are_sound`; its environment rely is D3 of its
own binding, `inner_releases_terminating_objects(k, b)`. The sync reconciler's
ESR is R1, R2 and R3s; its liveness dependency is the janitor's ESR; its partial
rely names the janitor; its environment rely is the conjunction of D3 over
`k.bindings`, `inner_releases_terminating_objects_all(k)`, read at the binding at
hand.
`compose_dep` composes the pair, and `widget_core_holds` proves `core` for the
cluster of any configuration -- the sync controller of a kind `k` and one janitor
per binding of `k` -- of which `widget_demo_core_holds` is the demo instance
(doc/widget_sync_fanout_design.md, section 5.1).

Welder proves nothing new here. It gives the closed statement about the
cluster running both controllers, with the janitor's ESR consumed rather than
assumed, and a mechanical check that each guarantee implies the other's rely.

The whole-repository composition (`src/controllers/composition/compose_all.rs`)
adds the Widget configurations to the cluster running the VReplicaSet,
VDeployment, VStatefulSet and RabbitMQ controllers: `core_holds_for` proves
`core` for the four controllers beside the sync controller and janitors of one
configured kind, `framework_and_kinds_core_holds` for the four beside the
controllers of a finite set of configured kinds, none of whose outer kinds is
one of the four framework kinds, and `core_holds` is the demo's instance. The Widget
controllers are composed first (`widget_fanout_core_holds` per kind, then
`widget_kinds_core_holds` over the kinds), so their liveness dependency is
discharged internally and the outer step is a plain `compose`. The
cross compatibilities are kind disjointness: the Widget controllers only send
requests to the model kinds of their own configuration (for the sync reconciler
this follows from `mirror_create_req`, whose Create is
`make_inner(outer).marshal()`), and the other four controllers only send requests
to Pods, PVCs, VReplicaSets and the RabbitMQ-managed kinds. The facts Verus does
not find on its own are that the four framework kind names differ and carry no
`@` (`framework_kind_names_ok`), from which no mirror kind of any configuration
is a framework kind (`widget_kinds_distinct_from_framework`); that each
configured outer kind is none of the four is a hypothesis, discharged for the
demo from its literals.

The pair's own instances exercise neither R2's premise nor D3, and D3 stays
unexercised: nothing writes finalizers, so its premise is never met and it holds
vacuously. That is by decision -- the inner controller is whatever the workload
cluster runs, the sync controller stays agnostic to it, and D3 is an assumption
about it, not a proof obligation. The echo controller in the testbed is an
unverified stand-in. Two separate instances add a third member with an empty ESR
and no rely: `widget_disturbed_core_holds` composes the disturber (section 2.4)
with the pair, and `widget_implemented_core_holds` the inner implementation
(section 2.5), whose status write is what R2's premise is about.

### 3.5 Assumptions

1. `cluster.init()` and `□cluster.next()`.
2. Weak fairness of the API server, both reconcilers, `schedule_controller_reconcile`, `disable_crash`, `disable_req_drop`, `disable_pod_monkey` and the built-in controllers. Read: the process stops crashing, lost responses stop, every API server stops failing requests.
3. Both kinds installed; both controller models registered under distinct ids.
4. The relies of 3.2 for every other controller id.
5. D3, and, for the round trip only, D4. R1, R2, R3 and R3s do not need D4.
6. Generation semantics as in section 5.1 on both real API servers (true for CRDs with the status subresource).
7. The hypotheses of the refinement in 2.2, and one outer cluster per inner cluster.
8. Operational: the inner namespace exists; CRD schema parity; the CRD is installed in the outer cluster whenever its API server answers; one replica; no mutating admission on the inner spec; the outer CRD declares the mirrored status fields, or sets `x-kubernetes-preserve-unknown-fields` on `status`, since a structural schema prunes what it does not declare.

## 4. Deployment shape

The deployment is the one `doc/widget_sync_fanout_design.md` describes in its
sections 1, 3.4 and 4; `deploy/widget_sync/README.md` has the manifests, the
flags and the operating procedures. In outline:

- One Deployment in the outer cluster, `replicas: 1`, `strategy: Recreate`,
  given its kinds as `--kind` flags.
- Outer RBAC: for each kind its plural (get, list, watch) and its status
  subresource (patch); `secrets` (get, list, watch) for the binding Secrets;
  `customresourcedefinitions` (get) for the shape check; `namespaces` (get) on
  `kube-system` for the outer cluster id; a Role in `default` for the
  crash-mode ConfigMap. Inner, per binding's credential: each kind's plural
  (get, list, watch, create, patch, delete) and the claim ConfigMap in
  `kube-system` (create; get by name).
- Bindings: one client pair per `<clusterName>-kubeconfig` Secret of type
  `cluster.x-k8s.io/secret`, validated before use, rebuilt when the Secret's
  `value` changes, dropped when it goes away.
- Watches: the outer objects of each kind (sync primary); per binding, the
  mirrors of each kind (janitor primary, and a same-name trigger stream for
  the sync controller).
- Requeue: a fixed 60 seconds after a reconcile that did not fail, and a
  per-object exponential backoff after one that did (10 seconds doubling to a
  cap of 5 minutes, reset when that object next succeeds; `build.md`). The
  remote clients have a short request timeout so a partition surfaces as a
  failed reconcile.
- The janitor pause gate: the ConfigMap `widget-sync-janitor` in the
  controller's namespace, shipped empty and mounted read-only at
  `/etc/widget-sync/janitor`; `JANITOR_PAUSE_FILE` points the binary at the
  key `pause` there. While the key exists the shim withholds every Delete
  (section 1.3); the README gives the pause and resume commands and the
  sequence to follow around a restore of the outer cluster.

The controller reports a usage error instead of exiting silently, sets a field
manager on every write, logs errors at warn level and tells a failed patch
`test` apart from other failures, rotates credentials through the binding
Secret, checks access per binding, and runs non-root with a startup probe on
the ready file, a security context and resource limits. A per-object backoff in
the shim's `error_policy` paces retries.

It emits no Events, sets no `lastTransitionTime`, does no leader election, and
has no deletion rate limit or dry-run mode. Mirrors carry no cluster identity;
the claim object of the fan-out design (its section 1.3) is what keeps two
bindings off one inner cluster.

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
modeled. The executable model implements both handlers
(`handle_patch_request`, `handle_patch_status_request`) as refinements of the
spec model's, with tests for a failed uid test, a failed generation test and a
no-op patch.

### 5.3 Cluster tag and routing

`ApiResource` and `DynamicObject` carry a `ClusterId`, `Primary` or
`Remote(ClusterRef)` with the binding's namespace and cluster name as data;
a wrapper type is bound to one cluster (`ClusterBound`) and its view kind is
the tagged kind. The shim holds the primary client and a map from `ClusterRef`
to a remote cluster's clients (`ClusterClients`), shared by every controller of
the process and changed while they run; a request to a `ClusterRef` with no
clients fails with `Timeout`, as one to an unreachable cluster does. It
routes each request by the tag of its
`ApiResource`, tags the objects it returns (and stamps list items, which carry
no type metadata of their own, with the listed resource's), and derives a
controller's primary watch cluster from its wrapper type. Two controllers can
run in one process.

### 5.4 Footprint

The framework changes under `src/kubernetes_cluster` are the multi-store model
and its refinement (`spec/multi_cluster.rs`, `proof/multi_cluster/`); the
data-driven twins of the generic invariants, for a synced kind
(`proof/synced_objects.rs`); the `keeps_identity` family and the uid facts
(`proof/api_server.rs`); installing a synced kind (`spec/install_helpers.rs`);
the generation rules and the JSON-patch handlers of 5.1 and 5.2
(`spec/api_server/state_machine.rs`); the Patch plumbing (`spec/message.rs`);
and two rules of temporal logic that `verus_temporal_logic` lacks
(`proof/temporal_rules.rs`). The remaining proof files gain the `Patch` and
`PatchStatus` arms of their case splits. `etcd_object_is_well_formed` records
that a custom resource carries a generation and a built-in kind does not, which
the no-op rule for an update carrying the stored object needs.

`step_compatible` and `inv` are opaque. The simulation carries both at every
position of an execution, and the quantifiers inside them would otherwise be
instantiated at every state the solver sees. A lemma that reads a conjunct of
`inv` reveals it, or asks for the conjuncts at one position
(`lemma_inv_parts_at`). The Widget pair's own proofs carry no solver budget.

## 6. Alternatives rejected

| Alternative | Why not |
|---|---|
| Finalizer on the outer copy for cleanup | "remove finalizer on NotFound" is irreversible under fault injection and under a CRD uninstall; deletion blocks on partitions |
| Native multi-store `ClusterState` | changes every `s.resources()` use and every `APIServerStep` case split in the repository; the multi-store model and refinement (section 2.2) give the same theorem without that |
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
| Step closures shared by both reconcilers' proofs | `widget_sync_controller/proof/predicate.rs` |
| Assumptions, invariant bundles, stable specs, phase I, the sync reconciler's layers | `widget_sync_controller/proof/liveness/spec.rs` |
| One step of the cluster at the mirror key and the outer copy | `widget_sync_controller/proof/liveness/api_actions.rs` |
| Termination of both reconcilers | `widget_sync_controller/proof/liveness/terminate.rs` |
| R1, R2, R3, R3s | `widget_sync_controller/proof/liveness/{sync_spec_proof,sync_status_proof,janitor_proof,cleanup_proof}.rs` |
| Store facts (uids, what each request leaves alone) and temporal rules the pair uses | `kubernetes_cluster/proof/{api_server,temporal_rules}.rs` |
| The disturber: model, guarantee, composition with the pair | `widget_sync_controller/model/disturber_reconciler.rs`, `proof/disturber.rs`, `composition/widget_disturber_reconciler.rs` |
| The inner implementation: model, guarantee, composition with the pair | `widget_sync_controller/model/inner_impl_reconciler.rs`, `proof/inner_impl.rs`, `composition/widget_inner_impl_reconciler.rs` |
| Welder specs and composition | `composition/widget_{janitor,sync,disturber,inner_impl}_reconciler.rs`, `composition/compose_all.rs` |
| Configured kinds composed with each other | `composition/widget_two_kinds.rs` |
| Multi-store model | `kubernetes_cluster/spec/multi_cluster.rs` |
| Refinement into the one-store model | `kubernetes_cluster/proof/multi_cluster/` |
| R1 to R3s on many clusters, for the pair beside admitted other controllers; the instances of the pair and of the pair with the disturber | `widget_sync_controller/proof/multi_cluster.rs` |
| R1 to R3s for every kind and binding of a whole deployment | `widget_sync_controller/proof/multi_cluster_kinds.rs` |
| Binaries, manifests, testbed, e2e | `src/bin/`, `deploy/widget_sync/`, `tools/two-cluster-test.sh`, `e2e/src/widget_sync_e2e.rs` |

Full-repository verification (`cargo verus verify --lib`) is the
`full-verification` job of `.github/workflows/ci.yml`, run on every push
after a plain `cargo build --lib`.

## 8. Future work

#49 is the register of what the formal work does not cover, and which of those
gaps need a decision before code. Open besides it: the e2e checks that need the
kind testbed (#14), and the pass that makes the branch reviewable upstream
(#16).

Out of scope by decision: a verified inner controller, so the sync controller
stays agnostic to the inner side and D3 remains an assumption; with it, the
owner-less transactional update that composing against one would need; and a
spec projection for inner-owned fields, since no spec field is owned by the
inner side.

An out-of-band edit that strips a mirror's identity stays excluded: the design
refuses to recover from it.
