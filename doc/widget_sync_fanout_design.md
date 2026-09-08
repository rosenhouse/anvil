# Widget sync controller: fan-out to many inner clusters, generic over kinds

This document is the design for issues #15 (many outer namespaces, each
with its own inner cluster) and #20 (controllers generic over kinds,
instantiated at boot). It extends `doc/widget_sync_design.md`, which
describes the single pair as it is verified today, and it records the
decisions of the project owner of 2026-09-08. Sections 1 to 4 are the
design; section 5 is what is proved and what is assumed once the work
lands; section 6 is the work breakdown and the order it is done in.

## 0. Summary

- The real system is Cluster API: the outer cluster is a management
  cluster whose namespaces hold zero or more workload (inner) clusters.
  Every parent object names its inner cluster, immutably, through either a
  spec field guarded by an immutability CEL rule on its CRD or its own
  `metadata.name`. The pair (namespace, cluster name) is a **binding**; the
  inner cluster of a binding is reached through the Secret
  `<clusterName>-kubeconfig` in that namespace, the Cluster API convention.
- The controller runs for a list of **kinds** given at boot. Each kind's CRD
  is read at boot and checked against the **shape** the controller needs
  (section 2.2); a kind that does not fit is refused. Spec and status are
  otherwise opaque: the spec is copied verbatim, the status is mirrored
  verbatim except for `observedGeneration` and `conditions`.
- A **claim** object in each inner cluster, created on first contact,
  records which binding owns it; a second binding pointing at a claimed
  cluster (a copied kubeconfig) is refused. This is what makes "one outer
  binding per inner cluster", an assumption of the proofs, true in practice,
  and it replaces the parent-cluster annotation on mirrors that #10
  proposed.
- In the model, a kind and a binding are data. The one-store model keeps
  one model kind per (kind, side): `widgets.anvil.dev` for the outer copy,
  `widgets.anvil.dev@<namespace>/<clusterName>` for the mirror in that
  binding. The sync reconciler is one controller per kind, routing each
  object by its cluster selection; the janitor is one controller per (kind,
  binding). R1, R2, R3 and R3s are stated with the kind, the selector and
  the bindings as parameters; distinctness of the model kinds and their
  assignment to sides are hypotheses.
- The two-store refinement stays at one remote side and is applied per
  binding. What that leaves unstated is section 5.3; the (n+1)-store
  refinement is a follow-up.

## 1. Bindings and cluster selection

### 1.1 The cluster selector

A configured kind carries a **cluster selector**, one of:

- `field:<path>`: a string field of the spec, for example
  `spec.clusterName`. The CRD must declare the field as a required string
  and guard it with an immutability rule, `x-kubernetes-validations:
  [{rule: "self == oldSelf"}]` on the field, or the equivalent rule naming
  the field on the object that holds it or on `spec`. The controller reads
  the CRD at boot and refuses the kind without the rule; it requires the rule
  in every *served* version of the CRD, since an update sent through another
  served version is an update.
- `name`: the object's `metadata.name` is the cluster name. This is the
  shape of Cluster API's `Cluster` object itself, and it is immutable by
  construction.

No templating, no other metadata field. `cluster_of(obj)` is the selected
cluster name, `None` when the field is missing, which the boot check makes
impossible for stored objects but the model does not assume.

Immutability is what lets the parent uid on a mirror stand alone as the
mirror's identity: a parent uid is bound to one cluster for the life of the
object, so a mirror in cluster `c` naming parent uid `u` is either the live
mirror of `u` or stale, never the mirror of `u` "before it moved". The
janitor nevertheless also checks the cluster (section 3.3), so that the
janitor's *decision* does not depend on the CEL rule; the rule's job is to
keep an edit from tearing down and rebuilding a workload cluster.

The proofs do lean on the rule in one place, which was not foreseen when
this was written. The janitor's per-binding delete-soundness invariant says
that a listed outer object stays selected for the binding it was seen in;
that is stable only because the installed type's `valid_transition` — the
model's reading of the CEL rule (section 2.3) — preserves `cluster_of`
across an update. `Cluster::lemma_api_server_step_preserves_cluster_of`
(`kubernetes_cluster/proof/synced_objects.rs`) is that step. So a kind
configured with a `field` selector whose CRD does not carry the immutability
rule breaks the invariant, not merely the operational guarantee. For a
`name` selector nothing is needed: `metadata.name` cannot change.

### 1.2 Bindings and their kubeconfigs

A **binding** is a pair `b = (namespace, clusterName)`. Its inner cluster is
reached through the Secret `<clusterName>-kubeconfig` in `namespace`, key
`value`, a self-contained kubeconfig (certificate data or an inline
token). This is the Cluster API convention, so a management cluster
provides the Secret without any help from us; the convention is taken whole,
so the Secret must also be of type `cluster.x-k8s.io/secret` and carry the
label `cluster.x-k8s.io/cluster-name`, whose value is the cluster name and
must agree with the name minus the suffix. A Secret merely named
`<something>-kubeconfig` is not a binding.

The controller watches the labelled Secrets in all namespaces (the label is a
selector on the watch; the type and the label's value are checked on each
event) and keeps one pair of clients (requests, watch; section 5.3 of the main
design) per binding whose Secret exists. A Secret that changes (a rotated credential; Cluster API
rewrites the Secret) rebuilds the binding's clients; a Secret that goes
away drops the binding, its janitors included. The `tokenFile` mechanism of
the single-pair deployment is not used: a Cluster API kubeconfig is inline
and rotation is the Secret changing.

A kubeconfig is code as much as it is a credential — `exec`, `auth-provider`,
`tokenFile`, `proxy-url`, `insecure-skip-tls-verify` all direct the client
library to run or read or trust something — so before a client is built the
document is held to the shape a Cluster API kubeconfig has: exactly one
cluster, user and context, an `https://` server, credentials as data and never
as a path or a command, no proxy and no skipped verification (`validate_kubeconfig`,
`shim_layer::bindings`); whoever may create such a Secret in a namespace
otherwise decides what the controller does there. A Secret the check refuses is
logged with the rule it broke and its binding stays unbound until the Secret
changes.

A parent whose binding has no Secret, or whose Secret does not parse, has no
entry in the process's client map, so it is not one of the bindings a reconcile
serves: the sync reconciler reports `Synced=False/InnerUnreachable` and ends
without addressing the inner side at all (section 3.2). The shim's answer for a
request to an unbound cluster, `Timeout`, which the reconciler reports the same
way, stays as the fallback for anything that does reach it -- a binding dropped
between the snapshot and the request, and every janitor request, since a janitor
does not consult the binding set. The model covers the fallback as `drop_req`.
A **refused** binding (section 1.3) is bound, so it *is* in the set a reconcile
serves: its requests are sent and the shim answers them `Forbidden`, which is
what makes its parents report `Forbidden` with `Stalled=True` rather than
`InnerUnreachable`. The deploy README says that a missing kubeconfig Secret
reads as `InnerUnreachable`.

### 1.3 The claim

On first contact with a binding's inner cluster the controller creates, in
the inner cluster, a ConfigMap `anvil-sync-claim` in namespace
`kube-system` with the data

```
owner:       <outer cluster id>
namespace:   <binding namespace>
clusterName: <binding cluster name>
```

The create is plain (no precondition beyond the name): `AlreadyExists`
means the cluster is claimed, and the existing ConfigMap is read and
compared. A match is the binding's own claim (a controller restart, a
re-created Secret); a mismatch means another binding, of this outer
cluster or another, owns the inner cluster. A claimed cluster is a
**refused binding**: the shim answers every request of the binding with
`Forbidden`, so its parents report `Synced=False/Forbidden` with
`Stalled=True`, and the janitors of the binding are never started. A
refused binding is re-checked at the Secret's next change and at a fixed
interval, so releasing the claim (deleting the ConfigMap by hand, which is
an operator's decision) recovers it. The deploy README documents the claim,
the log line and the recovery.

The **outer cluster id** is the uid of the outer cluster's `kube-system`
namespace, the de facto stable cluster identity, read once at boot; an
operator may override it with a flag, for a restore that recreated the
namespace.

The claim is not in the model. It is the operational mechanism that
discharges the model's assumption that each binding is its own store
(section 5.2), in the way the janitor pause gate discharges the restore
scenario: outside the verified code, with a plain argument for why it
cannot violate anything the proofs say. The claim only ever withholds
requests; a refused binding is a binding whose every request fails, which
the model covers.

What the claim does not cover: two outer clusters with the same
`kube-system` uid (a cloned management cluster). The override flag exists
for that case; the README says so.

### 1.4 Access check and readiness

The startup access check of the single pair (one cluster-wide
`SelfSubjectAccessReview` per verb, exit on any failure) becomes a
per-binding check at bind time, namespaced to the binding's namespace,
that never exits the process: a denied verb or an unreachable inner
cluster marks the binding degraded, is logged, and is retried with
backoff; while degraded the binding's requests are answered `Timeout`
(unreachable) or `Forbidden` (denied). The readiness file is created once
the boot checks of section 2.2 have passed and the outer watches are
running; one bad binding cannot take down the others.

## 2. Kinds

### 2.1 Configuration

The binary takes the kinds at boot:

```
widget_sync_controller run --kind anvil.dev/v1/Widget:field:spec.clusterName --kind anvil.dev/v1/Gadget:name
```

`<group>/<version>/<Kind>:<selector>`, repeated. Discovery in the outer
cluster resolves the plural and confirms the kind is served and
namespaced. `export` prints the demo CRDs.

### 2.2 The shape a kind must have

The controller reads and writes exactly these fields of an object:

| Field | Read or written | Requirement on the CRD |
|---|---|---|
| `metadata` | read; the mirror's name, namespace, label and annotation written on create | namespaced scope |
| `spec` | copied verbatim outer to inner; the selector field read when the selector is `field` | the selector field, when used: required string with the immutability rule |
| `status.observedGeneration` | read on the inner copy; written on the outer copy | integer |
| `status.conditions[]` | read on the inner copy (`Ready`, `Stalled`); written on the outer copy (`Synced`, `Ready`, `Stalled`) | array of objects with `type` (string, required), `status` (string, required), `reason`, `message` (strings), `observedGeneration` (integer) |
| every other status field | mirrored verbatim inner to outer while `Synced` | none |
| the status subresource | | enabled, so `metadata.generation` follows the spec |

At boot the controller fetches each kind's CRD in the outer cluster and
checks the table. The status rows are required as declarations of those
types even on a status that carries `x-kubernetes-preserve-unknown-fields`:
that setting keeps a field the API server does not know, it does not check
it, and the installed type of the kind (section 2.3) says that every stored
status unmarshals — which, for what other writers store, only the CRD's
schema makes true. A kind that fails any row is refused with a usage
error naming the row. Inner clusters are not checked for schema parity
beyond serving the kind with the status subresource (discovery at bind
time); parity stays an operational assumption, as today.

Assumed for this pass: fields are not removed from a CRD while the
controller runs, so the check, once true, stays true. Adding fields is
fine. A later pass can watch the CRDs and stop a kind whose shape breaks.

This is the structural subtype: the controller and its proofs are about
objects of this shape, and any CRD that has the shape can be reconciled.

### 2.3 The model of the shape

The typed views of the single pair (`OuterWidgetView`, `InnerWidgetView`,
with `count`, `message`, `ready`, `observedCount`) are replaced by one view
of the shape, with the kind as data:

```
SyncedObjectView { kind: Kind, metadata: ObjectMetaView, spec: Value, status: Option<SyncedStatusView> }
SyncedStatusView { observed_generation: Option<int>, conditions: Option<Seq<ConditionView>>, rest: Value }
```

`Value` is the model's opaque marshalled value. `spec` is kept as the raw
`Value`: copying it is equality, and no fact about its contents is needed
beyond the selector field. The status is the extracted fields plus `rest`,
the mirrored remainder, which is what `π` of the main design projects to.

The trusted boundary of the shape is a small set of uninterpreted spec
functions with round-trip axioms, in the style of the framework's
`marshal_spec`/`unmarshal_spec`:

```
unmarshal_status(v: Value) -> Result<Option<SyncedStatusView>, _>      // the shape check on a status value
marshal_status(s: Option<SyncedStatusView>) -> Value
   axiom: unmarshal_status(marshal_status(s)) == Ok(s)
spec_field(v: Value, path: Seq<StringView>) -> Option<StringView>      // the selector field
unmarshal(kind: Kind, obj: DynamicObjectView) -> Result<SyncedObjectView, _>
   := if obj.kind != kind then Err else match unmarshal_status(obj.status) { Ok(s) => Ok(SyncedObjectView { kind, metadata: obj.metadata, spec: obj.spec, status: s }), Err => Err }
marshal(o: SyncedObjectView) -> DynamicObjectView
   := DynamicObjectView { kind: o.kind, metadata: o.metadata, spec: o.spec, status: marshal_status(o.status) }
```

`unmarshal` and `marshal` are open definitions over the two trusted
functions, so `marshal_preserves_metadata`, `marshal_preserves_kind` and
the round trip are proved, not assumed. The view does not implement the
framework's `ResourceView` trait, whose `kind()` is a static function of
the type; the reconciler models are written over `SyncedObjectView`
directly, and the reconcile models are built from data (section 3.1).

The exec twin is a wrapper `SyncedObject` over `kube::api::DynamicObject`
plus the cluster tag, whose `unmarshal`, `marshal`, `has_kind` and
`api_resource` are `external_body` with the same postconditions as
today's wrapper macro, restated over the **registry** (section 2.4)
instead of a compiled type. The status accessors and `outer_status_for`
are `external_body` over `serde_json::Value`, as they are today over the
typed status.

The trusted surface of the shape is therefore no longer under the
controller, and the exec hygiene script pins it where it is, file by
file (`doc/widget_sync_design.md`, section 3, lists the items):

- `kubernetes_api_objects/spec/synced_object.rs`: the uninterpreted
  `unmarshal_status`, `marshal_status`, `spec_field` and
  `status_rest_ok`, and the axiom `marshal_status_preserves_integrity`.
- `kubernetes_api_objects/spec/model_kind.rs`: nothing — `model_kind`
  and its injectivity are proved, and the hypotheses injectivity rests
  on are checked on the exec side (boot check and Secret watch).
- `kubernetes_api_objects/exec/synced_object.rs`: the wrappers above,
  the free `marshal_status` and `cluster_of_dynamic`, `empty_rest`, and
  the two equality decisions `RawValue::eq` and `SyncedStatus::eq`,
  trusted as *iffs* over the view.
- `kubernetes_api_objects/exec/registry.rs`: `crd_name` and
  `api_resource`, the routing the model trusts.
- `widget_sync_controller/trusted/`: `outer_status_for`, the three
  `Marshallable` instances of the reconcile states, and the
  uninterpreted `default_status_rest()`.

The installed type of a kind of the shape is a function of the schema, not
of a type:

```
synced_installed_type(spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector) -> InstalledType
   unmarshallable_spec:   |v| true
   unmarshallable_status: |v| unmarshal_status(v) is Ok
   valid_object:          |obj| spec_ok(obj.spec)
   valid_transition:      |obj, old| cluster_of(selector, obj) == cluster_of(selector, old)     // the CEL rule
   marshalled_default_status: || marshal_status(None)
```

`spec_ok` is the CRD's schema, a parameter; the immutability rule is the
kind's `valid_transition`. The theorems take the outer kind and each
binding's inner kind to be installed with the same `spec_ok` and selector,
which is schema parity stated as a hypothesis.

### 2.4 The registry

Exec side, trusted. Built at boot from the configured kinds and the
discovered `ApiResource`s. It is the one place that ties a runtime kind and
cluster to a model kind:

```
model_kind(k: KindName, cluster: ClusterIdView) -> Kind
   Primary          => CustomResourceKind(k)
   Remote(ns, name) => CustomResourceKind(k + "@" + ns + "/" + name)
```

with `k` the CRD name `<plural>.<group>` (`widgets.anvil.dev`). Since `k`,
`ns` and `name` are DNS names and contain no `@`, `model_kind` is
injective; the lemma is proved once on the spec side
(`kubernetes_api_objects/spec/model_kind.rs`: `lemma_model_kind_injective`,
`lemma_model_kind_distinct`, `lemma_remote_kind_name_is_not_primary`) and is what
every distinctness hypothesis of the theorems is discharged with, for *any*
configuration and not only a concrete one.

"No `@`" is a hypothesis of those lemmas, and it is a real hypothesis of the
theorems too: `sync_kind_ok(k)` (the CRD name is free of `@`, and the outer kind
is the primary model kind of that name) and `binding_ok(b)` (the namespace free
of `@` and `/`, the cluster name free of `@`), in
`widget_sync_controller/trusted/spec_types.rs`. The boot checks are what
discharge them in the deployment: `check_kind_name`
(`shim_layer/crd_shape.rs`), run on each configured kind's CRD name before
anything else, refuses a name carrying `@`, and `binding_of_secret`
(`shim_layer/bindings.rs`) refuses a Secret whose namespace or cluster name
carries `@` or `/`. A configuration that reaches the running controller has
therefore already been checked for exactly what the proofs assume, and the demo
configuration discharges them from its literals in one line.

`ClusterId` becomes `Primary | Remote(ClusterRef { namespace, name })`, a
value; the wrapper's `has_kind(obj)` compares the object's tag and kube
kind against the registry entry, as it does today against the compiled
tag. The shim routes each request by the tag of its `ApiResource` to the
binding's client, and stamps the objects it returns with the tag of the
client they came from. `DynamicObject::kind()` stays out of controller
code (#19).

## 3. The controllers

### 3.1 Reconcile models from data

The cluster model's `ReconcileModel` is a struct of a kind and four spec
closures; the framework's `installed_reconcile_model::<R, S, K, ...>()`
is only an adapter from a type-level reconciler. The pair's models are
built directly:

```
widget_sync_controller_model(k: SyncKind) -> ControllerModel        // kind: k.outer_kind
widget_janitor_controller_model(k: SyncKind, b: Binding) -> ControllerModel  // kind: inner_kind(k, b)
SyncKind { outer_kind: Kind, name: KindName, selector: ClusterSelector, bindings: Set<Binding> }
inner_kind(k, b) := model_kind(k.name, Remote(b))
```

(`model/install.rs`. `bindings` is the finite set of section 3.2, added after this
was first written; section 5.2 says what it is for.)

The exec reconcilers carry the same data (`SyncReconciler { kind, registry
entry }`), and their conformance proofs relate them to the model with the
data as a parameter. The exec `Reconciler` trait is static today; a
`DynReconciler` variant with `&self` is added to the framework. The shim keeps
two entry points rather than one overloaded `reconcile_with`:
`reconcile_with` for a static `Reconciler` and `reconcile_dyn_with` for a
`DynReconciler` built per reconcile from a factory. What they share is the
`ReconcileDriver` trait and `run_reconcile`, the one loop; `StaticDriver` and
`DynDriver` are its two implementations
(`shim_layer::controller_runtime`).

### 3.2 The sync reconciler

One controller per kind, triggered by outer objects of that kind. Its
reconcile is the one of the main design, section 1.2, with two changes:

- At `Init`, `cluster_of(outer)` is read. `None` (the selector field is
  missing, which the boot check rules out for stored objects) is reported
  as `Synced=False/Rejected`, a permanent outcome, and the reconcile ends.
- Still at `Init`, the binding `binding_of(k, outer)` is looked up in the
  finite set `k.bindings` the reconciler was built with. A binding outside the
  set is reported as `Synced=False/InnerUnreachable` -- the failure-reporting
  path of any other failed request: `outer_status_for(g, outer.status,
  Failed(InnerUnreachable))`, a PatchStatus testing the outer copy's uid and
  generation, then `Error`, so the shim requeues -- and no request is sent to
  the inner side. This is what bounds the mirror kinds the model can write
  (section 5.2). A refused (claimed) binding stays in the set, because it is
  bound: its requests are sent and the shim answers them `Forbidden`.
  The one branch that would write a mirror, the Create after a `NotFound`, is
  guarded by the same test; that guard is unreachable at run time (Init already
  refused) and is there so that every Create the model emits names a mirror kind
  of `k.bindings` for *any* triggering object, which is what `models_ok` of the
  two-store refinement asks (section 5.2).
- The mirror key is `inner_key(k, outer) = (inner_kind(k, binding_of(k, outer)), ns, name)`,
  where `binding_of(k, outer) = (outer.metadata.namespace, cluster_of(outer))` --
  the mirror kind carries the namespace as well as the cluster name, because a
  binding is the pair. The Get, Create and Patch of the mirror carry that kind,
  and the shim routes them to the binding `binding_of(k, outer)`.

Exec side, `k.bindings` is a snapshot: the dynamic runners hold a *factory*
(`shim_layer::controller_runtime::ReconcilerFactory`) rather than a reconciler
value, and build the reconciler at the start of each reconcile from
`ClusterClients::remote_refs()`, the bound clusters of the moment, refused ones
included. The reconciler value, and so the model it conforms to, is then fixed
for the whole of that reconcile; no time-varying view enters the proofs.

The spec written on the mirror is the outer `spec` value; the outer status
is `outer_status_for(g, inner status, outcome)` as today, with `rest`
mirrored in place of the named fields.

### 3.3 The janitor

One controller per (kind, binding), triggered by mirrors of the binding's
inner kind. Its reconcile is the one of the main design, section 1.3, with
one change: the parent is listed when some listed outer object has the
mirror's parent uid **and** `cluster_of` equal to the binding's cluster
name. Under the CEL rule the second conjunct is redundant; without it the
janitor of the old cluster collects the mirror of a parent that moved.

R3's premise is the other side of that asymmetry: `parent_absent` says no outer
copy of the kind carries the mirror's parent uid, with nothing said about which
cluster such a copy would select, while the janitor's decision does check the
cluster. So there is a state R3 does not speak about and the janitor still acts
on: a stored outer copy with the mirror's parent uid that selects *another*
cluster, which the janitor reads as an absent parent and collects. Under the CEL
rule that state cannot arise -- the parent uid was issued for one object, and
that object's `cluster_of` never changes
(`Cluster::lemma_api_server_step_preserves_cluster_of`), so an outer copy with
that uid selects the binding it was created in -- and a uid is never reissued,
so no later object carries it either. Without the rule the janitor collects a
mirror whose parent has moved away, which is what one wants operationally; it is
simply not the case R3 is stated for. The delete-soundness invariant, which does
carry the cluster conjunct, is the statement that covers it
(`doc/widget_sync_design.md`, section 2.2).

A binding's janitors start when the binding is bound and its claim is
held, and stop when the Secret goes away. A mirror in a cluster whose
Secret is gone is unreachable by definition; nothing is said about it.

### 3.4 The binary and the shim

The binary:

1. Parses the kind flags; discovers each kind in the outer cluster; reads
   each CRD and runs the shape check (section 2.2); exits with a usage
   error on the first failure.
2. Reads the outer cluster id (section 1.3).
3. Starts one kube-runtime controller per kind on
   `Api<DynamicObject>` (`Controller::new_with` with the discovered
   `ApiResource`), the sync reconciler for that kind.
4. Starts the binding manager: a watch on Secrets in all namespaces, name
   suffix `-kubeconfig`. Per binding: build the clients, run the access
   check, create or verify the claim, start the janitors (one
   kube-runtime controller per kind on the binding's watch client, with a
   graceful-shutdown token), and register the clients with the sync
   controllers' client map. On change: rebuild the clients in place. On
   delete: stop the janitors, drop the clients.
5. Creates the readiness file.

The same-name secondary watch of the sync controller (a latency
optimization) is per binding as well, started with the binding's janitors
and mapped to the outer kind's controller.

The client map is `RwLock<HashMap<ClusterRef, RemoteClients>>` shared by all
controllers of the process, replacing the two-slot `ClusterClients`;
`client_for(api_resource)` looks up the tag. The janitor pause gate and the
fault-injection hook are unchanged; both act per process.

## 4. Deployment and test

- Outer RBAC adds `secrets` get, list, watch (cluster-wide: bindings live in
  any namespace), `customresourcedefinitions` get, and `namespaces` get on
  `kube-system`; the kind rules are generated per configured kind
  (`<plural>` get, list, watch; `<plural>/status` patch).
- Inner RBAC, per binding's credential: `<plural>` get, list, watch, create,
  patch, delete for each kind, and `configmaps` get and create in
  `kube-system`. The demo's testbed makes a service-account kubeconfig with
  these rights; a Cluster API workload cluster's kubeconfig is admin.
- The demo keeps `Widget` (selector `field:spec.clusterName`, the CRD gaining
  the field with its CEL rule) and adds `Gadget`, a kind with a different
  spec (`selector: name`) to show genericity. The echo controller becomes
  generic: for each kind it is given, it stamps `observedGeneration` and a
  `Ready` condition.
- The testbed and the e2e run three kind clusters: `outer`, `inner-a`,
  `inner-b`, with Secrets `a-kubeconfig` and `b-kubeconfig` in namespace
  `default`. Scenarios added to the nine of today: two Widgets in one
  namespace bound to different clusters; a Gadget named `a`; a Secret in a
  second namespace copied from `a-kubeconfig`, whose parents report
  `Forbidden` while the mirrors of namespace `default` survive; a Secret
  removed and re-added; a Secret whose `value` is replaced by an equivalent
  kubeconfig with other bytes, after which the bound objects keep their
  mirrors and a new edit still propagates; the claim of a bound binding
  deleted by hand and written again at the next re-check; a kind refused at
  boot for a missing rule.

## 5. What is proved, what is assumed

### 5.1 Theorems

The statements of the main design, section 3.3, with parameters:

- R1, R2: `∀ k: SyncKind, outer: SyncedObjectView` with `outer.kind == k.outer_kind`
  and `binding_of(k, outer) ∈ k.bindings` (an outer copy of a binding the
  reconciler does not serve is refused, section 3.2), under the sync controller
  for `k` and the janitors for `k` and every binding of the outer's namespace
  and `cluster_of(outer)`. The premise is carried by the ESR's own guard: the
  per-binding conjuncts of `widget_sync_esr(k, bs)` are stated for `b ∈ bs`, and
  `sync_membership` ties `bs` to `k.bindings`.
- R3, R3s: `∀ k, b, key, parent uid`, under the janitor for `(k, b)`.
- The janitor's delete soundness, per `(k, b)`.
- Composition: for one kind `k` and a finite set of bindings `B`, the
  controller set `{sync_k} ∪ {janitor_{k,b} | b ∈ B}` satisfies `core`; the
  sync controller's liveness dependency is the conjunction of the janitors'
  ESRs, discharged by composing the janitors one binding at a time. Kinds
  compose with each other and with the four other controllers of the
  repository by kind disjointness, exactly as the pair does today.
  `widget_two_kind_core_holds` (`composition/widget_two_kinds.rs`) is the first
  of those: two kinds `k1`, `k2` with `k1.outer_kind != k2.outer_kind` (and
  `sync_kind_ok` of both) compose, because each side's guarantee already implies
  the other's relies -- a sync controller touches only its own outer kind and its
  own mirror kinds, a janitor only its own outer kind (a List) and its own mirror
  (a Delete). The disjointness of the mirror kinds is
  `lemma_kinds_of_distinct_configurations`, and it holds for *every* binding, not
  only the configured ones, because the relies quantify over `is_inner_kind`.
  Neither side has a liveness dependency left, so this is plain `compose`.
  `two_kind_demo_core_holds` instantiates it for `widgets.anvil.dev` and
  `gadgets.anvil.dev` in one cluster. `core_holds_for`
  (`composition/compose_all.rs`) is the other: the four controllers of the
  repository beside the sync controller and janitors of any configured kind whose
  outer kind is none of the four framework kinds.

  `widget_fanout_core_holds` is that statement, for any `B` and any
  assignment `ids` of janitor ids that is injective on `B` and misses the sync
  controller's. It is proved in two moves. `widget_janitors_core_holds`
  composes the janitors of a subset of `B` one binding at a time, by induction
  on the subset's size (`Set` is finite, so `remove` decreases `len`); every
  step is Welder's `compose`, since no janitor has a liveness dependency, and
  the compatibility of each step is one fact, that a janitor's guarantee -- a
  List of outer copies and a Delete of its own mirror -- implies every other
  janitor's rely, which constrains only Creates and Updates of mirrors
  (`janitor_guarantee_implies_janitor_rely`). The union is then composed with
  the sync controller by `compose_dep`: the janitors' ESRs, read off the
  members of the union, are exactly `janitors_esr(k, B, ids)`, and recovering
  the binding of a member's id is where the injectivity of `ids` is used.
  `widget_pair_core_holds` is the singleton instance of it -- a call plus set
  extensionality, since the janitors' core set of a one-element binding set has
  the one janitor's id as its only member -- and it is what
  `composition/widget_disturber_reconciler.rs` puts beside the disturber.
  `widget_core_holds` closes the statement for the cluster of *any*
  configuration: `widget_cluster_for(k, spec_ok, sync_id, ids)` installs
  `k.outer_kind` and `inner_kind(k, b)` for each `b ∈ k.bindings` and runs the
  sync controller at `sync_id` and one janitor per binding at the ids an
  injective `ids` gives, under `sync_kind_ok(k)`, `binding_ok` of each binding,
  and `ids_ok`. `widget_demo_core_holds` and `widget_fanout_instance_core_holds`
  are two applications of it: the demo's one binding, and a two-binding cluster
  with the bindings `default/inner` and `default/second`, a janitor for each and
  the three model kinds they need installed.

Hypotheses added to the theorems, in place of the lemmas that today prove
them from the literal strings. `sync_kind_ok(k)` and `binding_ok(b)` are real
hypotheses of every statement that needs distinctness -- of the general theorems
and of the closed ones alike, since the closed ones are now stated for any
configuration. The boot checks discharge them for a running controller
(`check_kind_name` and `binding_of_secret`, section 2.4); the demo configuration
discharges them from its literals in one line, and that is the only thing the
literals are used for.

- the model kinds of the configuration are pairwise distinct custom kinds
  (discharged by the injectivity of `model_kind`:
  `lemma_model_kind_distinct`, `lemma_inner_kind_injective`,
  `lemma_kinds_of_distinct_configurations`, never by the length of a name);
- every kind is installed with `synced_installed_type(spec_ok, selector)`,
  the same `spec_ok` and selector for the outer kind and each of its inner
  kinds (schema parity);
- the sync controller of `k` and the janitors of `k` are registered under
  distinct ids; the relies of section 3.2 of the main design hold of every
  other id, now stated per inner kind.

### 5.2 Two stores, per binding

The two-store refinement is applied per binding: for binding `b`, the
remote kinds are the inner kinds `{inner_kind(k, b) | k}`. The sync
controller and the janitors of the other bindings appear on the primary
side as other controllers; they meet the refinement's hypotheses 1 to 3
(they are the same reconcilers, whose commutation lemmas are proved once
with the data as parameters). R1 to R3s and the delete soundness are then
read on two-store executions per binding, as today.

Three hypotheses the fixed pair did not need appear here. First, the folded
one-store cluster installs the mirror kind of every binding of `k.bindings`,
not only of `b`: the sync controller of `k` serves all of them, so a Create it
sends for an outer copy of another *served* binding must still name a known kind
(`TwoCluster::request_ok`, which `models_ok` asks of the reconcile model as a
function, for every object it could be triggered by, not only the stored ones).
The mirrors of the other served bindings then live on the primary side, which is
what the paragraph above says. Second, the selector of `k` must be a *field* of
the spec, not `metadata.name`: the refinement asks that the API server's
validation not read metadata (`installed_types_ignore_metadata`), and the
immutability rule of a `name` selector reads `metadata.name`. Third, the theorem
is read for one binding `b ∈ k.bindings` at a time: the ESRs it consumes and the
D3 it assumes are `b`'s, only `b`'s mirrors are remote, and the janitors of the
other bindings enter as other controllers, which is what "per binding" means.

`widget_two_cluster_theorem` (`widget_sync_controller/proof/two_cluster.rs`)
is that statement, for any cluster meeting the hypotheses, and it is proved.
R3s is read there with its one-store premise, `bound_parent_absent`, which
fixes the mirror key's kind; the two-store delete-soundness clause is read
with the conjuncts `parent_absent_forever` has since the port (the parent is
an outer copy of `k` that selects `b`'s cluster), not over every stored
object.

**Closed, and it was vacuous before.** The first hypothesis above used to
quantify over *every* binding: `all_inner_kinds_installed` asked that
`model_kind(k.name, Remote(ns, clusterName))` be installed for every pair
(namespace, cluster name). Those kinds are infinitely many -- `remote_kind_name`
is injective in the cluster name -- and `InstalledTypes` is vstd's `Map`, whose
domain is a finite `Set`, so no `Cluster` value satisfied the hypothesis. Between
the fan-out port (commit `7eebc12`) and this change, every statement of
`proof/two_cluster.rs` was therefore vacuous rather than merely missing an
instance, and the fixed pair's closed statements
(`widget_instance_two_cluster_theorem`, `widget_disturbed_two_cluster_theorem`)
could not be restated.

The remedy is the finite binding set of section 3.2. The sync reconciler's model
is parameterized by `k.bindings`; an outer copy whose binding is outside the set
is refused at `Init` with `Failed(InnerUnreachable)`, before any request, and the
Create of a mirror carries the same guard, so the mirror kinds the model can
write are exactly `{inner_kind(k, b) | b ∈ k.bindings}` -- as many as the
bindings, and `Set` is finite. `all_inner_kinds_installed` is now that finite
conjunction, `widget_cluster_with_others` and `widget_pair_cluster` take `bnd ∈
bs` (rather than pinning `bs` to `{bnd}`) with `k.bindings == bs` carried by
`sync_membership`, and the closed statements are back:
`lemma_widget_instance_is_pair_cluster` and `widget_instance_two_cluster_theorem`
for the cluster of `composition/widget_sync_reconciler.rs`, and
`lemma_widget_disturbed_instance_is_cluster_with_others` and
`widget_disturbed_two_cluster_theorem` for the one with the disturber. Those
concrete clusters install exactly `k.outer_kind` and `inner_kind(k, b)` for the
one binding they serve, and they are the satisfiability witness for every
hypothesis of the general theorem.

The three alternatives this rules out, recorded because they were the other ways
to close it: an `InstalledTypes` with an infinite domain (vstd's `IMap`), which
changes `Cluster` and every controller's concrete cluster; a `TwoCluster` whose
`request_ok` tolerates a Create of an uninstalled kind, which needs
`installed_types_ignore_metadata` and `installed_types_coherent` for every name
rather than every installed one (a `Map` says nothing about indexes outside its
domain, so a concrete map cannot provide that either); or narrowing the
hypothesis to a finite set of bindings without changing the model, which does not
work by itself, since `models_ok` quantifies over every object a reconcile could
be triggered by and the namespace of an outer copy is unbounded.

### 5.3 What that leaves unstated

The per-binding two-store theorem for `b` merges every other inner cluster
into the outer cluster's store, with one uid counter. It therefore never
considers an execution in which two inner clusters have independent
counters at the same time. Nothing the pair does compares uids across two
inner clusters: the sync controller compares an outer uid with the
annotation on the mirror of one binding, and the janitor of a binding
compares its mirror's annotation with outer uids. So no behaviour of the
controllers is uncovered; what is missing is one theorem about the
(n+1)-cluster system as a whole, which would follow from an (n+1)-store
refinement. That refinement generalizes `TwoCluster` to a family of stores
indexed by cluster id and redoes `kubernetes_cluster/proof/two_cluster/`
(about 4,000 lines) with the side as an index. It is filed as a follow-up
and is a natural continuation, not a rework: the per-binding theorems are
the pieces it assembles.

### 5.4 Assumptions

The assumptions of the main design, section 3.5, plus:

- Each binding is its own inner cluster: no two bindings reach the same
  API server. Enforced operationally by the claim (section 1.3).
- Schema parity per kind between the outer cluster and every inner
  cluster, and the shape of section 2.2 not shrinking while the
  controller runs. The immutability rule on the selector field (section 1.1) is
  part of that parity, not a property of the outer CRD alone: the theorems
  install the outer kind and every inner kind with the same
  `synced_installed_type(spec_ok, selector)`, whose `valid_transition` *is* the
  rule, so an inner CRD that does not carry it is a parity failure like any
  other schema drift.
- The registry's `model_kind` is the model kind of the objects the shim
  returns for a binding, which the model cannot check (the trusted
  routing of section 2.2 of the main design, now per binding).

## 6. Work breakdown and order

The two issues share one core: the model and proof rewrite must be done
once, with both the kind and the binding as parameters, because every
lemma that names a kind is touched either way and the mirror key changes
shape once. Around that core the exec and deployment work of the two
issues is separable. The order:

1. **Foundation** (#20 sub-issue): the framework and shim pieces with no
   change to the verified pair. `ClusterId::Remote(ClusterRef)`; the client
   map; dynamic kube-runtime controllers on `Api<DynamicObject>`; the
   `DynReconciler` exec trait; `ReconcileModel` built from data; the
   registry; the `SyncedObjectView` shape with its trusted accessors and the
   exec `SyncedObject` wrapper. The existing pair keeps verifying on the
   old wrappers so CI stays green.
2. **Model and proofs** (shared sub-issue): the pair rewritten over
   `SyncedObjectView` with `SyncKind` and `Binding` as parameters; the
   theorems of section 5.1; the per-binding two-store instance; the
   composition with the other controllers; the exec reconcilers over
   `SyncedObject` with their conformance proofs. The binary is adapted with
   one kind and one binding so the two-cluster e2e stays green.
3. **Bindings** (#15 sub-issue) and **kinds** (#20 sub-issue), in parallel:
   the binding manager, claim, per-binding janitors, access check, RBAC and
   the three-cluster testbed; the kind flags, boot shape check, `Gadget`,
   the generic echo controller and the kind scenarios of the e2e.
4. **Follow-up**: the (n+1)-store refinement (section 5.3).

Each step is one pull request against `gabe/sync-controller`, verified
with `cargo verus verify --lib` and the e2e before it merges.
