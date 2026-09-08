// Ghost (spec-level) types of the Widget sync example, with the kind and the
// binding as data (doc/widget_sync_fanout_design.md, sections 2.3, 2.4 and 3).
//
// One configured kind exists in an outer cluster and in the inner cluster of each
// of its bindings. The copy in the outer (primary) cluster is what users create;
// the copy in a binding's inner cluster is the mirror the sync controller
// maintains, and the inner cluster's own controller acts on it. Both copies are
// objects of the shape (spec::synced_object::SyncedObjectView); the model has one
// logical store keyed by (kind, namespace, name), so the cluster is folded into
// the model kind by spec::model_kind::model_kind: the outer copy has kind
// `k.outer_kind` and the mirror in binding `b` has kind `inner_kind(k, b)`.
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::api_resource::*;
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The kind and the binding.
// ---------------------------------------------------------------------------

// A binding: the namespace the outer copies live in and the name of the inner
// cluster they are mirrored into (design, section 1.2).
pub type Binding = ClusterRefView;

// A configured kind: the model kind of its outer copies, the CRD name the
// registry builds model kinds from, and the cluster selector that names each
// object's binding.
pub struct SyncKind {
    pub outer_kind: Kind,
    pub name: StringView,
    pub selector: ClusterSelector,
}

// The model kind of the mirrors of `k` in the binding `b`.
pub open spec fn inner_kind(k: SyncKind, b: Binding) -> Kind {
    model_kind(k.name, ClusterIdView::Remote(b))
}

// `kind` is the mirror kind of `k` in some binding. This is what the sync rely
// forbids Creates of, and what the sync guarantee's requests are addressed to.
pub open spec fn is_inner_kind(k: SyncKind, kind: Kind) -> bool {
    exists |b: Binding| kind == #[trigger] inner_kind(k, b)
}

// The kind is well formed: its name is one model_kind is injective on, and its
// outer kind is the primary model kind of that name. A hypothesis of the
// theorems, discharged for a concrete configuration by definition; it is what
// the distinctness of the outer kind from every inner kind rests on.
pub open spec fn sync_kind_ok(k: SyncKind) -> bool {
    &&& kind_name_ok(k.name)
    &&& k.outer_kind == model_kind(k.name, ClusterIdView::Primary)
}

pub open spec fn binding_ok(b: Binding) -> bool {
    cluster_ref_ok(b)
}

// The outer kind is never a mirror kind.
pub proof fn lemma_outer_kind_is_not_inner(k: SyncKind, b: Binding)
    requires sync_kind_ok(k),
    ensures k.outer_kind != inner_kind(k, b),
{
    lemma_remote_kind_name_is_not_primary(k.name, k.name, b);
}

pub proof fn lemma_outer_kind_is_not_any_inner(k: SyncKind)
    requires sync_kind_ok(k),
    ensures !is_inner_kind(k, k.outer_kind),
{
    assert forall |b: Binding| k.outer_kind != #[trigger] inner_kind(k, b) by {
        lemma_outer_kind_is_not_inner(k, b);
    }
}

// Two bindings of the same namespace with distinct cluster names give distinct
// mirror kinds, by cancelling the common prefix; no assumption about the names.
pub proof fn lemma_inner_kind_same_namespace_injective(k: SyncKind, ns: StringView, c1: StringView, c2: StringView)
    requires inner_kind(k, ClusterRefView { namespace: ns, name: c1 }) == inner_kind(k, ClusterRefView { namespace: ns, name: c2 }),
    ensures c1 == c2,
{
    let p = k.name + at_sign() + ns + slash();
    assert(remote_kind_name(k.name, ClusterRefView { namespace: ns, name: c1 }) =~= p + c1);
    assert(remote_kind_name(k.name, ClusterRefView { namespace: ns, name: c2 }) =~= p + c2);
    assert(c1 =~= c2) by {
        assert((p + c1).len() == (p + c2).len());
        assert forall |i: int| 0 <= i < c1.len() implies c1[i] == c2[i] by {
            assert((p + c1)[p.len() + i] == c1[i]);
            assert((p + c2)[p.len() + i] == c2[i]);
        }
    }
}

// Distinct bindings give distinct mirror kinds.
pub proof fn lemma_inner_kind_injective(k: SyncKind, b1: Binding, b2: Binding)
    requires
        sync_kind_ok(k),
        binding_ok(b1),
        binding_ok(b2),
        inner_kind(k, b1) == inner_kind(k, b2),
    ensures b1 == b2,
{
    lemma_model_kind_injective(k.name, ClusterIdView::Remote(b1), k.name, ClusterIdView::Remote(b2));
}

// ---------------------------------------------------------------------------
// Identity of a mirror.
// ---------------------------------------------------------------------------

// The label and annotation that identify a mirror and its parent.
pub open spec fn managed_by_key() -> StringView { "anvil.dev/managed-by"@ }
pub open spec fn managed_by_value() -> StringView { "widget-sync"@ }
pub open spec fn parent_uid_key() -> StringView { "anvil.dev/parent-uid"@ }

// The condition types the sync controller reports on the outer copy. Ready and
// Stalled are also the types it reads off the inner copy's status.
pub open spec fn synced_condition_type() -> StringView { "Synced"@ }
pub open spec fn ready_condition_type() -> StringView { "Ready"@ }
pub open spec fn stalled_condition_type() -> StringView { "Stalled"@ }
pub open spec fn condition_true() -> StringView { "True"@ }
pub open spec fn condition_false() -> StringView { "False"@ }

impl SyncedStatusView {
    pub open spec fn synced_condition(self) -> Option<SyncedConditionView> {
        self.condition(synced_condition_type())
    }

    pub open spec fn ready_condition(self) -> Option<SyncedConditionView> {
        self.condition(ready_condition_type())
    }

    pub open spec fn stalled_condition(self) -> Option<SyncedConditionView> {
        self.condition(stalled_condition_type())
    }
}

// The mirrored remainder of a status that was never written: what the outer copy
// reports before it has ever carried an inner status. Trusted, with the exec
// twin inside trusted::exec_types::outer_status_for.
pub uninterp spec fn default_status_rest() -> Value;

pub open spec fn default_synced_status() -> SyncedStatusView {
    SyncedStatusView {
        observed_generation: None,
        conditions: None,
        rest: default_status_rest(),
    }
}

// `status` if there is one, else the default status: the source of the mirrored
// fields the outer status keeps when the inner status is not consulted.
pub open spec fn status_or_default(status: Option<SyncedStatusView>) -> SyncedStatusView {
    if status is Some { status->0 } else { default_synced_status() }
}

// ---------------------------------------------------------------------------
// The outcome of one reconcile, and the status that reports it.
// ---------------------------------------------------------------------------

pub enum SyncOutcomeView {
    // The mirror carries the outer spec and the inner status observes it; that
    // status is consulted.
    Synced,
    // The inner status is for an older generation of the mirror.
    InnerConverging,
    // The mirror is terminating.
    InnerTerminating,
    // The object at the mirror key has no mirror identity; never touched.
    ForeignObject,
    // The object at the mirror key is a mirror of another incarnation of the
    // outer copy; the janitor removes it.
    StaleMirror,
    // A request of the reconcile failed, or the object names no inner cluster;
    // the reconcile is requeued.
    Failed(FailureReasonView),
}

impl SyncOutcomeView {
    pub open spec fn synced(self) -> bool {
        self is Synced
    }

    // The reason the Synced condition carries.
    pub open spec fn reason(self) -> StringView {
        match self {
            SyncOutcomeView::Synced => reason_synced(),
            SyncOutcomeView::InnerConverging => reason_inner_converging(),
            SyncOutcomeView::InnerTerminating => reason_inner_terminating(),
            SyncOutcomeView::ForeignObject => reason_foreign_object(),
            SyncOutcomeView::StaleMirror => reason_stale_mirror(),
            SyncOutcomeView::Failed(failure) => failure.reason(),
        }
    }

    // A case the reconciler cannot get out of by itself: a foreign object it
    // refuses to adopt, a credential the inner cluster refuses, a request it
    // rejects, an object that names no inner cluster.
    pub open spec fn permanent(self) -> bool {
        match self {
            SyncOutcomeView::ForeignObject => true,
            SyncOutcomeView::Failed(failure) => failure is Forbidden || failure is Rejected,
            _ => false,
        }
    }
}

pub open spec fn make_condition(type_: StringView, status: StringView, observed_generation: Option<int>, reason: Option<StringView>, message: Option<StringView>) -> SyncedConditionView {
    SyncedConditionView { type_: type_, status: status, observed_generation: observed_generation, reason: reason, message: message }
}

pub open spec fn condition_status(b: bool) -> StringView {
    if b { condition_true() } else { condition_false() }
}

// Synced: True exactly when the outcome is Synced, with the outcome's reason.
pub open spec fn synced_condition_for(outer_generation: Option<int>, outcome: SyncOutcomeView) -> SyncedConditionView {
    make_condition(synced_condition_type(), condition_status(outcome.synced()), outer_generation, Some(outcome.reason()), None)
}

// Ready: True exactly when the outcome is Synced and the inner copy's own Ready
// condition, if present, is True and its own Stalled condition, if present, is not
// True (so Ready and Stalled are never both True). Otherwise False: with reason
// NotSynced when not synced, else with the reason and message of the inner
// condition that denies it. `source` is consulted only when synced.
pub open spec fn ready_condition_for(outer_generation: Option<int>, source: SyncedStatusView, outcome: SyncOutcomeView) -> SyncedConditionView {
    let inner_ready = source.ready_condition();
    let inner_stalled = source.stalled_condition();
    if !outcome.synced() {
        make_condition(ready_condition_type(), condition_false(), outer_generation, Some(reason_not_synced()), None)
    } else if inner_stalled is Some && inner_stalled->0.status == condition_true() {
        make_condition(ready_condition_type(), condition_false(), outer_generation, inner_stalled->0.reason, inner_stalled->0.message)
    } else if inner_ready is Some {
        make_condition(ready_condition_type(), condition_status(inner_ready->0.status == condition_true()), outer_generation, inner_ready->0.reason, inner_ready->0.message)
    } else {
        make_condition(ready_condition_type(), condition_true(), outer_generation, Some(reason_synced()), None)
    }
}

// Stalled: True when the outcome is permanent, with the outcome's reason; else,
// when the inner status is consulted (synced) and the inner copy has a Stalled
// condition of its own, that condition's status, reason and message; else False
// with the outcome's reason.
pub open spec fn stalled_condition_for(outer_generation: Option<int>, source: SyncedStatusView, outcome: SyncOutcomeView) -> SyncedConditionView {
    let inner_stalled = source.stalled_condition();
    if outcome.permanent() {
        make_condition(stalled_condition_type(), condition_true(), outer_generation, Some(outcome.reason()), None)
    } else if outcome.synced() && inner_stalled is Some {
        make_condition(stalled_condition_type(), condition_status(inner_stalled->0.status == condition_true()), outer_generation, inner_stalled->0.reason, inner_stalled->0.message)
    } else {
        make_condition(stalled_condition_type(), condition_false(), outer_generation, Some(outcome.reason()), None)
    }
}

// The status the sync controller writes on the outer copy for a snapshot at
// generation `outer_generation`, as a function of that generation, of a source
// status and of the outcome of the reconcile. When the outcome is Synced the
// source is the inner copy's status: its mirrored remainder is copied and its
// Ready and Stalled conditions are merged into the outer copy's. Otherwise the
// source is the outer copy's previous status (status_or_default), whose mirrored
// remainder is kept as previously reported and whose conditions are not read.
// observed_generation and every condition carry `outer_generation`.
pub open spec fn outer_status_for(outer_generation: Option<int>, source: SyncedStatusView, outcome: SyncOutcomeView) -> SyncedStatusView {
    SyncedStatusView {
        observed_generation: outer_generation,
        rest: source.rest,
        conditions: Some(seq![
            synced_condition_for(outer_generation, outcome),
            ready_condition_for(outer_generation, source, outcome),
            stalled_condition_for(outer_generation, source, outcome),
        ]),
    }
}

// Reasons reported in the Synced condition.
pub open spec fn reason_inner_converging() -> StringView { "InnerConverging"@ }
pub open spec fn reason_foreign_object() -> StringView { "ForeignObject"@ }
// The object at the mirror key is a mirror (label and parent-uid annotation) of
// another incarnation of the outer copy; the janitor removes it.
pub open spec fn reason_stale_mirror() -> StringView { "StaleMirror"@ }
pub open spec fn reason_inner_terminating() -> StringView { "InnerTerminating"@ }
pub open spec fn reason_synced() -> StringView { "Synced"@ }
// The reason of a False Ready condition when the outer copy is not synced.
pub open spec fn reason_not_synced() -> StringView { "NotSynced"@ }

// Why a request of the reconcile failed, as reported in the Synced condition
// before the reconcile ends in Error.
pub enum FailureReasonView {
    // An authorization error in the inner cluster.
    Forbidden,
    // A timeout or a server-side failure: the inner cluster is not answering.
    InnerUnreachable,
    // NotFound answering the Create of the mirror: the inner namespace is missing.
    CreateFailed,
    // The request was rejected as invalid, or the object names no inner cluster.
    Rejected,
    // Anything else.
    RequestFailed,
}

impl FailureReasonView {
    pub open spec fn reason(self) -> StringView {
        match self {
            FailureReasonView::Forbidden => "Forbidden"@,
            FailureReasonView::InnerUnreachable => "InnerUnreachable"@,
            FailureReasonView::CreateFailed => "CreateFailed"@,
            FailureReasonView::Rejected => "Rejected"@,
            FailureReasonView::RequestFailed => "RequestFailed"@,
        }
    }
}

// The reason reported for an error response. `answering_create` says whether the
// failed request was the Create of the mirror, the one request for which NotFound
// has a meaning of its own (the namespace is missing); a NotFound answering a
// Patch says the mirror vanished since it was read, which the next reconcile
// recovers from. A failed JSON patch test is also answered with Invalid, so
// Rejected can follow a race on the mirror; the next reconcile clears it.
pub open spec fn error_reason(err: APIError, answering_create: bool) -> FailureReasonView {
    match err {
        APIError::Forbidden => FailureReasonView::Forbidden,
        APIError::Timeout => FailureReasonView::InnerUnreachable,
        APIError::ServerTimeout => FailureReasonView::InnerUnreachable,
        APIError::InternalError => FailureReasonView::InnerUnreachable,
        APIError::ObjectNotFound => if answering_create { FailureReasonView::CreateFailed } else { FailureReasonView::RequestFailed },
        APIError::Invalid => FailureReasonView::Rejected,
        APIError::BadRequest => FailureReasonView::Rejected,
        APIError::NotSupported => FailureReasonView::Rejected,
        _ => FailureReasonView::RequestFailed,
    }
}

// ---------------------------------------------------------------------------
// The mirror relation between an outer copy and an inner object.
// ---------------------------------------------------------------------------

// The name an object that selects no inner cluster is treated as naming, so that
// binding_of is total and the exec reconciler can compute it. The reconcile
// reports Rejected and ends before it ever sends a request to such a binding.
pub open spec fn no_cluster_name() -> StringView { ""@ }

// The binding of `outer`: its namespace and the cluster its selector names.
pub open spec fn binding_of(k: SyncKind, outer: SyncedObjectView) -> Binding {
    ClusterRefView {
        namespace: outer.metadata.namespace->0,
        name: match cluster_of(k.selector, outer) {
            Some(c) => c,
            None => no_cluster_name(),
        },
    }
}

// The key of the mirror of `outer`: same namespace and name, the model kind of
// `k` in the binding of `outer`.
pub open spec fn inner_key(k: SyncKind, outer: SyncedObjectView) -> ObjectRef {
    ObjectRef {
        kind: inner_kind(k, binding_of(k, outer)),
        namespace: outer.metadata.namespace->0,
        name: outer.metadata.name->0,
    }
}

// The mirror key of the outer copy at `outer_key` in the binding `b`.
pub open spec fn inner_key_of(k: SyncKind, b: Binding, outer_key: ObjectRef) -> ObjectRef {
    ObjectRef { kind: inner_kind(k, b), ..outer_key }
}

// The key of the outer copy a mirror at `key` would belong to.
pub open spec fn outer_key_of(k: SyncKind, key: ObjectRef) -> ObjectRef {
    ObjectRef { kind: k.outer_kind, ..key }
}

// The parent-uid annotation value: the outer copy's uid, copied as a string. Uids
// are opaque tokens; the controller only ever compares them for equality.
pub open spec fn parent_uid_of(outer: SyncedObjectView) -> StringView {
    int_to_string_view(outer.metadata.uid->0)
}

// The mirror the sync controller creates: same name and namespace, the identifying
// label and annotation, the outer spec verbatim, no owner references, no finalizers.
pub open spec fn make_inner(k: SyncKind, outer: SyncedObjectView) -> SyncedObjectView {
    SyncedObjectView {
        kind: inner_kind(k, binding_of(k, outer)),
        metadata: ObjectMetaView::default()
            .with_name(outer.metadata.name->0)
            .with_namespace(outer.metadata.namespace->0)
            .add_label(managed_by_key(), managed_by_value())
            .add_annotation(parent_uid_key(), parent_uid_of(outer)),
        spec: outer.spec,
        status: None,
    }
}

// An inner object is the mirror of `outer` iff it carries the managed-by label and
// its parent-uid annotation equals the outer copy's uid. Anything else is refused.
pub open spec fn is_mirror_of(inner: SyncedObjectView, outer: SyncedObjectView) -> bool {
    &&& inner.metadata.labels is Some
    &&& inner.metadata.labels->0.contains_key(managed_by_key())
    &&& inner.metadata.labels->0[managed_by_key()] == managed_by_value()
    &&& inner.metadata.annotations is Some
    &&& inner.metadata.annotations->0.contains_key(parent_uid_key())
    &&& inner.metadata.annotations->0[parent_uid_key()] == parent_uid_of(outer)
}

// The inner implementation has processed the mirror's current spec.
pub open spec fn inner_caught_up(inner: SyncedObjectView) -> bool {
    &&& inner.status is Some
    &&& inner.status->0.observed_generation is Some
    &&& inner.metadata.generation is Some
    &&& inner.status->0.observed_generation == inner.metadata.generation
}

// A mirror is one the sync controller created: it carries the managed-by label and
// a parent-uid annotation. Objects without both are left alone.
pub open spec fn has_mirror_identity(inner: SyncedObjectView) -> bool {
    &&& inner.metadata.labels is Some
    &&& inner.metadata.labels->0.contains_key(managed_by_key())
    &&& inner.metadata.labels->0[managed_by_key()] == managed_by_value()
    &&& inner.metadata.annotations is Some
    &&& inner.metadata.annotations->0.contains_key(parent_uid_key())
}

pub open spec fn parent_uid_annotation(inner: SyncedObjectView) -> StringView {
    inner.metadata.annotations->0[parent_uid_key()]
}

}
