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
// registry builds model kinds from, the cluster selector that names each
// object's binding, and the bindings the controller knows.
//
// `bindings` is what makes the mirror kinds of a configuration finitely many
// (doc/widget_sync_fanout_design.md, section 5.2): the sync reconciler serves
// exactly these bindings and refuses every other one before it sends a request,
// so the only mirror kinds it ever writes are `inner_kind(k, b)` for `b` in the
// set. Exec side it is the snapshot of the bound clusters the runner builds the
// reconciler with, one snapshot per reconcile (trusted::exec_types::SyncKindExec).
pub struct SyncKind {
    pub outer_kind: Kind,
    pub name: StringView,
    pub selector: ClusterSelector,
    pub bindings: Set<Binding>,
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

// Every binding the kind serves is well formed. Discharged for a concrete
// configuration by the boot check on each binding's names.
pub open spec fn bindings_ok(k: SyncKind) -> bool {
    forall |b: Binding| #[trigger] k.bindings.contains(b) ==> binding_ok(b)
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

// Two configured kinds with distinct outer kinds share no mirror kind, whatever
// bindings the two are read at -- including bindings no boot check has seen, which
// is what the relies quantify over (is_inner_kind). This is what makes two kinds
// compose: neither one's sync controller ever writes an object of the other's
// kinds.
pub proof fn lemma_kinds_of_distinct_configurations(k1: SyncKind, k2: SyncKind)
    requires
        sync_kind_ok(k1),
        sync_kind_ok(k2),
        k1.outer_kind != k2.outer_kind,
    ensures
        k1.name != k2.name,
        forall |b: Binding| #[trigger] inner_kind(k1, b) != k2.outer_kind,
        forall |b: Binding| #[trigger] inner_kind(k2, b) != k1.outer_kind,
        !is_inner_kind(k2, k1.outer_kind),
        !is_inner_kind(k1, k2.outer_kind),
        forall |b1: Binding, b2: Binding| #![trigger inner_kind(k1, b1), inner_kind(k2, b2)]
            inner_kind(k1, b1) != inner_kind(k2, b2),
        forall |b1: Binding| #[trigger] is_inner_kind(k1, inner_kind(k1, b1)) && !is_inner_kind(k2, inner_kind(k1, b1)),
        forall |b2: Binding| #[trigger] is_inner_kind(k2, inner_kind(k2, b2)) && !is_inner_kind(k1, inner_kind(k2, b2)),
{
    assert(k1.name != k2.name);
    assert forall |b: Binding| #[trigger] inner_kind(k1, b) != k2.outer_kind by {
        lemma_remote_kind_name_is_not_primary(k2.name, k1.name, b);
    }
    assert forall |b: Binding| #[trigger] inner_kind(k2, b) != k1.outer_kind by {
        lemma_remote_kind_name_is_not_primary(k1.name, k2.name, b);
    }
    assert forall |b1: Binding, b2: Binding| #![trigger inner_kind(k1, b1), inner_kind(k2, b2)]
        inner_kind(k1, b1) != inner_kind(k2, b2) by {
        lemma_remote_kind_names_of_distinct_kinds(k1.name, k2.name, b1, b2);
    }
    lemma_outer_kind_is_not_any_inner(k1);
    lemma_outer_kind_is_not_any_inner(k2);
    assert(!is_inner_kind(k2, k1.outer_kind)) by {
        assert forall |b: Binding| k1.outer_kind != #[trigger] inner_kind(k2, b) by {
            lemma_remote_kind_name_is_not_primary(k1.name, k2.name, b);
        }
    }
    assert(!is_inner_kind(k1, k2.outer_kind)) by {
        assert forall |b: Binding| k2.outer_kind != #[trigger] inner_kind(k1, b) by {
            lemma_remote_kind_name_is_not_primary(k2.name, k1.name, b);
        }
    }
    assert forall |b1: Binding| #[trigger] is_inner_kind(k1, inner_kind(k1, b1)) && !is_inner_kind(k2, inner_kind(k1, b1)) by {
        assert forall |b2: Binding| inner_kind(k1, b1) != #[trigger] inner_kind(k2, b2) by {
            lemma_remote_kind_names_of_distinct_kinds(k1.name, k2.name, b1, b2);
        }
    }
    assert forall |b2: Binding| #[trigger] is_inner_kind(k2, inner_kind(k2, b2)) && !is_inner_kind(k1, inner_kind(k2, b2)) by {
        assert forall |b1: Binding| inner_kind(k2, b2) != #[trigger] inner_kind(k1, b1) by {
            lemma_remote_kind_names_of_distinct_kinds(k1.name, k2.name, b1, b2);
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
pub open spec fn condition_unknown() -> StringView { "Unknown"@ }

// A condition status is one of the three; anything else an inner condition
// carries is reported as Unknown.
pub open spec fn three_valued(status: StringView) -> StringView {
    if status == condition_true() || status == condition_false() || status == condition_unknown() {
        status
    } else {
        condition_unknown()
    }
}

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
// reports before it has ever carried an inner status. The exec twin is inside
// trusted::exec_types::outer_status_for, which builds it with
// RawValue::empty_rest().
pub open spec fn default_status_rest() -> Value { empty_status_rest() }

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

// The source of the mirrored remainder is representable when the status it came
// from is: an inner status read out of a value, or the empty remainder.
pub proof fn lemma_status_or_default_rest_ok(status: Option<SyncedStatusView>)
    requires status_ok(status),
    ensures status_rest_ok(status_or_default(status).rest),
{
    empty_status_rest_ok();
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

    // Whether Ready reads Unknown rather than False while not synced. The split
    // is by reason. A reason that can arise without the reconcile having read a
    // caught-up inner status for the current spec -- the mirror is converging
    // or terminating (InnerConverging, InnerTerminating), the inner cluster did
    // not answer (InnerUnreachable), a request failed or was refused
    // (RequestFailed, Forbidden) -- reads Unknown: the mirror may still be
    // running the spec, and Ready does not deny it. A reason that arises only
    // once the reconcile knows no mirror of this copy runs the spec -- the
    // object at the mirror key is foreign or stale (ForeignObject, StaleMirror),
    // the Create failed (CreateFailed), a request was rejected (Rejected) --
    // reads False. Where a reason can arise both ways, such as a Create refused
    // after a NotFound, Unknown retracts nothing. reason_reads_ready_unknown is
    // the same split, keyed by the reason the request carries.
    pub open spec fn ready_unknown(self) -> bool {
        match self {
            SyncOutcomeView::InnerConverging => true,
            SyncOutcomeView::InnerTerminating => true,
            SyncOutcomeView::Failed(failure) => failure is InnerUnreachable || failure is RequestFailed || failure is Forbidden,
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

// Ready, three-valued. `source` is consulted only when synced.
//
// Not synced: reason NotSynced, no message; Unknown or False by the outcome
// (SyncOutcomeView::ready_unknown). Synced with an inner Stalled
// condition that is True: False, with that condition's reason and message.
// Synced with an inner Ready condition: that condition's status (three_valued),
// reason and message. Synced with no inner Ready condition: Unknown, reason
// NoInnerReadyCondition, no message.
//
// So Ready is True only when synced and the inner Ready condition is True, and
// never while Stalled is True.
pub open spec fn ready_condition_for(outer_generation: Option<int>, source: SyncedStatusView, outcome: SyncOutcomeView) -> SyncedConditionView {
    let inner_ready = source.ready_condition();
    let inner_stalled = source.stalled_condition();
    if !outcome.synced() {
        let status = if outcome.ready_unknown() { condition_unknown() } else { condition_false() };
        make_condition(ready_condition_type(), status, outer_generation, Some(reason_not_synced()), None)
    } else if inner_stalled is Some && inner_stalled->0.status == condition_true() {
        make_condition(ready_condition_type(), condition_false(), outer_generation, inner_stalled->0.reason, inner_stalled->0.message)
    } else if inner_ready is Some {
        make_condition(ready_condition_type(), three_valued(inner_ready->0.status), outer_generation, inner_ready->0.reason, inner_ready->0.message)
    } else {
        make_condition(ready_condition_type(), condition_unknown(), outer_generation, Some(reason_no_inner_ready_condition()), None)
    }
}

// Stalled: True when the outcome is permanent, with the outcome's reason and no
// message; else, when synced and the inner copy has a Stalled condition of its
// own, that condition's status (three_valued), reason and message; else False
// with the outcome's reason and no message. A synced mirror with no Stalled
// condition reads False with reason Synced.
pub open spec fn stalled_condition_for(outer_generation: Option<int>, source: SyncedStatusView, outcome: SyncOutcomeView) -> SyncedConditionView {
    let inner_stalled = source.stalled_condition();
    if outcome.permanent() {
        make_condition(stalled_condition_type(), condition_true(), outer_generation, Some(outcome.reason()), None)
    } else if outcome.synced() && inner_stalled is Some {
        make_condition(stalled_condition_type(), three_valued(inner_stalled->0.status), outer_generation, inner_stalled->0.reason, inner_stalled->0.message)
    } else {
        make_condition(stalled_condition_type(), condition_false(), outer_generation, Some(outcome.reason()), None)
    }
}

// The condition types the sync controller writes itself. An inner condition of
// one of these types is merged (Ready, Stalled) or dropped (Synced), never
// copied. Types match exactly: "ready" is another type.
pub open spec fn is_own_condition_type(type_: StringView) -> bool {
    ||| type_ == synced_condition_type()
    ||| type_ == ready_condition_type()
    ||| type_ == stalled_condition_type()
}

pub open spec fn has_condition_of_type(conds: Seq<SyncedConditionView>, type_: StringView) -> bool {
    exists |i: int| 0 <= i < conds.len() && #[trigger] conds[i].type_ == type_
}

// The conditions of `conds` the sync controller copies: those whose type is not
// one of its own, in order, the first of each type only -- the one condition()
// names -- with status, reason and message as they are. Defined from the back:
// a condition is kept when its type is not an own type and no earlier condition
// of its type was kept.
pub open spec fn copied_conditions(conds: Seq<SyncedConditionView>) -> Seq<SyncedConditionView>
    decreases conds.len(),
{
    if conds.len() == 0 {
        Seq::empty()
    } else {
        let kept = copied_conditions(conds.drop_last());
        let last = conds.last();
        if is_own_condition_type(last.type_) || has_condition_of_type(kept, last.type_) {
            kept
        } else {
            kept.push(last)
        }
    }
}

// `conds` with every condition stamped `generation`.
pub open spec fn stamped(conds: Seq<SyncedConditionView>, generation: Option<int>) -> Seq<SyncedConditionView> {
    conds.map_values(|c: SyncedConditionView| SyncedConditionView { observed_generation: generation, ..c })
}

pub open spec fn conditions_of(status: SyncedStatusView) -> Seq<SyncedConditionView> {
    if status.conditions is Some { status.conditions->0 } else { Seq::empty() }
}

// The conditions that follow the three own conditions on the outer copy. When
// synced they are the inner copy's copied conditions, stamped with the outer
// generation the caught-up inner status was read at. Otherwise they are the
// source's -- the outer copy's previous status -- kept with the stamp they were
// read at, and filtered the same way: the previous status may have been written
// by anyone, and the guarantee is proved of this function's result, not of what
// was stored. The kept stamp can equal the current generation; Synced=False is
// what says the tail is kept.
pub open spec fn copied_conditions_for(outer_generation: Option<int>, source: SyncedStatusView, outcome: SyncOutcomeView) -> Seq<SyncedConditionView> {
    if outcome.synced() {
        stamped(copied_conditions(conditions_of(source)), outer_generation)
    } else {
        copied_conditions(conditions_of(source))
    }
}

// The status the sync controller writes on the outer copy for a snapshot at
// generation `outer_generation`, as a function of that generation, of a source
// status and of the outcome of the reconcile. When the outcome is Synced the
// source is the inner copy's status: its mirrored remainder is copied, its Ready
// and Stalled conditions are merged into the outer copy's, and its other
// conditions follow those three (copied_conditions_for). Otherwise the source is
// the outer copy's previous status (status_or_default), whose mirrored remainder
// and copied conditions are kept as previously reported and whose own conditions
// are not read. observed_generation and the three own conditions carry
// `outer_generation`; a copied condition carries the outer generation at which
// it was read off the inner copy.
pub open spec fn outer_status_for(outer_generation: Option<int>, source: SyncedStatusView, outcome: SyncOutcomeView) -> SyncedStatusView {
    SyncedStatusView {
        observed_generation: outer_generation,
        rest: source.rest,
        conditions: Some(seq![
            synced_condition_for(outer_generation, outcome),
            ready_condition_for(outer_generation, source, outcome),
            stalled_condition_for(outer_generation, source, outcome),
        ] + copied_conditions_for(outer_generation, source, outcome)),
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
// The reason of the Ready condition when the outer copy is not synced.
pub open spec fn reason_not_synced() -> StringView { "NotSynced"@ }
// The reason of an Unknown Ready condition when the mirror is synced but its
// status carries no Ready condition.
pub open spec fn reason_no_inner_ready_condition() -> StringView { "NoInnerReadyCondition"@ }

// The Synced reasons under which a not-synced Ready reads Unknown:
// SyncOutcomeView::ready_unknown over the reason the request carries
// (proof::guarantee::lemma_ready_unknown_by_reason), which is how the guarantee
// states the split.
pub open spec fn reason_reads_ready_unknown(reason: StringView) -> bool {
    ||| reason == reason_inner_converging()
    ||| reason == reason_inner_terminating()
    ||| reason == FailureReasonView::InnerUnreachable.reason()
    ||| reason == FailureReasonView::RequestFailed.reason()
    ||| reason == FailureReasonView::Forbidden.reason()
}

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
// A selector-less outer copy is refused at `Init` (Failed(Rejected)) before
// `serves` is ever consulted, so a binding (ns, no_cluster_name()) that happens
// to be in `k.bindings` is never served for such an object.
pub open spec fn binding_of(k: SyncKind, outer: SyncedObjectView) -> Binding {
    ClusterRefView {
        namespace: outer.metadata.namespace->0,
        name: match cluster_of(k.selector, outer) {
            Some(c) => c,
            None => no_cluster_name(),
        },
    }
}

// The controller knows the binding of `outer`. A reconcile of an outer copy this
// is false of reports Failed(InnerUnreachable) and ends without ever addressing
// the inner side, so every request the sync reconciler sends names a binding of
// `k.bindings` and, with that set finite, a kind a concrete cluster can install.
pub open spec fn serves(k: SyncKind, outer: SyncedObjectView) -> bool {
    k.bindings.contains(binding_of(k, outer))
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
