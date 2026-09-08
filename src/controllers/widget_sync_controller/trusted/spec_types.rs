// Ghost (spec-level) types of the Widget sync example.
//
// One custom resource, Widget, exists in two clusters. The copy in the primary
// (outer) cluster is what users create; the copy in the remote (inner) cluster
// is the mirror the sync controller maintains, and the inner cluster's own
// Widget controller acts on it. The two copies share one spec and one status
// shape but get distinct model kinds ("widget" and "widget@inner"), because
// the model has a single logical store keyed by (kind, namespace, name); see
// kubernetes_api_objects::exec::api_resource::ClusterId for how the tag is
// attached at the exec/model boundary.
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

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

pub struct WidgetSpecView {
    pub count: int,
    pub message: Option<StringView>,
}

impl WidgetSpecView {
    pub open spec fn default() -> WidgetSpecView {
        WidgetSpecView {
            count: 0,
            message: None,
        }
    }
}

// A condition in the style of metav1.Condition. lastTransitionTime is omitted:
// the model has no clock, and a value that depends on the wall clock cannot be
// the output of a deterministic reconcile step.
pub struct WidgetConditionView {
    pub type_: StringView,
    pub status: StringView,
    pub observed_generation: Option<int>,
    pub reason: Option<StringView>,
    pub message: Option<StringView>,
}

impl WidgetConditionView {
    pub open spec fn default() -> WidgetConditionView {
        WidgetConditionView {
            type_: ""@,
            status: ""@,
            observed_generation: None,
            reason: None,
            message: None,
        }
    }
}

pub struct WidgetStatusView {
    // Conventional meaning on each copy: the generation its controller last processed.
    pub observed_generation: Option<int>,
    // Mirrored fields: written by the inner Widget controller on the inner copy,
    // copied verbatim onto the outer copy by the sync controller.
    pub ready: Option<bool>,
    pub observed_count: Option<int>,
    // Conditions are per copy and are never mirrored.
    pub conditions: Option<Seq<WidgetConditionView>>,
}

impl WidgetStatusView {
    pub open spec fn default() -> WidgetStatusView {
        WidgetStatusView {
            observed_generation: None,
            ready: None,
            observed_count: None,
            conditions: None,
        }
    }

    // The projection the sync controller copies from the inner copy to the outer
    // copy: the data fields, that is everything except the per-copy fields
    // observed_generation and conditions. Conditions are combined, not copied.
    pub open spec fn mirrored(self) -> WidgetStatusView {
        WidgetStatusView {
            observed_generation: None,
            conditions: None,
            ..self
        }
    }

    // The first condition of type `type_`, if any. First rather than any, so that
    // the exec code, which scans the list, computes the same condition.
    pub open spec fn condition(self, type_: StringView) -> Option<WidgetConditionView> {
        if self.conditions is Some {
            find_condition_from(self.conditions->0, type_, 0)
        } else {
            None
        }
    }

    pub open spec fn synced_condition(self) -> Option<WidgetConditionView> {
        self.condition(synced_condition_type())
    }

    pub open spec fn ready_condition(self) -> Option<WidgetConditionView> {
        self.condition(ready_condition_type())
    }

    pub open spec fn stalled_condition(self) -> Option<WidgetConditionView> {
        self.condition(stalled_condition_type())
    }
}

// The first condition of type `type_` at index `i` or later.
pub open spec fn find_condition_from(conditions: Seq<WidgetConditionView>, type_: StringView, i: int) -> Option<WidgetConditionView>
    decreases conditions.len() - i,
{
    if i < 0 || i >= conditions.len() {
        None
    } else if conditions[i].type_ == type_ {
        Some(conditions[i])
    } else {
        find_condition_from(conditions, type_, i + 1)
    }
}

// `status` if there is one, else the default status: the source of the data
// fields the outer status keeps when the inner status is not consulted.
pub open spec fn status_or_default(status: Option<WidgetStatusView>) -> WidgetStatusView {
    if status is Some { status->0 } else { WidgetStatusView::default() }
}

// The outcome of one reconcile of the outer copy, as its status reports it.
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
    // A request of the reconcile failed; the reconcile is requeued.
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
    // rejects. The transient cases (a converging or terminating inner copy, a
    // stale mirror the janitor removes, an unreachable inner cluster, a missing
    // namespace, a failed request) are not permanent.
    pub open spec fn permanent(self) -> bool {
        match self {
            SyncOutcomeView::ForeignObject => true,
            SyncOutcomeView::Failed(failure) => failure is Forbidden || failure is Rejected,
            _ => false,
        }
    }
}

pub open spec fn make_condition(type_: StringView, status: StringView, observed_generation: Option<int>, reason: Option<StringView>, message: Option<StringView>) -> WidgetConditionView {
    WidgetConditionView { type_: type_, status: status, observed_generation: observed_generation, reason: reason, message: message }
}

pub open spec fn condition_status(b: bool) -> StringView {
    if b { condition_true() } else { condition_false() }
}

// Synced: True exactly when the outcome is Synced, with the outcome's reason.
pub open spec fn synced_condition_for(outer_generation: Option<int>, outcome: SyncOutcomeView) -> WidgetConditionView {
    make_condition(synced_condition_type(), condition_status(outcome.synced()), outer_generation, Some(outcome.reason()), None)
}

// Ready: True exactly when the outcome is Synced and the inner copy's own Ready
// condition, if present, is True and its own Stalled condition, if present, is not
// True (so Ready and Stalled are never both True). Otherwise False: with reason
// NotSynced when not synced, else with the reason and message of the inner
// condition that denies it. `source` is consulted only when synced.
pub open spec fn ready_condition_for(outer_generation: Option<int>, source: WidgetStatusView, outcome: SyncOutcomeView) -> WidgetConditionView {
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
pub open spec fn stalled_condition_for(outer_generation: Option<int>, source: WidgetStatusView, outcome: SyncOutcomeView) -> WidgetConditionView {
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
// source is the inner copy's status: its data fields are mirrored and its Ready
// and Stalled conditions are merged into the outer copy's. Otherwise the source
// is the outer copy's previous status (status_or_default), whose data fields are
// kept as previously reported and whose conditions are not read. observed_generation
// and every condition carry `outer_generation`.
pub open spec fn outer_status_for(outer_generation: Option<int>, source: WidgetStatusView, outcome: SyncOutcomeView) -> WidgetStatusView {
    WidgetStatusView {
        observed_generation: outer_generation,
        ready: source.ready,
        observed_count: source.observed_count,
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
    // The request was rejected as invalid.
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

// The two copies as view types. They differ only in kind().

pub struct OuterWidgetView {
    pub metadata: ObjectMetaView,
    pub spec: WidgetSpecView,
    pub status: Option<WidgetStatusView>,
}

pub struct InnerWidgetView {
    pub metadata: ObjectMetaView,
    pub spec: WidgetSpecView,
    pub status: Option<WidgetStatusView>,
}

macro_rules! implement_widget_view_methods {
    ($t:ident, $kind_string:literal) => {
        verus! {

        impl $t {
            pub open spec fn well_formed(self) -> bool {
                &&& self.metadata.well_formed_for_namespaced()
                &&& self.state_validation()
            }

            pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> $t {
                $t { metadata: metadata, ..self }
            }

            pub open spec fn with_spec(self, spec: WidgetSpecView) -> $t {
                $t { spec: spec, ..self }
            }

            pub open spec fn with_status(self, status: WidgetStatusView) -> $t {
                $t { status: Some(status), ..self }
            }

            #[verifier(inline)]
            pub open spec fn _kind() -> Kind { Kind::CustomResourceKind($kind_string@) }

            #[verifier(inline)]
            pub open spec fn _state_validation(self) -> bool {
                self.spec.count >= 0
            }

            #[verifier(inline)]
            pub open spec fn _transition_validation(self, old_obj: $t) -> bool {
                true
            }
        }

        implement_resource_view_trait!($t, WidgetSpecView, WidgetSpecView::default(),
            Option<WidgetStatusView>, None, $t::_kind(), _state_validation, _transition_validation);

        impl CustomResourceView for $t {
            proof fn kind_is_custom_resource() {}

            open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool {
                $t {
                    metadata: arbitrary(),
                    spec: obj_spec,
                    status: obj_status,
                }.state_validation()
            }

            proof fn validation_result_determined_by_spec_and_status()
                ensures forall |obj: Self| #[trigger] obj.state_validation() == Self::spec_status_validation(obj.spec(), obj.status())
            {}
        }

        }
    };
}

implement_widget_view_methods!(OuterWidgetView, "widget");
implement_widget_view_methods!(InnerWidgetView, "widget@inner");


// ---------------------------------------------------------------------------
// The mirror relation between an outer copy and an inner object. Used by the
// reconcilers and by the theorems in liveness_theorem.rs.
// ---------------------------------------------------------------------------

// The key of the mirror of `outer` in the inner cluster: same namespace and name,
// the inner cluster's model kind.
pub open spec fn inner_key(outer: OuterWidgetView) -> ObjectRef {
    ObjectRef {
        kind: InnerWidgetView::kind(),
        namespace: outer.metadata.namespace->0,
        name: outer.metadata.name->0,
    }
}

// The parent-uid annotation value: the outer copy's uid, copied as a string. Uids
// are opaque tokens; the controller only ever compares them for equality.
pub open spec fn parent_uid_of(outer: OuterWidgetView) -> StringView {
    int_to_string_view(outer.metadata.uid->0)
}

// The mirror the sync controller creates: same name and namespace, the identifying
// label and annotation, the outer spec, no owner references, no finalizers.
pub open spec fn make_inner(outer: OuterWidgetView) -> InnerWidgetView {
    InnerWidgetView {
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
pub open spec fn is_mirror_of(inner: InnerWidgetView, outer: OuterWidgetView) -> bool {
    &&& inner.metadata.labels is Some
    &&& inner.metadata.labels->0.contains_key(managed_by_key())
    &&& inner.metadata.labels->0[managed_by_key()] == managed_by_value()
    &&& inner.metadata.annotations is Some
    &&& inner.metadata.annotations->0.contains_key(parent_uid_key())
    &&& inner.metadata.annotations->0[parent_uid_key()] == parent_uid_of(outer)
}

// The inner implementation has processed the mirror's current spec.
pub open spec fn inner_caught_up(inner: InnerWidgetView) -> bool {
    &&& inner.status is Some
    &&& inner.status->0.observed_generation is Some
    &&& inner.metadata.generation is Some
    &&& inner.status->0.observed_generation == inner.metadata.generation
}

// A mirror is one the sync controller created: it carries the managed-by label and
// a parent-uid annotation. Objects without both are left alone.
pub open spec fn has_mirror_identity(inner: InnerWidgetView) -> bool {
    &&& inner.metadata.labels is Some
    &&& inner.metadata.labels->0.contains_key(managed_by_key())
    &&& inner.metadata.labels->0[managed_by_key()] == managed_by_value()
    &&& inner.metadata.annotations is Some
    &&& inner.metadata.annotations->0.contains_key(parent_uid_key())
}

pub open spec fn parent_uid_annotation(inner: InnerWidgetView) -> StringView {
    inner.metadata.annotations->0[parent_uid_key()]
}

}
