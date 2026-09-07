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

// The condition type the sync controller reports on the outer copy.
pub open spec fn synced_condition_type() -> StringView { "Synced"@ }
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
    // copy: everything except the per-copy fields observed_generation and conditions.
    pub open spec fn mirrored(self) -> WidgetStatusView {
        WidgetStatusView {
            observed_generation: None,
            conditions: None,
            ..self
        }
    }

    pub open spec fn synced_condition(self) -> Option<WidgetConditionView> {
        if self.conditions is Some && exists |i: int| 0 <= i < self.conditions->0.len() && (#[trigger] self.conditions->0[i]).type_ == synced_condition_type() {
            let i = choose |i: int| 0 <= i < self.conditions->0.len() && (#[trigger] self.conditions->0[i]).type_ == synced_condition_type();
            Some(self.conditions->0[i])
        } else {
            None
        }
    }
}

// Builds the status the sync controller writes on the outer copy for a snapshot at
// generation `outer_generation`, from the inner copy's status: mirrored fields
// copied, observed_generation stamped, and a single Synced condition.
pub open spec fn outer_status_for(outer_generation: Option<int>, inner_status: WidgetStatusView, synced: bool, reason: StringView) -> WidgetStatusView {
    WidgetStatusView {
        observed_generation: outer_generation,
        ready: inner_status.ready,
        observed_count: inner_status.observed_count,
        conditions: Some(seq![WidgetConditionView {
            type_: synced_condition_type(),
            status: if synced { condition_true() } else { condition_false() },
            observed_generation: outer_generation,
            reason: Some(reason),
            message: None,
        }]),
    }
}

// The status the sync controller writes when there is no inner status to mirror
// (the mirror was just created, is foreign, or is terminating).
pub open spec fn outer_status_without_inner(outer_generation: Option<int>, previous: Option<WidgetStatusView>, reason: StringView) -> WidgetStatusView {
    let kept = if previous is Some { previous->0 } else { WidgetStatusView::default() };
    WidgetStatusView {
        observed_generation: outer_generation,
        ready: kept.ready,
        observed_count: kept.observed_count,
        conditions: Some(seq![WidgetConditionView {
            type_: synced_condition_type(),
            status: condition_false(),
            observed_generation: outer_generation,
            reason: Some(reason),
            message: None,
        }]),
    }
}

// Reasons reported in the Synced condition.
pub open spec fn reason_inner_converging() -> StringView { "InnerConverging"@ }
pub open spec fn reason_foreign_object() -> StringView { "ForeignObject"@ }
pub open spec fn reason_inner_terminating() -> StringView { "InnerTerminating"@ }
pub open spec fn reason_synced() -> StringView { "Synced"@ }

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
