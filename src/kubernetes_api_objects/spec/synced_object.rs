// The model of the shape a synced kind must have (doc/widget_sync_fanout_design.md,
// section 2.3). A controller generic over kinds reads and writes exactly the
// fields named here; everything else of an object is opaque, carried as the
// marshalled Value it came as.
//
// The trusted boundary is small: unmarshal_status and marshal_status, related by
// marshal_status_preserves_integrity, and spec_field, the selector field of a
// spec value. unmarshal and marshal are open definitions over them, so the facts
// about metadata, kind and the round trip are proved.
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*, object_meta::*, resource::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// A condition in the style of metav1.Condition, less lastTransitionTime (the
// model has no clock).
pub struct SyncedConditionView {
    pub type_: StringView,
    pub status: StringView,
    pub observed_generation: Option<int>,
    pub reason: Option<StringView>,
    pub message: Option<StringView>,
}

// The status of an object of the shape: the two fields the controller reads and
// writes, and the rest, mirrored verbatim.
pub struct SyncedStatusView {
    pub observed_generation: Option<int>,
    pub conditions: Option<Seq<SyncedConditionView>>,
    pub rest: Value,
}

impl SyncedStatusView {
    // The projection the sync controller copies from an inner copy to its outer
    // copy: everything except the per-copy fields.
    pub open spec fn mirrored(self) -> SyncedStatusView {
        SyncedStatusView {
            observed_generation: None,
            conditions: None,
            rest: self.rest,
        }
    }

    // The first condition of type `type_`, if any. First rather than any, so that
    // exec code, which scans the list, computes the same condition.
    pub open spec fn condition(self, type_: StringView) -> Option<SyncedConditionView> {
        if self.conditions is Some {
            find_synced_condition_from(self.conditions->0, type_, 0)
        } else {
            None
        }
    }
}

// The first condition of type `type_` at index `i` or later.
pub open spec fn find_synced_condition_from(conditions: Seq<SyncedConditionView>, type_: StringView, i: int) -> Option<SyncedConditionView>
    decreases conditions.len() - i,
{
    if i < 0 || i >= conditions.len() {
        None
    } else if conditions[i].type_ == type_ {
        Some(conditions[i])
    } else {
        find_synced_condition_from(conditions, type_, i + 1)
    }
}

// An object of the shape. The kind is data (the registry's model kind of the
// object's kind and cluster, spec::model_kind); the spec is kept as the raw
// value, copying it is equality. The view does not implement ResourceView,
// whose kind() is a function of the type.
pub struct SyncedObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub spec: Value,
    pub status: Option<SyncedStatusView>,
}

impl SyncedObjectView {
    pub open spec fn object_ref(self) -> ObjectRef
        recommends
            self.metadata.name is Some,
            self.metadata.namespace is Some,
    {
        ObjectRef {
            kind: self.kind,
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> SyncedObjectView {
        SyncedObjectView { metadata: metadata, ..self }
    }

    pub open spec fn with_spec(self, spec: Value) -> SyncedObjectView {
        SyncedObjectView { spec: spec, ..self }
    }

    pub open spec fn with_status(self, status: Option<SyncedStatusView>) -> SyncedObjectView {
        SyncedObjectView { status: status, ..self }
    }
}

// The shape check on a status value: Ok(None) for an absent status, Ok(Some(s))
// for a status object whose observedGeneration is an integer if present and
// whose conditions are a list of conditions if present, Err otherwise. Trusted;
// the exec twin is exec::synced_object::SyncedObject::unmarshal.
pub uninterp spec fn unmarshal_status(v: Value) -> Result<Option<SyncedStatusView>, UnmarshalError>;

pub uninterp spec fn marshal_status(s: Option<SyncedStatusView>) -> Value;

#[verifier(external_body)]
pub proof fn marshal_status_preserves_integrity()
    ensures forall |s: Option<SyncedStatusView>| unmarshal_status(#[trigger] marshal_status(s)) == Ok::<Option<SyncedStatusView>, UnmarshalError>(s),
{}

// The string at `path` in the spec value, None when the path does not lead to a
// string. Trusted; the exec twin is exec::synced_object::RawValue::field.
pub uninterp spec fn spec_field(v: Value, path: Seq<StringView>) -> Option<StringView>;

pub open spec fn unmarshal(kind: Kind, obj: DynamicObjectView) -> Result<SyncedObjectView, UnmarshalError> {
    if obj.kind != kind {
        Err(())
    } else {
        match unmarshal_status(obj.status) {
            Ok(s) => Ok(SyncedObjectView { kind: kind, metadata: obj.metadata, spec: obj.spec, status: s }),
            Err(e) => Err(e),
        }
    }
}

pub open spec fn marshal(o: SyncedObjectView) -> DynamicObjectView {
    DynamicObjectView {
        kind: o.kind,
        metadata: o.metadata,
        spec: o.spec,
        status: marshal_status(o.status),
    }
}

pub proof fn marshal_preserves_metadata()
    ensures forall |kind: Kind, d: DynamicObjectView| #[trigger] unmarshal(kind, d) is Ok ==> d.metadata == unmarshal(kind, d)->Ok_0.metadata,
{}

pub proof fn marshal_preserves_kind()
    ensures forall |kind: Kind, d: DynamicObjectView| #[trigger] unmarshal(kind, d) is Ok ==> d.kind == kind && unmarshal(kind, d)->Ok_0.kind == kind,
{}

pub proof fn unmarshal_of_marshal()
    ensures forall |o: SyncedObjectView| unmarshal(o.kind, #[trigger] marshal(o)) == Ok::<SyncedObjectView, UnmarshalError>(o),
{
    marshal_status_preserves_integrity();
}

// The selector that names the inner cluster of an object (design, section 1.1):
// the object's own name, or a string field of its spec.
pub enum ClusterSelector {
    Name,
    Field(Seq<StringView>),
}

pub open spec fn cluster_of(selector: ClusterSelector, obj: SyncedObjectView) -> Option<StringView> {
    match selector {
        ClusterSelector::Name => obj.metadata.name,
        ClusterSelector::Field(path) => spec_field(obj.spec, path),
    }
}

// The same selection on the stored object, which is what an installed type's
// validation sees. It agrees with cluster_of on every object that unmarshals.
pub open spec fn cluster_of_dynamic(selector: ClusterSelector, obj: DynamicObjectView) -> Option<StringView> {
    match selector {
        ClusterSelector::Name => obj.metadata.name,
        ClusterSelector::Field(path) => spec_field(obj.spec, path),
    }
}

pub proof fn lemma_cluster_of_dynamic_agrees(selector: ClusterSelector, kind: Kind, obj: DynamicObjectView)
    requires unmarshal(kind, obj) is Ok,
    ensures cluster_of_dynamic(selector, obj) == cluster_of(selector, unmarshal(kind, obj)->Ok_0),
{}

// The view of an object a data-driven reconciler is triggered by, as the cluster
// model hands it to a ReconcileModel: its kind, its metadata, and the
// DynamicObjectView it marshals to. reconciler::exec::reconciler::DynReconciler
// is stated over any K whose view has this.
pub trait DynamicObjectLike: Sized {
    spec fn kind(self) -> Kind;

    spec fn metadata(self) -> ObjectMetaView;

    spec fn marshal(self) -> DynamicObjectView;
}

impl DynamicObjectLike for SyncedObjectView {
    open spec fn kind(self) -> Kind {
        self.kind
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn marshal(self) -> DynamicObjectView {
        marshal(self)
    }
}

impl DynamicObjectLike for DynamicObjectView {
    open spec fn kind(self) -> Kind {
        self.kind
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn marshal(self) -> DynamicObjectView {
        self
    }
}

}
