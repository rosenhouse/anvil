// Exec twins of what the shape does not provide: the configured kind and the
// binding a reconciler is instantiated with, the outcome of one reconcile, and
// the status the sync controller writes on an outer copy.
//
// The objects themselves are exec::synced_object::SyncedObject, whose accessors,
// unmarshal, marshal, has_kind and api_resource are the trusted boundary of the
// shape; the registry (exec::registry) is what ties a runtime kind and a cluster
// to a model kind. What is left here is outer_status_for, which builds the outer
// status, its three conditions included, by hand to match the spec's definition.
use crate::kubernetes_api_objects::exec::{api_resource::*, registry::*, synced_object::*};
use crate::kubernetes_api_objects::spec::api_resource::ClusterIdView;
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::spec_types;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

// The set of bindings a Vec of cluster references stands for: the model's
// `SyncKind::bindings`, read off the snapshot the reconciler was built with.
pub open spec fn binding_set(v: Seq<ClusterRef>) -> Set<spec_types::Binding> {
    v.map_values(|c: ClusterRef| c@).to_set()
}

// A configured kind, exec side: the registry entry that names it, the cluster
// selector of its objects, and the bindings this reconciler knows -- the snapshot
// of the process's bound clusters the runner built it with, one per reconcile
// (doc/widget_sync_fanout_design.md, section 3.2). Its view is the model's
// SyncKind, whose outer kind is the primary model kind of the entry (so
// sync_kind_ok holds of it as soon as the CRD name is free of '@', which a DNS
// name is) and whose binding set is the snapshot's.
pub struct SyncKindExec {
    pub entry: RegistryEntry,
    pub selector: ClusterSelectorExec,
    pub bindings: Vec<ClusterRef>,
}

impl View for SyncKindExec {
    type V = spec_types::SyncKind;

    open spec fn view(&self) -> spec_types::SyncKind {
        spec_types::SyncKind {
            outer_kind: model_kind(self.entry@, ClusterIdView::Primary),
            name: self.entry@,
            selector: self.selector@,
            bindings: binding_set(self.bindings@),
        }
    }
}

impl SyncKindExec {
    // Whether `b` is one of the bindings this reconciler knows: the exec twin of
    // `k.bindings.contains(b)`, a scan of the snapshot.
    pub fn knows(&self, b: &ClusterRef) -> (res: bool)
        ensures res == self@.bindings.contains(b@),
    {
        broadcast use Seq::to_set_ensures;
        let ghost views = self.bindings@.map_values(|c: ClusterRef| c@);
        let mut i: usize = 0;
        while i < self.bindings.len()
            invariant
                0 <= i <= self.bindings.len(),
                views == self.bindings@.map_values(|c: ClusterRef| c@),
                views.len() == self.bindings.len(),
                forall |j: int| 0 <= j < i ==> #[trigger] views[j] != b@,
            decreases self.bindings.len() - i,
        {
            if self.bindings[i].eq(b) {
                assert(views[i as int] == b@);
                assert(views.contains(b@));
                return true;
            }
            i = i + 1;
        }
        assert(!views.contains(b@));
        false
    }

    // The ApiResource of the outer copies of this kind.
    pub fn outer_api_resource(&self) -> (res: ApiResource)
        ensures res@.kind == self@.outer_kind,
    {
        self.entry.api_resource(&ClusterId::Primary)
    }

    // The ApiResource of the mirrors of this kind in the binding `b`.
    pub fn inner_api_resource(&self, b: &ClusterRef) -> (res: ApiResource)
        ensures res@.kind == spec_types::inner_kind(self@, b@),
    {
        self.entry.api_resource(&ClusterId::Remote(b.clone()))
    }
}

// The view of an exec Option<i64> as the model's Option<int>; used to relate
// metadata.generation and status.observedGeneration values across the boundary.
pub open spec fn opt_i64_view(g: Option<i64>) -> Option<int> {
    opt_i64_as_int(g)
}

// The exec twin of spec_types::FailureReasonView.
pub enum FailureReason {
    Forbidden,
    InnerUnreachable,
    CreateFailed,
    Rejected,
    RequestFailed,
}

impl View for FailureReason {
    type V = spec_types::FailureReasonView;

    open spec fn view(&self) -> spec_types::FailureReasonView {
        match self {
            FailureReason::Forbidden => spec_types::FailureReasonView::Forbidden,
            FailureReason::InnerUnreachable => spec_types::FailureReasonView::InnerUnreachable,
            FailureReason::CreateFailed => spec_types::FailureReasonView::CreateFailed,
            FailureReason::Rejected => spec_types::FailureReasonView::Rejected,
            FailureReason::RequestFailed => spec_types::FailureReasonView::RequestFailed,
        }
    }
}

impl FailureReason {
    pub fn reason(&self) -> (reason: String)
        ensures reason@ == self@.reason(),
    {
        match self {
            FailureReason::Forbidden => "Forbidden".to_string(),
            FailureReason::InnerUnreachable => "InnerUnreachable".to_string(),
            FailureReason::CreateFailed => "CreateFailed".to_string(),
            FailureReason::Rejected => "Rejected".to_string(),
            FailureReason::RequestFailed => "RequestFailed".to_string(),
        }
    }
}

// The exec twin of spec_types::SyncOutcomeView.
pub enum SyncOutcome {
    Synced,
    InnerConverging,
    InnerTerminating,
    ForeignObject,
    StaleMirror,
    Failed(FailureReason),
}

impl View for SyncOutcome {
    type V = spec_types::SyncOutcomeView;

    open spec fn view(&self) -> spec_types::SyncOutcomeView {
        match self {
            SyncOutcome::Synced => spec_types::SyncOutcomeView::Synced,
            SyncOutcome::InnerConverging => spec_types::SyncOutcomeView::InnerConverging,
            SyncOutcome::InnerTerminating => spec_types::SyncOutcomeView::InnerTerminating,
            SyncOutcome::ForeignObject => spec_types::SyncOutcomeView::ForeignObject,
            SyncOutcome::StaleMirror => spec_types::SyncOutcomeView::StaleMirror,
            SyncOutcome::Failed(failure) => spec_types::SyncOutcomeView::Failed(failure@),
        }
    }
}

impl SyncOutcome {
    pub fn synced(&self) -> (b: bool)
        ensures b == self@.synced(),
    {
        match self {
            SyncOutcome::Synced => true,
            _ => false,
        }
    }

    pub fn reason(&self) -> (reason: String)
        ensures reason@ == self@.reason(),
    {
        match self {
            SyncOutcome::Synced => "Synced".to_string(),
            SyncOutcome::InnerConverging => "InnerConverging".to_string(),
            SyncOutcome::InnerTerminating => "InnerTerminating".to_string(),
            SyncOutcome::ForeignObject => "ForeignObject".to_string(),
            SyncOutcome::StaleMirror => "StaleMirror".to_string(),
            SyncOutcome::Failed(failure) => failure.reason(),
        }
    }

    pub fn permanent(&self) -> (b: bool)
        ensures b == self@.permanent(),
    {
        match self {
            SyncOutcome::ForeignObject => true,
            SyncOutcome::Failed(FailureReason::Forbidden) => true,
            SyncOutcome::Failed(FailureReason::Rejected) => true,
            _ => false,
        }
    }
}

// The status the sync controller writes on the outer copy, built by hand to
// match spec_types::outer_status_for: the mirrored remainder of `source`, and the
// three conditions, whose inner Ready and Stalled are the first of each type,
// which is the one the spec's condition() names. `source` absent is the status
// the outer copy has never carried, whose remainder is default_status_rest().
#[verifier(external_body)]
pub fn outer_status_for(outer_generation: Option<i64>, source: &Option<SyncedStatus>, outcome: &SyncOutcome) -> (status: SyncedStatus)
    ensures status@ == spec_types::outer_status_for(
        opt_i64_view(outer_generation),
        spec_types::status_or_default(source.deep_view()),
        outcome@,
    ),
{
    let synced = outcome.synced();
    let reason = outcome.reason();
    let permanent = outcome.permanent();
    let conditions: Vec<SyncedCondition> = source.as_ref().and_then(|s| s.conditions()).unwrap_or_default();
    let find = |type_: &str| -> Option<SyncedCondition> {
        conditions.iter().find(|c| c.type_() == type_).cloned()
    };
    let inner_ready = find("Ready");
    let inner_stalled = find("Stalled");
    let condition_status = |b: bool| if b { "True".to_string() } else { "False".to_string() };
    let make = |type_: &str, status: String, reason: Option<String>, message: Option<String>|
        SyncedCondition::new(type_.to_string(), status, outer_generation, reason, message);
    let synced_condition = make("Synced", condition_status(synced), Some(reason.clone()), None);
    let ready_condition = if !synced {
        make("Ready", "False".to_string(), Some("NotSynced".to_string()), None)
    } else if inner_stalled.as_ref().map_or(false, |c| c.status() == "True") {
        let c = inner_stalled.as_ref().unwrap();
        make("Ready", "False".to_string(), c.reason(), c.message())
    } else if let Some(c) = inner_ready.as_ref() {
        make("Ready", condition_status(c.status() == "True"), c.reason(), c.message())
    } else {
        make("Ready", "True".to_string(), Some("Synced".to_string()), None)
    };
    let stalled_condition = if permanent {
        make("Stalled", "True".to_string(), Some(reason.clone()), None)
    } else if synced && inner_stalled.is_some() {
        let c = inner_stalled.as_ref().unwrap();
        make("Stalled", condition_status(c.status() == "True"), c.reason(), c.message())
    } else {
        make("Stalled", "False".to_string(), Some(reason.clone()), None)
    };
    let rest = match source {
        Some(s) => s.rest(),
        // The mirrored remainder of a status that was never written: the model's
        // default_status_rest().
        None => RawValue::from_json(serde_json::Value::Object(serde_json::Map::new())),
    };
    SyncedStatus::new(outer_generation, Some(vec![synced_condition, ready_condition, stalled_condition]), rest)
}

}
