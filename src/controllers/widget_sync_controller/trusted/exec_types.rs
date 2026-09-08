// Exec wrappers of the Widget custom resource for the two clusters.
//
// OuterWidget and InnerWidget wrap the same kube type (crds::Widget). They are
// bound to different clusters (ClusterId::Primary and the one binding of the
// pair, inner_cluster()), so their views have different kinds and the shim
// routes their requests to the matching cluster. See
// kubernetes_api_objects::exec::api_resource::ClusterId.
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{api_resource::*, prelude::*};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::spec_types;
use kube::Resource;
use vstd::prelude::*;

verus! {

// The binding the pair's mirrors live in. The single pair has one inner
// cluster, so its ClusterRef is fixed here; the binary registers the remote
// clients under the same ref, which is what routes InnerWidget requests to
// them. The names are only a tag: nothing reads them back.
pub fn inner_cluster() -> ClusterId {
    ClusterId::remote("widget-sync".to_string(), "inner".to_string())
}

implement_object_wrapper_type!(
    OuterWidget,
    crate::crds::Widget,
    spec_types::OuterWidgetView
);

implement_object_wrapper_type!(
    InnerWidget,
    crate::crds::Widget,
    spec_types::InnerWidgetView,
    inner_cluster()
);

implement_field_wrapper_type!(
    WidgetSpec,
    crate::crds::WidgetSpec,
    spec_types::WidgetSpecView
);

implement_field_wrapper_type!(
    WidgetStatus,
    crate::crds::WidgetStatus,
    spec_types::WidgetStatusView
);

implement_field_wrapper_type!(
    WidgetCondition,
    crate::crds::WidgetCondition,
    spec_types::WidgetConditionView
);

implement_eq!(WidgetSpec);
implement_eq!(WidgetStatus);

}

macro_rules! implement_widget_object_methods {
    ($t:ident) => {
        verus! {

        impl $t {
            #[verifier(external_body)]
            pub fn well_formed(&self) -> (b: bool)
                ensures b == self@.well_formed(),
            {
                self.metadata().well_formed_for_namespaced()
                && self.state_validation()
            }

            #[verifier(external_body)]
            pub fn spec(&self) -> (spec: WidgetSpec)
                ensures spec@ == self@.spec,
            {
                WidgetSpec { inner: self.inner.spec.clone() }
            }

            #[verifier(external_body)]
            pub fn status(&self) -> (status: Option<WidgetStatus>)
                ensures
                    status is Some == self@.status is Some,
                    status is Some ==> status->0@ == self@.status->0,
            {
                match &self.inner.status {
                    Some(s) => Some(WidgetStatus { inner: s.clone() }),
                    None => None,
                }
            }

            #[verifier(external_body)]
            pub fn set_spec(&mut self, spec: WidgetSpec)
                ensures final(self)@ == old(self)@.with_spec(spec@),
            {
                self.inner.spec = spec.into_kube();
            }

            #[verifier(external_body)]
            pub fn set_status(&mut self, status: WidgetStatus)
                ensures final(self)@ == old(self)@.with_status(status@),
            {
                self.inner.status = Some(status.into_kube());
            }

            pub fn state_validation(&self) -> (res: bool)
                ensures res == self@.state_validation(),
            {
                self.spec().count() >= 0
            }
        }

        }
    };
}

implement_widget_object_methods!(OuterWidget);
implement_widget_object_methods!(InnerWidget);

verus! {

// The view of an exec Option<i64> as the model's Option<int>; used to relate
// metadata.generation and status.observedGeneration values across the boundary.
pub open spec fn opt_i64_view(g: Option<i64>) -> Option<int> {
    match g {
        Some(x) => Some(x as int),
        None => None,
    }
}

impl WidgetSpec {
    #[verifier(external_body)]
    pub fn count(&self) -> (count: i32)
        ensures count as int == self@.count,
    {
        self.inner.count
    }

    #[verifier(external_body)]
    pub fn message(&self) -> (message: Option<String>)
        ensures self@.message == message.deep_view(),
    {
        self.inner.message.clone()
    }
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

impl WidgetStatus {
    #[verifier(external_body)]
    pub fn observed_generation(&self) -> (observed_generation: Option<i64>)
        ensures
            observed_generation is Some == self@.observed_generation is Some,
            observed_generation is Some ==> observed_generation->0 as int == self@.observed_generation->0,
    {
        self.inner.observed_generation
    }

    #[verifier(external_body)]
    pub fn ready(&self) -> (ready: Option<bool>)
        ensures ready == self@.ready,
    {
        self.inner.ready
    }

    #[verifier(external_body)]
    pub fn observed_count(&self) -> (observed_count: Option<i32>)
        ensures
            observed_count is Some == self@.observed_count is Some,
            observed_count is Some ==> observed_count->0 as int == self@.observed_count->0,
    {
        self.inner.observed_count
    }

    // The status the sync controller writes on the outer copy, built by hand to
    // match spec_types::outer_status_for: the first inner condition of each type is
    // the one the spec's condition() names.
    #[verifier(external_body)]
    pub fn outer_status_for(outer_generation: Option<i64>, source: &WidgetStatus, outcome: &SyncOutcome) -> (status: WidgetStatus)
        ensures status@ == spec_types::outer_status_for(
            opt_i64_view(outer_generation),
            source@, outcome@,
        ),
    {
        let synced = outcome.synced();
        let reason = outcome.reason();
        let permanent = outcome.permanent();
        let find = |type_: &str| -> Option<crate::crds::WidgetCondition> {
            source.inner.conditions.as_ref().and_then(|conditions| conditions.iter().find(|c| c.type_ == type_).cloned())
        };
        let inner_ready = find("Ready");
        let inner_stalled = find("Stalled");
        let condition_status = |b: bool| if b { "True".to_string() } else { "False".to_string() };
        let make = |type_: &str, status: String, reason: Option<String>, message: Option<String>| crate::crds::WidgetCondition {
            type_: type_.to_string(),
            status: status,
            observed_generation: outer_generation,
            reason: reason,
            message: message,
        };
        let synced_condition = make("Synced", condition_status(synced), Some(reason.clone()), None);
        let ready_condition = if !synced {
            make("Ready", "False".to_string(), Some("NotSynced".to_string()), None)
        } else if inner_stalled.as_ref().map_or(false, |c| c.status == "True") {
            let c = inner_stalled.as_ref().unwrap();
            make("Ready", "False".to_string(), c.reason.clone(), c.message.clone())
        } else if let Some(c) = inner_ready.as_ref() {
            make("Ready", condition_status(c.status == "True"), c.reason.clone(), c.message.clone())
        } else {
            make("Ready", "True".to_string(), Some("Synced".to_string()), None)
        };
        let stalled_condition = if permanent {
            make("Stalled", "True".to_string(), Some(reason.clone()), None)
        } else if synced && inner_stalled.is_some() {
            let c = inner_stalled.as_ref().unwrap();
            make("Stalled", condition_status(c.status == "True"), c.reason.clone(), c.message.clone())
        } else {
            make("Stalled", "False".to_string(), Some(reason.clone()), None)
        };
        WidgetStatus { inner: crate::crds::WidgetStatus {
            observed_generation: outer_generation,
            ready: source.inner.ready,
            observed_count: source.inner.observed_count,
            conditions: Some(vec![synced_condition, ready_condition, stalled_condition]),
        } }
    }
}

}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;

    fn widget(kind: Option<&str>, cluster: ClusterId) -> DynamicObject {
        let mut obj = kube::api::DynamicObject::new("w", &kube::api::ApiResource::erase::<crate::crds::Widget>(&()));
        obj.types = kind.map(|k| kube::api::TypeMeta { api_version: "anvil.dev/v1".to_string(), kind: k.to_string() });
        DynamicObject::from_kube_in(obj, cluster)
    }

    // The kind test follows the cluster tag and the kube kind, never the model
    // kind string, and does not panic on a list item without type metadata.
    #[test]
    fn has_kind_follows_tag_and_kube_kind() {
        assert!(OuterWidget::has_kind(&widget(Some("Widget"), ClusterId::Primary)));
        assert!(!OuterWidget::has_kind(&widget(Some("Widget"), inner_cluster())));
        assert!(InnerWidget::has_kind(&widget(Some("Widget"), inner_cluster())));
        assert!(!InnerWidget::has_kind(&widget(Some("Widget"), ClusterId::Primary)));
        assert!(!InnerWidget::has_kind(&widget(Some("Widget"), ClusterId::remote("widget-sync".to_string(), "other".to_string()))));
        assert!(!OuterWidget::has_kind(&widget(Some("widget"), ClusterId::Primary)));
        assert!(!OuterWidget::has_kind(&widget(Some("Pod"), ClusterId::Primary)));
        assert!(!OuterWidget::has_kind(&widget(None, ClusterId::Primary)));
    }
}
