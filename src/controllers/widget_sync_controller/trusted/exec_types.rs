// Exec wrappers of the Widget custom resource for the two clusters.
//
// OuterWidget and InnerWidget wrap the same kube type (crds::Widget). They are
// bound to different clusters (ClusterId::Primary and ClusterId::Remote), so
// their views have different kinds and the shim routes their requests to the
// matching cluster. See kubernetes_api_objects::exec::api_resource::ClusterId.
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{api_resource::*, prelude::*};
use crate::kubernetes_api_objects::spec::resource::*;
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::trusted::spec_types;
use kube::Resource;
use vstd::prelude::*;

verus! {

implement_object_wrapper_type!(
    OuterWidget,
    crate::crds::Widget,
    spec_types::OuterWidgetView
);

implement_object_wrapper_type!(
    InnerWidget,
    crate::crds::Widget,
    spec_types::InnerWidgetView,
    ClusterId::Remote
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

    // The status the sync controller writes on the outer copy when it has an inner
    // status to mirror. See spec_types::outer_status_for.
    #[verifier(external_body)]
    pub fn outer_status_for(outer_generation: Option<i64>, inner_status: &WidgetStatus, synced: bool, reason: String) -> (status: WidgetStatus)
        ensures status@ == spec_types::outer_status_for(
            opt_i64_view(outer_generation),
            inner_status@, synced, reason@,
        ),
    {
        WidgetStatus { inner: crate::crds::WidgetStatus {
            observed_generation: outer_generation,
            ready: inner_status.inner.ready,
            observed_count: inner_status.inner.observed_count,
            conditions: Some(vec![crate::crds::WidgetCondition {
                type_: "Synced".to_string(),
                status: if synced { "True".to_string() } else { "False".to_string() },
                observed_generation: outer_generation,
                reason: Some(reason),
                message: None,
            }]),
        } }
    }

    // The status the sync controller writes on the outer copy when there is no inner
    // status to mirror. See spec_types::outer_status_without_inner.
    #[verifier(external_body)]
    pub fn outer_status_without_inner(outer_generation: Option<i64>, previous: &Option<WidgetStatus>, reason: String) -> (status: WidgetStatus)
        ensures status@ == spec_types::outer_status_without_inner(
            opt_i64_view(outer_generation),
            previous.deep_view(), reason@,
        ),
    {
        let (ready, observed_count) = match previous {
            Some(p) => (p.inner.ready, p.inner.observed_count),
            None => (None, None),
        };
        WidgetStatus { inner: crate::crds::WidgetStatus {
            observed_generation: outer_generation,
            ready: ready,
            observed_count: observed_count,
            conditions: Some(vec![crate::crds::WidgetCondition {
                type_: "Synced".to_string(),
                status: "False".to_string(),
                observed_generation: outer_generation,
                reason: Some(reason),
                message: None,
            }]),
        } }
    }
}

}
