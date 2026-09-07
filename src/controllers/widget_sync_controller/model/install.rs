use crate::kubernetes_api_objects::{error::*, spec::prelude::*};
use crate::kubernetes_cluster::spec::cluster::{Cluster, ControllerModel};
use crate::reconciler::spec::io::{VoidEReqView, VoidERespView};
use crate::widget_sync_controller::model::{janitor_reconciler::*, sync_reconciler::*};
use crate::widget_sync_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

impl Marshallable for WidgetSyncReconcileState {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0
    {}
}

impl Marshallable for WidgetJanitorReconcileState {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0
    {}
}

pub open spec fn widget_sync_controller_model() -> ControllerModel {
    ControllerModel {
        reconcile_model: Cluster::installed_reconcile_model::<WidgetSyncReconciler, WidgetSyncReconcileState, OuterWidgetView, VoidEReqView, VoidERespView>(),
        external_model: None,
    }
}

pub open spec fn widget_janitor_controller_model() -> ControllerModel {
    ControllerModel {
        reconcile_model: Cluster::installed_reconcile_model::<WidgetJanitorReconciler, WidgetJanitorReconcileState, InnerWidgetView, VoidEReqView, VoidERespView>(),
        external_model: None,
    }
}

}
