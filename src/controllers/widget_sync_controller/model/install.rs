use crate::kubernetes_api_objects::{error::*, spec::prelude::*};
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::spec::cluster::{Cluster, ControllerModel};
use crate::reconciler::spec::io::{VoidEReqView, VoidERespView};
use crate::widget_sync_controller::model::{disturber_reconciler, janitor_reconciler, sync_reconciler};
use crate::widget_sync_controller::model::{disturber_reconciler::WidgetDisturberReconcileState, janitor_reconciler::WidgetJanitorReconcileState, sync_reconciler::WidgetSyncReconcileState};
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

impl Marshallable for WidgetDisturberReconcileState {
    uninterp spec fn marshal(self) -> Value;

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0
    {}
}

// The sync controller of the kind `k`: triggered by outer copies of `k`.
pub open spec fn widget_sync_controller_model(k: SyncKind) -> ControllerModel {
    ControllerModel {
        reconcile_model: Cluster::synced_reconcile_model::<WidgetSyncReconcileState, VoidEReqView, VoidERespView>(
            k.outer_kind,
            || sync_reconciler::reconcile_init_state(),
            |obj: SyncedObjectView, resp_o, s| sync_reconciler::reconcile_core(k, obj, resp_o, s),
            |s| sync_reconciler::reconcile_done(s),
            |s| sync_reconciler::reconcile_error(s),
        ),
        external_model: None,
    }
}

// The janitor of the kind `k` in the binding `b`: triggered by mirrors of `k` in `b`.
pub open spec fn widget_janitor_controller_model(k: SyncKind, b: Binding) -> ControllerModel {
    ControllerModel {
        reconcile_model: Cluster::synced_reconcile_model::<WidgetJanitorReconcileState, VoidEReqView, VoidERespView>(
            inner_kind(k, b),
            || janitor_reconciler::reconcile_init_state(),
            |obj: SyncedObjectView, resp_o, s| janitor_reconciler::reconcile_core(k, b, obj, resp_o, s),
            |s| janitor_reconciler::reconcile_done(s),
            |s| janitor_reconciler::reconcile_error(s),
        ),
        external_model: None,
    }
}

// The disturber's edit is really an edit: it never writes back the value it
// found. `disturbed_spec` (model/disturber_reconciler.rs) is uninterpreted, so
// without this nothing rules out the identity, and a disturber that leaves the
// spec alone is not a disturbance -- the premise of R1 and R2, "no edit of the
// mirror's spec is in flight", would be met by a Patch that changes nothing.
//
// Trusted, and model-only: the disturber stands for a `kubectl edit`, it has no
// exec twin, and this is the one assumption made about what that edit writes.
// It is inventoried with the other trusted items of the pair
// (doc/widget_sync_design.md, section 3).
#[verifier(external_body)]
pub proof fn disturbed_spec_changes_the_spec()
    ensures forall |v: Value| #[trigger] disturber_reconciler::disturbed_spec(v) != v,
{}

// The out-of-band actor of model/disturber_reconciler.rs, as a controller model,
// acting on the objects of one inner kind.
pub open spec fn widget_disturber_controller_model(kind: Kind) -> ControllerModel {
    ControllerModel {
        reconcile_model: Cluster::synced_reconcile_model::<WidgetDisturberReconcileState, VoidEReqView, VoidERespView>(
            kind,
            || disturber_reconciler::reconcile_init_state(),
            |obj: SyncedObjectView, resp_o, s| disturber_reconciler::reconcile_core(kind, obj, resp_o, s),
            |s| disturber_reconciler::reconcile_done(s),
            |s| disturber_reconciler::reconcile_error(s),
        ),
        external_model: None,
    }
}

}
