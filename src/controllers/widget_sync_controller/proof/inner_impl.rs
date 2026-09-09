// The inner implementation's guarantee (model/inner_impl_reconciler.rs): every
// request it has in flight is a status Patch of the mirror it was triggered by,
// of its own kind. Proved as an invariant of the cluster model alone, in the
// style of disturber.rs, and shown to imply the relies of both reconcilers.
//
// That it implies the relies is the point: the sync reconciler's rely permits a
// status patch of anything but an outer copy, and the janitor's does not
// constrain one at all. So an inner implementation writing a status is a
// controller the pair tolerates.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::reconciler::spec::io::*;
use crate::widget_sync_controller::{
    model::{inner_impl_reconciler, inner_impl_reconciler::{WidgetInnerImplReconcileState, WidgetInnerImplStepView}, install::*},
    trusted::{rely_guarantee::*, spec_types::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// The body of widget_inner_impl_guarantee for one message.
pub open spec fn inner_impl_request_is_guaranteed(kind: Kind, msg: Message) -> bool {
    let inner_key = msg.src->Controller_1;
    match msg.content->APIRequest_0 {
        APIRequest::PatchStatusRequest(req) => req.key() == inner_key && req.kind == kind,
        _ => false,
    }
}

pub open spec fn widget_inner_impl_guarantee(kind: Kind, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> inner_impl_request_is_guaranteed(kind, msg)
    }
}

pub proof fn lemma_always_widget_inner_impl_guarantee(spec: TempPred<ClusterState>, cluster: Cluster, kind: Kind, spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(kind, spec_ok, selector),
        cluster.controller_models.contains_pair(controller_id, widget_inner_impl_controller_model(kind)),
    ensures spec.entails(always(lift_state(widget_inner_impl_guarantee(kind, controller_id)))),
{
    let inv = widget_inner_impl_guarantee(kind, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_synced_objects_in_reconcile_are_valid(spec, kind, spec_ok, selector, controller_id);
    cluster.lemma_always_objects_in_reconcile_have_kind(spec, kind, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)(s)
        &&& Cluster::objects_in_reconcile_have_kind(kind, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)),
        lift_state(Cluster::objects_in_reconcile_have_kind(kind, controller_id))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        unmarshal_of_marshal();
        WidgetInnerImplReconcileState::marshal_preserves_integrity();
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } implies inner_impl_request_is_guaranteed(kind, msg) by {
            if s.in_flight().contains(msg) {
                assert(inner_impl_request_is_guaranteed(kind, msg));
            } else {
                match step {
                    Step::ControllerStep(input) => {
                        let (id, resp_msg_opt, cr_key_opt) = input;
                        assert(id == controller_id);
                        let cr_key = cr_key_opt->0;
                        assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
                        assert(msg == s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0);
                        assert(msg.src == HostId::Controller(controller_id, cr_key));
                        lemma_inner_impl_new_request_is_guaranteed(cluster, kind, spec_ok, controller_id, s, s_prime, input, msg);
                    },
                    _ => { assert(false); },
                }
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

proof fn lemma_inner_impl_new_request_is_guaranteed(
    cluster: Cluster, kind: Kind, spec_ok: spec_fn(Value) -> bool, controller_id: int, s: ClusterState, s_prime: ClusterState,
    input: (int, Option<Message>, Option<ObjectRef>), msg: Message
)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_inner_impl_controller_model(kind)),
        cluster.next_step(s, s_prime, Step::ControllerStep(input)),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)(s),
        Cluster::objects_in_reconcile_have_kind(kind, controller_id)(s),
        input.0 == controller_id,
        input.2 is Some,
        s.ongoing_reconciles(controller_id).contains_key(input.2->0),
        s_prime.ongoing_reconciles(controller_id).contains_key(input.2->0),
        s_prime.ongoing_reconciles(controller_id)[input.2->0].pending_req_msg == Some(msg),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        msg.content is APIRequest,
    ensures inner_impl_request_is_guaranteed(kind, msg),
{
    unmarshal_of_marshal();
    WidgetInnerImplReconcileState::marshal_preserves_integrity();
    let cr_key = input.2->0;
    let reconcile = s.ongoing_reconciles(controller_id)[cr_key];
    assert(cr_key.kind == kind);
    assert(unmarshal(kind, reconcile.triggering_cr) is Ok);
    let inner = unmarshal(kind, reconcile.triggering_cr)->Ok_0;
    assert(inner.metadata == reconcile.triggering_cr.metadata);
    assert(reconcile.triggering_cr.object_ref() == cr_key);
    assert(inner.object_ref() == cr_key);
    let state = WidgetInnerImplReconcileState::unmarshal(reconcile.local_state)->Ok_0;
    let resp_o = if input.1 is Some {
        if input.1->0.content is APIResponse {
            Some(ResponseView::<VoidERespView>::KResponse(input.1->0.content->APIResponse_0))
        } else {
            Some(ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(input.1->0.content->ExternalResponse_0)->Ok_0))
        }
    } else {
        None
    };
    let (state_prime, req_o) = inner_impl_reconciler::reconcile_core(kind, inner, resp_o, state);
    assert(req_o is Some);
    assert(req_o->0 is KRequest);
    let req = req_o->0->KRequest_0;
    assert(msg.content->APIRequest_0 == req);
    assert(msg.src == HostId::Controller(controller_id, cr_key));
    match state.reconcile_step {
        WidgetInnerImplStepView::Init => {
            assert(req == APIRequest::PatchStatusRequest(inner_impl_reconciler::inner_status_patch(kind, inner)));
            assert(inner_impl_reconciler::inner_status_patch(kind, inner).key() == cr_key);
        },
        _ => { assert(false); },
    }
}

// The inner implementation's guarantee implies what both reconcilers rely on. It
// sends nothing but a status Patch of a mirror: the sync reconciler's rely asks
// only that a status Patch not name the outer kind, and a mirror kind is not the
// outer kind (lemma_outer_kind_is_not_inner); the janitor's rely constrains
// Creates and Updates, of which it sends neither.
pub proof fn inner_impl_guarantee_implies_relies(k: SyncKind, b: Binding, id: int)
    requires sync_kind_ok(k),
    ensures
        lift_state(widget_inner_impl_guarantee(inner_kind(k, b), id)).entails(lift_state(widget_sync_rely(k, id))),
        lift_state(widget_inner_impl_guarantee(inner_kind(k, b), id)).entails(lift_state(widget_janitor_rely(k, id))),
{
    let kind = inner_kind(k, b);
    lemma_outer_kind_is_not_inner(k, b);
    assert forall |s: ClusterState| #[trigger] widget_inner_impl_guarantee(kind, id)(s) implies widget_sync_rely(k, id)(s) && widget_janitor_rely(k, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies msg.content->APIRequest_0 is PatchStatusRequest
                && msg.content->APIRequest_0->PatchStatusRequest_0.kind == kind by {
            assert(inner_impl_request_is_guaranteed(kind, msg));
        }
    }
}

}
