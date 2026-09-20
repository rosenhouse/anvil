// The inner implementation's guarantee (model/inner_impl_reconciler.rs): every
// request it has in flight is a status Patch of the mirror it was triggered by,
// of its own kind, or, when it owns a finalizer, an Update of that mirror that
// takes or releases the finalizer and changes nothing else. Proved as an
// invariant of the cluster model alone, in the style of disturber.rs, and shown
// to imply the relies of both reconcilers.
//
// That it implies the relies is the point: the sync reconciler's rely permits a
// status patch of anything but an outer copy and an update of a mirror that
// keeps its identity, and the janitor's constrains the same update the same way.
// So an inner implementation writing a status, and finalizing the mirrors it
// works on, is a controller the pair tolerates.
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
use crate::vstd_ext::string_view::*;
use crate::widget_sync_controller::{
    model::{inner_impl_reconciler, inner_impl_reconciler::{WidgetInnerImplReconcileState, WidgetInnerImplStepView}, install::*},
    proof::{guarantee::*, sync_invariants::*},
    trusted::{rely_guarantee::*, spec_types::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// The Update the implementation sends for the mirror at `inner_key`: it carries
// the resource version it read the mirror with, and if it lands (that version is
// the stored one) it adds `f` or removes it and changes nothing else. A stale
// update, which the API server rejects with Conflict, is unconstrained. This is
// sync_finalizer_update_req, for the implementation's finalizer.
pub open spec fn inner_impl_finalizer_update_req(kind: Kind, f: StringView, req: UpdateRequest, inner_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let stored = s.resources()[req.key()];
        &&& req.obj.kind == kind
        &&& req.namespace == inner_key.namespace
        &&& req.name == inner_key.name
        &&& req.obj.metadata.resource_version is Some
        &&& (s.resources().contains_key(req.key()) && stored.metadata.resource_version == req.obj.metadata.resource_version) ==> {
            &&& req.obj.spec == stored.spec
            &&& ({
                ||| req.obj.metadata == with_finalizer(stored.metadata, f) && !has_finalizer(stored.metadata, f)
                ||| req.obj.metadata == without_finalizer(stored.metadata, f) && has_finalizer(stored.metadata, f)
            })
        }
    }
}

// The body of widget_inner_impl_guarantee for one message. The resource version
// an Update carries has been issued: that is what keeps the clause about the
// stored object true across a write of the store, which gives the object a
// version the Update cannot carry.
pub open spec fn inner_impl_request_is_guaranteed(kind: Kind, finalizer: Option<StringView>, msg: Message, s: ClusterState) -> bool {
    let inner_key = msg.src->Controller_1;
    match msg.content->APIRequest_0 {
        APIRequest::PatchStatusRequest(req) => req.key() == inner_key && req.kind == kind,
        APIRequest::UpdateRequest(req) => {
            &&& finalizer is Some
            &&& inner_impl_finalizer_update_req(kind, finalizer->0, req, inner_key)(s)
            &&& req.obj.metadata.resource_version->0 < s.api_server.resource_version_counter
        },
        _ => false,
    }
}

pub open spec fn widget_inner_impl_guarantee(kind: Kind, finalizer: Option<StringView>, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } ==> inner_impl_request_is_guaranteed(kind, finalizer, msg, s)
    }
}

pub proof fn lemma_always_widget_inner_impl_guarantee(spec: TempPred<ClusterState>, cluster: Cluster, kind: Kind, finalizer: Option<StringView>, spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(kind, spec_ok, selector),
        cluster.controller_models.contains_pair(controller_id, widget_inner_impl_controller_model(kind, finalizer)),
    ensures spec.entails(always(lift_state(widget_inner_impl_guarantee(kind, finalizer, controller_id)))),
{
    let inv = widget_inner_impl_guarantee(kind, finalizer, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_synced_objects_in_reconcile_are_valid(spec, kind, spec_ok, selector, controller_id);
    cluster.lemma_always_objects_in_reconcile_have_kind(spec, kind, controller_id);
    lemma_always_snapshots_are_current(spec, cluster, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)(s)
        &&& Cluster::objects_in_reconcile_have_kind(kind, controller_id)(s)
        &&& snapshots_are_current(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)),
        lift_state(Cluster::objects_in_reconcile_have_kind(kind, controller_id)),
        lift_state(snapshots_are_current(controller_id))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        unmarshal_of_marshal();
        WidgetInnerImplReconcileState::marshal_preserves_integrity();
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } implies inner_impl_request_is_guaranteed(kind, finalizer, msg, s_prime) by {
            match step {
                Step::APIServerStep(input) => {
                    // No new request from this controller; the store may have changed.
                    assert(s.in_flight().contains(msg));
                    assert(inner_impl_request_is_guaranteed(kind, finalizer, msg, s));
                    lemma_inner_impl_request_guarantee_is_preserved(cluster, kind, finalizer, msg, s, s_prime, step);
                },
                Step::ControllerStep(input) => {
                    assert(s_prime.api_server == s.api_server);
                    if s.in_flight().contains(msg) {
                        assert(inner_impl_request_is_guaranteed(kind, finalizer, msg, s));
                        lemma_inner_impl_request_guarantee_is_preserved(cluster, kind, finalizer, msg, s, s_prime, step);
                    } else {
                        // A request this controller just sent.
                        let (id, resp_msg_opt, cr_key_opt) = input;
                        assert(id == controller_id);
                        let cr_key = cr_key_opt->0;
                        assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
                        assert(msg == s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0);
                        assert(msg.src == HostId::Controller(controller_id, cr_key));
                        lemma_inner_impl_new_request_is_guaranteed(cluster, kind, finalizer, spec_ok, controller_id, s, s_prime, input, msg);
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                    assert(s.in_flight().contains(msg));
                    assert(inner_impl_request_is_guaranteed(kind, finalizer, msg, s));
                    lemma_inner_impl_request_guarantee_is_preserved(cluster, kind, finalizer, msg, s, s_prime, step);
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// A guaranteed request stays guaranteed: only the API server writes the store,
// and a write stamps a version the Update does not carry.
proof fn lemma_inner_impl_request_guarantee_is_preserved(cluster: Cluster, kind: Kind, finalizer: Option<StringView>, msg: Message, s: ClusterState, s_prime: ClusterState, step: Step)
    requires
        inner_impl_request_is_guaranteed(kind, finalizer, msg, s),
        cluster.next_step(s, s_prime, step),
    ensures inner_impl_request_is_guaranteed(kind, finalizer, msg, s_prime),
{
    match msg.content->APIRequest_0 {
        APIRequest::UpdateRequest(req) => {
            let ukey = req.key();
            match step {
                Step::APIServerStep(input) => {
                    lemma_api_server_step_stamps_resource_version(cluster, s, s_prime, input->0, ukey);
                    if s_prime.resources().contains_key(ukey) {
                        if s.resources().contains_key(ukey) && s_prime.resources()[ukey] == s.resources()[ukey] {
                        } else {
                            assert(s_prime.resources()[ukey].metadata.resource_version != req.obj.metadata.resource_version);
                        }
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                },
            }
        },
        _ => {},
    }
}

// The Update of the finalizer built from the snapshot is guaranteed: the snapshot
// carries the stored object's version only if it is the stored object.
proof fn lemma_snapshot_inner_finalizer_update_is_guaranteed(kind: Kind, f: StringView, controller_id: int, s: ClusterState, cr_key: ObjectRef, add: bool)
    requires
        snapshots_are_current(controller_id)(s),
        s.ongoing_reconciles(controller_id).contains_key(cr_key),
        cr_key.kind == kind,
        unmarshal(kind, s.ongoing_reconciles(controller_id)[cr_key].triggering_cr) is Ok,
        unmarshal(kind, s.ongoing_reconciles(controller_id)[cr_key].triggering_cr)->Ok_0.object_ref() == cr_key,
        add == !has_finalizer(unmarshal(kind, s.ongoing_reconciles(controller_id)[cr_key].triggering_cr)->Ok_0.metadata, f),
    ensures ({
        let inner = unmarshal(kind, s.ongoing_reconciles(controller_id)[cr_key].triggering_cr)->Ok_0;
        let req = inner_impl_reconciler::inner_finalizer_update(inner, f, add);
        &&& inner_impl_finalizer_update_req(kind, f, req, cr_key)(s)
        &&& req.obj.metadata.resource_version->0 < s.api_server.resource_version_counter
    }),
{
    marshal_preserves_metadata();
    marshal_preserves_kind();
    let cr = s.ongoing_reconciles(controller_id)[cr_key].triggering_cr;
    let inner = unmarshal(kind, cr)->Ok_0;
    assert(inner.metadata == cr.metadata);
    assert(inner.spec == cr.spec);
    assert(inner.kind == kind);
    let metadata = if add { with_finalizer(inner.metadata, f) } else { without_finalizer(inner.metadata, f) };
    let req = inner_impl_reconciler::inner_finalizer_update(inner, f, add);
    assert(req.obj == marshal(inner.with_metadata(metadata)));
    assert(req.obj.kind == kind);
    assert(req.obj.metadata == metadata);
    assert(req.obj.spec == inner.spec);
    assert(req.obj.metadata.resource_version == cr.metadata.resource_version);
    assert(req.key() == cr_key);
    assert(snapshot_is_current_at(cr_key, cr, s));
    if s.resources().contains_key(cr_key) && s.resources()[cr_key].metadata.resource_version == req.obj.metadata.resource_version {
        assert(s.resources()[cr_key] == cr);
    }
}

proof fn lemma_inner_impl_new_request_is_guaranteed(
    cluster: Cluster, kind: Kind, finalizer: Option<StringView>, spec_ok: spec_fn(Value) -> bool, controller_id: int, s: ClusterState, s_prime: ClusterState,
    input: (int, Option<Message>, Option<ObjectRef>), msg: Message
)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_inner_impl_controller_model(kind, finalizer)),
        cluster.next_step(s, s_prime, Step::ControllerStep(input)),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)(s),
        Cluster::objects_in_reconcile_have_kind(kind, controller_id)(s),
        snapshots_are_current(controller_id)(s),
        input.0 == controller_id,
        input.2 is Some,
        s.ongoing_reconciles(controller_id).contains_key(input.2->0),
        s_prime.ongoing_reconciles(controller_id).contains_key(input.2->0),
        s_prime.ongoing_reconciles(controller_id)[input.2->0].pending_req_msg == Some(msg),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        msg.content is APIRequest,
    ensures inner_impl_request_is_guaranteed(kind, finalizer, msg, s_prime),
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
    let (state_prime, req_o) = inner_impl_reconciler::reconcile_core(kind, finalizer, inner, resp_o, state);
    assert(req_o is Some);
    assert(req_o->0 is KRequest);
    let req = req_o->0->KRequest_0;
    assert(msg.content->APIRequest_0 == req);
    assert(msg.src == HostId::Controller(controller_id, cr_key));
    assert(s_prime.api_server == s.api_server);
    match state.reconcile_step {
        WidgetInnerImplStepView::Init => {
            if finalizer is Some && inner.metadata.deletion_timestamp is Some {
                assert(has_finalizer(inner.metadata, finalizer->0));
                assert(req == APIRequest::UpdateRequest(inner_impl_reconciler::inner_finalizer_update(inner, finalizer->0, false)));
                lemma_snapshot_inner_finalizer_update_is_guaranteed(kind, finalizer->0, controller_id, s, cr_key, false);
            } else if finalizer is Some && !has_finalizer(inner.metadata, finalizer->0) {
                assert(req == APIRequest::UpdateRequest(inner_impl_reconciler::inner_finalizer_update(inner, finalizer->0, true)));
                lemma_snapshot_inner_finalizer_update_is_guaranteed(kind, finalizer->0, controller_id, s, cr_key, true);
            } else {
                assert(req == APIRequest::PatchStatusRequest(inner_impl_reconciler::inner_status_patch(kind, inner)));
                assert(inner_impl_reconciler::inner_status_patch(kind, inner).key() == cr_key);
            }
        },
        _ => { assert(false); },
    }
}

// Taking or releasing a finalizer keeps a mirror's identity: the labels, the
// annotations and the owner references are untouched.
pub proof fn lemma_finalizer_update_keeps_identity(meta: ObjectMetaView, f: StringView)
    ensures
        with_finalizer(meta, f).labels == meta.labels,
        with_finalizer(meta, f).annotations == meta.annotations,
        with_finalizer(meta, f).owner_references == meta.owner_references,
        without_finalizer(meta, f).labels == meta.labels,
        without_finalizer(meta, f).annotations == meta.annotations,
        without_finalizer(meta, f).owner_references == meta.owner_references,
        preserves_mirror_identity(meta, with_finalizer(meta, f)),
        preserves_mirror_identity(meta, without_finalizer(meta, f)),
{
}

// The inner implementation's guarantee implies what both reconcilers rely on. A
// status Patch of a mirror: the sync reconciler's rely asks only that it not name
// the outer kind, and a mirror kind is not the outer kind
// (lemma_outer_kind_is_not_inner); the janitor's rely does not constrain it. An
// Update of a mirror's finalizers: both relies ask that it carry a version and,
// if it lands, keep the owner references and the identity, which it does.
pub proof fn inner_impl_guarantee_implies_relies(k: SyncKind, b: Binding, finalizer: Option<StringView>, id: int)
    requires sync_kind_ok(k),
    ensures
        lift_state(widget_inner_impl_guarantee(inner_kind(k, b), finalizer, id)).entails(lift_state(widget_sync_rely(k, id))),
        lift_state(widget_inner_impl_guarantee(inner_kind(k, b), finalizer, id)).entails(lift_state(widget_janitor_rely(k, id))),
{
    let kind = inner_kind(k, b);
    lemma_outer_kind_is_not_inner(k, b);
    assert forall |s: ClusterState| #[trigger] widget_inner_impl_guarantee(kind, finalizer, id)(s) implies widget_sync_rely(k, id)(s) && widget_janitor_rely(k, id)(s) by {
        assert forall |msg| #[trigger] s.in_flight().contains(msg)
            && msg.content is APIRequest
            && msg.src.is_controller_id(id)
            implies {
                ||| msg.content->APIRequest_0 is PatchStatusRequest && msg.content->APIRequest_0->PatchStatusRequest_0.kind == kind
                ||| msg.content->APIRequest_0 is UpdateRequest && mirror_update_req(k, msg.content->APIRequest_0->UpdateRequest_0)(s)
            } by {
            assert(inner_impl_request_is_guaranteed(kind, finalizer, msg, s));
            if msg.content->APIRequest_0 is UpdateRequest {
                let req = msg.content->APIRequest_0->UpdateRequest_0;
                let stored = s.resources()[req.key()];
                lemma_finalizer_update_keeps_identity(stored.metadata, finalizer->0);
            }
        }
    }
}

}
