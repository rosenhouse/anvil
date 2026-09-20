// D3 for the cluster that runs the inner implementation
// (model/inner_impl_reconciler.rs) beside the pair: a terminating mirror of the
// implementation's kind is eventually gone.
//
// With the implementation's finalizer set, the mirror's finalizers are the
// implementation's alone (nothing else in this cluster writes finalizers of that
// kind), so a terminating mirror holds exactly that finalizer, and the
// implementation's next reconcile of it, working from a current snapshot, sends
// the Update that releases it, which removes the mirror. Nothing else writes a
// terminating mirror: the sync controller's spec patches and the
// implementation's own status patches test the generation of a live view of the
// mirror, and the deletion stamp bumped it. With no finalizer, no mirror of the
// kind ever carries one, so none ever terminates, and D3 holds vacuously.
#![allow(unused_imports)]
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::kubernetes_cluster::proof::{api_server::*, temporal_rules::*};
use crate::kubernetes_cluster::spec::install_helpers::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use crate::reconciler::spec::io::*;
use crate::vstd_ext::{set_lib::*, string_view::*};
use crate::widget_sync_controller::{
    model::{inner_impl_reconciler, inner_impl_reconciler::{WidgetInnerImplReconcileState, WidgetInnerImplStepView}, install::*, sync_reconciler, sync_reconciler::WidgetSyncReconcileState},
    proof::{guarantee::*, helper_invariants::*, inner_impl::*, liveness::finalizer_proof::*, liveness::spec::*, predicate::*, sync_invariants::*},
    trusted::{liveness_theorem::*, rely_guarantee::*, spec_types::*, step::*},
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// The fairness the D3 proof assumes of the implementation: its own steps, the
// API server, scheduling, and the disabling of failures. The same shape as
// sync_next_with_wf.
pub open spec fn inner_impl_next_with_wf(cluster: Cluster, controller_id: int) -> TempPred<ClusterState> {
    always(lift_action(cluster.next()))
    .and(tla_forall(|input| cluster.api_server_next().weak_fairness(input)))
    .and(tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))))
    .and(tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))))
    .and(tla_forall(|input| cluster.disable_crash().weak_fairness(input)))
    .and(tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))))
    .and(cluster.disable_req_drop().weak_fairness(()))
    .and(cluster.disable_pod_monkey().weak_fairness(()))
}

// ---------------------------------------------------------------------------
// Generations: a view of an object is never ahead of the store.
// ---------------------------------------------------------------------------

// A step of the API server never lowers the generation of a custom resource that
// keeps its uid, and changes it whenever it changes the object's deletion state:
// a spec change bumps it, and so does the deletion stamp.
pub proof fn lemma_api_server_step_keeps_generation(cluster: Cluster, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        key.kind is CustomResourceKind,
        s.resources().contains_key(key),
        s_prime.resources().contains_key(key),
        s_prime.resources()[key].metadata.uid == s.resources()[key].metadata.uid,
        s.resources()[key].metadata.generation is Some,
    ensures
        s_prime.resources()[key].metadata.generation is Some,
        s.resources()[key].metadata.generation->0 <= s_prime.resources()[key].metadata.generation->0,
        s_prime.resources()[key].metadata.generation == s.resources()[key].metadata.generation
            ==> (s_prime.resources()[key].metadata.deletion_timestamp is Some) == (s.resources()[key].metadata.deletion_timestamp is Some),
{
    let old = s.resources()[key];
    let new = s_prime.resources()[key];
    assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    assert(old.object_ref() == key);
    assert(old.kind is CustomResourceKind);
    if new != old {
        match msg.content->APIRequest_0 {
            APIRequest::CreateRequest(req) => {
                // The key is taken: the Create fails, or writes another key.
                assert(new.metadata.uid == Some(s.api_server.uid_counter));
                assert(old.metadata.uid->0 < s.api_server.uid_counter);
                assert(false);
            },
            APIRequest::UpdateRequest(req) => {
                assert(new.metadata.generation == next_generation(old, req.obj.spec));
                assert(new.metadata.deletion_timestamp == old.metadata.deletion_timestamp);
            },
            APIRequest::GetThenUpdateRequest(req) => {
                assert(new.metadata.generation == next_generation(old, req.obj.spec));
                assert(new.metadata.deletion_timestamp == old.metadata.deletion_timestamp);
            },
            APIRequest::PatchRequest(req) => {
                assert(new.metadata.generation == next_generation(old, req.spec));
                assert(new.metadata.deletion_timestamp == old.metadata.deletion_timestamp);
            },
            APIRequest::DeleteRequest(req) => {
                assert(new.metadata.generation == bumped_generation(old));
                assert(new.metadata.deletion_timestamp is Some);
            },
            APIRequest::GetThenDeleteRequest(req) => {
                assert(new.metadata.generation == bumped_generation(old));
                assert(new.metadata.deletion_timestamp is Some);
            },
            _ => {
                // Status writes keep the metadata but the version.
                assert(new.metadata.generation == old.metadata.generation);
                assert(new.metadata.deletion_timestamp == old.metadata.deletion_timestamp);
            },
        }
    }
}

// Every stored custom resource carries a generation: a Create gives it one, and
// every write keeps or bumps it.
pub open spec fn custom_resources_have_generations() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.resources().contains_key(key) && key.kind is CustomResourceKind
            ==> s.resources()[key].metadata.generation is Some
    }
}

pub proof fn lemma_always_custom_resources_have_generations(spec: TempPred<ClusterState>, cluster: Cluster)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(custom_resources_have_generations()))),
{
    let inv = custom_resources_have_generations();
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && key.kind is CustomResourceKind
            implies s_prime.resources()[key].metadata.generation is Some by {
            match step {
                Step::APIServerStep(input) => {
                    let msg = input->0;
                    if s.resources().contains_key(key) && s_prime.resources()[key] == s.resources()[key] {
                    } else {
                        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s) || !s.resources().contains_key(key));
                        match msg.content->APIRequest_0 {
                            APIRequest::CreateRequest(req) => {
                                assert(s_prime.resources()[key].metadata.generation == initial_generation(req.obj.kind));
                                assert(req.obj.kind == key.kind);
                            },
                            APIRequest::UpdateRequest(req) => {
                                let old = s.resources()[key];
                                assert(s_prime.resources()[key].metadata.generation == next_generation(old, req.obj.spec));
                                assert(old.kind == key.kind);
                            },
                            APIRequest::GetThenUpdateRequest(req) => {
                                let old = s.resources()[key];
                                assert(s_prime.resources()[key].metadata.generation == next_generation(old, req.obj.spec));
                                assert(old.kind == key.kind);
                            },
                            APIRequest::PatchRequest(req) => {
                                let old = s.resources()[key];
                                assert(s_prime.resources()[key].metadata.generation == next_generation(old, req.spec));
                                assert(old.kind == key.kind);
                            },
                            APIRequest::DeleteRequest(req) => {
                                let old = s.resources()[key];
                                assert(s_prime.resources()[key].metadata.generation == bumped_generation(old));
                                assert(old.kind == key.kind);
                            },
                            APIRequest::GetThenDeleteRequest(req) => {
                                let old = s.resources()[key];
                                assert(s_prime.resources()[key].metadata.generation == bumped_generation(old));
                                assert(old.kind == key.kind);
                            },
                            _ => {
                                assert(s_prime.resources()[key].metadata.generation == s.resources()[key].metadata.generation);
                            },
                        }
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// The view `o` of the object at `key` is not ahead of the store: it names an
// issued uid, and a stored custom resource at `key` with that uid has a generation
// at least the view's, and at the view's generation the view's deletion state.
pub open spec fn view_is_not_ahead_at(key: ObjectRef, o: DynamicObjectView, s: ClusterState) -> bool {
    let stored = s.resources()[key];
    &&& o.metadata.uid is Some
    &&& o.metadata.uid->0 < s.api_server.uid_counter
    &&& key.kind is CustomResourceKind ==> o.metadata.generation is Some
    &&& (key.kind is CustomResourceKind
        && s.resources().contains_key(key) && stored.metadata.uid == o.metadata.uid) ==> {
        &&& stored.metadata.generation is Some
        &&& o.metadata.generation->0 <= stored.metadata.generation->0
        &&& stored.metadata.generation == o.metadata.generation
            ==> (stored.metadata.deletion_timestamp is Some) == (o.metadata.deletion_timestamp is Some)
    }
}

// A step of the API server keeps a view not ahead: the object it writes at the key
// keeps its uid and moves its generation forward, or is a new one with a fresh uid.
proof fn lemma_view_stays_not_ahead_across_api_server_step(cluster: Cluster, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef, o: DynamicObjectView)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        view_is_not_ahead_at(key, o, s),
    ensures view_is_not_ahead_at(key, o, s_prime),
{
    assert(s_prime.api_server.uid_counter >= s.api_server.uid_counter);
    if key.kind is CustomResourceKind
        && s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == o.metadata.uid {
        if s.resources().contains_key(key) && s.resources()[key].metadata.uid == o.metadata.uid {
            lemma_api_server_step_keeps_generation(cluster, s, s_prime, msg, key);
        } else {
            // A new object at the key, with a fresh uid the view does not name.
            assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
            assert(false);
        }
    }
}

// The snapshots a controller works from are not ahead of the store.
pub open spec fn snapshots_are_not_ahead(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |key: ObjectRef| #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            ==> view_is_not_ahead_at(key, s.scheduled_reconciles(controller_id)[key], s)
        &&& forall |key: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> view_is_not_ahead_at(key, s.ongoing_reconciles(controller_id)[key].triggering_cr, s)
    }
}

pub proof fn lemma_always_snapshots_are_not_ahead(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(snapshots_are_not_ahead(controller_id)))),
{
    let inv = snapshots_are_not_ahead(controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    lemma_always_custom_resources_have_generations(spec, cluster);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& custom_resources_have_generations()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(custom_resources_have_generations())
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                assert(s_prime.scheduled_reconciles(controller_id) == s.scheduled_reconciles(controller_id));
                assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                    implies view_is_not_ahead_at(key, s_prime.scheduled_reconciles(controller_id)[key], s_prime) by {
                    lemma_view_stays_not_ahead_across_api_server_step(cluster, s, s_prime, input->0, key, s.scheduled_reconciles(controller_id)[key]);
                }
                assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
                    implies view_is_not_ahead_at(key, s_prime.ongoing_reconciles(controller_id)[key].triggering_cr, s_prime) by {
                    lemma_view_stays_not_ahead_across_api_server_step(cluster, s, s_prime, input->0, key, s.ongoing_reconciles(controller_id)[key].triggering_cr);
                }
            },
            Step::ScheduleControllerReconcileStep(input) => {
                assert(s_prime.api_server == s.api_server);
                assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                    implies view_is_not_ahead_at(key, s_prime.scheduled_reconciles(controller_id)[key], s_prime) by {
                    if input.0 == controller_id && input.1 == key {
                        // The new snapshot is the stored object.
                        assert(s.resources().contains_key(key));
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.resources()[key]);
                        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                    } else {
                        assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                    }
                }
            },
            Step::ControllerStep(input) => {
                assert(s_prime.api_server == s.api_server);
                assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
                    implies view_is_not_ahead_at(key, s_prime.scheduled_reconciles(controller_id)[key], s_prime) by {
                    assert(s.scheduled_reconciles(controller_id).contains_key(key));
                    assert(s_prime.scheduled_reconciles(controller_id)[key] == s.scheduled_reconciles(controller_id)[key]);
                }
                assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
                    implies view_is_not_ahead_at(key, s_prime.ongoing_reconciles(controller_id)[key].triggering_cr, s_prime) by {
                    if input.0 == controller_id && input.2 == Some(key) {
                        if s.ongoing_reconciles(controller_id).contains_key(key) {
                            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.ongoing_reconciles(controller_id)[key].triggering_cr);
                        } else {
                            assert(s.scheduled_reconciles(controller_id).contains_key(key));
                            assert(s_prime.ongoing_reconciles(controller_id)[key].triggering_cr == s.scheduled_reconciles(controller_id)[key]);
                        }
                    } else {
                        assert(s_prime.ongoing_reconciles(controller_id)[key] == s.ongoing_reconciles(controller_id)[key]);
                    }
                }
            },
            Step::RestartControllerStep(id) => {
                assert(s_prime.api_server == s.api_server);
                if id == controller_id {
                    assert(s_prime.scheduled_reconciles(controller_id) =~= Map::empty());
                    assert(s_prime.ongoing_reconciles(controller_id) =~= Map::empty());
                } else {
                    assert(s_prime.scheduled_reconciles(controller_id) == s.scheduled_reconciles(controller_id));
                    assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
                }
            },
            _ => {
                assert(s_prime.api_server == s.api_server);
                assert(s_prime.scheduled_reconciles(controller_id) == s.scheduled_reconciles(controller_id));
                assert(s_prime.ongoing_reconciles(controller_id) == s.ongoing_reconciles(controller_id));
            },
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// The object a Get answered with: well formed, the only holder of its uid, and
// not ahead of the store at its own key.
pub open spec fn get_response_is_not_ahead(obj: DynamicObjectView, s: ClusterState) -> bool {
    &&& obj.metadata.well_formed_for_namespaced()
    &&& forall |key: ObjectRef| #[trigger] s.resources().contains_key(key) && s.resources()[key].metadata.uid == obj.metadata.uid
        ==> key == obj.object_ref()
    &&& view_is_not_ahead_at(obj.object_ref(), obj, s)
}

// Every Get in flight was answered with such an object.
pub open spec fn get_responses_are_not_ahead() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIResponse
            &&& msg.content->APIResponse_0 is GetResponse
            &&& msg.content->APIResponse_0->GetResponse_0.res is Ok
        } ==> get_response_is_not_ahead(msg.content->APIResponse_0->GetResponse_0.res->Ok_0, s)
    }
}

proof fn lemma_get_response_stays_not_ahead_across_api_server_step(cluster: Cluster, s: ClusterState, s_prime: ClusterState, msg: Message, obj: DynamicObjectView)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        get_response_is_not_ahead(obj, s),
    ensures get_response_is_not_ahead(obj, s_prime),
{
    lemma_view_stays_not_ahead_across_api_server_step(cluster, s, s_prime, msg, obj.object_ref(), obj);
    assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == obj.metadata.uid
        implies key == obj.object_ref() by {
        if !(s.resources().contains_key(key) && s.resources()[key].metadata.uid == obj.metadata.uid) {
            // A new object at the key, with a fresh uid.
            assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
            assert(false);
        }
    }
}

pub proof fn lemma_always_get_responses_are_not_ahead(spec: TempPred<ClusterState>, cluster: Cluster)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
    ensures spec.entails(always(lift_state(get_responses_are_not_ahead()))),
{
    let inv = get_responses_are_not_ahead();
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_etcd_objects_have_unique_uids(spec);
    lemma_always_custom_resources_have_generations(spec, cluster);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::etcd_objects_have_unique_uids()(s)
        &&& custom_resources_have_generations()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::etcd_objects_have_unique_uids()),
        lift_state(custom_resources_have_generations())
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIResponse
            &&& msg.content->APIResponse_0 is GetResponse
            &&& msg.content->APIResponse_0->GetResponse_0.res is Ok
        } implies get_response_is_not_ahead(msg.content->APIResponse_0->GetResponse_0.res->Ok_0, s_prime) by {
            let obj = msg.content->APIResponse_0->GetResponse_0.res->Ok_0;
            match step {
                Step::APIServerStep(input) => {
                    let req_msg = input->0;
                    if s.in_flight().contains(msg) {
                        lemma_get_response_stays_not_ahead_across_api_server_step(cluster, s, s_prime, req_msg, obj);
                    } else {
                        // The answer to the Get handled in this step: the stored object
                        // at the key, which the step leaves as it is.
                        assert(msg == transition_by_etcd(cluster.installed_types, req_msg, s.api_server).1);
                        assert(req_msg.content->APIRequest_0 is GetRequest);
                        let key = req_msg.content->APIRequest_0->GetRequest_0.key;
                        assert(s.resources().contains_key(key));
                        assert(obj == s.resources()[key]);
                        assert(s_prime.api_server == s.api_server);
                        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                        assert(obj.object_ref() == key);
                        assert forall |k2: ObjectRef| #[trigger] s_prime.resources().contains_key(k2) && s_prime.resources()[k2].metadata.uid == obj.metadata.uid
                            implies k2 == key by {
                            if k2 != key {
                                assert(s.resources()[k2].metadata.uid->0 != s.resources()[key].metadata.uid->0);
                            }
                        }
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                    assert(s.in_flight().contains(msg));
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// ---------------------------------------------------------------------------
// Patches test live generations.
// ---------------------------------------------------------------------------

// The tests of a patch of the object at `key` name an issued uid and a
// generation, and the stored object with that uid has a generation at least the
// tested one, and is live at the tested one: the tests were read off a live view.
pub open spec fn patch_tests_are_not_ahead(tests: PatchTestsView, key: ObjectRef, s: ClusterState) -> bool {
    let stored = s.resources()[key];
    &&& tests.uid is Some
    &&& tests.generation is Some
    &&& tests.uid->0 < s.api_server.uid_counter
    &&& (s.resources().contains_key(key) && stored.metadata.uid == tests.uid) ==> {
        &&& stored.metadata.generation is Some
        &&& tests.generation->0 <= stored.metadata.generation->0
        &&& stored.metadata.generation == tests.generation ==> stored.metadata.deletion_timestamp is None
    }
}

proof fn lemma_patch_tests_stay_not_ahead_across_api_server_step(cluster: Cluster, s: ClusterState, s_prime: ClusterState, msg: Message, tests: PatchTestsView, key: ObjectRef)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        key.kind is CustomResourceKind,
        patch_tests_are_not_ahead(tests, key, s),
    ensures patch_tests_are_not_ahead(tests, key, s_prime),
{
    assert(s_prime.api_server.uid_counter >= s.api_server.uid_counter);
    if s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == tests.uid {
        if s.resources().contains_key(key) && s.resources()[key].metadata.uid == tests.uid {
            lemma_api_server_step_keeps_generation(cluster, s, s_prime, msg, key);
        } else {
            assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
            assert(false);
        }
    }
}

// The tests of a patch built from a live view of the object are not ahead.
proof fn lemma_patch_tests_from_live_view(o: DynamicObjectView, key: ObjectRef, s: ClusterState)
    requires
        o.metadata.deletion_timestamp is None,
        key.kind is CustomResourceKind,
        view_is_not_ahead_at(key, o, s),
    ensures patch_tests_are_not_ahead(PatchTestsView::default().with_uid_from_object_meta(o.metadata).with_generation_from_object_meta(o.metadata), key, s),
{
}

// Every spec Patch of the sync reconciler tests a live generation: it is built
// from the answer to its Get, which showed the mirror live.
pub open spec fn sync_patches_are_not_ahead(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.content->APIRequest_0 is PatchRequest
        } ==> patch_tests_are_not_ahead(msg.content->APIRequest_0->PatchRequest_0.tests, msg.content->APIRequest_0->PatchRequest_0.key(), s)
    }
}

pub proof fn lemma_always_sync_patches_are_not_ahead(spec: TempPred<ClusterState>, cluster: Cluster, k: SyncKind, spec_ok: spec_fn(Value) -> bool, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector),
        cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model(k)),
    ensures spec.entails(always(lift_state(sync_patches_are_not_ahead(controller_id)))),
{
    let inv = sync_patches_are_not_ahead(controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    lemma_always_get_responses_are_not_ahead(spec, cluster);
    lemma_always_widget_sync_guarantee(spec, cluster, k, spec_ok, controller_id);
    cluster.lemma_always_synced_objects_in_reconcile_are_valid(spec, k.outer_kind, spec_ok, k.selector, controller_id);
    cluster.lemma_always_objects_in_reconcile_have_kind(spec, k.outer_kind, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& get_responses_are_not_ahead()(s)
        &&& widget_sync_guarantee(k, controller_id)(s)
        &&& cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)(s)
        &&& Cluster::objects_in_reconcile_have_kind(k.outer_kind, controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(get_responses_are_not_ahead()),
        lift_state(widget_sync_guarantee(k, controller_id)),
        lift_state(cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)),
        lift_state(Cluster::objects_in_reconcile_have_kind(k.outer_kind, controller_id))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.content->APIRequest_0 is PatchRequest
        } implies patch_tests_are_not_ahead(msg.content->APIRequest_0->PatchRequest_0.tests, msg.content->APIRequest_0->PatchRequest_0.key(), s_prime) by {
            let req = msg.content->APIRequest_0->PatchRequest_0;
            match step {
                Step::APIServerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    assert(widget_sync_guarantee(k, controller_id)(s_prime) || true);
                    // The patch names a mirror kind, a custom resource.
                    assert(is_inner_kind(k, req.kind));
                    let b = choose |b: Binding| req.kind == #[trigger] inner_kind(k, b);
                    assert(req.key().kind is CustomResourceKind);
                    lemma_patch_tests_stay_not_ahead_across_api_server_step(cluster, s, s_prime, input->0, req.tests, req.key());
                },
                Step::ControllerStep(input) => {
                    assert(s_prime.api_server == s.api_server);
                    if s.in_flight().contains(msg) {
                    } else {
                        lemma_sync_new_patch_is_not_ahead(cluster, k, spec_ok, controller_id, s, s_prime, input, msg);
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                    assert(s.in_flight().contains(msg));
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// The Patch the sync reconciler just sent tests the uid and generation of the
// object its Get was answered with, which was live.
proof fn lemma_sync_new_patch_is_not_ahead(
    cluster: Cluster, k: SyncKind, spec_ok: spec_fn(Value) -> bool, controller_id: int, s: ClusterState, s_prime: ClusterState,
    input: (int, Option<Message>, Option<ObjectRef>), msg: Message
)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_sync_controller_model(k)),
        cluster.next_step(s, s_prime, Step::ControllerStep(input)),
        Cluster::there_is_the_controller_state(controller_id)(s),
        get_responses_are_not_ahead()(s),
        cluster.synced_objects_in_reconcile_are_valid(k.outer_kind, spec_ok, controller_id)(s),
        Cluster::objects_in_reconcile_have_kind(k.outer_kind, controller_id)(s),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        msg.content is APIRequest,
        msg.src.is_controller_id(controller_id),
        msg.content->APIRequest_0 is PatchRequest,
    ensures patch_tests_are_not_ahead(msg.content->APIRequest_0->PatchRequest_0.tests, msg.content->APIRequest_0->PatchRequest_0.key(), s_prime),
{
    hide(ready_condition_for);
    hide(stalled_condition_for);
    unmarshal_of_marshal();
    WidgetSyncReconcileState::marshal_preserves_integrity();
    marshal_preserves_metadata();
    let (id, resp_msg_opt, cr_key_opt) = input;
    assert(id == controller_id);
    let cr_key = cr_key_opt->0;
    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
    assert(msg == s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0);
    let reconcile = s.ongoing_reconciles(controller_id)[cr_key];
    assert(cr_key.kind == k.outer_kind);
    assert(unmarshal(k.outer_kind, reconcile.triggering_cr) is Ok);
    let outer = unmarshal(k.outer_kind, reconcile.triggering_cr)->Ok_0;
    let state = WidgetSyncReconcileState::unmarshal(reconcile.local_state)->Ok_0;
    let resp_o = if input.1 is Some {
        if input.1->0.content is APIResponse {
            Some(ResponseView::<VoidERespView>::KResponse(input.1->0.content->APIResponse_0))
        } else {
            Some(ResponseView::<VoidERespView>::ExternalResponse(VoidERespView::unmarshal(input.1->0.content->ExternalResponse_0)->Ok_0))
        }
    } else {
        None
    };
    let (state_prime, req_o) = sync_reconciler::reconcile_core(k, outer, resp_o, state);
    assert(req_o is Some);
    assert(req_o->0 is KRequest);
    let req = req_o->0->KRequest_0;
    assert(msg.content->APIRequest_0 == req);
    assert(s_prime.api_server == s.api_server);
    // Only AfterGetInner sends a Patch, from the Get's answer.
    assert(state.reconcile_step is AfterGetInner);
    assert(input.1 is Some);
    let resp = input.1->0;
    assert(s.in_flight().contains(resp));
    assert(resp.content is APIResponse);
    assert(resp.content->APIResponse_0 is GetResponse);
    let res = resp.content->APIResponse_0->GetResponse_0.res;
    assert(res is Ok);
    let obj = res->Ok_0;
    assert(get_response_is_not_ahead(obj, s));
    let inner = unmarshal(inner_key(k, outer).kind, obj)->Ok_0;
    assert(inner.metadata == obj.metadata);
    assert(inner.metadata.deletion_timestamp is None);
    assert(req == APIRequest::PatchRequest(sync_reconciler::inner_spec_patch(k, inner, outer)));
    let preq = sync_reconciler::inner_spec_patch(k, inner, outer);
    assert(preq.tests == PatchTestsView::default().with_uid_from_object_meta(obj.metadata).with_generation_from_object_meta(obj.metadata));
    let key = preq.key();
    assert(key.kind == inner_key(k, outer).kind);
    assert(key.kind is CustomResourceKind);
    // The tests are not ahead at the object's own key; at the patch's key a stored
    // object with the tested uid is the same object, so at the same key.
    assert(obj.object_ref().kind == obj.kind);
    assert(obj.kind == key.kind);
    if s.resources().contains_key(key) && s.resources()[key].metadata.uid == obj.metadata.uid {
        assert(key == obj.object_ref());
        lemma_patch_tests_from_live_view(obj, key, s);
    } else {
        assert(view_is_not_ahead_at(obj.object_ref(), obj, s));
    }
}

// Every status Patch of an implementation that owns a finalizer tests a live
// generation: it writes a status only from a live snapshot.
pub open spec fn inner_impl_status_patches_are_not_ahead(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.content->APIRequest_0 is PatchStatusRequest
        } ==> patch_tests_are_not_ahead(msg.content->APIRequest_0->PatchStatusRequest_0.tests, msg.content->APIRequest_0->PatchStatusRequest_0.key(), s)
    }
}

pub proof fn lemma_always_inner_impl_status_patches_are_not_ahead(spec: TempPred<ClusterState>, cluster: Cluster, kind: Kind, f: StringView, spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.synced_type_is_installed(kind, spec_ok, selector),
        cluster.controller_models.contains_pair(controller_id, widget_inner_impl_controller_model(kind, Some(f))),
    ensures spec.entails(always(lift_state(inner_impl_status_patches_are_not_ahead(controller_id)))),
{
    let inv = inner_impl_status_patches_are_not_ahead(controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_synced_objects_in_reconcile_are_valid(spec, kind, spec_ok, selector, controller_id);
    cluster.lemma_always_objects_in_reconcile_have_kind(spec, kind, controller_id);
    lemma_always_snapshots_are_not_ahead(spec, cluster, controller_id);
    lemma_always_widget_inner_impl_guarantee(spec, cluster, kind, Some(f), spec_ok, selector, controller_id);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)(s)
        &&& Cluster::objects_in_reconcile_have_kind(kind, controller_id)(s)
        &&& snapshots_are_not_ahead(controller_id)(s)
        &&& widget_inner_impl_guarantee(kind, Some(f), controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)),
        lift_state(Cluster::objects_in_reconcile_have_kind(kind, controller_id)),
        lift_state(snapshots_are_not_ahead(controller_id)),
        lift_state(widget_inner_impl_guarantee(kind, Some(f), controller_id))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.content->APIRequest_0 is PatchStatusRequest
        } implies patch_tests_are_not_ahead(msg.content->APIRequest_0->PatchStatusRequest_0.tests, msg.content->APIRequest_0->PatchStatusRequest_0.key(), s_prime) by {
            let req = msg.content->APIRequest_0->PatchStatusRequest_0;
            match step {
                Step::APIServerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    assert(inner_impl_request_is_guaranteed(kind, Some(f), msg, s));
                    assert(req.kind == kind);
                    lemma_patch_tests_stay_not_ahead_across_api_server_step(cluster, s, s_prime, input->0, req.tests, req.key());
                },
                Step::ControllerStep(input) => {
                    assert(s_prime.api_server == s.api_server);
                    if s.in_flight().contains(msg) {
                    } else {
                        lemma_inner_impl_new_status_patch_is_not_ahead(cluster, kind, f, spec_ok, controller_id, s, s_prime, input, msg);
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                    assert(s.in_flight().contains(msg));
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// The status Patch the implementation just sent tests the uid and generation of
// its snapshot, which is live.
proof fn lemma_inner_impl_new_status_patch_is_not_ahead(
    cluster: Cluster, kind: Kind, f: StringView, spec_ok: spec_fn(Value) -> bool, controller_id: int, s: ClusterState, s_prime: ClusterState,
    input: (int, Option<Message>, Option<ObjectRef>), msg: Message
)
    requires
        cluster.controller_models.contains_pair(controller_id, widget_inner_impl_controller_model(kind, Some(f))),
        kind is CustomResourceKind,
        cluster.next_step(s, s_prime, Step::ControllerStep(input)),
        Cluster::there_is_the_controller_state(controller_id)(s),
        Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s),
        cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)(s),
        Cluster::objects_in_reconcile_have_kind(kind, controller_id)(s),
        snapshots_are_not_ahead(controller_id)(s),
        !s.in_flight().contains(msg),
        s_prime.in_flight().contains(msg),
        msg.content is APIRequest,
        msg.src.is_controller_id(controller_id),
        msg.content->APIRequest_0 is PatchStatusRequest,
    ensures patch_tests_are_not_ahead(msg.content->APIRequest_0->PatchStatusRequest_0.tests, msg.content->APIRequest_0->PatchStatusRequest_0.key(), s_prime),
{
    unmarshal_of_marshal();
    WidgetInnerImplReconcileState::marshal_preserves_integrity();
    let (id, resp_msg_opt, cr_key_opt) = input;
    assert(id == controller_id);
    let cr_key = cr_key_opt->0;
    assert(s.ongoing_reconciles(controller_id).contains_key(cr_key));
    assert(msg == s_prime.ongoing_reconciles(controller_id)[cr_key].pending_req_msg->0);
    let reconcile = s.ongoing_reconciles(controller_id)[cr_key];
    let cr = reconcile.triggering_cr;
    assert(cr_key.kind == kind);
    assert(unmarshal(kind, cr) is Ok);
    let inner = unmarshal(kind, cr)->Ok_0;
    assert(inner.metadata == cr.metadata);
    assert(cr.object_ref() == cr_key);
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
    let (state_prime, req_o) = inner_impl_reconciler::reconcile_core(kind, Some(f), inner, resp_o, state);
    assert(req_o is Some);
    assert(req_o->0 is KRequest);
    let req = req_o->0->KRequest_0;
    assert(msg.content->APIRequest_0 == req);
    assert(s_prime.api_server == s.api_server);
    // Only Init sends a status Patch, and with a finalizer only from a live snapshot.
    assert(state.reconcile_step is Init);
    assert(inner.metadata.deletion_timestamp is None);
    assert(req == APIRequest::PatchStatusRequest(inner_impl_reconciler::inner_status_patch(kind, inner)));
    let preq = inner_impl_reconciler::inner_status_patch(kind, inner);
    assert(preq.key() == cr_key);
    assert(preq.tests == PatchTestsView::default().with_uid_from_object_meta(cr.metadata).with_generation_from_object_meta(cr.metadata));
    assert(view_is_not_ahead_at(cr_key, cr, s));
    lemma_patch_tests_from_live_view(cr, cr_key, s);
}

// ---------------------------------------------------------------------------
// The finalizers of the implementation's kind are the implementation's.
// ---------------------------------------------------------------------------

// The finalizers of a mirror of the implementation's kind are all the
// implementation's (none, when it owns none), and a terminating one has some:
// the API server removes a terminating object whose last finalizer goes.
pub open spec fn finalizers_are_the_impls(meta: ObjectMetaView, finalizer: Option<StringView>) -> bool {
    &&& meta.finalizers is Some ==> (finalizer is Some && forall |i: int| 0 <= i < meta.finalizers->0.len()
        ==> #[trigger] meta.finalizers->0[i] == finalizer->0)
    &&& meta.deletion_timestamp is Some ==> meta.finalizers is Some && meta.finalizers->0.len() > 0
}

// Metadata with the same finalizers as metadata whose finalizers are the
// implementation's, and no deletion timestamp without a finalizer behind it,
// has the implementation's finalizers too.
pub proof fn lemma_finalizers_are_the_impls_carry(old_meta: ObjectMetaView, new_meta: ObjectMetaView, finalizer: Option<StringView>)
    requires
        finalizers_are_the_impls(old_meta, finalizer),
        new_meta.finalizers == old_meta.finalizers,
        new_meta.deletion_timestamp is Some ==> new_meta.finalizers is Some && new_meta.finalizers->0.len() > 0,
    ensures finalizers_are_the_impls(new_meta, finalizer),
{
    if new_meta.finalizers is Some {
        assert forall |i: int| 0 <= i < new_meta.finalizers->0.len()
            implies #[trigger] new_meta.finalizers->0[i] == finalizer->0 by {
            assert(old_meta.finalizers->0[i] == finalizer->0);
        }
    }
}

pub open spec fn inner_finalizers_are_the_impls(kind: Kind, finalizer: Option<StringView>) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.resources().contains_key(key) && key.kind == kind
            ==> finalizers_are_the_impls(s.resources()[key].metadata, finalizer)
    }
}

// What the cluster running the pair and the implementation, and nothing else, has
// in flight: every request is one of the three controllers', a built-in
// controller's Delete, or the pod monkey's request about a Pod.
pub open spec fn implemented_cluster_requests(k: SyncKind, b: Binding, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& widget_sync_guarantee(k, sync_id)(s)
        &&& widget_janitor_guarantee(k, b, janitor_id)(s)
        &&& widget_inner_impl_guarantee(inner_kind(k, b), finalizer, impl_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& Cluster::no_pending_request_to_api_server_from_api_server_or_external()(s)
        &&& Cluster::all_requests_from_pod_monkey_are_api_pod_requests()(s)
        &&& Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()(s)
    }
}

// The implemented cluster runs exactly the three controllers.
pub open spec fn implemented_cluster_ids(cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int) -> bool {
    forall |id: int| #[trigger] cluster.controller_models.contains_key(id) ==> id == sync_id || id == janitor_id || id == impl_id
}

// Taking or releasing a finalizer that is the implementation's keeps the
// finalizers the implementation's.
proof fn lemma_finalizer_update_keeps_finalizers_the_impls(meta: ObjectMetaView, f: StringView)
    requires
        meta.finalizers is Some ==> forall |i: int| 0 <= i < meta.finalizers->0.len() ==> #[trigger] meta.finalizers->0[i] == f,
    ensures
        ({
            let added = with_finalizer(meta, f);
            added.finalizers is Some && forall |i: int| 0 <= i < added.finalizers->0.len() ==> #[trigger] added.finalizers->0[i] == f
        }),
        without_finalizer(meta, f).finalizers is None,
{
    broadcast use Seq::lemma_filter_pred;
    let all = finalizers_or_empty(meta);
    let added = with_finalizer(meta, f);
    assert forall |i: int| 0 <= i < added.finalizers->0.len() implies #[trigger] added.finalizers->0[i] == f by {
        if i < all.len() {
            assert(added.finalizers->0[i] == all[i]);
        } else {
            assert(added.finalizers->0[i] == f);
        }
    }
    let rest = all.filter(not_finalizer(f));
    if rest.len() > 0 {
        assert(not_finalizer(f)(rest[0]));
        assert(rest[0] != f);
        assert(all.contains(rest[0])) by {
            broadcast use Seq::lemma_filter_contains_rev;
            assert(rest.contains(rest[0]));
        }
        let j = choose |j: int| 0 <= j < all.len() && all[j] == rest[0];
        assert(all[j] == f);
        assert(false);
    }
}

pub proof fn lemma_always_inner_finalizers_are_the_impls(spec: TempPred<ClusterState>, cluster: Cluster, k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>)
    requires
        sync_kind_ok(k),
        k.bindings.contains(b),
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(implemented_cluster_requests(k, b, cluster, sync_id, janitor_id, impl_id, finalizer)))),
        implemented_cluster_ids(cluster, sync_id, janitor_id, impl_id),
    ensures spec.entails(always(lift_state(inner_finalizers_are_the_impls(inner_kind(k, b), finalizer)))),
{
    let kind = inner_kind(k, b);
    let inv = inner_finalizers_are_the_impls(kind, finalizer);
    lemma_outer_kind_is_not_inner(k, b);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& implemented_cluster_requests(k, b, cluster, sync_id, janitor_id, impl_id, finalizer)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(implemented_cluster_requests(k, b, cluster, sync_id, janitor_id, impl_id, finalizer))
    );
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && key.kind == kind
            implies finalizers_are_the_impls(s_prime.resources()[key].metadata, finalizer) by {
            match step {
                Step::APIServerStep(input) => {
                    if s.resources().contains_key(key) && s_prime.resources()[key] == s.resources()[key] {
                    } else {
                        lemma_inner_finalizers_after_write(cluster, k, b, sync_id, janitor_id, impl_id, finalizer, s, s_prime, input->0, key);
                    }
                },
                _ => {
                    assert(s_prime.api_server == s.api_server);
                },
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

// A write of an object of the implementation's kind keeps its finalizers the
// implementation's: the sync controller creates mirrors without finalizers and
// updates only outer copies, the janitor and the built-in controllers only
// delete, the pod monkey touches Pods, and the implementation takes or releases
// its own finalizer on the stored object.
proof fn lemma_inner_finalizers_after_write(cluster: Cluster, k: SyncKind, b: Binding, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>,
    s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef
)
    requires
        sync_kind_ok(k),
        k.bindings.contains(b),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        implemented_cluster_requests(k, b, cluster, sync_id, janitor_id, impl_id, finalizer)(s),
        implemented_cluster_ids(cluster, sync_id, janitor_id, impl_id),
        inner_finalizers_are_the_impls(inner_kind(k, b), finalizer)(s),
        key.kind == inner_kind(k, b),
        s_prime.resources().contains_key(key),
        !(s.resources().contains_key(key) && s_prime.resources()[key] == s.resources()[key]),
    ensures finalizers_are_the_impls(s_prime.resources()[key].metadata, finalizer),
{
    let kind = inner_kind(k, b);
    lemma_outer_kind_is_not_inner(k, b);
    assert(s.in_flight().contains(msg));
    assert(msg.content is APIRequest);
    assert(msg.dst is APIServer);
    let new = s_prime.resources()[key];
    // The request comes from one of the three controllers, a built-in controller,
    // or the pod monkey.
    match msg.src {
        HostId::Controller(id, ckey) => {
            assert(cluster.controller_models.contains_key(id));
            assert(id == sync_id || id == janitor_id || id == impl_id);
        },
        HostId::BuiltinController => {},
        HostId::PodMonkey => {},
        _ => { assert(false); },
    }
    if !(msg.content->APIRequest_0 is CreateRequest) {
        // Nothing but a Create fills a key.
        assert(s.resources().contains_key(key));
        assert(finalizers_are_the_impls(s.resources()[key].metadata, finalizer));
    }
    match msg.content->APIRequest_0 {
        APIRequest::CreateRequest(req) => {
            // A new object at the key: the sync controller's mirror, without finalizers.
            assert(new.metadata.finalizers == req.obj.metadata.finalizers);
            assert(new.metadata.deletion_timestamp is None);
            assert(req.obj.kind == kind);
            match msg.src {
                HostId::Controller(id, ckey) => {
                    if id == sync_id {
                        assert(mirror_create_req(k, req, ckey)(s));
                        let outer = choose |outer: SyncedObjectView| {
                            &&& outer.kind == k.outer_kind
                            &&& outer.object_ref() == ckey
                            &&& outer.metadata.uid is Some
                            &&& cluster_of(k.selector, outer) is Some
                            &&& req.namespace == ckey.namespace
                            &&& req.obj == #[trigger] marshal(make_inner(k, outer))
                            &&& parent_uid_is_bound_to_key(outer.metadata.uid->0, ckey)(s)
                        };
                        assert(req.obj.metadata == make_inner(k, outer).metadata);
                        assert(req.obj.metadata.finalizers is None);
                    } else {
                        assert(false);
                    }
                },
                _ => { assert(false); },
            }
            assert(finalizers_are_the_impls(new.metadata, finalizer));
        },
        APIRequest::UpdateRequest(req) => {
            // The implementation's, on the stored object: it lands with the
            // stored version, adding its finalizer to the stored ones or removing
            // it, which empties the list.
            assert(req.key() == key);
            let old = s.resources()[key];
            match msg.src {
                HostId::Controller(id, ckey) => {
                    if id == sync_id {
                        assert(req.obj.kind == k.outer_kind);
                        assert(false);
                    } else if id == impl_id {
                        assert(inner_impl_request_is_guaranteed(kind, finalizer, msg, s));
                        assert(finalizer is Some);
                        let f = finalizer->0;
                        assert(req.obj.metadata.resource_version == old.metadata.resource_version);
                        assert(finalizers_are_the_impls(old.metadata, finalizer));
                        lemma_finalizer_update_keeps_finalizers_the_impls(old.metadata, f);
                        assert(new.metadata.finalizers == req.obj.metadata.finalizers);
                        assert(new.metadata.deletion_timestamp == old.metadata.deletion_timestamp);
                        if req.obj.metadata == with_finalizer(old.metadata, f) {
                            assert(new.metadata.finalizers is Some);
                            assert(new.metadata.finalizers->0.len() > 0);
                            assert(new.metadata.finalizers == with_finalizer(old.metadata, f).finalizers);
                            assert forall |i: int| 0 <= i < new.metadata.finalizers->0.len() implies #[trigger] new.metadata.finalizers->0[i] == f by {
                                assert(with_finalizer(old.metadata, f).finalizers->0[i] == f);
                            }
                        } else {
                            // The finalizers are gone: a terminating object is removed.
                            assert(new.metadata.finalizers is None);
                            assert(new.metadata.deletion_timestamp is None);
                        }
                        assert(finalizers_are_the_impls(new.metadata, finalizer));
                    } else {
                        assert(false);
                    }
                },
                _ => { assert(false); },
            }
        },
        APIRequest::GetThenUpdateRequest(req) => {
            match msg.src {
                HostId::Controller(id, ckey) => { assert(false); },
                _ => { assert(false); },
            }
        },
        APIRequest::PatchRequest(req) => {
            // The metadata is the stored object's.
            let old = s.resources()[key];
            assert(new.metadata.finalizers == old.metadata.finalizers);
            assert(new.metadata.deletion_timestamp == old.metadata.deletion_timestamp);
            lemma_finalizers_are_the_impls_carry(old.metadata, new.metadata, finalizer);
        },
        APIRequest::DeleteRequest(req) => {
            // Stamped: the finalizers are the stored ones, and there are some.
            let old = s.resources()[key];
            assert(new.metadata.finalizers == old.metadata.finalizers);
            assert(old.metadata.finalizers is Some && old.metadata.finalizers->0.len() > 0);
            lemma_finalizers_are_the_impls_carry(old.metadata, new.metadata, finalizer);
        },
        APIRequest::GetThenDeleteRequest(req) => {
            let old = s.resources()[key];
            assert(new.metadata.finalizers == old.metadata.finalizers);
            assert(old.metadata.finalizers is Some && old.metadata.finalizers->0.len() > 0);
            lemma_finalizers_are_the_impls_carry(old.metadata, new.metadata, finalizer);
        },
        _ => {
            // Status writes keep the metadata.
            let old = s.resources()[key];
            assert(new.metadata.finalizers == old.metadata.finalizers);
            assert(new.metadata.deletion_timestamp == old.metadata.deletion_timestamp);
            lemma_finalizers_are_the_impls_carry(old.metadata, new.metadata, finalizer);
        },
    }
}

// ---------------------------------------------------------------------------
// The implementation's reconciles: each middle step comes with a pending
// request, and every reconcile ends.
// ---------------------------------------------------------------------------

pub open spec fn at_impl_step_closure(step: WidgetInnerImplStepView) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| WidgetInnerImplReconcileState::unmarshal(s).unwrap().reconcile_step == step
}

pub open spec fn at_impl_step(controller_id: int, key: ObjectRef, step: WidgetInnerImplStepView) -> StatePred<ClusterState> {
    Cluster::at_expected_reconcile_states(controller_id, key, at_impl_step_closure(step))
}

pub open spec fn impl_step_after_init() -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| {
        let step = WidgetInnerImplReconcileState::unmarshal(s).unwrap().reconcile_step;
        ||| step == WidgetInnerImplStepView::AfterAddFinalizer
        ||| step == WidgetInnerImplStepView::AfterRemoveFinalizer
        ||| step == WidgetInnerImplStepView::AfterPatchStatus
        ||| step == WidgetInnerImplStepView::Done
    }
}

// The model never starts over, sends a request into each middle step and none
// into Done, and every step but Init ends in Done.
proof fn lemma_impl_core_requests(kind: Kind, finalizer: Option<StringView>, inner: SyncedObjectView, resp_o: Option<ResponseView<VoidERespView>>, state: WidgetInnerImplReconcileState)
    ensures ({
        let (state_prime, req_o) = inner_impl_reconciler::reconcile_core(kind, finalizer, inner, resp_o, state);
        &&& !(state_prime.reconcile_step is Init)
        &&& state_prime.reconcile_step is Done <==> req_o is None
        &&& req_o is Some ==> req_o->0 is KRequest
        &&& !(state.reconcile_step is Init) ==> state_prime.reconcile_step is Done
    }),
{
}

// The preconditions of the framework's lemmas about the implementation's steps.
pub proof fn lemma_impl_step_facts(cluster: Cluster, kind: Kind, finalizer: Option<StringView>, controller_id: int)
    requires cluster.controller_models.contains_pair(controller_id, widget_inner_impl_controller_model(kind, finalizer)),
    ensures
        cluster.state_comes_with_a_pending_request(controller_id, at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer)),
        cluster.state_comes_with_a_pending_request(controller_id, at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer)),
        cluster.state_comes_with_a_pending_request(controller_id, at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus)),
        forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
            #[trigger] at_impl_step_closure(WidgetInnerImplStepView::Init)((cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0)
            ==> (cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1 is None,
        forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
            #[trigger] (cluster.reconcile_model(controller_id).done)((cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0)
            ==> (cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1 is None,
        forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
            #[trigger] (cluster.reconcile_model(controller_id).error)((cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).0)
            ==> (cluster.controller_models[controller_id].reconcile_model.transition)(cr, resp_o, pre_state).1 is None,
        Cluster::reconcile_model_sends_no_external_request(cluster.reconcile_model(controller_id)),
{
    unmarshal_of_marshal();
    WidgetInnerImplReconcileState::marshal_preserves_integrity();
    let model = cluster.controller_models[controller_id].reconcile_model;
    assert forall |cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState|
        true implies ({
            let inner = unmarshal(kind, cr)->Ok_0;
            let resp_um = unmarshal_response_content::<VoidERespView>(resp_o);
            let st = WidgetInnerImplReconcileState::unmarshal(pre_state)->Ok_0;
            let (state_prime, req_o) = inner_impl_reconciler::reconcile_core(kind, finalizer, inner, resp_um, st);
            &&& #[trigger] (model.transition)(cr, resp_o, pre_state) == (state_prime.marshal(), marshal_request_view::<VoidEReqView>(req_o))
            &&& WidgetInnerImplReconcileState::unmarshal(state_prime.marshal()) == Ok::<WidgetInnerImplReconcileState, UnmarshalError>(state_prime)
            &&& !(state_prime.reconcile_step is Init)
            &&& (state_prime.reconcile_step is Done <==> req_o is None)
            &&& (req_o is Some ==> req_o->0 is KRequest)
        }) by {
        let inner = unmarshal(kind, cr)->Ok_0;
        let resp_um = unmarshal_response_content::<VoidERespView>(resp_o);
        let st = WidgetInnerImplReconcileState::unmarshal(pre_state)->Ok_0;
        lemma_impl_core_requests(kind, finalizer, inner, resp_um, st);
    }
    assert forall |s: ReconcileLocalState| #[trigger] at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer)(s) implies s != (model.init)() by {
        assert((model.init)() == inner_impl_reconciler::reconcile_init_state().marshal());
    }
    assert forall |s: ReconcileLocalState| #[trigger] at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer)(s) implies s != (model.init)() by {
        assert((model.init)() == inner_impl_reconciler::reconcile_init_state().marshal());
    }
    assert forall |s: ReconcileLocalState| #[trigger] at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus)(s) implies s != (model.init)() by {
        assert((model.init)() == inner_impl_reconciler::reconcile_init_state().marshal());
    }
}

// Every state is idle, or at one of the steps.
proof fn lemma_true_equal_to_impl_idle_or_at_any_step(controller_id: int, key: ObjectRef)
    ensures
        true_pred::<ClusterState>() == lift_state(Cluster::reconcile_idle(controller_id, key))
            .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::Init)))
            .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterAddFinalizer)))
            .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterRemoveFinalizer)))
            .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterPatchStatus)))
            .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::Done))),
{
    let rhs = lift_state(Cluster::reconcile_idle(controller_id, key))
        .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::Init)))
        .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterAddFinalizer)))
        .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterRemoveFinalizer)))
        .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterPatchStatus)))
        .or(lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::Done)));
    assert forall |ex: Execution<ClusterState>| #[trigger] true_pred::<ClusterState>().satisfied_by(ex) implies rhs.satisfied_by(ex) by {
        let s = ex.head();
        if s.ongoing_reconciles(controller_id).contains_key(key) {
            let step = WidgetInnerImplReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap().reconcile_step;
            match step {
                WidgetInnerImplStepView::Init => assert(at_impl_step(controller_id, key, WidgetInnerImplStepView::Init)(s)),
                WidgetInnerImplStepView::AfterAddFinalizer => assert(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterAddFinalizer)(s)),
                WidgetInnerImplStepView::AfterRemoveFinalizer => assert(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterRemoveFinalizer)(s)),
                WidgetInnerImplStepView::AfterPatchStatus => assert(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterPatchStatus)(s)),
                WidgetInnerImplStepView::Done => assert(at_impl_step(controller_id, key, WidgetInnerImplStepView::Done)(s)),
            }
        }
    }
    temp_pred_equality(true_pred::<ClusterState>(), rhs);
}

// Every reconcile of the implementation ends.
pub proof fn inner_impl_reconcile_eventually_terminates_on_key(cluster: Cluster, kind: Kind, finalizer: Option<StringView>,
    spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef
)
    requires
        key.kind == kind,
        spec.entails(always(lift_action(cluster.next()))),
        cluster.controller_models.contains_pair(controller_id, widget_inner_impl_controller_model(kind, finalizer)),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(controller_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(controller_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))),
        spec.entails(always(lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, key)))),
        spec.entails(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, key, at_impl_step_closure(WidgetInnerImplStepView::Init))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer))))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus))))),
    ensures spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(controller_id, key)))),
{
    let idle = lift_state(Cluster::reconcile_idle(controller_id, key));
    WidgetInnerImplReconcileState::marshal_preserves_integrity();
    unmarshal_of_marshal();

    // Done ends the reconcile; nothing ends in Error.
    cluster.lemma_reconcile_done_leads_to_reconcile_idle(spec, controller_id, key);
    temp_pred_equality(
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::Done)),
        lift_state(cluster.reconciler_reconcile_done(controller_id, key))
    );

    // Each middle step ends in Done, whatever the response.
    assert forall |input_cr, resp_o, s| at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer)(s)
        implies #[trigger] at_impl_step_closure(WidgetInnerImplStepView::Done)((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0) by {
        lemma_impl_transition_from_step(cluster, kind, finalizer, controller_id, input_cr, resp_o, s);
    }
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer), at_impl_step_closure(WidgetInnerImplStepView::Done));
    assert forall |input_cr, resp_o, s| at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer)(s)
        implies #[trigger] at_impl_step_closure(WidgetInnerImplStepView::Done)((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0) by {
        lemma_impl_transition_from_step(cluster, kind, finalizer, controller_id, input_cr, resp_o, s);
    }
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer), at_impl_step_closure(WidgetInnerImplStepView::Done));
    assert forall |input_cr, resp_o, s| at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus)(s)
        implies #[trigger] at_impl_step_closure(WidgetInnerImplStepView::Done)((cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0) by {
        lemma_impl_transition_from_step(cluster, kind, finalizer, controller_id, input_cr, resp_o, s);
    }
    cluster.lemma_from_some_state_to_arbitrary_next_state_to_reconcile_idle(spec, controller_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus), at_impl_step_closure(WidgetInnerImplStepView::Done));

    // Init moves to one of them, or to Done.
    or_leads_to_combine_and_equality!(
        spec, lift_state(Cluster::at_expected_reconcile_states(controller_id, key, impl_step_after_init())),
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterAddFinalizer)),
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterRemoveFinalizer)),
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterPatchStatus)),
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::Done));
        idle
    );
    assert forall |input_cr, resp_o, s| at_impl_step_closure(WidgetInnerImplStepView::Init)(s)
        implies impl_step_after_init()(#[trigger] (cluster.reconcile_model(controller_id).transition)(input_cr, resp_o, s).0) by {
        lemma_impl_transition_from_step(cluster, kind, finalizer, controller_id, input_cr, resp_o, s);
    }
    cluster.lemma_from_init_state_to_next_state_to_reconcile_idle(spec, controller_id, key, at_impl_step_closure(WidgetInnerImplStepView::Init), impl_step_after_init());

    // Every state is idle or at one of the steps.
    entails_implies_leads_to(spec, idle, idle);
    lemma_true_equal_to_impl_idle_or_at_any_step(controller_id, key);
    or_leads_to_combine_and_equality!(
        spec, true_pred(),
        idle,
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::Init)),
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterAddFinalizer)),
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterRemoveFinalizer)),
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::AfterPatchStatus)),
        lift_state(at_impl_step(controller_id, key, WidgetInnerImplStepView::Done));
        idle
    );
}

// What one transition of the model does to the step, on the marshalled forms.
proof fn lemma_impl_transition_from_step(cluster: Cluster, kind: Kind, finalizer: Option<StringView>, controller_id: int,
    cr: DynamicObjectView, resp_o: Option<ResponseContent>, pre_state: ReconcileLocalState
)
    requires cluster.controller_models.contains_pair(controller_id, widget_inner_impl_controller_model(kind, finalizer)),
    ensures ({
        let post = (cluster.reconcile_model(controller_id).transition)(cr, resp_o, pre_state).0;
        let step = WidgetInnerImplReconcileState::unmarshal(pre_state).unwrap().reconcile_step;
        &&& WidgetInnerImplReconcileState::unmarshal(post) is Ok
        &&& !(WidgetInnerImplReconcileState::unmarshal(post).unwrap().reconcile_step is Init)
        &&& !(step is Init) ==> WidgetInnerImplReconcileState::unmarshal(post).unwrap().reconcile_step is Done
        &&& !(cluster.reconcile_model(controller_id).error)(pre_state)
        &&& (cluster.reconcile_model(controller_id).done)(pre_state) == (step is Done)
    }),
{
    unmarshal_of_marshal();
    WidgetInnerImplReconcileState::marshal_preserves_integrity();
    let model = cluster.controller_models[controller_id].reconcile_model;
    let inner = unmarshal(kind, cr)->Ok_0;
    let resp_um = unmarshal_response_content::<VoidERespView>(resp_o);
    let st = WidgetInnerImplReconcileState::unmarshal(pre_state)->Ok_0;
    let (state_prime, req_o) = inner_impl_reconciler::reconcile_core(kind, finalizer, inner, resp_um, st);
    assert((model.transition)(cr, resp_o, pre_state) == (state_prime.marshal(), marshal_request_view::<VoidEReqView>(req_o)));
    assert(WidgetInnerImplReconcileState::unmarshal(state_prime.marshal()) == Ok::<WidgetInnerImplReconcileState, UnmarshalError>(state_prime));
    lemma_impl_core_requests(kind, finalizer, inner, resp_um, st);
}

// ---------------------------------------------------------------------------
// The facts of the implemented cluster, always: its stable spec.
// ---------------------------------------------------------------------------

// The invariants the D3 proof works under.
pub open spec fn d3_ctx(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& cluster.each_synced_object_in_etcd_is_well_formed(inner_kind(k, b))(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& implemented_cluster_requests(k, b, cluster, sync_id, janitor_id, impl_id, finalizer)(s)
        &&& inner_finalizers_are_the_impls(inner_kind(k, b), finalizer)(s)
        &&& sync_patches_are_not_ahead(sync_id)(s)
        &&& finalizer is Some ==> inner_impl_status_patches_are_not_ahead(impl_id)(s)
        &&& snapshots_are_current(impl_id)(s)
        &&& Cluster::there_is_the_controller_state(impl_id)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(impl_id)(s)
        &&& cluster.synced_objects_in_reconcile_are_valid(inner_kind(k, b), spec_ok, impl_id)(s)
        &&& Cluster::objects_in_reconcile_have_kind(inner_kind(k, b), impl_id)(s)
        &&& Cluster::every_in_flight_msg_has_unique_id()(s)
        &&& Cluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()(s)
        &&& Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(impl_id)(s)
        &&& Cluster::there_is_no_request_msg_to_external_from_controller(impl_id)(s)
    }
}

// The per-key bookkeeping of the implementation's reconciles.
pub open spec fn d3_key_facts(cluster: Cluster, impl_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& Cluster::pending_req_of_key_is_unique_with_unique_id(impl_id, key)(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::Init))(s)
        &&& Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer))(s)
        &&& Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer))(s)
        &&& Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus))(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, cluster.reconcile_model(impl_id).done)(s)
        &&& Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, cluster.reconcile_model(impl_id).error)(s)
    }
}

pub open spec fn d3_stable_spec(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>) -> TempPred<ClusterState> {
    inner_impl_next_with_wf(cluster, impl_id)
    .and(always(lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer))))
    .and(always(tla_forall(|key: ObjectRef| lift_state(d3_key_facts(cluster, impl_id, key)))))
}

pub proof fn inner_impl_next_with_wf_is_stable(cluster: Cluster, controller_id: int)
    ensures valid(stable(inner_impl_next_with_wf(cluster, controller_id))),
{
    always_p_is_stable(lift_action(cluster.next()));
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.api_server_next());
    cluster.tla_forall_controller_next_weak_fairness_is_stable(controller_id);
    cluster.tla_forall_schedule_controller_reconcile_weak_fairness_is_stable(controller_id);
    Cluster::tla_forall_action_weak_fairness_is_stable(cluster.disable_crash());
    cluster.tla_forall_external_next_weak_fairness_is_stable(controller_id);
    Cluster::action_weak_fairness_is_stable(cluster.disable_req_drop());
    Cluster::action_weak_fairness_is_stable(cluster.disable_pod_monkey());
    stable_and_n!(
        always(lift_action(cluster.next())),
        tla_forall(|input| cluster.api_server_next().weak_fairness(input)),
        tla_forall(|input: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((controller_id, input.0, input.1))),
        tla_forall(|input| cluster.schedule_controller_reconcile().weak_fairness((controller_id, input))),
        tla_forall(|input| cluster.disable_crash().weak_fairness(input)),
        tla_forall(|input| cluster.external_next().weak_fairness((controller_id, input))),
        cluster.disable_req_drop().weak_fairness(()),
        cluster.disable_pod_monkey().weak_fairness(())
    );
}

pub proof fn d3_stable_spec_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>)
    ensures valid(stable(d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer))),
{
    inner_impl_next_with_wf_is_stable(cluster, impl_id);
    always_p_is_stable(lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)));
    always_p_is_stable(tla_forall(|key: ObjectRef| lift_state(d3_key_facts(cluster, impl_id, key))));
    stable_and_n!(
        inner_impl_next_with_wf(cluster, impl_id),
        always(lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer))),
        always(tla_forall(|key: ObjectRef| lift_state(d3_key_facts(cluster, impl_id, key))))
    );
}

// The membership of the implemented cluster: the three controllers, and nothing
// else, with the two model kinds installed.
pub open spec fn d3_membership(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>) -> bool {
    &&& sync_kind_ok(k)
    &&& k.bindings.contains(b)
    &&& cluster.controller_models.contains_pair(sync_id, widget_sync_controller_model(k))
    &&& cluster.controller_models.contains_pair(janitor_id, widget_janitor_controller_model(k, b))
    &&& cluster.controller_models.contains_pair(impl_id, widget_inner_impl_controller_model(inner_kind(k, b), finalizer))
    &&& implemented_cluster_ids(cluster, sync_id, janitor_id, impl_id)
    &&& cluster.synced_type_is_installed(inner_kind(k, b), spec_ok, k.selector)
    &&& cluster.synced_type_is_installed(k.outer_kind, spec_ok, k.selector)
}

pub proof fn lemma_unfold_d3_stable_spec(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef)
    requires spec.entails(d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
    ensures
        spec.entails(inner_impl_next_with_wf(cluster, impl_id)),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((impl_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((impl_id, i)))),
        spec.entails(tla_forall(|input| cluster.disable_crash().weak_fairness(input))),
        spec.entails(tla_forall(|i| cluster.external_next().weak_fairness((impl_id, i)))),
        spec.entails(cluster.disable_req_drop().weak_fairness(())),
        spec.entails(cluster.disable_pod_monkey().weak_fairness(())),
        spec.entails(always(lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)))),
        spec.entails(always(lift_state(d3_key_facts(cluster, impl_id, key)))),
        spec.entails(always(lift_state(Cluster::there_is_the_controller_state(impl_id)))),
{
    let wf = inner_impl_next_with_wf(cluster, impl_id);
    let ctx = always(lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)));
    let keys = always(tla_forall(|key: ObjectRef| lift_state(d3_key_facts(cluster, impl_id, key))));
    entails_and_split(spec, wf.and(ctx), keys);
    entails_and_split(spec, wf, ctx);
    always_tla_forall_apply(spec, |key: ObjectRef| lift_state(d3_key_facts(cluster, impl_id, key)), key);
    assert(wf.entails(always(lift_action(cluster.next()))));
    entails_trans(spec, wf, always(lift_action(cluster.next())));
    assert(wf.entails(tla_forall(|i| cluster.api_server_next().weak_fairness(i))));
    entails_trans(spec, wf, tla_forall(|i| cluster.api_server_next().weak_fairness(i)));
    assert(wf.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((impl_id, i.0, i.1)))));
    entails_trans(spec, wf, tla_forall(|i: (Option<Message>, Option<ObjectRef>)| cluster.controller_next().weak_fairness((impl_id, i.0, i.1))));
    assert(wf.entails(tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((impl_id, i)))));
    entails_trans(spec, wf, tla_forall(|i| cluster.schedule_controller_reconcile().weak_fairness((impl_id, i))));
    assert(wf.entails(tla_forall(|input| cluster.disable_crash().weak_fairness(input))));
    entails_trans(spec, wf, tla_forall(|input| cluster.disable_crash().weak_fairness(input)));
    assert(wf.entails(tla_forall(|i| cluster.external_next().weak_fairness((impl_id, i)))));
    entails_trans(spec, wf, tla_forall(|i| cluster.external_next().weak_fairness((impl_id, i))));
    assert(wf.entails(cluster.disable_req_drop().weak_fairness(())));
    entails_trans(spec, wf, cluster.disable_req_drop().weak_fairness(()));
    assert(wf.entails(cluster.disable_pod_monkey().weak_fairness(())));
    entails_trans(spec, wf, cluster.disable_pod_monkey().weak_fairness(()));
    always_weaken(spec, lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)), lift_state(Cluster::there_is_the_controller_state(impl_id)));
}

// The stable spec holds of the implemented cluster from its initial state, its
// steps and the implementation's fairness.
pub proof fn lemma_d3_stable_spec_holds(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        spec.entails(lift_state(cluster.init())),
        spec.entails(inner_impl_next_with_wf(cluster, impl_id)),
    ensures spec.entails(d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
{
    let kind = inner_kind(k, b);
    let wf = inner_impl_next_with_wf(cluster, impl_id);
    assert(wf.entails(always(lift_action(cluster.next()))));
    entails_trans(spec, wf, always(lift_action(cluster.next())));
    // The invariants.
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    cluster.lemma_always_each_synced_object_in_etcd_is_well_formed(spec, kind, spec_ok, k.selector);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    lemma_always_widget_sync_guarantee(spec, cluster, k, spec_ok, sync_id);
    lemma_always_widget_janitor_guarantee(spec, cluster, k, b, spec_ok, janitor_id);
    lemma_always_widget_inner_impl_guarantee(spec, cluster, kind, finalizer, spec_ok, k.selector, impl_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    cluster.lemma_always_no_pending_request_to_api_server_from_api_server_or_external(spec);
    cluster.lemma_always_all_requests_from_pod_monkey_are_api_pod_requests(spec);
    cluster.lemma_always_all_requests_from_builtin_controllers_are_api_delete_requests(spec);
    entails_always_and_n!(
        spec,
        lift_state(widget_sync_guarantee(k, sync_id)),
        lift_state(widget_janitor_guarantee(k, b, janitor_id)),
        lift_state(widget_inner_impl_guarantee(kind, finalizer, impl_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()),
        lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()),
        lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests())
    );
    temp_pred_equality(
        lift_state(implemented_cluster_requests(k, b, cluster, sync_id, janitor_id, impl_id, finalizer)),
        lift_state(widget_sync_guarantee(k, sync_id))
            .and(lift_state(widget_janitor_guarantee(k, b, janitor_id)))
            .and(lift_state(widget_inner_impl_guarantee(kind, finalizer, impl_id)))
            .and(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()))
            .and(lift_state(Cluster::no_pending_request_to_api_server_from_api_server_or_external()))
            .and(lift_state(Cluster::all_requests_from_pod_monkey_are_api_pod_requests()))
            .and(lift_state(Cluster::all_requests_from_builtin_controllers_are_api_delete_requests()))
    );
    lemma_always_inner_finalizers_are_the_impls(spec, cluster, k, b, spec_ok, sync_id, janitor_id, impl_id, finalizer);
    lemma_always_sync_patches_are_not_ahead(spec, cluster, k, spec_ok, sync_id);
    let patches = lift_state(|s: ClusterState| finalizer is Some ==> inner_impl_status_patches_are_not_ahead(impl_id)(s));
    if finalizer is Some {
        lemma_always_inner_impl_status_patches_are_not_ahead(spec, cluster, kind, finalizer->0, spec_ok, k.selector, impl_id);
        always_weaken(spec, lift_state(inner_impl_status_patches_are_not_ahead(impl_id)), patches);
    } else {
        always_weaken(spec, lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()), patches);
    }
    lemma_always_snapshots_are_current(spec, cluster, impl_id);
    cluster.lemma_always_there_is_the_controller_state(spec, impl_id);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, impl_id);
    cluster.lemma_always_synced_objects_in_reconcile_are_valid(spec, kind, spec_ok, k.selector, impl_id);
    cluster.lemma_always_objects_in_reconcile_have_kind(spec, kind, impl_id);
    cluster.lemma_always_every_in_flight_msg_has_unique_id(spec);
    cluster.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    cluster.lemma_always_every_in_flight_msg_has_no_replicas_and_has_unique_id(spec);
    cluster.lemma_always_every_ongoing_reconcile_has_lower_id_than_allocator(spec, impl_id);
    lemma_impl_step_facts(cluster, kind, finalizer, impl_id);
    cluster.lemma_always_there_is_no_request_msg_to_external_from_controller(spec, impl_id);
    entails_always_and_n!(
        spec,
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(cluster.each_synced_object_in_etcd_is_well_formed(kind)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(implemented_cluster_requests(k, b, cluster, sync_id, janitor_id, impl_id, finalizer)),
        lift_state(inner_finalizers_are_the_impls(kind, finalizer)),
        lift_state(sync_patches_are_not_ahead(sync_id)),
        patches,
        lift_state(snapshots_are_current(impl_id)),
        lift_state(Cluster::there_is_the_controller_state(impl_id)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(impl_id)),
        lift_state(cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, impl_id)),
        lift_state(Cluster::objects_in_reconcile_have_kind(kind, impl_id)),
        lift_state(Cluster::every_in_flight_msg_has_unique_id()),
        lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()),
        lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(impl_id)),
        lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(impl_id))
    );
    temp_pred_equality(
        lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
            .and(lift_state(cluster.each_synced_object_in_etcd_is_well_formed(kind)))
            .and(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()))
            .and(lift_state(implemented_cluster_requests(k, b, cluster, sync_id, janitor_id, impl_id, finalizer)))
            .and(lift_state(inner_finalizers_are_the_impls(kind, finalizer)))
            .and(lift_state(sync_patches_are_not_ahead(sync_id)))
            .and(patches)
            .and(lift_state(snapshots_are_current(impl_id)))
            .and(lift_state(Cluster::there_is_the_controller_state(impl_id)))
            .and(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(impl_id)))
            .and(lift_state(cluster.synced_objects_in_reconcile_are_valid(kind, spec_ok, impl_id)))
            .and(lift_state(Cluster::objects_in_reconcile_have_kind(kind, impl_id)))
            .and(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
            .and(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()))
            .and(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()))
            .and(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(impl_id)))
            .and(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(impl_id)))
    );
    // The per-key facts.
    WidgetInnerImplReconcileState::marshal_preserves_integrity();
    assert forall |key: ObjectRef| spec.entails(always(lift_state(#[trigger] d3_key_facts(cluster, impl_id, key)))) by {
        cluster.lemma_always_pending_req_of_key_is_unique_with_unique_id(spec, impl_id, key);
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::Init));
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer));
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer));
        cluster.lemma_always_pending_req_in_flight_or_resp_in_flight_at_reconcile_state(spec, impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus));
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, impl_id, key, cluster.reconcile_model(impl_id).done);
        cluster.lemma_always_no_pending_req_msg_at_reconcile_state(spec, impl_id, key, cluster.reconcile_model(impl_id).error);
        entails_always_and_n!(
            spec,
            lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(impl_id, key)),
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::Init))),
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer))),
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer))),
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus))),
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, cluster.reconcile_model(impl_id).done)),
            lift_state(Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, cluster.reconcile_model(impl_id).error))
        );
        temp_pred_equality(
            lift_state(d3_key_facts(cluster, impl_id, key)),
            lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(impl_id, key))
                .and(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::Init))))
                .and(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer))))
                .and(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer))))
                .and(lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus))))
                .and(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, cluster.reconcile_model(impl_id).done)))
                .and(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, cluster.reconcile_model(impl_id).error)))
        );
    }
    spec_entails_always_tla_forall_equality(spec, |key: ObjectRef| lift_state(d3_key_facts(cluster, impl_id, key)));
    entails_and_n!(
        spec,
        inner_impl_next_with_wf(cluster, impl_id),
        always(lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer))),
        always(tla_forall(|key: ObjectRef| lift_state(d3_key_facts(cluster, impl_id, key))))
    );
}

// Termination of the implementation's reconciles, under phase I.
pub proof fn lemma_impl_terminates(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        key.kind == inner_kind(k, b),
        spec.entails(d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
        spec.entails(always(lift_state(Cluster::crash_disabled(impl_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
    ensures spec.entails(true_pred().leads_to(lift_state(Cluster::reconcile_idle(impl_id, key)))),
{
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    let ctx = lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer));
    let kf = lift_state(d3_key_facts(cluster, impl_id, key));
    always_weaken(spec, ctx, lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(impl_id)));
    always_weaken(spec, ctx, lift_state(Cluster::every_in_flight_msg_has_unique_id()));
    always_weaken(spec, kf, lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(impl_id, key)));
    always_weaken(spec, kf, lift_state(Cluster::no_pending_req_msg_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::Init))));
    always_weaken(spec, kf, lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterAddFinalizer))));
    always_weaken(spec, kf, lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterRemoveFinalizer))));
    always_weaken(spec, kf, lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(impl_id, key, at_impl_step_closure(WidgetInnerImplStepView::AfterPatchStatus))));
    inner_impl_reconcile_eventually_terminates_on_key(cluster, inner_kind(k, b), finalizer, spec, impl_id, key);
}

// ---------------------------------------------------------------------------
// One terminating mirror: what a step keeps of it.
// ---------------------------------------------------------------------------

// The object with uid `uid` is at `key`, terminating.
pub open spec fn terminating_mirror(key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.resources().contains_key(key)
        &&& s.resources()[key].metadata.uid == Some(uid)
        &&& s.resources()[key].metadata.deletion_timestamp is Some
    }
}

// The object is gone and its uid has been issued, so nothing brings it back.
pub open spec fn gone_for_good(key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| object_is_gone(key, uid)(s) && uid < s.api_server.uid_counter
}

pub open spec fn gone_or_terminating(key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| gone_for_good(key, uid)(s) || terminating_mirror(key, uid)(s)
}

// One step of the implemented cluster, under its invariants.
pub open spec fn d3_base_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)(s)
    }
}

pub proof fn lemma_always_d3_base_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>)
    requires spec.entails(d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
    ensures spec.entails(always(lift_action(d3_base_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)))),
{
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, ObjectRef { kind: inner_kind(k, b), namespace: ""@, name: ""@ });
    combine_spec_entails_always_n!(
        spec, lift_action(d3_base_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
        lift_action(cluster.next()),
        lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer))
    );
}

// A step of the API server that puts an object with a uid the key did not hold
// at the key creates it, with the uid counter as its uid.
proof fn lemma_api_server_step_stamps_uid(cluster: Cluster, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef)
    requires cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures
        s_prime.api_server.uid_counter >= s.api_server.uid_counter,
        s_prime.resources().contains_key(key) && !(s.resources().contains_key(key) && s.resources()[key].metadata.uid == s_prime.resources()[key].metadata.uid)
            ==> s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter),
{
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(_) => {},
        APIRequest::ListRequest(_) => {},
        APIRequest::CreateRequest(_) => {},
        APIRequest::DeleteRequest(_) => {},
        APIRequest::UpdateRequest(_) => {},
        APIRequest::UpdateStatusRequest(_) => {},
        APIRequest::GetThenDeleteRequest(_) => {},
        APIRequest::GetThenUpdateRequest(_) => {},
        APIRequest::GetThenUpdateStatusRequest(_) => {},
        APIRequest::PatchRequest(_) => {},
        APIRequest::PatchStatusRequest(_) => {},
    }
}

// A step keeps a terminating mirror of the implementation's kind as it is, or
// removes it: nothing else writes it. A Create finds the key taken. An Update of
// the kind is the implementation's, and on the stored mirror it is the release,
// which removes the mirror since its finalizer is the only one. A spec Patch is
// the sync controller's and a status Patch the implementation's; both test the
// generation of a live view, which the deletion stamp moved past. A Delete of a
// terminating object with finalizers does nothing.
pub proof fn lemma_terminating_mirror_after_step(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>,
    s: ClusterState, s_prime: ClusterState, key: ObjectRef, uid: Uid
)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        d3_base_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)(s, s_prime),
        key.kind == inner_kind(k, b),
        terminating_mirror(key, uid)(s),
    ensures object_is_gone(key, uid)(s_prime) || s_prime.resources()[key] == s.resources()[key],
{
    let kind = inner_kind(k, b);
    lemma_outer_kind_is_not_inner(k, b);
    assert(key.kind is CustomResourceKind);
    let old = s.resources()[key];
    assert(finalizers_are_the_impls(old.metadata, finalizer));
    assert(old.metadata.finalizers is Some && old.metadata.finalizers->0.len() > 0);
    assert(finalizer is Some);
    let f = finalizer->0;
    assert(old.metadata.finalizers->0[0] == f);
    assert(has_finalizer(old.metadata, f));
    assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
    assert(old.metadata.uid->0 < s.api_server.uid_counter);
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(input) => {
            let msg = input->0;
            lemma_api_server_step_stamps_uid(cluster, s, s_prime, msg, key);
            if s_prime.resources().contains_key(key) && s_prime.resources()[key].metadata.uid == Some(uid) && s_prime.resources()[key] != old {
                let new = s_prime.resources()[key];
                assert(s.in_flight().contains(msg));
                assert(msg.content is APIRequest);
                match msg.src {
                    HostId::Controller(id, ckey) => {
                        assert(cluster.controller_models.contains_key(id));
                        assert(id == sync_id || id == janitor_id || id == impl_id);
                    },
                    HostId::BuiltinController => {},
                    HostId::PodMonkey => {},
                    _ => { assert(false); },
                }
                match msg.content->APIRequest_0 {
                    APIRequest::CreateRequest(req) => {
                        // The key is taken.
                        assert(false);
                    },
                    APIRequest::UpdateRequest(req) => {
                        assert(req.key() == key);
                        match msg.src {
                            HostId::Controller(id, ckey) => {
                                if id == sync_id {
                                    assert(req.obj.kind == k.outer_kind);
                                    assert(false);
                                } else if id == impl_id {
                                    assert(inner_impl_request_is_guaranteed(kind, finalizer, msg, s));
                                    assert(req.obj.metadata.resource_version == old.metadata.resource_version);
                                    // The mirror has the finalizer, so this is the release,
                                    // which empties the finalizers and removes the mirror.
                                    assert(req.obj.metadata == without_finalizer(old.metadata, f));
                                    lemma_finalizer_update_keeps_finalizers_the_impls(old.metadata, f);
                                    assert(req.obj.metadata.finalizers is None);
                                    assert(new.metadata.finalizers is None);
                                    assert(new.metadata.deletion_timestamp is Some);
                                    assert(false);
                                } else {
                                    assert(false);
                                }
                            },
                            _ => { assert(false); },
                        }
                    },
                    APIRequest::PatchRequest(req) => {
                        assert(req.key() == key);
                        assert(req.tests.pass(old));
                        match msg.src {
                            HostId::Controller(id, ckey) => {
                                if id == sync_id {
                                    assert(patch_tests_are_not_ahead(req.tests, key, s));
                                    assert(req.tests.uid == old.metadata.uid);
                                    assert(req.tests.generation == old.metadata.generation);
                                    assert(old.metadata.deletion_timestamp is None);
                                    assert(false);
                                } else {
                                    assert(false);
                                }
                            },
                            _ => { assert(false); },
                        }
                    },
                    APIRequest::PatchStatusRequest(req) => {
                        assert(req.key() == key);
                        assert(req.tests.pass(old));
                        match msg.src {
                            HostId::Controller(id, ckey) => {
                                if id == impl_id {
                                    assert(inner_impl_status_patches_are_not_ahead(impl_id)(s));
                                    assert(patch_tests_are_not_ahead(req.tests, key, s));
                                    assert(req.tests.uid == old.metadata.uid);
                                    assert(req.tests.generation == old.metadata.generation);
                                    assert(old.metadata.deletion_timestamp is None);
                                    assert(false);
                                } else if id == sync_id {
                                    assert(req.kind == k.outer_kind);
                                    assert(false);
                                } else {
                                    assert(false);
                                }
                            },
                            _ => { assert(false); },
                        }
                    },
                    APIRequest::DeleteRequest(req) => {
                        // A terminating object with finalizers is left as it is.
                        assert(false);
                    },
                    APIRequest::GetThenDeleteRequest(req) => {
                        assert(false);
                    },
                    APIRequest::GetThenUpdateRequest(req) => {
                        match msg.src {
                            HostId::Controller(id, ckey) => { assert(false); },
                            _ => { assert(false); },
                        }
                    },
                    APIRequest::UpdateStatusRequest(req) => {
                        match msg.src {
                            HostId::Controller(id, ckey) => { assert(false); },
                            _ => { assert(false); },
                        }
                    },
                    APIRequest::GetThenUpdateStatusRequest(req) => {
                        match msg.src {
                            HostId::Controller(id, ckey) => { assert(false); },
                            _ => { assert(false); },
                        }
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// Gone or terminating is kept by every step: a terminating mirror stays as it is
// or goes, and a gone one never comes back, its uid being issued.
pub proof fn lemma_gone_or_terminating_after_step(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>,
    s: ClusterState, s_prime: ClusterState, key: ObjectRef, uid: Uid
)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        d3_base_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)(s, s_prime),
        key.kind == inner_kind(k, b),
        gone_or_terminating(key, uid)(s),
    ensures gone_or_terminating(key, uid)(s_prime),
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    if terminating_mirror(key, uid)(s) {
        lemma_terminating_mirror_after_step(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, s, s_prime, key, uid);
        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
        assert(uid < s.api_server.uid_counter);
    }
    match step {
        Step::APIServerStep(input) => {
            lemma_api_server_step_stamps_uid(cluster, s, s_prime, input->0, key);
            if object_is_gone(key, uid)(s) && !object_is_gone(key, uid)(s_prime) {
                assert(s_prime.resources()[key].metadata.uid == Some(s.api_server.uid_counter));
                assert(false);
            }
        },
        _ => {
            assert(s_prime.api_server == s.api_server);
        },
    }
}

// ---------------------------------------------------------------------------
// The layers, per terminating mirror.
// ---------------------------------------------------------------------------

pub open spec fn d3_spec_with_phase_i(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>) -> TempPred<ClusterState> {
    d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer).and(always(lift_state(phase_i(impl_id))))
}

pub open spec fn d3_spec_with_e(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid) -> TempPred<ClusterState> {
    d3_spec_with_phase_i(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer).and(always(lift_state(gone_or_terminating(key, uid))))
}

pub open spec fn d3_spec_with_xor(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid) -> TempPred<ClusterState> {
    d3_spec_with_e(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)
        .and(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(impl_id, key))))
}

// A snapshot of the mirror carries the stored version, unless the mirror is gone.
pub open spec fn impl_snapshot_current_or_gone(key: ObjectRef, uid: Uid) -> spec_fn(DynamicObjectView, ClusterState) -> bool {
    |o: DynamicObjectView, s: ClusterState| {
        ||| gone_for_good(key, uid)(s)
        ||| (terminating_mirror(key, uid)(s) && o.metadata.resource_version == s.resources()[key].metadata.resource_version)
    }
}

pub open spec fn d3_spec_with_snap(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid) -> TempPred<ClusterState> {
    d3_spec_with_xor(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)
        .and(always(lift_state(snapshots_satisfy(impl_id, key, impl_snapshot_current_or_gone(key, uid)))))
}

pub proof fn d3_spec_with_phase_i_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>)
    ensures valid(stable(d3_spec_with_phase_i(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer))),
{
    d3_stable_spec_is_stable(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer);
    always_p_is_stable(lift_state(phase_i(impl_id)));
    stable_and_n!(d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer), always(lift_state(phase_i(impl_id))));
}

pub proof fn d3_spec_with_e_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    ensures valid(stable(d3_spec_with_e(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid))),
{
    d3_spec_with_phase_i_is_stable(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer);
    always_p_is_stable(lift_state(gone_or_terminating(key, uid)));
    stable_and_n!(d3_spec_with_phase_i(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer), always(lift_state(gone_or_terminating(key, uid))));
}

pub proof fn d3_spec_with_xor_is_stable(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    ensures valid(stable(d3_spec_with_xor(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid))),
{
    d3_spec_with_e_is_stable(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    always_p_is_stable(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(impl_id, key)));
    stable_and_n!(
        d3_spec_with_e(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid),
        always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(impl_id, key)))
    );
}

pub proof fn lemma_unfold_d3_spec_with_snap(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    requires spec.entails(d3_spec_with_snap(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
    ensures
        spec.entails(d3_spec_with_xor(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
        spec.entails(always(lift_state(snapshots_satisfy(impl_id, key, impl_snapshot_current_or_gone(key, uid))))),
{
    entails_and_split(spec, d3_spec_with_xor(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid), always(lift_state(snapshots_satisfy(impl_id, key, impl_snapshot_current_or_gone(key, uid)))));
}

pub proof fn lemma_unfold_d3_spec_with_xor(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    requires spec.entails(d3_spec_with_xor(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
    ensures
        spec.entails(d3_spec_with_e(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
        spec.entails(d3_spec_with_phase_i(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
        spec.entails(d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
        spec.entails(always(lift_state(phase_i(impl_id)))),
        spec.entails(always(lift_state(Cluster::crash_disabled(impl_id)))),
        spec.entails(always(lift_state(Cluster::req_drop_disabled()))),
        spec.entails(always(lift_state(Cluster::pod_monkey_disabled()))),
        spec.entails(always(lift_state(gone_or_terminating(key, uid)))),
        spec.entails(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(impl_id, key)))),
{
    entails_and_split(spec, d3_spec_with_e(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid), always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(impl_id, key))));
    entails_and_split(spec, d3_spec_with_phase_i(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer), always(lift_state(gone_or_terminating(key, uid))));
    entails_and_split(spec, d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer), always(lift_state(phase_i(impl_id))));
    always_weaken(spec, lift_state(phase_i(impl_id)), lift_state(Cluster::crash_disabled(impl_id)));
    always_weaken(spec, lift_state(phase_i(impl_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(impl_id)), lift_state(Cluster::pod_monkey_disabled()));
}

// The action the walk's step lemmas assume.
pub open spec fn d3_walk_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid) -> ActionPred<ClusterState> {
    |s: ClusterState, s_prime: ClusterState| {
        &&& d3_base_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)(s, s_prime)
        &&& d3_key_facts(cluster, impl_id, key)(s)
        &&& phase_i(impl_id)(s)
        &&& Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(impl_id, key)(s)
        &&& gone_or_terminating(key, uid)(s)
        &&& snapshots_satisfy(impl_id, key, impl_snapshot_current_or_gone(key, uid))(s)
    }
}

pub proof fn lemma_always_d3_walk_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    requires spec.entails(d3_spec_with_snap(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
    ensures spec.entails(always(lift_action(d3_walk_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)))),
{
    lemma_unfold_d3_spec_with_snap(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_spec_with_xor(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    lemma_always_d3_base_next(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer);
    combine_spec_entails_always_n!(
        spec, lift_action(d3_walk_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
        lift_action(d3_base_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
        lift_state(d3_key_facts(cluster, impl_id, key)),
        lift_state(phase_i(impl_id)),
        lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(impl_id, key)),
        lift_state(gone_or_terminating(key, uid)),
        lift_state(snapshots_satisfy(impl_id, key, impl_snapshot_current_or_gone(key, uid)))
    );
}

// ---------------------------------------------------------------------------
// The walk: idle ~> scheduled ~> Init ~> the release in flight ~> gone.
// ---------------------------------------------------------------------------

pub open spec fn st_impl_init(impl_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& at_impl_step(impl_id, key, WidgetInnerImplStepView::Init)(s)
        &&& Cluster::no_pending_req_msg(impl_id, s, key)
    }
}

// The release, built from the snapshot `cr`.
pub open spec fn release_req_msg_for(kind: Kind, f: StringView, impl_id: int, key: ObjectRef, msg: Message, cr: DynamicObjectView) -> bool {
    &&& msg.src == HostId::Controller(impl_id, key)
    &&& msg.dst is APIServer
    &&& msg.content is APIRequest
    &&& msg.content->APIRequest_0 == APIRequest::UpdateRequest(inner_impl_reconciler::inner_finalizer_update(unmarshal(kind, cr)->Ok_0, f, false))
}

// The release is in flight, and the mirror is gone or still at the snapshot's
// version, in which case the release lands.
pub open spec fn st_release_req_msg_in_flight(kind: Kind, f: StringView, impl_id: int, key: ObjectRef, uid: Uid, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let cr = s.ongoing_reconciles(impl_id)[key].triggering_cr;
        &&& at_impl_step(impl_id, key, WidgetInnerImplStepView::AfterRemoveFinalizer)(s)
        &&& s.ongoing_reconciles(impl_id)[key].pending_req_msg == Some(msg)
        &&& release_req_msg_for(kind, f, impl_id, key, msg, cr)
        &&& s.in_flight().contains(msg)
        &&& impl_snapshot_current_or_gone(key, uid)(cr, s)
    }
}

pub open spec fn st_release_req_in_flight(kind: Kind, f: StringView, impl_id: int, key: ObjectRef, uid: Uid) -> StatePred<ClusterState> {
    |s: ClusterState| exists |msg: Message| #[trigger] st_release_req_msg_in_flight(kind, f, impl_id, key, uid, msg)(s)
}

// A pending request of the implementation's reconcile of `key` stays pending and
// in flight through any step but the one that answers it.
proof fn lemma_d3_pending_req_stays(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>,
    s: ClusterState, s_prime: ClusterState, key: ObjectRef, uid: Uid, msg: Message
)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        d3_walk_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)(s, s_prime),
        s.ongoing_reconciles(impl_id).contains_key(key),
        s.ongoing_reconciles(impl_id)[key].pending_req_msg == Some(msg),
        msg.src == HostId::Controller(impl_id, key),
        msg.dst is APIServer,
        msg.content is APIRequest,
        s.in_flight().contains(msg),
        !cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures
        s_prime.ongoing_reconciles(impl_id).contains_key(key),
        s_prime.ongoing_reconciles(impl_id)[key] == s.ongoing_reconciles(impl_id)[key],
        s_prime.in_flight().contains(msg),
{
    let step = choose |step| cluster.next_step(s, s_prime, step);
    match step {
        Step::APIServerStep(i) => {
            assert(i->0 != msg);
            assert(s_prime.in_flight().contains(msg));
            assert(s_prime.ongoing_reconciles(impl_id) == s.ongoing_reconciles(impl_id));
        },
        Step::ControllerStep(i) => {
            if i.0 == impl_id && i.2 == Some(key) {
                assert(i.1 is Some);
                assert(s.in_flight().contains(i.1->0) && resp_msg_matches_req_msg(i.1->0, msg));
                assert(false);
            } else {
                assert(s_prime.ongoing_reconciles(impl_id)[key] == s.ongoing_reconciles(impl_id)[key]);
                assert(s_prime.in_flight().contains(msg));
            }
        },
        Step::RestartControllerStep(id) => {
            assert(id != impl_id);
        },
        _ => {
            assert(s_prime.ongoing_reconciles(impl_id)[key] == s.ongoing_reconciles(impl_id)[key]);
            assert(s_prime.in_flight().contains(msg));
        },
    }
}

// idle ~> scheduled, unless the mirror is gone.
proof fn lemma_d3_idle_leads_to_scheduled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        key.kind == inner_kind(k, b),
        spec.entails(d3_spec_with_snap(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
    ensures
        spec.entails(lift_state(Cluster::reconcile_idle(impl_id, key))
            .leads_to(lift_state(|s: ClusterState| {
                &&& !s.ongoing_reconciles(impl_id).contains_key(key)
                &&& s.scheduled_reconciles(impl_id).contains_key(key)
            }).or(lift_state(gone_for_good(key, uid))))),
{
    lemma_unfold_d3_spec_with_snap(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_spec_with_xor(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    let sched = |s: ClusterState| {
        &&& !s.ongoing_reconciles(impl_id).contains_key(key)
        &&& s.scheduled_reconciles(impl_id).contains_key(key)
    };
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(impl_id).contains_key(key)
        &&& !s.scheduled_reconciles(impl_id).contains_key(key)
        &&& s.resources().contains_key(key)
    };
    let post = |s: ClusterState| sched(s) || !s.resources().contains_key(key);
    let next = cluster.next();
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
        && cluster.schedule_controller_reconcile().forward((impl_id, key))(s, s_prime) implies post(s_prime) by {}
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.schedule_controller_reconcile().pre((impl_id, key))(s) by {
        assert(key.kind == cluster.controller_models[impl_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, impl_id, key, next, pre, post);
    let rest = |s: ClusterState| Cluster::reconcile_idle(impl_id, key)(s) && !pre(s);
    entails_implies_leads_to(spec, lift_state(rest), lift_state(post));
    or_leads_to(spec, lift_state(pre), lift_state(rest), lift_state(post));
    temp_pred_equality(lift_state(pre).or(lift_state(rest)), lift_state(Cluster::reconcile_idle(impl_id, key)));
    // A missing mirror is a gone one, under the layer.
    let target = lift_state(sched).or(lift_state(gone_for_good(key, uid)));
    assert forall |s: ClusterState| #[trigger] gone_or_terminating(key, uid)(s) && post(s) implies sched(s) || gone_for_good(key, uid)(s) by {}
    always_weaken(spec, lift_state(gone_or_terminating(key, uid)), lift_state(post).implies(target));
    always_implies_to_leads_to(spec, lift_state(post), target);
    leads_to_trans(spec, lift_state(Cluster::reconcile_idle(impl_id, key)), lift_state(post), target);
}

// scheduled ~> Init with no pending request.
proof fn lemma_d3_scheduled_leads_to_init(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        key.kind == inner_kind(k, b),
        spec.entails(d3_spec_with_snap(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
    ensures
        spec.entails(lift_state(|s: ClusterState| {
                &&& !s.ongoing_reconciles(impl_id).contains_key(key)
                &&& s.scheduled_reconciles(impl_id).contains_key(key)
            }).leads_to(lift_state(st_impl_init(impl_id, key)))),
{
    lemma_unfold_d3_spec_with_snap(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_spec_with_xor(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    WidgetInnerImplReconcileState::marshal_preserves_integrity();
    let pre = |s: ClusterState| {
        &&& !s.ongoing_reconciles(impl_id).contains_key(key)
        &&& s.scheduled_reconciles(impl_id).contains_key(key)
    };
    let post = st_impl_init(impl_id, key);
    let input = (None::<Message>, Some(key));
    let stronger_next = |s, s_prime: ClusterState| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(impl_id)(s)
        &&& Cluster::crash_disabled(impl_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(impl_id)),
        lift_state(Cluster::crash_disabled(impl_id))
    );
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        if s_prime.ongoing_reconciles(impl_id).contains_key(key) {
            assert(s_prime.ongoing_reconciles(impl_id)[key].local_state == inner_impl_reconciler::reconcile_init_state().marshal());
            assert(s_prime.ongoing_reconciles(impl_id)[key].pending_req_msg is None);
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] stronger_next(s, s_prime)
        && cluster.controller_next().forward((impl_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.ongoing_reconciles(impl_id)[key].local_state == inner_impl_reconciler::reconcile_init_state().marshal());
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::RunScheduledReconcile, (impl_id, input.0, input.1))(s) by {
        assert(key.kind == cluster.controller_models[impl_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, impl_id, input, stronger_next, ControllerStep::RunScheduledReconcile, pre, post);
}

// Init ~> the release is in flight, unless the mirror is gone: the snapshot is
// the stored mirror, terminating and carrying the implementation's finalizer.
proof fn lemma_d3_init_leads_to_release_req(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, f: StringView, key: ObjectRef, uid: Uid)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, Some(f)),
        key.kind == inner_kind(k, b),
        spec.entails(d3_spec_with_snap(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, Some(f), key, uid)),
    ensures
        spec.entails(lift_state(st_impl_init(impl_id, key))
            .leads_to(lift_state(st_release_req_in_flight(inner_kind(k, b), f, impl_id, key, uid)).or(lift_state(gone_for_good(key, uid))))),
{
    let kind = inner_kind(k, b);
    let finalizer = Some(f);
    lemma_unfold_d3_spec_with_snap(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_spec_with_xor(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    lemma_always_d3_walk_next(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    unmarshal_of_marshal();
    marshal_preserves_metadata();
    WidgetInnerImplReconcileState::marshal_preserves_integrity();
    let pre = st_impl_init(impl_id, key);
    let post = |s: ClusterState| st_release_req_in_flight(kind, f, impl_id, key, uid)(s) || gone_for_good(key, uid)(s);
    let input = (None::<Message>, Some(key));
    let next = d3_walk_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
        && cluster.controller_next().forward((impl_id, input.0, input.1))(s, s_prime) implies post(s_prime) by {
        assert(s_prime.api_server == s.api_server);
        let cr = s.ongoing_reconciles(impl_id)[key].triggering_cr;
        assert(impl_snapshot_current_or_gone(key, uid)(cr, s));
        if gone_for_good(key, uid)(s) {
            assert(gone_for_good(key, uid)(s_prime));
        } else {
            // The snapshot is the stored mirror.
            assert(terminating_mirror(key, uid)(s));
            assert(snapshot_is_current_at(key, cr, s));
            assert(s.resources()[key] == cr);
            assert(unmarshal(kind, cr) is Ok);
            let inner = unmarshal(kind, cr)->Ok_0;
            assert(inner.metadata == cr.metadata);
            assert(inner.metadata.deletion_timestamp is Some);
            assert(finalizers_are_the_impls(cr.metadata, finalizer));
            assert(cr.metadata.finalizers is Some && cr.metadata.finalizers->0.len() > 0);
            assert(cr.metadata.finalizers->0[0] == f);
            assert(has_finalizer(inner.metadata, f));
            let req = APIRequest::UpdateRequest(inner_impl_reconciler::inner_finalizer_update(inner, f, false));
            let msg = controller_req_msg(impl_id, key, s.rpc_id_allocator.allocate().1, req);
            assert(s_prime.ongoing_reconciles(impl_id)[key].pending_req_msg == Some(msg));
            assert(s_prime.ongoing_reconciles(impl_id)[key].triggering_cr == cr);
            assert(s_prime.in_flight().contains(msg));
            assert(s_prime.ongoing_reconciles(impl_id)[key].local_state == inner_impl_reconciler::at_step(WidgetInnerImplStepView::AfterRemoveFinalizer).marshal());
            assert(release_req_msg_for(kind, f, impl_id, key, msg, cr));
            assert(st_release_req_msg_in_flight(kind, f, impl_id, key, uid, msg)(s_prime));
        }
    }
    assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
        let step = choose |step| cluster.next_step(s, s_prime, step);
        match step {
            Step::ControllerStep(i) => {
                if i.0 == impl_id && i.2 == Some(key) {
                    assert(i.1 is None);
                    assert(cluster.controller_next().forward((impl_id, input.0, input.1))(s, s_prime));
                } else {
                    assert(s_prime.ongoing_reconciles(impl_id)[key] == s.ongoing_reconciles(impl_id)[key]);
                }
            },
            _ => {
                assert(s_prime.ongoing_reconciles(impl_id)[key] == s.ongoing_reconciles(impl_id)[key]);
            },
        }
    }
    assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.controller_action_pre(ControllerStep::ContinueReconcile, (impl_id, input.0, input.1))(s) by {
        assert(key.kind == cluster.controller_models[impl_id].reconcile_model.kind);
    }
    cluster.lemma_pre_leads_to_post_by_controller(spec, impl_id, input, next, ControllerStep::ContinueReconcile, pre, post);
    temp_pred_equality(lift_state(post), lift_state(st_release_req_in_flight(kind, f, impl_id, key, uid)).or(lift_state(gone_for_good(key, uid))));
}

// The API server handles the release: the mirror is still the snapshot, so the
// Update lands, empties the finalizers and removes it.
proof fn lemma_d3_release_req_handled(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, f: StringView,
    s: ClusterState, s_prime: ClusterState, key: ObjectRef, uid: Uid, msg: Message
)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, Some(f)),
        key.kind == inner_kind(k, b),
        d3_walk_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, Some(f), key, uid)(s, s_prime),
        st_release_req_msg_in_flight(inner_kind(k, b), f, impl_id, key, uid, msg)(s),
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    ensures gone_for_good(key, uid)(s_prime),
{
    let kind = inner_kind(k, b);
    let finalizer = Some(f);
    marshal_status_preserves_integrity();
    marshal_preserves_metadata();
    marshal_preserves_kind();
    unmarshal_is_representable();
    if gone_for_good(key, uid)(s) {
        lemma_gone_or_terminating_after_step(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, s, s_prime, key, uid);
        assert(!terminating_mirror(key, uid)(s_prime));
    } else {
        let cr = s.ongoing_reconciles(impl_id)[key].triggering_cr;
        assert(terminating_mirror(key, uid)(s));
        assert(snapshot_is_current_at(key, cr, s));
        let old = s.resources()[key];
        assert(old == cr);
        assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
        assert(cluster.etcd_object_is_well_formed(key)(s));
        assert(Cluster::etcd_object_has_at_most_one_controller_owner(key)(s));
        assert(unmarshal(kind, cr) is Ok);
        let inner = unmarshal(kind, cr)->Ok_0;
        assert(inner.metadata == old.metadata);
        assert(inner.spec == old.spec);
        assert(inner.kind == kind);
        let req = msg.content->APIRequest_0->UpdateRequest_0;
        let updated_meta = without_finalizer(inner.metadata, f);
        assert(finalizers_are_the_impls(old.metadata, finalizer));
        lemma_finalizer_update_keeps_finalizers_the_impls(old.metadata, f);
        assert(updated_meta.finalizers is None);
        assert(req == inner_impl_reconciler::inner_finalizer_update(inner, f, false));
        assert(req.obj == marshal(inner.with_metadata(updated_meta)));
        assert(req.obj.kind == kind);
        assert(req.obj.metadata == updated_meta);
        assert(req.obj.spec == old.spec);
        assert(req.obj.status == marshal_status(inner.status));
        // Admission: the object names itself, unmarshals, exists, and carries the
        // stored version and uid.
        assert(req.key() == key);
        assert(kind is CustomResourceKind);
        assert(cluster.installed_types[kind->CustomResourceKind_0] == Cluster::synced_installed_type(spec_ok, k.selector));
        assert(unmarshallable_object(req.obj, cluster.installed_types)) by {
            assert(unmarshal_status(marshal_status(inner.status)) is Ok);
        }
        assert(update_request_admission_check(cluster.installed_types, req, s.api_server) is None);
        let updated = updated_object(req, old);
        assert(updated.metadata.finalizers is None);
        assert(updated != old);
        let with_rv = updated.with_resource_version(s.api_server.resource_version_counter);
        assert(old.metadata.deletion_timestamp is Some);
        assert(with_rv.metadata.owner_references == old.metadata.owner_references);
        assert(metadata_validity_check(with_rv) is None);
        assert(metadata_transition_validity_check(with_rv, old) is None);
        assert(valid_object(old, cluster.installed_types));
        assert(valid_object(with_rv, cluster.installed_types));
        assert(valid_transition(with_rv, old, cluster.installed_types)) by {
            assert(with_rv.spec == old.spec);
        }
        assert(updated_object_validity_check(with_rv, old, cluster.installed_types) is None);
        // Terminating and without finalizers: removed.
        assert(with_rv.metadata.deletion_timestamp is Some);
        assert(with_rv.object_ref() == key);
        assert(!s_prime.resources().contains_key(key));
        assert(uid < s.api_server.uid_counter);
        assert(s_prime.api_server.uid_counter == s.api_server.uid_counter);
    }
}

// One step from the release in flight: it stays in flight, or the mirror is gone.
proof fn lemma_d3_release_req_msg_next(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, f: StringView,
    s: ClusterState, s_prime: ClusterState, key: ObjectRef, uid: Uid, msg: Message
)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, Some(f)),
        key.kind == inner_kind(k, b),
        d3_walk_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, Some(f), key, uid)(s, s_prime),
        st_release_req_msg_in_flight(inner_kind(k, b), f, impl_id, key, uid, msg)(s),
    ensures
        st_release_req_msg_in_flight(inner_kind(k, b), f, impl_id, key, uid, msg)(s_prime) || gone_for_good(key, uid)(s_prime),
        cluster.api_server_next().forward(Some(msg))(s, s_prime) ==> gone_for_good(key, uid)(s_prime),
{
    let kind = inner_kind(k, b);
    let finalizer = Some(f);
    if cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))) {
        lemma_d3_release_req_handled(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, f, s, s_prime, key, uid, msg);
    } else {
        lemma_d3_pending_req_stays(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, s, s_prime, key, uid, msg);
        let cr = s.ongoing_reconciles(impl_id)[key].triggering_cr;
        if gone_for_good(key, uid)(s) {
            lemma_gone_or_terminating_after_step(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, s, s_prime, key, uid);
            assert(!terminating_mirror(key, uid)(s_prime));
        } else {
            lemma_terminating_mirror_after_step(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, s, s_prime, key, uid);
            if object_is_gone(key, uid)(s_prime) {
                assert(Cluster::etcd_object_is_weakly_well_formed(key)(s));
                let step = choose |step| cluster.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(i) => {
                        lemma_api_server_step_stamps_uid(cluster, s, s_prime, i->0, key);
                    },
                    _ => {
                        assert(s_prime.api_server == s.api_server);
                    },
                }
                assert(gone_for_good(key, uid)(s_prime));
            } else {
                assert(s_prime.resources()[key] == s.resources()[key]);
                assert(impl_snapshot_current_or_gone(key, uid)(cr, s_prime));
            }
        }
    }
}

// The release in flight ~> gone.
proof fn lemma_d3_release_req_leads_to_gone(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, f: StringView, key: ObjectRef, uid: Uid)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, Some(f)),
        key.kind == inner_kind(k, b),
        spec.entails(d3_spec_with_snap(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, Some(f), key, uid)),
    ensures
        spec.entails(lift_state(st_release_req_in_flight(inner_kind(k, b), f, impl_id, key, uid)).leads_to(lift_state(gone_for_good(key, uid)))),
{
    let kind = inner_kind(k, b);
    let finalizer = Some(f);
    lemma_unfold_d3_spec_with_snap(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_spec_with_xor(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    lemma_always_d3_walk_next(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    let next = d3_walk_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    let post = gone_for_good(key, uid);
    let pre_of = |msg: Message| lift_state(st_release_req_msg_in_flight(kind, f, impl_id, key, uid, msg));
    assert forall |msg: Message| spec.entails(#[trigger] pre_of(msg).leads_to(lift_state(post))) by {
        let pre = st_release_req_msg_in_flight(kind, f, impl_id, key, uid, msg);
        let input = Some(msg);
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime)
            && cluster.api_server_next().forward(input)(s, s_prime) implies post(s_prime) by {
            lemma_d3_release_req_msg_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, f, s, s_prime, key, uid, msg);
        }
        assert forall |s, s_prime: ClusterState| pre(s) && #[trigger] next(s, s_prime) implies pre(s_prime) || post(s_prime) by {
            lemma_d3_release_req_msg_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, f, s, s_prime, key, uid, msg);
        }
        assert forall |s: ClusterState| #[trigger] pre(s) implies cluster.api_server_action_pre(APIServerStep::HandleRequest, input)(s) by {
            assert(release_req_msg_for(kind, f, impl_id, key, msg, s.ongoing_reconciles(impl_id)[key].triggering_cr));
        }
        cluster.lemma_pre_leads_to_post_by_api_server(spec, input, next, APIServerStep::HandleRequest, pre, post);
    }
    leads_to_exists_intro(spec, pre_of, lift_state(post));
    assert_by(tla_exists(pre_of) == lift_state(st_release_req_in_flight(kind, f, impl_id, key, uid)), {
        assert forall |ex| #[trigger] lift_state(st_release_req_in_flight(kind, f, impl_id, key, uid)).satisfied_by(ex)
        implies tla_exists(pre_of).satisfied_by(ex) by {
            let s = ex.head();
            let msg = choose |msg: Message| #[trigger] st_release_req_msg_in_flight(kind, f, impl_id, key, uid, msg)(s);
            assert(pre_of(msg).satisfied_by(ex));
        }
        temp_pred_equality(tla_exists(pre_of), lift_state(st_release_req_in_flight(kind, f, impl_id, key, uid)));
    });
}

// ---------------------------------------------------------------------------
// Assembly.
// ---------------------------------------------------------------------------

// Under all layers: the mirror is eventually gone.
proof fn lemma_d3_true_leads_to_gone(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        key.kind == inner_kind(k, b),
        spec.entails(d3_spec_with_snap(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
    ensures spec.entails(true_pred().leads_to(lift_state(gone_for_good(key, uid)))),
{
    let kind = inner_kind(k, b);
    lemma_unfold_d3_spec_with_snap(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_spec_with_xor(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    let gone = lift_state(gone_for_good(key, uid));
    if finalizer is None {
        // No mirror of the kind ever terminates, so the layer says the mirror is gone.
        let ctx = d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer);
        assert forall |s: ClusterState| #[trigger] ctx(s) && gone_or_terminating(key, uid)(s) implies gone_for_good(key, uid)(s) by {
            if terminating_mirror(key, uid)(s) {
                assert(finalizers_are_the_impls(s.resources()[key].metadata, finalizer));
                assert(s.resources()[key].metadata.finalizers is Some);
                assert(false);
            }
        }
        entails_always_and_n!(spec, lift_state(ctx), lift_state(gone_or_terminating(key, uid)));
        always_weaken(spec, lift_state(ctx).and(lift_state(gone_or_terminating(key, uid))), true_pred().implies(gone));
        always_implies_to_leads_to(spec, true_pred(), gone);
    } else {
        let f = finalizer->0;
        lemma_impl_terminates(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
        let idle = lift_state(Cluster::reconcile_idle(impl_id, key));
        let sched = lift_state(|s: ClusterState| {
            &&& !s.ongoing_reconciles(impl_id).contains_key(key)
            &&& s.scheduled_reconciles(impl_id).contains_key(key)
        });
        let init = lift_state(st_impl_init(impl_id, key));
        let release = lift_state(st_release_req_in_flight(kind, f, impl_id, key, uid));
        lemma_d3_idle_leads_to_scheduled(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
        lemma_d3_scheduled_leads_to_init(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
        lemma_d3_init_leads_to_release_req(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, f, key, uid);
        lemma_d3_release_req_leads_to_gone(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, f, key, uid);
        entails_implies_leads_to(spec, gone, gone);
        or_leads_to(spec, release, gone, gone);
        leads_to_trans(spec, init, release.or(gone), gone);
        leads_to_trans(spec, sched, init, gone);
        or_leads_to(spec, sched, gone, gone);
        leads_to_trans(spec, idle, sched.or(gone), gone);
        leads_to_trans(spec, true_pred(), idle, gone);
    }
}

// The snapshot layer: under the layers below it, the snapshots eventually carry
// the stored version, since nothing writes a terminating mirror but its release.
proof fn lemma_d3_true_leads_to_always_snap(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        key.kind == inner_kind(k, b),
        valid(stable(spec)),
        spec.entails(d3_spec_with_xor(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(snapshots_satisfy(impl_id, key, impl_snapshot_current_or_gone(key, uid)))))),
{
    lemma_unfold_d3_spec_with_xor(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    lemma_always_d3_base_next(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer);
    lemma_impl_terminates(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    let pred = impl_snapshot_current_or_gone(key, uid);
    let next = |s: ClusterState, s_prime: ClusterState| {
        &&& d3_base_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)(s, s_prime)
        &&& gone_or_terminating(key, uid)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(d3_base_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
        lift_state(gone_or_terminating(key, uid))
    );
    assert forall |s, s_prime: ClusterState| #[trigger] next(s, s_prime) implies preserves(pred)(s, s_prime) by {
        assert forall |o: DynamicObjectView| #[trigger] pred(o, s) implies pred(o, s_prime) by {
            lemma_gone_or_terminating_after_step(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, s, s_prime, key, uid);
            if !gone_for_good(key, uid)(s) {
                lemma_terminating_mirror_after_step(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, s, s_prime, key, uid);
            }
        }
    }
    always_weaken(spec, lift_action(next), lift_action(preserves(pred)));
    assert forall |s: ClusterState| #[trigger] gone_or_terminating(key, uid)(s) implies stored_satisfies(key, pred)(s) by {}
    always_weaken(spec, lift_state(gone_or_terminating(key, uid)), lift_state(stored_satisfies(key, pred)));
    lemma_snapshots_eventually_satisfy(spec, cluster, impl_id, key, pred);
}

// The message facts of the implementation's reconcile of `key`, under phase I.
proof fn lemma_d3_true_leads_to_always_xor(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        spec.entails(d3_spec_with_phase_i(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(impl_id, key))))),
{
    let kind = inner_kind(k, b);
    entails_and_split(spec, d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer), always(lift_state(phase_i(impl_id))));
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    always_weaken(spec, lift_state(phase_i(impl_id)), lift_state(Cluster::crash_disabled(impl_id)));
    always_weaken(spec, lift_state(phase_i(impl_id)), lift_state(Cluster::req_drop_disabled()));
    always_weaken(spec, lift_state(phase_i(impl_id)), lift_state(Cluster::pod_monkey_disabled()));
    let ctx = lift_state(d3_ctx(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer));
    always_weaken(spec, lift_state(d3_key_facts(cluster, impl_id, key)), lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(impl_id, key)));
    always_weaken(spec, ctx, lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(impl_id)));
    always_weaken(spec, ctx, lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator()));
    always_weaken(spec, ctx, lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id()));
    always_weaken(spec, ctx, lift_state(Cluster::objects_in_reconcile_have_kind(kind, impl_id)));
    // Every reconcile of the implementation ends: those of its kind by termination,
    // and there are no others.
    let idle_of = |key: ObjectRef| true_pred().leads_to(lift_state(|s: ClusterState| !(s.ongoing_reconciles(impl_id).contains_key(key))));
    assert forall |key2: ObjectRef| spec.entails(#[trigger] idle_of(key2)) by {
        if key2.kind == kind {
            lemma_impl_terminates(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, key2);
            temp_pred_equality(lift_state(Cluster::reconcile_idle(impl_id, key2)), lift_state(|s: ClusterState| !(s.ongoing_reconciles(impl_id).contains_key(key2))));
        } else {
            assert forall |s: ClusterState| #[trigger] Cluster::objects_in_reconcile_have_kind(kind, impl_id)(s) implies !(s.ongoing_reconciles(impl_id).contains_key(key2)) by {}
            always_weaken(spec, lift_state(Cluster::objects_in_reconcile_have_kind(kind, impl_id)), true_pred().implies(lift_state(|s: ClusterState| !(s.ongoing_reconciles(impl_id).contains_key(key2)))));
            always_implies_to_leads_to(spec, true_pred(), lift_state(|s: ClusterState| !(s.ongoing_reconciles(impl_id).contains_key(key2))));
        }
    }
    spec_entails_tla_forall(spec, idle_of);
    cluster.lemma_true_leads_to_always_pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(spec, impl_id, key);
}

// D3 for one mirror: terminating ~> gone.
proof fn lemma_d3_per_object(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>, key: ObjectRef, uid: Uid)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        key.kind == inner_kind(k, b),
        spec.entails(d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer)),
    ensures spec.entails(lift_state(inner_terminating_object(k, b, key, uid)).leads_to(lift_state(object_is_gone(key, uid)))),
{
    let spec_p = d3_stable_spec(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer);
    let spec_i = d3_spec_with_phase_i(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer);
    let spec_e = d3_spec_with_e(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    let spec_x = d3_spec_with_xor(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    let spec_s = d3_spec_with_snap(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    let t = lift_state(inner_terminating_object(k, b, key, uid));
    let e = lift_state(gone_or_terminating(key, uid));
    let gone = lift_state(gone_for_good(key, uid));
    let phase = lift_state(phase_i(impl_id));
    let xor = lift_state(Cluster::pending_req_in_flight_xor_resp_in_flight_if_has_pending_req_msg(impl_id, key));
    let snap = lift_state(snapshots_satisfy(impl_id, key, impl_snapshot_current_or_gone(key, uid)));

    // Under all layers.
    assert(spec_s.entails(spec_s));
    lemma_d3_true_leads_to_gone(k, b, spec_ok, spec_s, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    // Remove the snapshot layer.
    d3_spec_with_xor_is_stable(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    unpack_conditions_from_spec(spec_x, always(snap), true_pred(), gone);
    temp_pred_equality(true_pred().and(always(snap)), always(snap));
    assert(spec_x.entails(spec_x));
    lemma_d3_true_leads_to_always_snap(k, b, spec_ok, spec_x, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    leads_to_trans(spec_x, true_pred(), always(snap), gone);
    // Remove the message layer.
    d3_spec_with_e_is_stable(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, key, uid);
    unpack_conditions_from_spec(spec_e, always(xor), true_pred(), gone);
    temp_pred_equality(true_pred().and(always(xor)), always(xor));
    assert(spec_e.entails(spec_e));
    entails_and_split(spec_e, spec_i, always(e));
    lemma_d3_true_leads_to_always_xor(k, b, spec_ok, spec_e, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    leads_to_trans(spec_e, true_pred(), always(xor), gone);
    // Remove the gone-or-terminating layer, then phase I.
    d3_spec_with_phase_i_is_stable(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer);
    unpack_conditions_from_spec(spec_i, always(e), true_pred(), gone);
    temp_pred_equality(true_pred().and(always(e)), always(e));
    d3_stable_spec_is_stable(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer);
    unpack_conditions_from_spec(spec_p, always(phase), always(e), gone);
    // Under the stable spec: terminating ~> [](gone or terminating) /\ []phase I.
    assert(spec_p.entails(spec_p));
    lemma_unfold_d3_stable_spec(k, b, spec_ok, spec_p, cluster, sync_id, janitor_id, impl_id, finalizer, key);
    lemma_always_d3_base_next(k, b, spec_ok, spec_p, cluster, sync_id, janitor_id, impl_id, finalizer);
    let next = d3_base_next(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer);
    assert forall |s, s_prime: ClusterState| gone_or_terminating(key, uid)(s) && #[trigger] next(s, s_prime) implies gone_or_terminating(key, uid)(s_prime) by {
        lemma_gone_or_terminating_after_step(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer, s, s_prime, key, uid);
    }
    entails_implies_leads_to(spec_p, t, e);
    leads_to_stable(spec_p, lift_action(next), t, e);
    lemma_true_leads_to_always_phase_i(k, b, spec_p, cluster, impl_id);
    always_weaken(spec_p, lift_action(next), t.implies(true_pred()));
    always_weaken(spec_p, lift_action(next), always(phase).implies(always(phase)));
    leads_to_weaken(spec_p, true_pred(), always(phase), t, always(phase));
    leads_to_always_and(spec_p, t, e, phase);
    leads_to_trans(spec_p, t, always(e).and(always(phase)), gone);
    // gone for good is gone.
    always_weaken(spec_p, lift_action(next), gone.implies(lift_state(object_is_gone(key, uid))));
    leads_to_weaken(spec_p, t, gone, t, lift_state(object_is_gone(key, uid)));
    entails_trans(spec, spec_p, t.leads_to(lift_state(object_is_gone(key, uid))));
}

// D3 for the implemented cluster: every terminating mirror of the
// implementation's kind is eventually gone.
pub proof fn inner_impl_releases(k: SyncKind, b: Binding, spec_ok: spec_fn(Value) -> bool, spec: TempPred<ClusterState>, cluster: Cluster, sync_id: int, janitor_id: int, impl_id: int, finalizer: Option<StringView>)
    requires
        d3_membership(k, b, spec_ok, cluster, sync_id, janitor_id, impl_id, finalizer),
        spec.entails(lift_state(cluster.init())),
        spec.entails(inner_impl_next_with_wf(cluster, impl_id)),
    ensures spec.entails(inner_releases_terminating_objects(k, b)),
{
    lemma_d3_stable_spec_holds(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer);
    let per_object = |i: (ObjectRef, Uid)| lift_state(inner_terminating_object(k, b, i.0, i.1)).leads_to(lift_state(object_is_gone(i.0, i.1)));
    assert forall |i: (ObjectRef, Uid)| spec.entails(#[trigger] per_object(i)) by {
        if i.0.kind == inner_kind(k, b) {
            lemma_d3_per_object(k, b, spec_ok, spec, cluster, sync_id, janitor_id, impl_id, finalizer, i.0, i.1);
        } else {
            // No object of another kind is a terminating mirror.
            assert forall |ex: Execution<ClusterState>| #[trigger] lift_state(inner_terminating_object(k, b, i.0, i.1)).satisfied_by(ex)
                implies lift_state(object_is_gone(i.0, i.1)).satisfied_by(ex) by {
                assert(!inner_terminating_object(k, b, i.0, i.1)(ex.head()));
            }
            entails_implies_leads_to(spec, lift_state(inner_terminating_object(k, b, i.0, i.1)), lift_state(object_is_gone(i.0, i.1)));
        }
    }
    spec_entails_tla_forall(spec, per_object);
}

}
