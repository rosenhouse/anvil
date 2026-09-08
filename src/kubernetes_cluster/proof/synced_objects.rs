// Data-driven counterparts of the CustomResourceView-generic invariants, for a
// kind of the shape (kubernetes_api_objects::spec::synced_object) whose installed
// type is Cluster::synced_installed_type(spec_ok, selector).
//
// Every item here is the same statement as its `<T: CustomResourceView>` twin in
// objects_in_store.rs, controller_runtime_safety.rs, controller_runtime_liveness.rs
// and spec/esr.rs, with `T::kind()` replaced by a `kind: Kind` parameter and
// `T::unmarshal` by `synced_object::unmarshal(kind, _)`. They exist because the
// shape's view is not a ResourceView: its kind is data, not a function of a type
// (doc/widget_sync_fanout_design.md, section 2.3).
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_api_objects::spec::synced_object::*;
use crate::reconciler::spec::io::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::*},
    cluster::*,
    controller::types::*,
    message::*,
};
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl Cluster {

// The kind is installed with the shape's installed type for `spec_ok` and `selector`.
pub open spec fn synced_type_is_installed(self, kind: Kind, spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector) -> bool {
    &&& kind is CustomResourceKind
    &&& self.installed_types.contains_key(kind->CustomResourceKind_0)
    &&& self.installed_types[kind->CustomResourceKind_0] == Self::synced_installed_type(spec_ok, selector)
}

// ---------------------------------------------------------------------------
// Objects of the kind in etcd.
// ---------------------------------------------------------------------------

pub open spec fn each_synced_object_in_etcd_is_well_formed(self, kind: Kind) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
            && key.kind == kind
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

pub proof fn lemma_always_each_synced_object_in_etcd_is_well_formed(
    self, spec: TempPred<ClusterState>, kind: Kind, spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.synced_type_is_installed(kind, spec_ok, selector),
    ensures spec.entails(always(lift_state(self.each_synced_object_in_etcd_is_well_formed(kind)))),
{
    let invariant = self.each_synced_object_in_etcd_is_well_formed(kind);

    assert forall |s, s_prime| invariant(s) && #[trigger] self.next()(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && key.kind == kind
        implies self.etcd_object_is_well_formed(key)(s_prime) by {
            marshal_status_preserves_integrity();
            if s.resources().contains_key(key) {
                assert(self.etcd_object_is_well_formed(key)(s));
            }
        }
    }

    init_invariant(spec, self.init(), self.next(), invariant);
}

// Every stored object of the kind unmarshals to the shape and its spec passes
// the schema check. The counterpart of cr_objects_in_etcd_satisfy_state_validation.
pub open spec fn synced_objects_in_etcd_are_valid(self, kind: Kind, spec_ok: spec_fn(Value) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            #[trigger] s.resources().contains_key(key)
            && key.kind == kind
            ==> unmarshal(kind, s.resources()[key]) is Ok && spec_ok(s.resources()[key].spec)
        }
    }
}

pub proof fn lemma_always_synced_objects_in_etcd_are_valid(
    self, spec: TempPred<ClusterState>, kind: Kind, spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.synced_type_is_installed(kind, spec_ok, selector),
    ensures spec.entails(always(lift_state(self.synced_objects_in_etcd_are_valid(kind, spec_ok)))),
{
    self.lemma_always_each_synced_object_in_etcd_is_well_formed(spec, kind, spec_ok, selector);
    let p = self.each_synced_object_in_etcd_is_well_formed(kind);
    assert forall |s: ClusterState| #[trigger] p(s) implies self.synced_objects_in_etcd_are_valid(kind, spec_ok)(s) by {
        assert forall |key: ObjectRef| #[trigger] s.resources().contains_key(key) && key.kind == kind
        implies unmarshal(kind, s.resources()[key]) is Ok && spec_ok(s.resources()[key].spec) by {
            assert(self.etcd_object_is_well_formed(key)(s));
            assert(s.resources()[key].kind == kind);
        }
    }
    always_weaken(spec, lift_state(p), lift_state(self.synced_objects_in_etcd_are_valid(kind, spec_ok)));
}

// ---------------------------------------------------------------------------
// Objects of the kind in a controller's schedule and ongoing reconciles.
// ---------------------------------------------------------------------------

pub open spec fn synced_objects_in_schedule_are_valid(self, kind: Kind, spec_ok: spec_fn(Value) -> bool, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            && key.kind == kind
            ==> unmarshal(kind, s.scheduled_reconciles(controller_id)[key]) is Ok
                && spec_ok(s.scheduled_reconciles(controller_id)[key].spec)
        }
    }
}

pub proof fn lemma_always_synced_objects_in_schedule_are_valid(
    self, spec: TempPred<ClusterState>, kind: Kind, spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector, controller_id: int
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.synced_type_is_installed(kind, spec_ok, selector),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(self.synced_objects_in_schedule_are_valid(kind, spec_ok, controller_id)))),
{
    let inv = self.synced_objects_in_schedule_are_valid(kind, spec_ok, controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& self.synced_objects_in_etcd_are_valid(kind, spec_ok)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_synced_objects_in_etcd_are_valid(spec, kind, spec_ok, selector);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(self.synced_objects_in_etcd_are_valid(kind, spec_ok)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

pub open spec fn synced_objects_in_reconcile_are_valid(self, kind: Kind, spec_ok: spec_fn(Value) -> bool, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            && key.kind == kind
            ==> unmarshal(kind, s.ongoing_reconciles(controller_id)[key].triggering_cr) is Ok
                && spec_ok(s.ongoing_reconciles(controller_id)[key].triggering_cr.spec)
        }
    }
}

pub proof fn lemma_always_synced_objects_in_reconcile_are_valid(
    self, spec: TempPred<ClusterState>, kind: Kind, spec_ok: spec_fn(Value) -> bool, selector: ClusterSelector, controller_id: int
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.synced_type_is_installed(kind, spec_ok, selector),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(self.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id)))),
{
    let inv = self.synced_objects_in_reconcile_are_valid(kind, spec_ok, controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& self.synced_objects_in_etcd_are_valid(kind, spec_ok)(s)
        &&& self.synced_objects_in_schedule_are_valid(kind, spec_ok, controller_id)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_synced_objects_in_etcd_are_valid(spec, kind, spec_ok, selector);
    self.lemma_always_synced_objects_in_schedule_are_valid(spec, kind, spec_ok, selector, controller_id);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(self.synced_objects_in_etcd_are_valid(kind, spec_ok)),
        lift_state(self.synced_objects_in_schedule_are_valid(kind, spec_ok, controller_id)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

// The local state of every ongoing reconcile of a data-driven controller
// unmarshals. The counterpart of cr_states_are_unmarshallable.
pub open spec fn synced_states_are_unmarshallable<S: Marshallable>(kind: Kind, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            && key.kind == kind
            ==> S::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state) is Ok
        }
    }
}

pub proof fn lemma_always_synced_states_are_unmarshallable<S, EReq, EResp>(
    self, spec: TempPred<ClusterState>, kind: Kind,
    init: spec_fn() -> S,
    core: spec_fn(SyncedObjectView, Option<ResponseView<EResp>>, S) -> (S, Option<RequestView<EReq>>),
    done: spec_fn(S) -> bool,
    error: spec_fn(S) -> bool,
    controller_id: int,
)
    where
        S: Marshallable,
        EReq: Marshallable,
        EResp: Marshallable,
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model == Self::synced_reconcile_model::<S, EReq, EResp>(kind, init, core, done, error),
    ensures spec.entails(always(lift_state(Self::synced_states_are_unmarshallable::<S>(kind, controller_id)))),
{
    let inv = Self::synced_states_are_unmarshallable::<S>(kind, controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    S::marshal_preserves_integrity();
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

// ---------------------------------------------------------------------------
// The keys a controller of the kind works on.
// ---------------------------------------------------------------------------

pub open spec fn objects_in_schedule_have_kind(kind: Kind, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.scheduled_reconciles(controller_id).contains_key(key) ==> key.kind == kind
    }
}

pub proof fn lemma_always_objects_in_schedule_have_kind(self, spec: TempPred<ClusterState>, kind: Kind, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model.kind == kind,
    ensures spec.entails(always(lift_state(Self::objects_in_schedule_have_kind(kind, controller_id)))),
{
    let inv = Self::objects_in_schedule_have_kind(kind, controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

pub open spec fn objects_in_reconcile_have_kind(kind: Kind, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| #[trigger] s.ongoing_reconciles(controller_id).contains_key(key) ==> key.kind == kind
    }
}

pub proof fn lemma_always_objects_in_reconcile_have_kind(self, spec: TempPred<ClusterState>, kind: Kind, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model.kind == kind,
    ensures spec.entails(always(lift_state(Self::objects_in_reconcile_have_kind(kind, controller_id)))),
{
    let inv = Self::objects_in_reconcile_have_kind(kind, controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
        &&& Self::objects_in_schedule_have_kind(kind, controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    self.lemma_always_objects_in_schedule_have_kind(spec, kind, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id)),
        lift_state(Self::objects_in_schedule_have_kind(kind, controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

pub open spec fn every_in_flight_msg_from_controller_has_key_kind(kind: Kind, controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.dst is APIServer
        } ==> match msg.src {
            HostId::Controller(id, key) => key.kind == kind,
            _ => false,
        }
    }
}

pub proof fn lemma_always_every_in_flight_msg_from_controller_has_key_kind(
    self, spec: TempPred<ClusterState>, kind: Kind, controller_id: int
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
        self.controller_models[controller_id].reconcile_model.kind == kind,
    ensures spec.entails(always(lift_state(Self::every_in_flight_msg_from_controller_has_key_kind(kind, controller_id)))),
{
    let inv = Self::every_in_flight_msg_from_controller_has_key_kind(kind, controller_id);
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
        &&& Self::objects_in_reconcile_have_kind(kind, controller_id)(s)
    };
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    self.lemma_always_objects_in_reconcile_have_kind(spec, kind, controller_id);
    assert forall |s, s_prime: ClusterState| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: Message| {
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.dst is APIServer
        } implies match msg.src {
            HostId::Controller(id, key) => key.kind == kind,
            _ => false,
        } by {
            if s.in_flight().contains(msg) {} else {}
        }
    }
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id)),
        lift_state(Self::objects_in_reconcile_have_kind(kind, controller_id))
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

// ---------------------------------------------------------------------------
// The desired state of an object of the shape, and the object a reconcile runs on.
// ---------------------------------------------------------------------------

pub open spec fn synced_desired_state_is(cr: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& cr.metadata.name is Some
        &&& cr.metadata.namespace is Some
        &&& s.resources().contains_key(cr.object_ref())
        &&& s.resources()[cr.object_ref()].metadata.uid == cr.metadata.uid
        &&& s.resources()[cr.object_ref()].metadata.deletion_timestamp is None
        &&& unmarshal(cr.kind, s.resources()[cr.object_ref()]) is Ok
        &&& unmarshal(cr.kind, s.resources()[cr.object_ref()])->Ok_0.spec == cr.spec
    }
}

pub open spec fn the_synced_object_in_schedule_is(controller_id: int, cr: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| s.scheduled_reconciles(controller_id).contains_key(cr.object_ref())
        ==> s.scheduled_reconciles(controller_id)[cr.object_ref()].metadata.uid == cr.metadata.uid
        && unmarshal(cr.kind, s.scheduled_reconciles(controller_id)[cr.object_ref()]) is Ok
        && unmarshal(cr.kind, s.scheduled_reconciles(controller_id)[cr.object_ref()])->Ok_0.spec == cr.spec
}

pub proof fn lemma_true_leads_to_always_the_synced_object_in_schedule_is(
    self, spec: TempPred<ClusterState>, controller_id: int, cr: SyncedObjectView
)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::synced_desired_state_is(cr)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::the_synced_object_in_schedule_is(controller_id, cr))))),
{
    let stronger_pre = Self::synced_desired_state_is(cr);
    let post = Self::the_synced_object_in_schedule_is(controller_id, cr);
    let input = cr.object_ref();
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::synced_desired_state_is(cr)(s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    always_to_always_later(spec, lift_state(Self::synced_desired_state_is(cr)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        later(lift_state(Self::synced_desired_state_is(cr))),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    self.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, input, stronger_next, stronger_pre, post);
    temp_pred_equality(true_pred().and(lift_state(Self::synced_desired_state_is(cr))), lift_state(stronger_pre));
    leads_to_by_borrowing_inv(spec, true_pred(), lift_state(post), lift_state(Self::synced_desired_state_is(cr)));
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(post));
}

pub open spec fn the_synced_object_in_reconcile_is(controller_id: int, cr: SyncedObjectView) -> StatePred<ClusterState> {
    |s: ClusterState| s.ongoing_reconciles(controller_id).contains_key(cr.object_ref())
        ==> s.ongoing_reconciles(controller_id)[cr.object_ref()].triggering_cr.metadata.uid == cr.metadata.uid
        && unmarshal(cr.kind, s.ongoing_reconciles(controller_id)[cr.object_ref()].triggering_cr) is Ok
        && unmarshal(cr.kind, s.ongoing_reconciles(controller_id)[cr.object_ref()].triggering_cr)->Ok_0.spec == cr.spec
}

pub proof fn lemma_true_leads_to_always_the_synced_object_in_reconcile_is(
    self, spec: TempPred<ClusterState>, controller_id: int, cr: SyncedObjectView
)
    requires
        self.controller_models.contains_key(controller_id),
        self.reconcile_model(controller_id).kind == cr.kind,
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i: (Option<Message>, Option<ObjectRef>)| self.controller_next().weak_fairness((controller_id, i.0, i.1)))),
        spec.entails(tla_forall(|i| self.schedule_controller_reconcile().weak_fairness((controller_id, i)))),
        spec.entails(always(lift_state(Self::synced_desired_state_is(cr)))),
        spec.entails(always(lift_state(Self::the_synced_object_in_schedule_is(controller_id, cr)))),
        spec.entails(always(lift_state(Self::there_is_the_controller_state(controller_id)))),
        spec.entails(true_pred().leads_to(lift_state(Self::reconcile_idle(controller_id, cr.object_ref())))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::the_synced_object_in_reconcile_is(controller_id, cr))))),
{
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::the_synced_object_in_schedule_is(controller_id, cr)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::the_synced_object_in_schedule_is(controller_id, cr)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    let not_scheduled_or_reconcile = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(cr.object_ref())
        &&& !s.scheduled_reconciles(controller_id).contains_key(cr.object_ref())
    };
    let scheduled_and_not_reconcile = |s: ClusterState| {
        &&& !s.ongoing_reconciles(controller_id).contains_key(cr.object_ref())
        &&& s.scheduled_reconciles(controller_id).contains_key(cr.object_ref())
    };
    assert_by(spec.entails(lift_state(not_scheduled_or_reconcile).leads_to(lift_state(scheduled_and_not_reconcile))), {
        let input = cr.object_ref();
        let pre = not_scheduled_or_reconcile;
        let post = scheduled_and_not_reconcile;
        let stronger_pre = |s| {
            &&& pre(s)
            &&& Self::synced_desired_state_is(cr)(s)
        };
        let even_stronger_next = |s, s_prime| {
            &&& stronger_next(s, s_prime)
            &&& Self::synced_desired_state_is(cr)(s_prime)
        };
        always_to_always_later(spec, lift_state(Self::synced_desired_state_is(cr)));
        combine_spec_entails_always_n!(
            spec, lift_action(even_stronger_next),
            lift_action(stronger_next),
            later(lift_state(Self::synced_desired_state_is(cr)))
        );
        self.lemma_pre_leads_to_post_by_schedule_controller_reconcile(spec, controller_id, input, even_stronger_next, stronger_pre, post);
        temp_pred_equality(lift_state(pre).and(lift_state(Self::synced_desired_state_is(cr))), lift_state(stronger_pre));
        leads_to_by_borrowing_inv(spec, lift_state(pre), lift_state(post), lift_state(Self::synced_desired_state_is(cr)));
    });
    assert_by(spec.entails(lift_state(scheduled_and_not_reconcile).leads_to(lift_state(Self::the_synced_object_in_reconcile_is(controller_id, cr)))), {
        let post = Self::the_synced_object_in_reconcile_is(controller_id, cr);
        let input = (None, Some(cr.object_ref()));
        self.lemma_pre_leads_to_post_by_controller(spec, controller_id, input, stronger_next, ControllerStep::RunScheduledReconcile, scheduled_and_not_reconcile, post);
    });
    leads_to_trans(spec, lift_state(not_scheduled_or_reconcile), lift_state(scheduled_and_not_reconcile), lift_state(Self::the_synced_object_in_reconcile_is(controller_id, cr)));
    let not_reconcile = Self::reconcile_idle(controller_id, cr.object_ref());
    or_leads_to_combine_and_equality!(
        spec, lift_state(not_reconcile), lift_state(scheduled_and_not_reconcile), lift_state(not_scheduled_or_reconcile);
        lift_state(Self::the_synced_object_in_reconcile_is(controller_id, cr))
    );
    leads_to_trans(
        spec, true_pred(), lift_state(Self::reconcile_idle(controller_id, cr.object_ref())),
        lift_state(Self::the_synced_object_in_reconcile_is(controller_id, cr))
    );
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(Self::the_synced_object_in_reconcile_is(controller_id, cr)));
}

}

}
