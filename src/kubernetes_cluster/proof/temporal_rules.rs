// Rules of temporal logic that verus_temporal_logic does not provide. They are
// generic over the state type and belong in that crate; it is an external
// dependency, so they live here until they are upstreamed.
use verus_temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

// spec |= p /\ q gives spec |= p and spec |= q.
pub proof fn entails_and_split<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires spec.entails(p.and(q)),
    ensures spec.entails(p), spec.entails(q),
{
    assert(p.and(q).entails(p));
    assert(p.and(q).entails(q));
    entails_trans(spec, p.and(q), p);
    entails_trans(spec, p.and(q), q);
}

// From spec |= []p derive spec |= true ~> p.
pub proof fn always_to_true_leads_to<T>(spec: TempPred<T>, p: TempPred<T>)
    requires spec.entails(always(p)),
    ensures spec.entails(true_pred().leads_to(p)),
{
    temp_pred_equality(true_pred::<T>().implies(p), p);
    always_implies_to_leads_to(spec, true_pred(), p);
}

}
