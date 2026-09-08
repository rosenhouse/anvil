pub mod vreplicaset_reconciler;
pub mod vdeployment_reconciler;
pub mod vstatefulset_reconciler;
pub mod rabbitmq_reconciler;
// PORT-DISABLED pub mod compose_all;
// PORT-DISABLED pub mod widget_disturber_reconciler;
// PORT-DISABLED pub mod widget_janitor_reconciler;
// PORT-DISABLED pub mod widget_sync_reconciler;

// Turn composition into a Verus module
use vstd::prelude::*;


verus! { spec fn trivial() ->bool {true} } // makes verus recognize this as a mod
