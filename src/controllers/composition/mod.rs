pub mod vreplicaset_reconciler;
pub mod vdeployment_reconciler;
pub mod vstatefulset_reconciler;
pub mod rabbitmq_reconciler;
pub mod compose_all;
pub mod widget_disturber_reconciler;
pub mod widget_janitor_reconciler;
pub mod widget_sync_reconciler;

// Turn composition into a Verus module
use vstd::prelude::*;


verus! { spec fn trivial() ->bool {true} } // makes verus recognize this as a mod
