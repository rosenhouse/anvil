// The liveness proofs of the Widget pair, against the one-store cluster model.
//
// spec.rs             what the property proofs share: assumptions, invariants,
//                     stable specs, phase I, the sync reconciler's layers
// api_actions.rs      what one step of the cluster does at the watched keys
// terminate.rs        every reconcile of either reconciler terminates
// sync_spec_proof.rs  R1, the mirror carries the outer spec
// sync_status_proof.rs R2, the outer copy carries the mirrored status
// janitor_proof.rs    R3, a mirror whose parent is gone is removed
// cleanup_proof.rs    R3s, and none pointing at that parent comes back
pub mod api_actions;
pub mod cleanup_proof;
pub mod janitor_proof;
pub mod spec;
pub mod sync_spec_proof;
pub mod sync_status_proof;
pub mod terminate;
