use crate::kubernetes_api_objects::spec::{
    common::{Generation, Uid},
    dynamic::*,
    object_meta::*,
};
use vstd::prelude::*;

verus! {

// PatchTestsView models the `test` operations of a JSON patch that pin the object a
// patch may apply to.
//
// A patch carries no resourceVersion: the API server applies it to the latest
// version of the object, so writers of other fields (status, labels, annotations,
// finalizers) do not make it fail. What a patch sender usually wants to pin is
// the *spec* it read, and metadata.generation changes exactly when the spec does,
// so testing generation is the optimistic-concurrency token for spec-level
// decisions. Testing metadata.uid pins the incarnation of the object (a stale
// patch must not land on a same-named object created later).
pub struct PatchTestsView {
    pub uid: Option<Uid>,
    pub generation: Option<Generation>,
}

impl PatchTestsView {
    pub open spec fn default() -> PatchTestsView {
        PatchTestsView {
            uid: None,
            generation: None,
        }
    }

    pub open spec fn with_uid_from_object_meta(self, object_meta: ObjectMetaView) -> PatchTestsView {
        PatchTestsView {
            uid: object_meta.uid,
            ..self
        }
    }

    pub open spec fn with_generation_from_object_meta(self, object_meta: ObjectMetaView) -> PatchTestsView {
        PatchTestsView {
            generation: object_meta.generation,
            ..self
        }
    }

    // pass holds iff every test present agrees with the stored object.
    pub open spec fn pass(self, obj: DynamicObjectView) -> bool {
        &&& self.uid is Some ==> self.uid == obj.metadata.uid
        &&& self.generation is Some ==> self.generation == obj.metadata.generation
    }
}

}
