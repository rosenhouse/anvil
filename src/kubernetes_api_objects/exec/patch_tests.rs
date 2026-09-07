use crate::kubernetes_api_objects::exec::{object_meta::*, resource::*};
use crate::kubernetes_api_objects::spec::patch_tests::*;
use vstd::prelude::*;

verus! {

// PatchTests is the exec counterpart of PatchTestsView: the `test` operations a
// JSON patch carries. Values are copied from an ObjectMeta, never read by the
// controller as values, which keeps the exec/model correspondence the same as for
// Preconditions (the rv and uid there are opaque tokens compared for equality).

#[verifier(external_body)]
pub struct PatchTests {
    uid: Option<std::string::String>,
    generation: Option<i64>,
}

implement_view_trait!(PatchTests, PatchTestsView);
implement_deep_view_trait!(PatchTests, PatchTestsView);

impl PatchTests {
    #[verifier(external_body)]
    pub fn default() -> (tests: PatchTests)
        ensures tests@ == PatchTestsView::default(),
    {
        PatchTests { uid: None, generation: None }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (tests: PatchTests)
        ensures tests@ == self@,
    {
        PatchTests { uid: self.uid.clone(), generation: self.generation }
    }

    #[verifier(external_body)]
    pub fn set_uid_from_object_meta(&mut self, object_meta: ObjectMeta)
        ensures final(self)@ == old(self)@.with_uid_from_object_meta(object_meta@),
    {
        self.uid = object_meta.into_kube().uid;
    }

    #[verifier(external_body)]
    pub fn set_generation_from_object_meta(&mut self, object_meta: ObjectMeta)
        ensures final(self)@ == old(self)@.with_generation_from_object_meta(object_meta@),
    {
        self.generation = object_meta.into_kube().generation;
    }
}

// Read accessors for the shim layer, which turns the tests into JSON patch
// operations. Not for controller code.
#[verifier(external)]
impl PatchTests {
    pub fn uid_value(&self) -> Option<std::string::String> {
        self.uid.clone()
    }

    pub fn generation_value(&self) -> Option<i64> {
        self.generation
    }
}

}
