use vstd::prelude::*;

verus! {

// Steps of the sync reconciler, which reconciles the outer copy of a Widget.
pub enum WidgetSyncStep {
    Init,
    // After the Update of the outer copy that adds or removes the sync finalizer.
    AfterAddFinalizer,
    AfterRemoveFinalizer,
    AfterGetInner,
    AfterCreateInner,
    AfterPatchInner,
    // Teardown of a terminating outer copy: the List that reads the mirror key,
    // the Get of the mirror it lists, and the Delete of the mirror.
    AfterListMirror,
    AfterGetMirror,
    AfterDeleteMirror,
    AfterPatchOuterStatus,
    // After the status write that reports a failed request; ends in Error.
    AfterReportError,
    Done,
    Error,
}

impl std::marker::Copy for WidgetSyncStep {}

impl std::clone::Clone for WidgetSyncStep {
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

impl View for WidgetSyncStep {
    type V = WidgetSyncStepView;

    open spec fn view(&self) -> WidgetSyncStepView {
        match self {
            WidgetSyncStep::Init => WidgetSyncStepView::Init,
            WidgetSyncStep::AfterAddFinalizer => WidgetSyncStepView::AfterAddFinalizer,
            WidgetSyncStep::AfterRemoveFinalizer => WidgetSyncStepView::AfterRemoveFinalizer,
            WidgetSyncStep::AfterGetInner => WidgetSyncStepView::AfterGetInner,
            WidgetSyncStep::AfterCreateInner => WidgetSyncStepView::AfterCreateInner,
            WidgetSyncStep::AfterPatchInner => WidgetSyncStepView::AfterPatchInner,
            WidgetSyncStep::AfterListMirror => WidgetSyncStepView::AfterListMirror,
            WidgetSyncStep::AfterGetMirror => WidgetSyncStepView::AfterGetMirror,
            WidgetSyncStep::AfterDeleteMirror => WidgetSyncStepView::AfterDeleteMirror,
            WidgetSyncStep::AfterPatchOuterStatus => WidgetSyncStepView::AfterPatchOuterStatus,
            WidgetSyncStep::AfterReportError => WidgetSyncStepView::AfterReportError,
            WidgetSyncStep::Done => WidgetSyncStepView::Done,
            WidgetSyncStep::Error => WidgetSyncStepView::Error,
        }
    }
}

pub enum WidgetSyncStepView {
    Init,
    AfterAddFinalizer,
    AfterRemoveFinalizer,
    AfterGetInner,
    AfterCreateInner,
    AfterPatchInner,
    AfterListMirror,
    AfterGetMirror,
    AfterDeleteMirror,
    AfterPatchOuterStatus,
    AfterReportError,
    Done,
    Error,
}

// Steps of the janitor reconciler, which reconciles the inner copy (the mirror).
pub enum WidgetJanitorStep {
    Init,
    AfterListOuter,
    AfterDeleteInner,
    Done,
    Error,
}

impl std::marker::Copy for WidgetJanitorStep {}

impl std::clone::Clone for WidgetJanitorStep {
    fn clone(&self) -> (result: Self)
        ensures result == self
    { *self }
}

impl View for WidgetJanitorStep {
    type V = WidgetJanitorStepView;

    open spec fn view(&self) -> WidgetJanitorStepView {
        match self {
            WidgetJanitorStep::Init => WidgetJanitorStepView::Init,
            WidgetJanitorStep::AfterListOuter => WidgetJanitorStepView::AfterListOuter,
            WidgetJanitorStep::AfterDeleteInner => WidgetJanitorStepView::AfterDeleteInner,
            WidgetJanitorStep::Done => WidgetJanitorStepView::Done,
            WidgetJanitorStep::Error => WidgetJanitorStepView::Error,
        }
    }
}

pub enum WidgetJanitorStepView {
    Init,
    AfterListOuter,
    AfterDeleteInner,
    Done,
    Error,
}

}
