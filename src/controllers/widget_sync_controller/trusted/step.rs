use vstd::prelude::*;

verus! {

// Steps of the sync reconciler, which reconciles the outer copy of a Widget.
pub enum WidgetSyncStep {
    Init,
    AfterGetInner,
    AfterCreateInner,
    AfterPatchInner,
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
            WidgetSyncStep::AfterGetInner => WidgetSyncStepView::AfterGetInner,
            WidgetSyncStep::AfterCreateInner => WidgetSyncStepView::AfterCreateInner,
            WidgetSyncStep::AfterPatchInner => WidgetSyncStepView::AfterPatchInner,
            WidgetSyncStep::AfterPatchOuterStatus => WidgetSyncStepView::AfterPatchOuterStatus,
            WidgetSyncStep::AfterReportError => WidgetSyncStepView::AfterReportError,
            WidgetSyncStep::Done => WidgetSyncStepView::Done,
            WidgetSyncStep::Error => WidgetSyncStepView::Error,
        }
    }
}

pub enum WidgetSyncStepView {
    Init,
    AfterGetInner,
    AfterCreateInner,
    AfterPatchInner,
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
