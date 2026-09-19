// exec_types::outer_status_for is external_body: its postcondition names
// spec_types::outer_status_for, and nothing verified checks the body against
// it. These tests pin the body to the spec, case by case, over the JSON the
// status is written as.
//
// The table of not-synced outcomes is the one deploy/widget_sync/README.md
// prints under "What to look at".
use crate::kubernetes_api_objects::exec::synced_object::*;
use crate::widget_sync_controller::trusted::exec_types::*;
use serde_json::{json, Value};

fn status(json: Value) -> Option<SyncedStatus> {
    SyncedStatus::parse(Some(&json)).unwrap()
}

fn written(generation: Option<i64>, source: Option<Value>, outcome: SyncOutcome) -> Value {
    let source = source.and_then(status);
    outer_status_for(generation, &source, &outcome).as_json().clone()
}

fn condition<'a>(status: &'a Value, type_: &str) -> &'a Value {
    status["conditions"].as_array().unwrap().iter().find(|c| c["type"] == type_).unwrap()
}

// A condition as the controller writes it: no lastTransitionTime, and absent
// reason and message left out rather than null.
fn cond(type_: &str, status: &str, generation: i64, reason: Option<&str>, message: Option<&str>) -> Value {
    let mut c = json!({ "type": type_, "status": status, "observedGeneration": generation });
    if let Some(r) = reason {
        c["reason"] = json!(r);
    }
    if let Some(m) = message {
        c["message"] = json!(m);
    }
    c
}

// Every not-synced outcome, with what the README table says of it: Synced's
// reason, whether Stalled is True, and Ready's status.
fn not_synced_outcomes() -> Vec<(SyncOutcome, &'static str, bool, &'static str)> {
    vec![
        (SyncOutcome::InnerConverging, "InnerConverging", false, "Unknown"),
        (SyncOutcome::InnerTerminating, "InnerTerminating", false, "Unknown"),
        (SyncOutcome::StaleMirror, "StaleMirror", false, "False"),
        (SyncOutcome::ForeignObject, "ForeignObject", true, "False"),
        (SyncOutcome::Failed(FailureReason::Forbidden), "Forbidden", true, "Unknown"),
        (SyncOutcome::Failed(FailureReason::InnerUnreachable), "InnerUnreachable", false, "Unknown"),
        (SyncOutcome::Failed(FailureReason::CreateFailed), "CreateFailed", false, "False"),
        (SyncOutcome::Failed(FailureReason::Rejected), "Rejected", true, "False"),
        (SyncOutcome::Failed(FailureReason::RequestFailed), "RequestFailed", false, "Unknown"),
    ]
}

#[test]
fn synced_copies_the_inner_ready_and_stalled_verbatim() {
    let inner = json!({
        "observedGeneration": 7,
        "conditions": [
            { "type": "Ready", "status": "False", "reason": "Pulling", "message": "image pull in progress", "observedGeneration": 7 },
            { "type": "Stalled", "status": "False", "reason": "Progressing", "observedGeneration": 7 },
        ],
        "observedCount": 3,
    });
    assert_eq!(
        written(Some(4), Some(inner), SyncOutcome::Synced),
        json!({
            "observedGeneration": 4,
            "conditions": [
                cond("Synced", "True", 4, Some("Synced"), None),
                cond("Ready", "False", 4, Some("Pulling"), Some("image pull in progress")),
                cond("Stalled", "False", 4, Some("Progressing"), None),
            ],
            "observedCount": 3,
        })
    );
}

#[test]
fn synced_passes_an_unknown_ready_and_stalled_through() {
    let inner = json!({
        "conditions": [
            { "type": "Ready", "status": "Unknown", "reason": "Probing", "message": "no probe result yet" },
            { "type": "Stalled", "status": "Unknown", "reason": "NoDeadline" },
        ],
    });
    let outer = written(Some(2), Some(inner), SyncOutcome::Synced);
    assert_eq!(condition(&outer, "Ready"), &cond("Ready", "Unknown", 2, Some("Probing"), Some("no probe result yet")));
    assert_eq!(condition(&outer, "Stalled"), &cond("Stalled", "Unknown", 2, Some("NoDeadline"), None));
}

#[test]
fn synced_with_no_inner_ready_condition_reads_ready_unknown() {
    let outer = written(Some(2), Some(json!({ "conditions": [] })), SyncOutcome::Synced);
    assert_eq!(condition(&outer, "Ready"), &cond("Ready", "Unknown", 2, Some("NoInnerReadyCondition"), None));
    assert_eq!(condition(&outer, "Stalled"), &cond("Stalled", "False", 2, Some("Synced"), None));
    // The same with no conditions list at all.
    let outer = written(Some(2), Some(json!({ "observedCount": 1 })), SyncOutcome::Synced);
    assert_eq!(condition(&outer, "Ready"), &cond("Ready", "Unknown", 2, Some("NoInnerReadyCondition"), None));
    assert_eq!(condition(&outer, "Stalled"), &cond("Stalled", "False", 2, Some("Synced"), None));
}

#[test]
fn an_inner_stalled_true_forces_ready_false_with_its_text() {
    let inner = json!({
        "conditions": [
            { "type": "Ready", "status": "True", "reason": "Running" },
            { "type": "Stalled", "status": "True", "reason": "QuotaExceeded", "message": "no room" },
        ],
    });
    let outer = written(Some(3), Some(inner), SyncOutcome::Synced);
    assert_eq!(condition(&outer, "Ready"), &cond("Ready", "False", 3, Some("QuotaExceeded"), Some("no room")));
    assert_eq!(condition(&outer, "Stalled"), &cond("Stalled", "True", 3, Some("QuotaExceeded"), Some("no room")));
}

#[test]
fn an_inner_status_that_is_none_of_the_three_reads_unknown() {
    let inner = json!({
        "conditions": [
            { "type": "Ready", "status": "Maybe", "reason": "Odd" },
            { "type": "Stalled", "status": "true", "reason": "Lowercase" },
        ],
    });
    let outer = written(Some(1), Some(inner), SyncOutcome::Synced);
    assert_eq!(condition(&outer, "Ready"), &cond("Ready", "Unknown", 1, Some("Odd"), None));
    assert_eq!(condition(&outer, "Stalled"), &cond("Stalled", "Unknown", 1, Some("Lowercase"), None));
}

#[test]
fn the_first_inner_condition_of_a_type_is_the_one_read() {
    let inner = json!({
        "conditions": [
            { "type": "Ready", "status": "True", "reason": "First" },
            { "type": "Ready", "status": "False", "reason": "Second" },
        ],
    });
    let outer = written(Some(1), Some(inner), SyncOutcome::Synced);
    assert_eq!(condition(&outer, "Ready"), &cond("Ready", "True", 1, Some("First"), None));
}

#[test]
fn not_synced_reports_the_readme_table() {
    let previous = json!({
        "observedGeneration": 1,
        "conditions": [
            cond("Synced", "True", 1, Some("Synced"), None),
            cond("Ready", "True", 1, Some("Echoed"), None),
            cond("Stalled", "False", 1, Some("Synced"), None),
        ],
        "observedCount": 3,
    });
    for (outcome, reason, stalled, ready) in not_synced_outcomes() {
        let outer = written(Some(2), Some(previous.clone()), outcome);
        assert_eq!(
            outer,
            json!({
                "observedGeneration": 2,
                "conditions": [
                    cond("Synced", "False", 2, Some(reason), None),
                    cond("Ready", ready, 2, Some("NotSynced"), None),
                    cond("Stalled", if stalled { "True" } else { "False" }, 2, Some(reason), None),
                ],
                // The mirrored remainder is kept as last reported.
                "observedCount": 3,
            }),
            "{}",
            reason
        );
    }
}

#[test]
fn a_status_never_written_has_the_empty_remainder() {
    assert_eq!(
        written(Some(1), None, SyncOutcome::Failed(FailureReason::InnerUnreachable)),
        json!({
            "observedGeneration": 1,
            "conditions": [
                cond("Synced", "False", 1, Some("InnerUnreachable"), None),
                cond("Ready", "Unknown", 1, Some("NotSynced"), None),
                cond("Stalled", "False", 1, Some("InnerUnreachable"), None),
            ],
        })
    );
}

#[test]
fn an_absent_generation_is_stamped_absent() {
    let outer = written(None, None, SyncOutcome::Synced);
    assert_eq!(outer["observedGeneration"], Value::Null);
    for c in outer["conditions"].as_array().unwrap() {
        assert_eq!(c["observedGeneration"], Value::Null);
    }
}
