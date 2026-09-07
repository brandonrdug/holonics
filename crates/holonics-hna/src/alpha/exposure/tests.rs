use super::*;
use serde_json::{json, Value};
use std::fs;

fn manifest() -> Value {
    json!({
        "schema": EXPOSURE_SCHEMA, "kind":"manifest",
        "temporal_cut":"2026-09-04T00:00:00Z",
        "temporal_cut_normalized":"2026-09-04T00:00:00.000000+00:00",
        "private_sources":[{"source":1,"provider":"codex","private_path":"private/source.jsonl",
            "captured_octets":10000,"records":100}],
        "visible_parts":{"human":["human-text"],"agent":["agent-text"]},
        "boundary":{}
    })
}

fn occurrence(sequence: u64, id: &str, role: &str, text: &str) -> Value {
    let kind = if role == "human" {
        "human-text"
    } else {
        "agent-text"
    };
    json!({
        "schema":EXPOSURE_SCHEMA,"kind":"occurrence-family","sequence":sequence,
        "position":{"first_source":1,"first_record":sequence+1,"first_event":sequence+1},
        "conflicts":[],
        "family":{"provider":"codex","record_group":format!("declared:{id}")},
        "partition":"development","partition_reasons":[],
        "views":[{"event":sequence+1,"source":1,"provider":"codex",
            "record":{"number":sequence+1,"byte_start":sequence*100,"byte_end":(sequence+1)*100},
            "timestamp":"2026-09-03T00:00:00Z",
            "normalized_timestamp":"2026-09-03T00:00:00.000000+00:00",
            "native_id":id,"parent_id":null,"session_id":"session","branch_id":null,
            "workspace":null,"phase":null,"turn_id":null,"model":null,
            "author_class":role,"record_kind":"message","flags":[],"provider_metadata":{},"previous_record":null,
            "visible_parts":[{"ordinal":0,"pointer":"/payload/content/0/text","kind":kind,"text":text}],
            "nonvisible_part_references":[],"links":[]
        }]
    })
}

fn write_stream(root: &Path, frames: &[Value]) -> std::path::PathBuf {
    let path = root.join("exposure.jsonl");
    let mut bytes = serde_json::to_vec(&manifest()).unwrap();
    bytes.push(b'\n');
    for frame in frames {
        bytes.extend(serde_json::to_vec(frame).unwrap());
        bytes.push(b'\n');
    }
    fs::write(&path, bytes).unwrap();
    path
}

#[test]
fn actual_response_is_a_later_frame_and_pending_delivery_survives_reopen() {
    let root = tempfile::tempdir().unwrap();
    let path = write_stream(
        root.path(),
        &[
            occurrence(0, "request", "human", "Explain the relation"),
            occurrence(1, "response", "agent-visible", "An observed answer"),
        ],
    );
    let mut reader = ExposureReader::open(&path).unwrap();
    let initial = reader.cursor();
    let request = reader.peek().unwrap().unwrap();
    assert_eq!(
        request.development_parts().unwrap()[0].text.as_deref(),
        Some("Explain the relation")
    );
    assert!(!serde_json::to_string(request)
        .unwrap()
        .contains("An observed answer"));
    assert_eq!(reader.cursor(), initial);
    assert!(reader.acknowledge(1).is_err());
    drop(reader);
    let mut resumed = ExposureReader::resume(initial).unwrap();
    assert_eq!(resumed.peek().unwrap().unwrap().sequence, 0);
    resumed.acknowledge(0).unwrap();
    let after_request = resumed.cursor();
    drop(resumed);
    let mut resumed = ExposureReader::resume(after_request).unwrap();
    assert_eq!(
        resumed
            .peek()
            .unwrap()
            .unwrap()
            .development_parts()
            .unwrap()[0]
            .text
            .as_deref(),
        Some("An observed answer")
    );
    resumed.acknowledge(1).unwrap();
    assert!(resumed.peek().unwrap().is_none());
}

#[test]
fn future_and_unknown_times_cannot_be_declared_development() {
    for time in [
        Some("2026-09-04T00:00:00.000000+00:00"),
        Some("2026-09-05T00:00:00.000000+00:00"),
        None,
    ] {
        let root = tempfile::tempdir().unwrap();
        let mut frame = occurrence(0, "u", "human", "material");
        frame["views"][0]["normalized_timestamp"] = json!(time);
        let path = write_stream(root.path(), &[frame]);
        let mut reader = ExposureReader::open(path).unwrap();
        let cursor = reader.cursor();
        assert!(reader.peek().is_err());
        assert_eq!(reader.cursor(), cursor);
        assert!(reader.peek().is_err()); // refusal does not skip into another record
    }
}

#[test]
fn deferred_conflicting_views_remain_plural_and_cannot_be_selected_as_training() {
    let root = tempfile::tempdir().unwrap();
    let mut frame = occurrence(0, "shared", "human", "one captured reading");
    let mut other = frame["views"][0].clone();
    other["event"] = json!(9);
    other["record"]["number"] = json!(9);
    other["visible_parts"][0]["text"] = json!("a conflicting captured reading");
    frame["views"].as_array_mut().unwrap().push(other);
    frame["partition"] = json!("deferred");
    frame["partition_reasons"] = json!(["conflicting-presentations"]);
    let path = write_stream(root.path(), &[frame]);
    let mut reader = ExposureReader::open(path).unwrap();
    let frame = reader.peek().unwrap().unwrap();
    assert_eq!(frame.views.len(), 2);
    assert!(frame.shared_visible_parts().is_err());
    assert!(frame.development_parts().is_err());
}

#[test]
fn repeated_words_in_distinct_occurrences_do_not_merge() {
    let root = tempfile::tempdir().unwrap();
    let path = write_stream(
        root.path(),
        &[
            occurrence(0, "a", "human", "same"),
            occurrence(1, "b", "human", "same"),
        ],
    );
    let mut reader = ExposureReader::open(path).unwrap();
    let first = reader.peek().unwrap().unwrap().family.clone();
    reader.acknowledge(0).unwrap();
    let second = &reader.peek().unwrap().unwrap().family;
    assert_ne!(&first, second);
}

#[test]
fn hidden_material_and_future_target_text_do_not_fit_the_wire() {
    let root = tempfile::tempdir().unwrap();
    let mut frame = occurrence(0, "u", "human", "visible");
    frame["views"][0]["visible_parts"][0]["kind"] = json!("reasoning");
    let path = write_stream(root.path(), &[frame]);
    assert!(ExposureReader::open(path).unwrap().peek().is_err());
    let mut frame = occurrence(0, "u", "human", "visible");
    frame["views"][0]["links"] = json!([{
        "kind":"provider-parent","target_event":2,"reference":"later","evidence":"declared",
        "availability":"not-prior","target":{"event":2,"source":1,"provider":"codex",
            "record_group":"declared:later","timestamp":null,"normalized_timestamp":null,
            "text":"a future answer must not be embedded here"}}]);
    let path = write_stream(root.path(), &[frame]);
    assert!(ExposureReader::open(path).unwrap().peek().is_err());
}

#[test]
fn an_immutable_source_pin_refuses_changed_data_on_resume() {
    let root = tempfile::tempdir().unwrap();
    let path = write_stream(root.path(), &[occurrence(0, "u", "human", "first")]);
    let reader = ExposureReader::open(&path).unwrap();
    let cursor = reader.cursor();
    drop(reader);
    write_stream(root.path(), &[occurrence(0, "u", "human", "other")]);
    assert!(matches!(
        ExposureReader::resume(cursor),
        Err(ExposureError::Source(_))
    ));
}

#[test]
fn incomplete_or_reordered_frames_do_not_advance_a_saved_cursor() {
    let root = tempfile::tempdir().unwrap();
    let path = write_stream(
        root.path(),
        &[occurrence(1, "u", "human", "wrong sequence")],
    );
    let mut reader = ExposureReader::open(&path).unwrap();
    let cursor = reader.cursor();
    assert!(reader.peek().is_err());
    assert_eq!(reader.cursor(), cursor);
    let path = write_stream(root.path(), &[occurrence(0, "u", "human", "incomplete")]);
    let mut bytes = fs::read(&path).unwrap();
    bytes.pop();
    fs::write(&path, bytes).unwrap();
    let mut reader = ExposureReader::open(&path).unwrap();
    let cursor = reader.cursor();
    assert!(reader.peek().is_err());
    assert_eq!(reader.cursor(), cursor);
}

#[test]
fn normalized_clock_validates_calendar_and_utc_chart() {
    assert!(normalized_time("2024-02-29T23:59:59.123456+00:00"));
    assert!(normalized_time("2000-02-29T00:00:00.000000+00:00"));
    assert!(!normalized_time("1900-02-29T00:00:00.000000+00:00"));
    assert!(!normalized_time("2026-09-03T00:00:00.000000-07:00"));
    assert!(!normalized_time("2026-09-03T24:00:00.000000+00:00"));
}

#[test]
fn reference_availability_and_source_metadata_are_recomputed() {
    let manifest: ExposureManifest = serde_json::from_value(manifest()).unwrap();
    let mut wire = occurrence(0, "u", "human", "material");
    wire["views"][0]["links"] = json!([{
        "kind":"provider-parent","target_event":2,"reference":"parent","evidence":"declared",
        "availability":"prior","target":{"event":2,"source":1,"provider":"codex",
            "record_group":"declared:parent","timestamp":"2026-09-02T00:00:00Z",
            "normalized_timestamp":"2026-09-02T00:00:00.000000+00:00"}}]);
    let mut frame: ExposureOccurrence = serde_json::from_value(wire).unwrap();
    frame.validate(&manifest).unwrap();
    frame.views[0].links[0].availability = ExposureAvailability::NotPrior;
    assert!(frame.validate(&manifest).is_err());
    frame.views[0].links[0].availability = ExposureAvailability::Prior;
    frame.views[0].links[0].target.as_mut().unwrap().provider = "another-source".into();
    assert!(frame.validate(&manifest).is_err());
    frame.views[0].links[0].target.as_mut().unwrap().provider = "codex".into();
    frame.views[0].links[0].kind = "parent-candidate".into();
    assert!(frame.validate(&manifest).is_err());
    frame.views[0].links[0].availability = ExposureAvailability::Ambiguous;
    frame.validate(&manifest).unwrap();
}

#[test]
fn shared_parent_keeps_common_evidence_and_refuses_a_link_order_choice() {
    let mut frame: ExposureOccurrence =
        serde_json::from_value(occurrence(3, "reply", "agent-visible", "response")).unwrap();
    assert_eq!(frame.shared_prior_parent().unwrap(), None);
    let target = ExposureTarget {
        event: 1,
        source: 1,
        provider: "codex".into(),
        record_group: "declared:request".into(),
        timestamp: None,
        normalized_timestamp: None,
    };
    let link = ExposureLink {
        kind: "comparison-request".into(),
        target_event: Some(1),
        reference: None,
        evidence: "captured".into(),
        target: Some(target),
        availability: ExposureAvailability::Prior,
    };
    frame.views[0].links = vec![link.clone(), link.clone()];
    frame.views.push(frame.views[0].clone());
    assert_eq!(
        frame.shared_prior_parent().unwrap().unwrap().record_group,
        "declared:request"
    );
    frame.views[1].links.clear();
    assert!(frame.shared_prior_parent().is_err());
    frame.views.pop();
    let mut other = link.clone();
    other.target.as_mut().unwrap().record_group = "declared:different".into();
    for links in [vec![link.clone(), other.clone()], vec![other, link.clone()]] {
        frame.views[0].links = links;
        assert!(frame.shared_prior_parent().is_err());
    }
    for unavailable in [
        ExposureAvailability::NotPrior,
        ExposureAvailability::Ambiguous,
        ExposureAvailability::Unresolved,
    ] {
        frame.views[0].links = vec![ExposureLink {
            availability: unavailable,
            ..link.clone()
        }];
        assert!(frame.shared_prior_parent().is_err());
    }
}
