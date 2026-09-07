//! Cold reader for the exact AMI response-link index.
//!
//! This module retains corpus annotation and clock lineage only.  It does not turn speaker
//! labels, temporal proximity, or annotation types into native currents or contacts.

use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::{One, Signed, ToPrimitive};
use serde_json::{Map, Value};
use std::fs;
use std::path::Path;
use thiserror::Error;

mod sections;
pub use sections::{RecordedResponseSections, RecordedSectionError};

#[derive(Debug, Error)]
pub enum RecordedResponseLinkError {
    #[error("recorded response-link I/O: {0}")]
    Io(#[from] std::io::Error),
    #[error("recorded response-link JSON on line {line}: {source}")]
    JsonLine {
        line: usize,
        #[source]
        source: serde_json::Error,
    },
    #[error("recorded response-link line {line} is not a JSON object")]
    NotObject { line: usize },
}

/// An exact non-negative annotation interval.  The original decimal spellings remain beside
/// their reduced rational values so the source clock can be audited without floating point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedInterval {
    pub begin_decimal: String,
    pub end_decimal: String,
    pub begin: Rat,
    pub end: Rat,
}

impl RecordedInterval {
    /// Return the smallest PCM frame cover of this interval.
    ///
    /// The start is floored and the end is ceiled using exact integer arithmetic.  The interval
    /// must lie inside `[0, sample_count / sample_rate]`; no timestamp is rounded through `f64`.
    pub fn covering_frames(
        &self,
        sample_rate: u64,
        sample_count: u64,
    ) -> Result<PcmFrameBounds, RecordedIntervalError> {
        if sample_rate == 0 {
            return Err(RecordedIntervalError::InvalidSampleRate);
        }
        if self.begin.is_negative() || self.end.is_negative() {
            return Err(RecordedIntervalError::OutsideRecording);
        }
        if self.begin >= self.end {
            return Err(if self.begin == self.end {
                RecordedIntervalError::Empty
            } else {
                RecordedIntervalError::Reversed
            });
        }
        let recording_end = Rat::new(BigInt::from(sample_count), BigInt::from(sample_rate));
        if self.end > recording_end {
            return Err(RecordedIntervalError::OutsideRecording);
        }

        let begin_product = &self.begin * BigInt::from(sample_rate);
        let end_product = &self.end * BigInt::from(sample_rate);
        let begin_frame = floor_nonnegative(&begin_product)?;
        let end_frame = ceil_nonnegative(&end_product)?;
        if end_frame > sample_count || begin_frame > sample_count {
            return Err(RecordedIntervalError::OutsideRecording);
        }
        Ok(PcmFrameBounds {
            begin_frame,
            end_frame,
            sample_rate,
            sample_count,
            begin: self.begin.clone(),
            end: self.end.clone(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcmFrameBounds {
    pub begin_frame: u64,
    pub end_frame: u64,
    pub sample_rate: u64,
    pub sample_count: u64,
    pub begin: Rat,
    pub end: Rat,
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum RecordedIntervalError {
    #[error("sample rate must be positive")]
    InvalidSampleRate,
    #[error("interval is empty")]
    Empty,
    #[error("interval is reversed")]
    Reversed,
    #[error("interval lies outside the recording")]
    OutsideRecording,
    #[error("frame bound does not fit in u64")]
    FrameOverflow,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedSpeaker {
    pub agent: String,
    pub channel: u64,
    pub global_name: String,
    pub role: String,
    pub source_attributes: Value,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedPointer {
    pub role: String,
    pub href: String,
    pub source_attributes: Value,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedEndpoint {
    pub dialogue_act_id: String,
    pub speaker_agent: String,
    pub speaker: RecordedSpeaker,
    pub source_file: String,
    pub source_word_href: String,
    pub source_pointers: Vec<RecordedPointer>,
    pub clock_refusals: Vec<Value>,
    pub interval: RecordedInterval,
    /// The complete endpoint JSON value is retained as cold source testimony.
    pub raw: Value,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedRefusal {
    pub code: String,
    pub detail: String,
    pub source_clock_refusals: Vec<Value>,
    pub target_clock_refusals: Vec<Value>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordedResponseDisposition {
    ResolvedDirectSourceTarget {
        source: RecordedEndpoint,
        target: RecordedEndpoint,
    },
    Refused(RecordedRefusal),
}

/// One original line from `response-links.exact.jsonl`, including its complete raw JSON value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedResponseLink {
    pub raw: Value,
    pub session: Option<String>,
    pub adjacency_pair_id: Option<String>,
    pub link_pointers: Vec<RecordedPointer>,
    pub disposition: RecordedResponseDisposition,
}

impl RecordedResponseLink {
    pub fn resolved(&self) -> Option<(&RecordedEndpoint, &RecordedEndpoint)> {
        match &self.disposition {
            RecordedResponseDisposition::ResolvedDirectSourceTarget { source, target } => {
                Some((source, target))
            }
            RecordedResponseDisposition::Refused(_) => None,
        }
    }

    pub fn refusal(&self) -> Option<&RecordedRefusal> {
        match &self.disposition {
            RecordedResponseDisposition::ResolvedDirectSourceTarget { .. } => None,
            RecordedResponseDisposition::Refused(refusal) => Some(refusal),
        }
    }
}

/// Parse one original response-link object.  Semantic defects become retained refusals so a
/// caller cannot accidentally drop the corpus' refusal population.
pub fn parse_recorded_response_link(raw: Value) -> RecordedResponseLink {
    let object = raw.as_object();
    let session = object
        .and_then(|value| string_field(value, "session"))
        .map(str::to_owned);
    let adjacency_pair_id = object
        .and_then(|value| string_field(value, "adjacency_pair_id"))
        .map(str::to_owned);
    let link_pointers = object
        .and_then(|value| value.get("source_pointers"))
        .and_then(Value::as_array)
        .map(|pointers| {
            pointers
                .iter()
                .filter_map(parse_pointer)
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();

    let disposition = match object {
        None => RecordedResponseDisposition::Refused(RecordedRefusal {
            code: "malformed-record".to_owned(),
            detail: "response-link is not an object".to_owned(),
            source_clock_refusals: Vec::new(),
            target_clock_refusals: Vec::new(),
        }),
        Some(object) => match string_field(object, "resolution_status") {
            Some("resolved-direct-source-pointer") => {
                match parse_resolved(object, &link_pointers) {
                    Ok((source, target)) => {
                        RecordedResponseDisposition::ResolvedDirectSourceTarget { source, target }
                    }
                    Err(failure) => {
                        RecordedResponseDisposition::Refused(failure.into_refusal(object))
                    }
                }
            }
            Some(status) if status.starts_with("refused-") => {
                RecordedResponseDisposition::Refused(explicit_refusal(object, status))
            }
            Some(status) => RecordedResponseDisposition::Refused(RecordedRefusal {
                code: "unknown-resolution-status".to_owned(),
                detail: format!("unsupported resolution_status {status:?}"),
                source_clock_refusals: endpoint_clock_refusals(object, "source"),
                target_clock_refusals: endpoint_clock_refusals(object, "target"),
            }),
            None => RecordedResponseDisposition::Refused(RecordedRefusal {
                code: "malformed-record".to_owned(),
                detail: "missing resolution_status".to_owned(),
                source_clock_refusals: endpoint_clock_refusals(object, "source"),
                target_clock_refusals: endpoint_clock_refusals(object, "target"),
            }),
        },
    };

    RecordedResponseLink {
        raw,
        session,
        adjacency_pair_id,
        link_pointers,
        disposition,
    }
}

pub fn parse_response_links_jsonl(
    input: &str,
) -> Result<Vec<RecordedResponseLink>, RecordedResponseLinkError> {
    input
        .lines()
        .enumerate()
        .filter(|(_, line)| !line.trim().is_empty())
        .map(|(line_index, line)| {
            let raw = serde_json::from_str::<Value>(line).map_err(|source| {
                RecordedResponseLinkError::JsonLine {
                    line: line_index + 1,
                    source,
                }
            })?;
            if !raw.is_object() {
                return Err(RecordedResponseLinkError::NotObject {
                    line: line_index + 1,
                });
            }
            Ok(parse_recorded_response_link(raw))
        })
        .collect()
}

pub fn read_response_links(
    path: impl AsRef<Path>,
) -> Result<Vec<RecordedResponseLink>, RecordedResponseLinkError> {
    parse_response_links_jsonl(&fs::read_to_string(path)?)
}

#[derive(Debug)]
struct ResolutionFailure {
    code: &'static str,
    detail: String,
}

impl ResolutionFailure {
    fn into_refusal(self, object: &Map<String, Value>) -> RecordedRefusal {
        RecordedRefusal {
            code: self.code.to_owned(),
            detail: self.detail,
            source_clock_refusals: endpoint_clock_refusals(object, "source"),
            target_clock_refusals: endpoint_clock_refusals(object, "target"),
        }
    }
}

fn parse_resolved(
    object: &Map<String, Value>,
    link_pointers: &[RecordedPointer],
) -> Result<(RecordedEndpoint, RecordedEndpoint), ResolutionFailure> {
    let _session = required_string(object, "session", "link")?;
    let _identifier = required_string(object, "adjacency_pair_id", "link")?;
    let source_file = required_string(object, "source_file", "link")?;
    let raw_pointers = object
        .get("source_pointers")
        .and_then(Value::as_array)
        .ok_or_else(|| failure("malformed-pointer", "link source_pointers must be an array"))?;
    if raw_pointers.len() != link_pointers.len() {
        return Err(failure(
            "malformed-pointer",
            "link contains an unparsed pointer",
        ));
    }
    let mut roles = std::collections::BTreeSet::new();
    if link_pointers.iter().any(|p| !roles.insert(&p.role)) {
        return Err(failure(
            "malformed-pointer",
            "link contains repeated pointer roles",
        ));
    }
    let source_value = object
        .get("source")
        .ok_or_else(|| failure("missing-endpoint", "missing source endpoint"))?;
    let target_value = object
        .get("target")
        .ok_or_else(|| failure("missing-endpoint", "missing target endpoint"))?;
    let source = parse_endpoint(source_value, "source")?;
    let target = parse_endpoint(target_value, "target")?;
    validate_link_pointers(&source_file, link_pointers, &source, &target)?;
    Ok((source, target))
}

fn parse_endpoint(value: &Value, role: &str) -> Result<RecordedEndpoint, ResolutionFailure> {
    let object = value.as_object().ok_or_else(|| {
        failure(
            "malformed-endpoint",
            format!("{role} endpoint is not an object"),
        )
    })?;
    let dialogue_act_id = required_string(object, "dialog_act_id", role)?;
    let speaker_agent = required_string(object, "speaker_agent", role)?;
    let source_file = required_string(object, "source_file", role)?;
    let source_word_href = required_string(object, "source_word_href", role)?;
    if !source_word_href.contains("#id(") {
        return Err(failure(
            "malformed-pointer",
            format!("{role} source_word_href has no NXT id"),
        ));
    }
    let speaker_value = object
        .get("speaker")
        .ok_or_else(|| failure("malformed-speaker", format!("{role} speaker is missing")))?;
    let speaker = parse_speaker(speaker_value, role)?;
    if speaker.agent != speaker_agent {
        return Err(failure(
            "identifier-mismatch",
            format!("{role} speaker agent disagrees with speaker metadata"),
        ));
    }
    let source_pointers = object
        .get("source_pointers")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            failure(
                "malformed-pointer",
                format!("{role} source_pointers is missing"),
            )
        })?
        .iter()
        .map(|pointer| {
            parse_pointer(pointer).ok_or_else(|| {
                failure(
                    "malformed-pointer",
                    format!("{role} contains a malformed source pointer"),
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let clock_refusals = object
        .get("clock_refusals")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            failure(
                "malformed-clock",
                format!("{role} clock_refusals must be an array"),
            )
        })?
        .clone();
    if !clock_refusals.is_empty() {
        return Err(failure(
            "clock-refusal",
            format!("{role} retains clock refusals: {clock_refusals:?}"),
        ));
    }
    let begin_decimal = required_string(object, "start", role)?;
    let end_decimal = required_string(object, "end", role)?;
    let begin = parse_decimal(&begin_decimal)
        .map_err(|detail| failure("malformed-clock", format!("{role} start: {detail}")))?;
    let end = parse_decimal(&end_decimal)
        .map_err(|detail| failure("malformed-clock", format!("{role} end: {detail}")))?;
    if begin.is_negative() || end.is_negative() {
        return Err(failure(
            "clock-outside",
            format!("{role} clock is negative"),
        ));
    }
    if begin >= end {
        return Err(failure(
            "clock-reversed",
            format!("{role} clock is empty or reversed"),
        ));
    }
    Ok(RecordedEndpoint {
        dialogue_act_id,
        speaker_agent,
        speaker,
        source_file,
        source_word_href,
        source_pointers,
        clock_refusals,
        interval: RecordedInterval {
            begin_decimal,
            end_decimal,
            begin,
            end,
        },
        raw: value.clone(),
    })
}

fn parse_speaker(value: &Value, role: &str) -> Result<RecordedSpeaker, ResolutionFailure> {
    let object = value.as_object().ok_or_else(|| {
        failure(
            "malformed-speaker",
            format!("{role} speaker is not an object"),
        )
    })?;
    let agent = required_string(object, "agent", role)?;
    let channel = object.get("channel").and_then(value_u64).ok_or_else(|| {
        failure(
            "malformed-speaker",
            format!("{role} speaker channel is not a non-negative integer"),
        )
    })?;
    let global_name = required_string(object, "global_name", role)?;
    let speaker_role = required_string(object, "role", role)?;
    Ok(RecordedSpeaker {
        agent,
        channel,
        global_name,
        role: speaker_role,
        source_attributes: object
            .get("source_attributes")
            .cloned()
            .unwrap_or(Value::Null),
    })
}

fn validate_link_pointers(
    source_file: &str,
    pointers: &[RecordedPointer],
    source: &RecordedEndpoint,
    target: &RecordedEndpoint,
) -> Result<(), ResolutionFailure> {
    let source_pointers = pointers
        .iter()
        .filter(|pointer| pointer.role == "source")
        .collect::<Vec<_>>();
    let target_pointers = pointers
        .iter()
        .filter(|pointer| pointer.role == "target")
        .collect::<Vec<_>>();
    if source_pointers.len() != 1 || target_pointers.len() != 1 {
        return Err(failure(
            "malformed-pointer",
            "resolved record must contain exactly one source and target pointer",
        ));
    }
    if !pointer_matches_endpoint(source_file, &source_pointers[0].href, source) {
        return Err(failure(
            "unresolved-pointer",
            "source pointer does not identify the source dialogue act",
        ));
    }
    if !pointer_matches_endpoint(source_file, &target_pointers[0].href, target) {
        return Err(failure(
            "unresolved-pointer",
            "target pointer does not identify the target dialogue act",
        ));
    }
    Ok(())
}

fn pointer_matches_endpoint(source_file: &str, href: &str, endpoint: &RecordedEndpoint) -> bool {
    let Some((file, fragment)) = href.split_once('#') else {
        return false;
    };
    if fragment != format!("id({})", endpoint.dialogue_act_id) {
        return false;
    }
    // NXT hrefs are relative to their owning annotation. Equal basenames or suffixes are
    // insufficient: a different directory is a different exterior source address.
    let parent = Path::new(source_file)
        .parent()
        .unwrap_or_else(|| Path::new(""));
    let Some(resolved) = relative_annotation_path(&parent.join(file)) else {
        return false;
    };
    relative_annotation_path(Path::new(&endpoint.source_file)).is_some_and(|p| p == resolved)
}

fn relative_annotation_path(path: &Path) -> Option<std::path::PathBuf> {
    use std::path::Component;
    let mut normalized = std::path::PathBuf::new();
    for component in path.components() {
        match component {
            Component::Normal(part) => normalized.push(part),
            Component::CurDir => {}
            Component::ParentDir => {
                if !normalized.pop() {
                    return None;
                }
            }
            Component::RootDir | Component::Prefix(_) => return None,
        }
    }
    Some(normalized)
}

fn parse_pointer(value: &Value) -> Option<RecordedPointer> {
    let object = value.as_object()?;
    Some(RecordedPointer {
        role: string_field(object, "role")?.to_owned(),
        href: string_field(object, "href")?.to_owned(),
        source_attributes: object
            .get("source_attributes")
            .cloned()
            .unwrap_or(Value::Null),
    })
}

fn explicit_refusal(object: &Map<String, Value>, status: &str) -> RecordedRefusal {
    RecordedRefusal {
        code: status.to_owned(),
        detail: string_field(object, "refusal")
            .unwrap_or("source record explicitly refused")
            .to_owned(),
        source_clock_refusals: endpoint_clock_refusals(object, "source"),
        target_clock_refusals: endpoint_clock_refusals(object, "target"),
    }
}

fn endpoint_clock_refusals(object: &Map<String, Value>, role: &str) -> Vec<Value> {
    object
        .get(role)
        .and_then(Value::as_object)
        .and_then(|endpoint| endpoint.get("clock_refusals"))
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default()
}

fn required_string(
    object: &Map<String, Value>,
    key: &str,
    role: &str,
) -> Result<String, ResolutionFailure> {
    string_field(object, key).map(str::to_owned).ok_or_else(|| {
        failure(
            "malformed-endpoint",
            format!("{role} endpoint field {key:?} is missing or empty"),
        )
    })
}

fn string_field<'a>(object: &'a Map<String, Value>, key: &str) -> Option<&'a str> {
    object
        .get(key)
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
}

fn value_u64(value: &Value) -> Option<u64> {
    value.as_u64().or_else(|| value.as_str()?.parse().ok())
}

fn failure(code: &'static str, detail: impl Into<String>) -> ResolutionFailure {
    ResolutionFailure {
        code,
        detail: detail.into(),
    }
}

fn parse_decimal(value: &str) -> Result<Rat, String> {
    if value.is_empty() || value.trim() != value {
        return Err("decimal is empty or contains surrounding whitespace".to_owned());
    }
    let (negative, unsigned) = match value.as_bytes().first() {
        Some(b'-') => (true, &value[1..]),
        Some(b'+') => (false, &value[1..]),
        _ => (false, value),
    };
    let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    if whole.is_empty()
        || (!whole.bytes().all(|byte| byte.is_ascii_digit()))
        || !fraction.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err("not a decimal clock".to_owned());
    }
    let digits = format!("{whole}{fraction}");
    let mut numerator = BigInt::parse_bytes(digits.as_bytes(), 10)
        .ok_or_else(|| "decimal digits do not parse".to_owned())?;
    if negative {
        numerator = -numerator;
    }
    let exponent = u32::try_from(fraction.len())
        .map_err(|_| "decimal precision exceeds its integer carrier")?;
    let denominator = BigInt::from(10_u8).pow(exponent);
    Ok(Rat::new(numerator, denominator))
}

fn floor_nonnegative(value: &Rat) -> Result<u64, RecordedIntervalError> {
    if value.is_negative() {
        return Err(RecordedIntervalError::OutsideRecording);
    }
    (value.numer() / value.denom())
        .to_u64()
        .ok_or(RecordedIntervalError::FrameOverflow)
}

fn ceil_nonnegative(value: &Rat) -> Result<u64, RecordedIntervalError> {
    if value.is_negative() {
        return Err(RecordedIntervalError::OutsideRecording);
    }
    let numerator = value.numer();
    let denominator = value.denom();
    let quotient = (numerator + denominator - BigInt::one()) / denominator;
    quotient
        .to_u64()
        .ok_or(RecordedIntervalError::FrameOverflow)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn resolved(start: &str, end: &str) -> Value {
        serde_json::json!({
            "session": "ES2002a",
            "adjacency_pair_id": "ES2002a.adjacency-pairs.test",
            "source_file": "dialogueActs/ES2002a.adjacency-pairs.xml",
            "source": {
                "dialog_act_id": "ES2002a.B.dialog-act.source",
                "speaker_agent": "B",
                "speaker": {"agent":"B","channel":1,"global_name":"FEE005","role":"PM"},
                "start": start, "end": end,
                "source_file": "dialogueActs/ES2002a.B.dialog-act.xml",
                "source_word_href": "ES2002a.B.words.xml#id(ES2002a.B.words1)..id(ES2002a.B.words2)",
                "source_pointers": [], "clock_refusals": []
            },
            "target": {
                "dialog_act_id": "ES2002a.A.dialog-act.target",
                "speaker_agent": "A",
                "speaker": {"agent":"A","channel":0,"global_name":"MEE006","role":"ID"},
                "start": "3.25", "end": "4.5",
                "source_file": "dialogueActs/ES2002a.A.dialog-act.xml",
                "source_word_href": "ES2002a.A.words.xml#id(ES2002a.A.words1)..id(ES2002a.A.words2)",
                "source_pointers": [], "clock_refusals": []
            },
            "source_pointers": [
                {"role":"source","href":"ES2002a.B.dialog-act.xml#id(ES2002a.B.dialog-act.source)"},
                {"role":"target","href":"ES2002a.A.dialog-act.xml#id(ES2002a.A.dialog-act.target)"}
            ],
            "resolution_status":"resolved-direct-source-pointer"
        })
    }

    #[test]
    fn exact_non_aligned_decimal_edges_cover_without_float() {
        let link = parse_recorded_response_link(resolved("1.0001", "1.0009"));
        let (source, _) = link.resolved().unwrap();
        let frames = source.interval.covering_frames(1_000, 2_000).unwrap();
        assert_eq!((frames.begin_frame, frames.end_frame), (1000, 1001));
        assert_eq!(source.interval.begin_decimal, "1.0001");
    }

    #[test]
    fn exact_pointers_and_metadata_are_retained() {
        let raw = resolved("1", "2");
        let link = parse_recorded_response_link(raw.clone());
        assert_eq!(link.raw, raw);
        let (source, target) = link.resolved().unwrap();
        assert_eq!(source.dialogue_act_id, "ES2002a.B.dialog-act.source");
        assert_eq!(target.speaker.global_name, "MEE006");
        assert_eq!(link.link_pointers.len(), 2);
    }

    #[test]
    fn a_pointer_suffix_or_dropped_malformed_role_cannot_select_an_endpoint() {
        let mut wrong_directory = resolved("1", "2");
        wrong_directory["source_pointers"][0]["href"] =
            Value::from("foreign/ES2002a.B.dialog-act.xml#id(ES2002a.B.dialog-act.source)");
        assert_eq!(
            parse_recorded_response_link(wrong_directory)
                .refusal()
                .unwrap()
                .code,
            "unresolved-pointer"
        );
        let mut malformed = resolved("1", "2");
        malformed["source_pointers"]
            .as_array_mut()
            .unwrap()
            .push(serde_json::json!({"role":"source", "href":null}));
        assert_eq!(
            parse_recorded_response_link(malformed)
                .refusal()
                .unwrap()
                .code,
            "malformed-pointer"
        );
    }

    #[test]
    fn structured_clock_refusals_and_line_order_survive_the_jsonl_reader() {
        let mut raw = resolved("1", "2");
        let clock = serde_json::json!({"word":"w7", "refusal":"end precedes start"});
        raw["source"]["clock_refusals"] = serde_json::json!([clock.clone()]);
        let text = format!("{}\n{}\n", raw, resolved("2", "3"));
        let records = parse_response_links_jsonl(&text).unwrap();
        assert_eq!(records.len(), 2);
        assert_eq!(records[0].raw, raw);
        assert_eq!(
            records[0].refusal().unwrap().source_clock_refusals,
            vec![clock]
        );
        assert!(records[1].resolved().is_some());
    }

    #[test]
    fn bound_sections_keep_the_annotation_and_its_subsample_overhang() {
        use holonic_engine::phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId};
        use life::mathematical_source::ExactAcousticOccurrence;
        let mut wav = Vec::new();
        for bytes in [
            b"RIFF".as_slice(),
            &10036u32.to_le_bytes(),
            b"WAVEfmt ",
            &16u32.to_le_bytes(),
            &1u16.to_le_bytes(),
            &1u16.to_le_bytes(),
            &1000u32.to_le_bytes(),
            &2000u32.to_le_bytes(),
            &2u16.to_le_bytes(),
            &16u16.to_le_bytes(),
            b"data",
            &10000u32.to_le_bytes(),
        ] {
            wav.extend_from_slice(bytes);
        }
        for i in 0..5000i16 {
            wav.extend_from_slice(&i.to_le_bytes());
        }
        let recording =
            ExactAcousticOccurrence::from_wav_bytes(&wav, "ES2002a", "memory.wav", 500, 500, 1)
                .unwrap();
        let link = parse_recorded_response_link(resolved("1.0001", "1.0009"));
        let origin = Rat::new(7.into(), 3.into());
        let bind = |recording: &ExactAcousticOccurrence| {
            RecordedResponseSections::bind(
                &link,
                recording,
                PhaseCurrentReceiverId(1),
                PhaseCurrentLineageId(7),
                PhaseCurrentLineageId(8),
                origin.clone(),
                2,
                32768,
            )
        };
        let sections = bind(&recording).unwrap();
        assert_eq!(
            sections.source_frames().begin,
            Rat::new(10001.into(), 10000.into())
        );
        assert_eq!(sections.source().source_range(), 1000..1001);
        assert_eq!(sections.source().reconstruct_samples(), vec![1000]);
        assert_eq!(
            sections.source().section().origin,
            &origin + Rat::from_integer(1.into())
        );
        assert_eq!(sections.target().source_range(), 3250..4500);
        assert_eq!(sections.source().source_sha256(), recording.source_sha256);
        assert!(std::ptr::eq(sections.link(), &link));
        let mut foreign = recording;
        foreign.occurrence = "different-recording".into();
        assert!(matches!(
            bind(&foreign),
            Err(RecordedSectionError::RecordingBinding)
        ));
    }

    #[test]
    fn reversed_and_outside_frame_bounds_are_rejected() {
        let reversed = RecordedInterval {
            begin_decimal: "2".to_owned(),
            end_decimal: "1".to_owned(),
            begin: parse_decimal("2").unwrap(),
            end: parse_decimal("1").unwrap(),
        };
        assert_eq!(
            reversed.covering_frames(1_000, 3_000),
            Err(RecordedIntervalError::Reversed)
        );
        let outside = RecordedInterval {
            begin_decimal: "2.9".to_owned(),
            end_decimal: "3.1".to_owned(),
            begin: parse_decimal("2.9").unwrap(),
            end: parse_decimal("3.1").unwrap(),
        };
        assert_eq!(
            outside.covering_frames(1_000, 3_000),
            Err(RecordedIntervalError::OutsideRecording)
        );
    }

    #[test]
    fn explicit_refusal_keeps_raw_record_and_clock_refusal() {
        let raw = serde_json::json!({
            "session":"ES2002a", "adjacency_pair_id":"refused",
            "resolution_status":"refused-incomplete-pointers",
            "refusal":"missing roles: target",
            "source":{"clock_refusals":["source word interval is reversed"]}
        });
        let link = parse_recorded_response_link(raw.clone());
        assert_eq!(link.raw, raw);
        let refusal = link.refusal().unwrap();
        assert_eq!(refusal.code, "refused-incomplete-pointers");
        assert_eq!(
            refusal.source_clock_refusals,
            vec!["source word interval is reversed"]
        );
    }
}
