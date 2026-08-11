//! Parsing and import of external text containers into exact witnessed occurrences.

use std::{
    fs::File,
    io::{BufRead, BufReader, Read},
    ops::Range,
    path::Path,
    thread,
};

use serde_json::Value;
use sha2::{Digest, Sha256};

use super::{
    hex_digest, sha256_hex, ParsedTextDocument, TextMaterialContainerReceipt, TextMaterialError,
    TextMaterialIdentitySpecies, TextMaterialInput, TextMaterialMap, TextMaterialOccurrence,
    TextMaterialPhase, TextMaterialRole, TextMaterialSet, TextMaterialSourceKind,
    TextMaterialVector, TextMaterialWitness,
};

#[derive(Clone)]
pub(super) struct ParsedOccurrence {
    pub(super) native_identity: String,
    pub(super) role: TextMaterialRole,
    pub(super) phase: TextMaterialPhase,
    pub(super) text: String,
    pub(super) witness: TextMaterialWitness,
    pub(super) caused_by: TextMaterialSet<String>,
}

pub(super) struct ParsedContainer {
    pub(super) receipt: TextMaterialContainerReceipt,
    pub(super) occurrences: TextMaterialVector<ParsedOccurrence>,
}

pub(super) fn import_parallel(
    inputs: &[TextMaterialInput],
    thread_budget: usize,
) -> Result<TextMaterialVector<ParsedContainer>, TextMaterialError> {
    if inputs.is_empty() {
        return Ok(TextMaterialVector::new());
    }
    let threads = thread_budget.min(inputs.len()).max(1);
    let chunk = inputs.len().div_ceil(threads);
    let joined = thread::scope(|scope| {
        let mut workers = TextMaterialVector::new();
        for (chunk_at, inputs) in inputs.chunks(chunk).enumerate() {
            workers.push(scope.spawn(move || {
                let start = chunk_at * chunk;
                let mut parsed = TextMaterialVector::with_capacity(inputs.len());
                for (local, input) in inputs.iter().enumerate() {
                    let container = match input {
                        TextMaterialInput::CodexRollout(path) => parse_codex(path),
                        TextMaterialInput::CodexHistory(path) => parse_codex_history(path),
                        TextMaterialInput::ClaudeCode(path) => parse_claude(path),
                        TextMaterialInput::ClaudeHistory(path) => parse_claude_history(path),
                    }?;
                    parsed.push((start + local, container));
                }
                Ok::<_, TextMaterialError>(parsed)
            }));
        }
        let mut out = TextMaterialVector::with_capacity(inputs.len());
        for worker in workers {
            out.extend(
                worker
                    .join()
                    .map_err(|_| TextMaterialError::WorkerPanicked)??,
            );
        }
        Ok::<_, TextMaterialError>(out)
    })?;
    let mut joined = joined;
    joined.sort_by_key(|(at, _)| *at);
    let mut parsed = TextMaterialVector::with_capacity(joined.len());
    for (_, container) in joined.drain(..) {
        parsed.push(container);
    }
    Ok(parsed)
}

fn parse_codex(path: &Path) -> Result<ParsedContainer, TextMaterialError> {
    parse_jsonl(path, TextMaterialSourceKind::CodexRollout, codex_visible)
}

fn parse_claude(path: &Path) -> Result<ParsedContainer, TextMaterialError> {
    parse_jsonl(path, TextMaterialSourceKind::ClaudeCode, claude_visible)
}

fn parse_codex_history(path: &Path) -> Result<ParsedContainer, TextMaterialError> {
    parse_jsonl(
        path,
        TextMaterialSourceKind::CodexHistory,
        codex_history_visible,
    )
}

fn parse_claude_history(path: &Path) -> Result<ParsedContainer, TextMaterialError> {
    parse_jsonl(
        path,
        TextMaterialSourceKind::ClaudeHistory,
        claude_history_visible,
    )
}

fn parse_jsonl(
    path: &Path,
    source_kind: TextMaterialSourceKind,
    visible: fn(&Value, &Path, &str, u64, Range<u64>) -> Result<VisibleRecord, TextMaterialError>,
) -> Result<ParsedContainer, TextMaterialError> {
    let metadata = path
        .metadata()
        .map_err(|error| TextMaterialError::Io(format!("inspect {}: {error}", path.display())))?;
    if !metadata.is_file() {
        return Err(TextMaterialError::Io(format!(
            "{} is not a regular text-material container",
            path.display()
        )));
    }
    let extent = metadata.len();
    let input = File::open(path)
        .map_err(|error| TextMaterialError::Io(format!("open {}: {error}", path.display())))?;
    let mut input = BufReader::new(input).take(extent);
    let mut raw = TextMaterialVector::new();
    let mut raw_at = 0u64;
    let mut record = 0u64;
    let mut complete_records = 0u64;
    let mut prefix = Sha256::new();
    let mut excluded_control_occurrences = 0usize;
    let mut founded_identity_occurrences = 0usize;
    let mut occurrences = TextMaterialVector::new();
    let mut conversation = path
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("unidentified-conversation")
        .to_owned();
    let mut conversations = TextMaterialSet::new();
    let mut previous = TextMaterialMap::<String, String>::new();
    let mut partial_tail_bytes = 0u64;
    loop {
        raw.clear();
        let read = input.read_until(b'\n', &mut raw).map_err(|error| {
            TextMaterialError::Io(format!("read {} record {record}: {error}", path.display()))
        })?;
        if read == 0 {
            break;
        }
        prefix.update(&raw);
        let raw_end = raw_at
            .checked_add(u64::try_from(read).map_err(|_| TextMaterialError::CarrierExtent)?)
            .ok_or(TextMaterialError::CarrierExtent)?;
        if raw.last() != Some(&b'\n') {
            partial_tail_bytes =
                u64::try_from(read).map_err(|_| TextMaterialError::CarrierExtent)?;
            raw_at = raw_end;
            break;
        }
        if !raw.iter().any(|octet| !octet.is_ascii_whitespace()) {
            raw_at = raw_end;
            continue;
        }
        complete_records = complete_records
            .checked_add(1)
            .ok_or(TextMaterialError::CarrierExtent)?;
        if candidate_record(source_kind, &raw) {
            let value: Value = serde_json::from_slice(&raw).map_err(|error| {
                TextMaterialError::Json(format!(
                    "parse {} record {record} raw[{raw_at}..{raw_end}]: {error}",
                    path.display()
                ))
            })?;
            if let Some(session) = record_conversation(source_kind, &value) {
                conversation = session.to_owned();
            }
            match visible(&value, path, &conversation, record, raw_at..raw_end)? {
                VisibleRecord::Absent => {}
                VisibleRecord::Control => {
                    excluded_control_occurrences = excluded_control_occurrences
                        .checked_add(1)
                        .ok_or(TextMaterialError::CarrierExtent)?;
                }
                VisibleRecord::Occurrence(mut occurrence) => {
                    if occurrence.witness.identity_species
                        == TextMaterialIdentitySpecies::FoundedFromContainerRecordRange
                    {
                        founded_identity_occurrences = founded_identity_occurrences
                            .checked_add(1)
                            .ok_or(TextMaterialError::CarrierExtent)?;
                    }
                    let occurrence_conversation = occurrence.witness.conversation.to_owned();
                    conversations.insert(occurrence_conversation.to_owned());
                    if let Some(prior) = previous.get(&occurrence_conversation) {
                        occurrence.caused_by.insert(prior.to_owned());
                    }
                    previous.insert(
                        occurrence_conversation,
                        occurrence.native_identity.to_owned(),
                    );
                    occurrences.push(occurrence);
                }
            }
        }
        raw_at = raw_end;
        record = record
            .checked_add(1)
            .ok_or(TextMaterialError::CarrierExtent)?;
    }
    let receipt_conversation = match conversations.len() {
        0 => conversation,
        1 => conversations
            .iter()
            .next()
            .map(|value| value.to_owned())
            .unwrap_or(conversation),
        count => format!("plural:{count}"),
    };
    Ok(ParsedContainer {
        receipt: TextMaterialContainerReceipt {
            source_kind,
            source: path.display().to_string(),
            conversation: receipt_conversation,
            raw_extent: raw_at,
            raw_sha256: hex_digest(&prefix.finalize()),
            complete_records,
            visible_occurrences: occurrences.len(),
            founded_identity_occurrences,
            excluded_control_occurrences,
            partial_tail_bytes,
        },
        occurrences,
    })
}

enum VisibleRecord {
    Absent,
    Control,
    Occurrence(ParsedOccurrence),
}

fn codex_visible(
    value: &Value,
    path: &Path,
    conversation: &str,
    raw_record: u64,
    raw_range: Range<u64>,
) -> Result<VisibleRecord, TextMaterialError> {
    if value.get("type").and_then(Value::as_str) != Some("response_item") {
        return Ok(VisibleRecord::Absent);
    }
    let Some(payload) = value.get("payload") else {
        return Ok(VisibleRecord::Absent);
    };
    if payload.get("type").and_then(Value::as_str) != Some("message") {
        return Ok(VisibleRecord::Absent);
    }
    let role = match payload.get("role").and_then(Value::as_str) {
        Some("user") => TextMaterialRole::Human,
        Some("assistant") => TextMaterialRole::Assistant,
        _ => return Ok(VisibleRecord::Absent),
    };
    let phase = match (role, payload.get("phase").and_then(Value::as_str)) {
        (TextMaterialRole::Human, _) => TextMaterialPhase::Received,
        (TextMaterialRole::Assistant, Some("commentary")) => TextMaterialPhase::Commentary,
        (TextMaterialRole::Assistant, Some("final_answer")) => TextMaterialPhase::FinalAnswer,
        (TextMaterialRole::Assistant, Some(other)) => TextMaterialPhase::Other(other.to_owned()),
        (TextMaterialRole::Assistant, None) => TextMaterialPhase::Response,
        (TextMaterialRole::Document, _) => TextMaterialPhase::Document,
    };
    let mut text = String::new();
    let Some(content) = payload.get("content").and_then(Value::as_array) else {
        return Ok(VisibleRecord::Absent);
    };
    for block in content {
        let admitted = match role {
            TextMaterialRole::Human => {
                block.get("type").and_then(Value::as_str) == Some("input_text")
            }
            TextMaterialRole::Assistant => {
                block.get("type").and_then(Value::as_str) == Some("output_text")
            }
            TextMaterialRole::Document => false,
        };
        if !admitted {
            continue;
        }
        let Some(surface) = block.get("text").and_then(Value::as_str) else {
            continue;
        };
        if generated_control_surface(surface) || attachment_wrapper(surface) {
            continue;
        }
        text.push_str(surface);
    }
    if text.trim().len() < 2 {
        return Ok(VisibleRecord::Control);
    }
    let timestamp = value
        .get("timestamp")
        .and_then(Value::as_str)
        .unwrap_or_default();
    let (native_identity, identity_species) = if let Some(native) =
        payload.get("id").and_then(Value::as_str)
    {
        (
            format!("codex:{native}"),
            TextMaterialIdentitySpecies::ProviderSupplied,
        )
    } else {
        (
            founded_record_identity("codex-rollout", path, conversation, raw_record, &raw_range),
            TextMaterialIdentitySpecies::FoundedFromContainerRecordRange,
        )
    };
    Ok(VisibleRecord::Occurrence(ParsedOccurrence {
        native_identity,
        role,
        phase,
        text,
        witness: TextMaterialWitness {
            source_kind: TextMaterialSourceKind::CodexRollout,
            identity_species,
            container: path.display().to_string(),
            conversation: conversation.to_owned(),
            raw_record,
            raw_start: raw_range.start,
            raw_end: raw_range.end,
            timestamp: timestamp.to_owned(),
            native_parent: None,
            sidechain: false,
        },
        caused_by: TextMaterialSet::new(),
    }))
}

fn claude_visible(
    value: &Value,
    path: &Path,
    conversation: &str,
    raw_record: u64,
    raw_range: Range<u64>,
) -> Result<VisibleRecord, TextMaterialError> {
    if value.get("isMeta").and_then(Value::as_bool) == Some(true) {
        return Ok(VisibleRecord::Control);
    }
    let role = match value.get("type").and_then(Value::as_str) {
        Some("user") => TextMaterialRole::Human,
        Some("assistant") => TextMaterialRole::Assistant,
        _ => return Ok(VisibleRecord::Absent),
    };
    let Some(message) = value.get("message") else {
        return Ok(VisibleRecord::Absent);
    };
    let expected_role = match role {
        TextMaterialRole::Human => "user",
        TextMaterialRole::Assistant => "assistant",
        TextMaterialRole::Document => "document",
    };
    if message.get("role").and_then(Value::as_str) != Some(expected_role) {
        return Ok(VisibleRecord::Absent);
    }
    let text = claude_text_blocks(message.get("content"));
    if text.trim().len() < 2 {
        return Ok(VisibleRecord::Control);
    }
    let (native_identity, identity_species) =
        if let Some(native) = value.get("uuid").and_then(Value::as_str) {
            (
                format!("claude-code:{native}"),
                TextMaterialIdentitySpecies::ProviderSupplied,
            )
        } else {
            (
                founded_record_identity("claude-code", path, conversation, raw_record, &raw_range),
                TextMaterialIdentitySpecies::FoundedFromContainerRecordRange,
            )
        };
    let parent = value
        .get("parentUuid")
        .and_then(Value::as_str)
        .map(|parent| format!("claude-code:{parent}"));
    Ok(VisibleRecord::Occurrence(ParsedOccurrence {
        native_identity,
        role,
        phase: if role == TextMaterialRole::Human {
            TextMaterialPhase::Received
        } else {
            TextMaterialPhase::Response
        },
        text,
        witness: TextMaterialWitness {
            source_kind: TextMaterialSourceKind::ClaudeCode,
            identity_species,
            container: path.display().to_string(),
            conversation: conversation.to_owned(),
            raw_record,
            raw_start: raw_range.start,
            raw_end: raw_range.end,
            timestamp: value
                .get("timestamp")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_owned(),
            native_parent: parent.to_owned(),
            sidechain: value
                .get("isSidechain")
                .and_then(Value::as_bool)
                .unwrap_or(false),
        },
        caused_by: {
            let mut caused_by = TextMaterialSet::new();
            if let Some(parent) = parent {
                caused_by.insert(parent);
            }
            caused_by
        },
    }))
}

fn codex_history_visible(
    value: &Value,
    path: &Path,
    conversation: &str,
    raw_record: u64,
    raw_range: Range<u64>,
) -> Result<VisibleRecord, TextMaterialError> {
    history_visible(
        value,
        path,
        conversation,
        raw_record,
        raw_range,
        TextMaterialSourceKind::CodexHistory,
        "codex-history",
        "text",
        "ts",
    )
}

fn claude_history_visible(
    value: &Value,
    path: &Path,
    conversation: &str,
    raw_record: u64,
    raw_range: Range<u64>,
) -> Result<VisibleRecord, TextMaterialError> {
    history_visible(
        value,
        path,
        conversation,
        raw_record,
        raw_range,
        TextMaterialSourceKind::ClaudeHistory,
        "claude-history",
        "display",
        "timestamp",
    )
}

#[allow(clippy::too_many_arguments)]
fn history_visible(
    value: &Value,
    path: &Path,
    conversation: &str,
    raw_record: u64,
    raw_range: Range<u64>,
    source_kind: TextMaterialSourceKind,
    identity_prefix: &str,
    text_field: &str,
    timestamp_field: &str,
) -> Result<VisibleRecord, TextMaterialError> {
    let Some(text) = value.get(text_field).and_then(Value::as_str) else {
        return Ok(VisibleRecord::Absent);
    };
    if text.trim().len() < 2 {
        return Ok(VisibleRecord::Control);
    }
    if generated_control_surface(text) || generated_claude_wrapper(text) {
        return Ok(VisibleRecord::Control);
    }
    Ok(VisibleRecord::Occurrence(ParsedOccurrence {
        native_identity: founded_record_identity(
            identity_prefix,
            path,
            conversation,
            raw_record,
            &raw_range,
        ),
        role: TextMaterialRole::Human,
        phase: TextMaterialPhase::Received,
        text: text.to_owned(),
        witness: TextMaterialWitness {
            source_kind,
            identity_species: TextMaterialIdentitySpecies::FoundedFromContainerRecordRange,
            container: path.display().to_string(),
            conversation: conversation.to_owned(),
            raw_record,
            raw_start: raw_range.start,
            raw_end: raw_range.end,
            timestamp: scalar_text(value.get(timestamp_field)),
            native_parent: None,
            sidechain: false,
        },
        caused_by: TextMaterialSet::new(),
    }))
}

fn founded_record_identity(
    prefix: &str,
    path: &Path,
    conversation: &str,
    raw_record: u64,
    raw_range: &Range<u64>,
) -> String {
    format!(
        "{prefix}:founded:container={}:conversation={conversation}:record={raw_record}:raw={}..{}",
        path.display(),
        raw_range.start,
        raw_range.end
    )
}

fn scalar_text(value: Option<&Value>) -> String {
    match value {
        Some(Value::String(value)) => value.to_owned(),
        Some(Value::Number(value)) => value.to_string(),
        _ => String::new(),
    }
}

fn record_conversation(kind: TextMaterialSourceKind, value: &Value) -> Option<&str> {
    match kind {
        TextMaterialSourceKind::CodexRollout => value
            .get("payload")
            .and_then(|payload| payload.get("session_id").or_else(|| payload.get("id")))
            .and_then(Value::as_str),
        TextMaterialSourceKind::CodexHistory => value.get("session_id").and_then(Value::as_str),
        TextMaterialSourceKind::ClaudeCode | TextMaterialSourceKind::ClaudeHistory => {
            value.get("sessionId").and_then(Value::as_str)
        }
        TextMaterialSourceKind::ParsedDocument | TextMaterialSourceKind::SelfEmanated => None,
    }
}

pub(super) fn parse_document(
    document: &ParsedTextDocument,
) -> Result<ParsedContainer, TextMaterialError> {
    if document.identity.trim().is_empty() || document.sections.is_empty() {
        return Err(TextMaterialError::EmptySource);
    }
    let mut raw = Sha256::new();
    let mut raw_extent = 0u64;
    let mut occurrences = TextMaterialVector::new();
    let mut previous = None::<String>;
    for (ordinal, text) in document.sections.iter().enumerate() {
        if text.trim().len() < 2 {
            continue;
        }
        raw.update(text.as_bytes());
        raw.update([0]);
        raw_extent = raw_extent
            .checked_add(
                u64::try_from(text.len() + 1).map_err(|_| TextMaterialError::CarrierExtent)?,
            )
            .ok_or(TextMaterialError::CarrierExtent)?;
        let native_identity = format!("document:{}:{ordinal}", document.identity);
        let mut caused_by = TextMaterialSet::new();
        if let Some(prior) = &previous {
            caused_by.insert(prior.to_owned());
        }
        occurrences.push(ParsedOccurrence {
            native_identity: native_identity.to_owned(),
            role: TextMaterialRole::Document,
            phase: TextMaterialPhase::Document,
            text: text.to_owned(),
            witness: TextMaterialWitness {
                source_kind: TextMaterialSourceKind::ParsedDocument,
                identity_species: TextMaterialIdentitySpecies::DeclaredDocument,
                container: document.source.to_owned(),
                conversation: document.identity.to_owned(),
                raw_record: u64::try_from(ordinal).map_err(|_| TextMaterialError::CarrierExtent)?,
                raw_start: 0,
                raw_end: u64::try_from(text.len()).map_err(|_| TextMaterialError::CarrierExtent)?,
                timestamp: String::new(),
                native_parent: previous.to_owned(),
                sidechain: false,
            },
            caused_by,
        });
        previous = Some(native_identity);
    }
    if occurrences.is_empty() {
        return Err(TextMaterialError::EmptyText);
    }
    Ok(ParsedContainer {
        receipt: TextMaterialContainerReceipt {
            source_kind: TextMaterialSourceKind::ParsedDocument,
            source: document.source.to_owned(),
            conversation: document.identity.to_owned(),
            raw_extent,
            raw_sha256: hex_digest(&raw.finalize()),
            complete_records: u64::try_from(document.sections.len())
                .map_err(|_| TextMaterialError::CarrierExtent)?,
            visible_occurrences: occurrences.len(),
            founded_identity_occurrences: 0,
            excluded_control_occurrences: document.sections.len() - occurrences.len(),
            partial_tail_bytes: 0,
        },
        occurrences,
    })
}

pub(super) fn merge_occurrence(
    versions: &mut TextMaterialMap<String, TextMaterialOccurrence>,
    occurrence: ParsedOccurrence,
) -> Result<(), TextMaterialError> {
    let digest = sha256_hex(occurrence.text.as_bytes());
    let identity = format!("{}:{digest}", occurrence.native_identity);
    if let Some(prior) = versions.get_mut(&identity) {
        if prior.role != occurrence.role
            || prior.phase != occurrence.phase
            || prior.text != occurrence.text
        {
            return Err(TextMaterialError::InvalidRest);
        }
        prior.witnesses.insert(occurrence.witness);
        prior.caused_by.extend(occurrence.caused_by);
        return Ok(());
    }
    versions.insert(
        identity.to_owned(),
        TextMaterialOccurrence {
            identity,
            native_identity: occurrence.native_identity,
            surface_sha256: digest,
            ordinal: 0,
            role: occurrence.role,
            phase: occurrence.phase,
            text: occurrence.text,
            witnesses: TextMaterialSet::from([occurrence.witness]),
            caused_by: occurrence.caused_by,
        },
    );
    Ok(())
}

fn candidate_record(kind: TextMaterialSourceKind, raw: &[u8]) -> bool {
    match kind {
        TextMaterialSourceKind::CodexRollout => {
            contains(raw, br#""type":"session_meta""#)
                || (contains(raw, br#""type":"response_item""#)
                    && contains(raw, br#""type":"message""#)
                    && (contains(raw, br#""role":"user""#)
                        || contains(raw, br#""role":"assistant""#)))
        }
        TextMaterialSourceKind::CodexHistory => {
            contains(raw, br#""session_id":"#) && contains(raw, br#""text":"#)
        }
        TextMaterialSourceKind::ClaudeCode => {
            contains(raw, br#""message":"#)
                && (contains(raw, br#""type":"user""#) || contains(raw, br#""type":"assistant""#))
                && (contains(raw, br#""content":""#)
                    || contains(raw, br#""type":"text""#)
                    || contains(raw, br#""isMeta":true"#))
        }
        TextMaterialSourceKind::ClaudeHistory => {
            contains(raw, br#""sessionId":"#) && contains(raw, br#""display":"#)
        }
        TextMaterialSourceKind::ParsedDocument | TextMaterialSourceKind::SelfEmanated => false,
    }
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty()
        && haystack
            .windows(needle.len())
            .any(|window| window == needle)
}

fn claude_text_blocks(content: Option<&Value>) -> String {
    let Some(content) = content else {
        return String::new();
    };
    if let Some(text) = content.as_str() {
        return (!generated_claude_wrapper(text))
            .then(|| text.to_owned())
            .unwrap_or_default();
    }
    let mut out = String::new();
    if let Some(blocks) = content.as_array() {
        for block in blocks {
            if block.get("type").and_then(Value::as_str) != Some("text") {
                continue;
            }
            if let Some(text) = block.get("text").and_then(Value::as_str) {
                if !generated_claude_wrapper(text) {
                    out.push_str(text);
                }
            }
        }
    }
    out
}

fn generated_control_surface(text: &str) -> bool {
    let trimmed = text.trim_start();
    [
        "# AGENTS.md instructions for ",
        "<environment_context>",
        "<permissions instructions>",
        "<collaboration_mode>",
        "<apps_instructions>",
        "<plugins_instructions>",
        "<skills_instructions>",
        "<local-command-caveat>",
        "<command-name>",
        "<command-message>",
        "<local-command-stdout>",
        "<system-reminder>",
        "<task-notification>",
    ]
    .iter()
    .any(|prefix| trimmed.starts_with(prefix))
}

fn attachment_wrapper(text: &str) -> bool {
    let trimmed = text.trim();
    trimmed == "</image>"
        || (trimmed.starts_with("<image ") && !trimmed.contains('\n') && trimmed.ends_with('>'))
}

fn generated_claude_wrapper(text: &str) -> bool {
    [
        "<command-name>",
        "<command-message>",
        "<local-command-caveat>",
        "<local-command-stdout>",
        "<system-reminder>",
        "<task-notification>",
        "<persisted-output>",
        "<bash-input>",
        "<bash-stdout>",
        "This session is being continued from a previous conversation",
    ]
    .iter()
    .any(|prefix| text.trim_start().starts_with(prefix))
}
