//! Exact visible-dialogue lineage imported from an append-only Codex rollout.
//!
//! A rollout is a world container, not a transcript. It also carries instructions, tool calls,
//! tool returns, encrypted reasoning, scheduling events, and duplicated presentation events. This
//! membrane admits only visible `response_item/message` occurrences whose role is `user` or
//! `assistant`. Message identity, turn identity, phase, timestamp, raw record range, chronology,
//! and addressed predecessor remain testimony; none of those coordinates is inserted into the
//! linguistic surface.

use std::{
    collections::BTreeSet,
    fs::File,
    io::{BufRead, BufReader},
    ops::Range,
    path::Path,
};

use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

use crate::morphological_language::MorphologicalLanguagePassage;

const USER_RECEIVER: u64 = 20_000_000;
const ASSISTANT_COMMENTARY_RECEIVER: u64 = 20_000_001;
const ASSISTANT_FINAL_RECEIVER: u64 = 20_000_002;
const ASSISTANT_OTHER_RECEIVER: u64 = 20_000_003;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DialogueSpeaker {
    User,
    Assistant,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DialoguePhase {
    Received,
    Commentary,
    FinalAnswer,
    Other(String),
}

/// Where an occurrence's identity came from.
///
/// A container may or may not supply one. When it does not, the occurrence still has an exact,
/// reproducible address — the raw record range this membrane already computes and already retains
/// — so the identity is **founded** from it rather than the container being refused whole.
///
/// The species is carried because the two are not the same testimony and must never be conflated:
/// a supplied identity is the container's coordinate, a founded one is this membrane's. Measured
/// 2026-08-10 on the largest rollout on disk: **466 of 2,667** visible message records carry no
/// `id`, and every one of them is real user or assistant text. Refusing on their account deleted a
/// 2.1 GB container to protect a coordinate that is testimony rather than content.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DialogueIdentitySpecies {
    /// The container supplied `payload.id`.
    Supplied,
    /// The container supplied none; the identity is this membrane's own record address.
    FoundedFromRecordRange,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DialogueLineageOccurrence {
    pub ordinal: u64,
    pub identity: String,
    pub identity_species: DialogueIdentitySpecies,
    pub turn: String,
    pub timestamp: String,
    pub speaker: DialogueSpeaker,
    pub phase: DialoguePhase,
    pub text: String,
    pub raw_record: u64,
    pub raw_range: Range<u64>,
    /// The latest visible occurrence from the other speaker when this occurrence arrived.
    pub addressed: Option<String>,
    /// Immediate chronology and the addressed occurrence remain distinct causal predecessors.
    pub caused_by: BTreeSet<String>,
}

impl DialogueLineageOccurrence {
    pub const fn receiver(&self) -> u64 {
        match (&self.speaker, &self.phase) {
            (DialogueSpeaker::User, _) => USER_RECEIVER,
            (DialogueSpeaker::Assistant, DialoguePhase::Commentary) => {
                ASSISTANT_COMMENTARY_RECEIVER
            }
            (DialogueSpeaker::Assistant, DialoguePhase::FinalAnswer) => ASSISTANT_FINAL_RECEIVER,
            (DialogueSpeaker::Assistant, _) => ASSISTANT_OTHER_RECEIVER,
        }
    }

    pub fn passage(&self) -> MorphologicalLanguagePassage {
        MorphologicalLanguagePassage::new(
            self.identity.clone(),
            format!(
                "codex-dialogue/{}/{}/{}",
                speaker_name(self.speaker),
                phase_name(&self.phase),
                self.turn
            ),
            self.receiver(),
            self.text.clone(),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodexDialogueImportSpec {
    /// Stop immediately after this admitted visible message. Later assistant work cannot leak
    /// into a run which is intended to grade the consequence of this boundary.
    pub through_occurrence: Option<String>,
    pub include_commentary: bool,
}

impl Default for CodexDialogueImportSpec {
    fn default() -> Self {
        Self {
            through_occurrence: None,
            include_commentary: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodexDialogueLineageReceipt {
    pub schema: String,
    pub source: String,
    pub raw_extent: u64,
    pub raw_prefix_sha256: String,
    pub complete_records: u64,
    pub visible_occurrences: usize,
    pub user_occurrences: usize,
    pub assistant_commentary_occurrences: usize,
    pub assistant_final_occurrences: usize,
    pub assistant_other_occurrences: usize,
    pub excluded_control_occurrences: usize,
    /// Visible occurrences whose identity this membrane founded from its own record address
    /// because the container supplied none. Never silent: an identity that is this membrane's
    /// coordinate rather than the container's is counted here and typed on every occurrence.
    pub founded_identity_occurrences: usize,
    pub through_occurrence: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactDialogueLineage {
    occurrences: Vec<DialogueLineageOccurrence>,
    receipt: CodexDialogueLineageReceipt,
}

impl ExactDialogueLineage {
    pub fn import_codex_rollout(
        path: &Path,
        spec: &CodexDialogueImportSpec,
    ) -> Result<Self, String> {
        let metadata = path
            .metadata()
            .map_err(|error| format!("inspect {}: {error}", path.display()))?;
        if !metadata.is_file() {
            return Err(format!("{} is not a Codex rollout file", path.display()));
        }
        let input =
            File::open(path).map_err(|error| format!("open {}: {error}", path.display()))?;
        let mut input = BufReader::new(input);
        let mut raw = Vec::new();
        let mut raw_at = 0_u64;
        let mut record = 0_u64;
        let mut prefix = Sha256::new();
        let mut occurrences = Vec::new();
        let mut excluded_control_occurrences = 0usize;
        let mut founded_identities = 0usize;
        let mut reached_boundary = spec.through_occurrence.is_none();
        loop {
            raw.clear();
            let read = input
                .read_until(b'\n', &mut raw)
                .map_err(|error| format!("read {} record {record}: {error}", path.display()))?;
            if read == 0 {
                break;
            }
            let raw_end = raw_at
                .checked_add(u64::try_from(read).map_err(|_| "raw record extent".to_owned())?)
                .ok_or_else(|| "raw dialogue extent".to_owned())?;
            prefix.update(&raw);
            if raw.iter().any(|octet| !octet.is_ascii_whitespace()) {
                let value: Value = serde_json::from_slice(&raw).map_err(|error| {
                    format!(
                        "parse {} record {record} raw[{raw_at}..{raw_end}]: {error}",
                        path.display()
                    )
                })?;
                if let Some(candidate) = visible_message(&value, spec.include_commentary)? {
                    match candidate {
                        VisibleMessage::Control => {
                            excluded_control_occurrences = excluded_control_occurrences
                                .checked_add(1)
                                .ok_or_else(|| "control occurrence extent".to_owned())?;
                        }
                        VisibleMessage::Dialogue {
                            identity,
                            turn,
                            timestamp,
                            speaker,
                            phase,
                            text,
                        } => {
                            let ordinal = u64::try_from(occurrences.len())
                                .map_err(|_| "dialogue occurrence extent".to_owned())?;
                            // The record address is exact, reproducible, and already retained on
                            // the occurrence below, so it founds an identity when the container
                            // supplies none. The species is carried beside it.
                            let (identity, identity_species) = match identity {
                                Some(supplied) => {
                                    (supplied, DialogueIdentitySpecies::Supplied)
                                }
                                None => {
                                    founded_identities = founded_identities
                                        .checked_add(1)
                                        .ok_or_else(|| "founded identity extent".to_owned())?;
                                    (
                                        format!("codex-record/{record}/{raw_at}-{raw_end}"),
                                        DialogueIdentitySpecies::FoundedFromRecordRange,
                                    )
                                }
                            };
                            let is_boundary = spec
                                .through_occurrence
                                .as_deref()
                                .is_some_and(|boundary| boundary == identity);
                            occurrences.push(DialogueLineageOccurrence {
                                ordinal,
                                identity,
                                identity_species,
                                turn,
                                timestamp,
                                speaker,
                                phase,
                                text,
                                raw_record: record,
                                raw_range: raw_at..raw_end,
                                addressed: None,
                                caused_by: BTreeSet::new(),
                            });
                            if is_boundary {
                                reached_boundary = true;
                                raw_at = raw_end;
                                record = record
                                    .checked_add(1)
                                    .ok_or_else(|| "raw record extent".to_owned())?;
                                break;
                            }
                        }
                    }
                }
                record = record
                    .checked_add(1)
                    .ok_or_else(|| "raw record extent".to_owned())?;
            }
            raw_at = raw_end;
        }
        if !reached_boundary {
            return Err(format!(
                "{} contains no admitted occurrence {:?}",
                path.display(),
                spec.through_occurrence
            ));
        }
        if occurrences.is_empty() {
            return Err(format!(
                "{} contains no admitted visible dialogue occurrence",
                path.display()
            ));
        }
        found_predecessors(&mut occurrences);
        let user_occurrences = occurrences
            .iter()
            .filter(|occurrence| occurrence.speaker == DialogueSpeaker::User)
            .count();
        let assistant_commentary_occurrences = occurrences
            .iter()
            .filter(|occurrence| occurrence.phase == DialoguePhase::Commentary)
            .count();
        let assistant_final_occurrences = occurrences
            .iter()
            .filter(|occurrence| occurrence.phase == DialoguePhase::FinalAnswer)
            .count();
        let assistant_other_occurrences = occurrences
            .len()
            .saturating_sub(user_occurrences)
            .saturating_sub(assistant_commentary_occurrences)
            .saturating_sub(assistant_final_occurrences);
        let receipt = CodexDialogueLineageReceipt {
            schema: "life.codex-dialogue-lineage.v1".to_owned(),
            source: path.display().to_string(),
            raw_extent: raw_at,
            raw_prefix_sha256: hex_digest(prefix.finalize().as_slice()),
            complete_records: record,
            visible_occurrences: occurrences.len(),
            user_occurrences,
            assistant_commentary_occurrences,
            assistant_final_occurrences,
            assistant_other_occurrences,
            excluded_control_occurrences,
            founded_identity_occurrences: founded_identities,
            through_occurrence: spec.through_occurrence.clone(),
        };
        Ok(Self {
            occurrences,
            receipt,
        })
    }

    pub fn occurrences(&self) -> &[DialogueLineageOccurrence] {
        &self.occurrences
    }

    pub const fn receipt(&self) -> &CodexDialogueLineageReceipt {
        &self.receipt
    }

    pub fn passages(&self) -> Vec<MorphologicalLanguagePassage> {
        self.occurrences
            .iter()
            .map(DialogueLineageOccurrence::passage)
            .collect()
    }
}

enum VisibleMessage {
    Control,
    Dialogue {
        /// `None` when the container supplied no `payload.id`.
        identity: Option<String>,
        turn: String,
        timestamp: String,
        speaker: DialogueSpeaker,
        phase: DialoguePhase,
        text: String,
    },
}

fn visible_message(
    value: &Value,
    include_commentary: bool,
) -> Result<Option<VisibleMessage>, String> {
    if value.get("type").and_then(Value::as_str) != Some("response_item") {
        return Ok(None);
    }
    let Some(payload) = value.get("payload") else {
        return Ok(None);
    };
    if payload.get("type").and_then(Value::as_str) != Some("message") {
        return Ok(None);
    }
    let speaker = match payload.get("role").and_then(Value::as_str) {
        Some("user") => DialogueSpeaker::User,
        Some("assistant") => DialogueSpeaker::Assistant,
        _ => return Ok(None),
    };
    let phase = match (speaker, payload.get("phase").and_then(Value::as_str)) {
        (DialogueSpeaker::User, _) => DialoguePhase::Received,
        (DialogueSpeaker::Assistant, Some("commentary")) => DialoguePhase::Commentary,
        (DialogueSpeaker::Assistant, Some("final_answer")) => DialoguePhase::FinalAnswer,
        (DialogueSpeaker::Assistant, Some(other)) => DialoguePhase::Other(other.to_owned()),
        (DialogueSpeaker::Assistant, None) => DialoguePhase::Other("unspecified".to_owned()),
    };
    if phase == DialoguePhase::Commentary && !include_commentary {
        return Ok(None);
    }
    // An absent `id` is a condition of the container, not a corruption of it. It is returned as
    // `None` and founded from the record address at the push site, where the address is known.
    let identity = payload
        .get("id")
        .and_then(Value::as_str)
        .map(str::to_owned);
    let turn = payload
        .get("internal_chat_message_metadata_passthrough")
        .and_then(|metadata| metadata.get("turn_id"))
        .and_then(Value::as_str)
        .unwrap_or("unaddressed-turn")
        .to_owned();
    let timestamp = value
        .get("timestamp")
        .and_then(Value::as_str)
        .unwrap_or("unrecorded-time")
        .to_owned();
    let mut text = String::new();
    let mut admitted_blocks = 0usize;
    let Some(content) = payload.get("content").and_then(Value::as_array) else {
        return Ok(None);
    };
    for block in content {
        let block_type = block.get("type").and_then(Value::as_str);
        let admitted_type = match speaker {
            DialogueSpeaker::User => block_type == Some("input_text"),
            DialogueSpeaker::Assistant => block_type == Some("output_text"),
        };
        if !admitted_type {
            continue;
        }
        let Some(surface) = block.get("text").and_then(Value::as_str) else {
            continue;
        };
        if generated_control_surface(surface) || attachment_wrapper(surface) {
            continue;
        }
        admitted_blocks = admitted_blocks
            .checked_add(1)
            .ok_or_else(|| "dialogue content extent".to_owned())?;
        text.push_str(surface);
    }
    if admitted_blocks == 0 || text.trim().len() < 2 {
        return Ok(Some(VisibleMessage::Control));
    }
    Ok(Some(VisibleMessage::Dialogue {
        identity,
        turn,
        timestamp,
        speaker,
        phase,
        text,
    }))
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

fn found_predecessors(occurrences: &mut [DialogueLineageOccurrence]) {
    let mut last_user = None::<String>;
    let mut last_assistant = None::<String>;
    let mut previous = None::<String>;
    for occurrence in occurrences {
        let addressed = match occurrence.speaker {
            DialogueSpeaker::User => last_assistant.clone(),
            DialogueSpeaker::Assistant => last_user.clone(),
        };
        let mut caused_by = BTreeSet::new();
        if let Some(addressed) = &addressed {
            caused_by.insert(addressed.clone());
        }
        if let Some(previous) = &previous {
            caused_by.insert(previous.clone());
        }
        occurrence.addressed = addressed;
        occurrence.caused_by = caused_by;
        match occurrence.speaker {
            DialogueSpeaker::User => last_user = Some(occurrence.identity.clone()),
            DialogueSpeaker::Assistant => last_assistant = Some(occurrence.identity.clone()),
        }
        previous = Some(occurrence.identity.clone());
    }
}

const fn speaker_name(speaker: DialogueSpeaker) -> &'static str {
    match speaker {
        DialogueSpeaker::User => "user",
        DialogueSpeaker::Assistant => "assistant",
    }
}

fn phase_name(phase: &DialoguePhase) -> &str {
    match phase {
        DialoguePhase::Received => "received",
        DialoguePhase::Commentary => "commentary",
        DialoguePhase::FinalAnswer => "final-answer",
        DialoguePhase::Other(value) => value,
    }
}

fn hex_digest(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temporary() -> std::path::PathBuf {
        let serial = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!(
            "soma-dialogue-lineage-{}-{serial}.jsonl",
            std::process::id()
        ))
    }

    #[test]
    fn visible_messages_retain_roles_turns_and_addressed_chronology() {
        let path = temporary();
        let material = concat!(
            "{\"timestamp\":\"t0\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"id\":\"control\",\"internal_chat_message_metadata_passthrough\":{\"turn_id\":\"turn-0\"},\"content\":[{\"type\":\"input_text\",\"text\":\"# AGENTS.md instructions for /tmp\"}]}}\n",
            "{\"timestamp\":\"t1\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"id\":\"user-1\",\"internal_chat_message_metadata_passthrough\":{\"turn_id\":\"turn-1\"},\"content\":[{\"type\":\"input_text\",\"text\":\"How does current return?\"}]}}\n",
            "{\"timestamp\":\"t2\",\"type\":\"response_item\",\"payload\":{\"type\":\"reasoning\",\"encrypted_content\":\"dark\"}}\n",
            "{\"timestamp\":\"t3\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"assistant\",\"phase\":\"commentary\",\"id\":\"assistant-1\",\"internal_chat_message_metadata_passthrough\":{\"turn_id\":\"turn-1\"},\"content\":[{\"type\":\"output_text\",\"text\":\"Current crosses the membrane.\"}]}}\n",
            "{\"timestamp\":\"t4\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"assistant\",\"phase\":\"final_answer\",\"id\":\"assistant-2\",\"internal_chat_message_metadata_passthrough\":{\"turn_id\":\"turn-1\"},\"content\":[{\"type\":\"output_text\",\"text\":\"The returned current changes standing.\"}]}}\n",
            "{\"timestamp\":\"t5\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"id\":\"user-2\",\"internal_chat_message_metadata_passthrough\":{\"turn_id\":\"turn-2\"},\"content\":[{\"type\":\"input_text\",\"text\":\"Apply that correction.\"}]}}\n"
        );
        std::fs::write(&path, material).unwrap();
        let lineage = ExactDialogueLineage::import_codex_rollout(
            &path,
            &CodexDialogueImportSpec {
                through_occurrence: Some("user-2".to_owned()),
                include_commentary: true,
            },
        )
        .unwrap();
        assert_eq!(lineage.occurrences.len(), 4);
        assert_eq!(lineage.receipt.excluded_control_occurrences, 1);
        assert_eq!(lineage.occurrences[1].addressed.as_deref(), Some("user-1"));
        assert!(lineage.occurrences[2].caused_by.contains("assistant-1"));
        assert_eq!(
            lineage.occurrences[3].addressed.as_deref(),
            Some("assistant-2")
        );
        assert_eq!(lineage.passages()[0].text, "How does current return?");
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn a_container_supplying_no_identity_founds_one_from_the_record_address() {
        // Measured on the largest rollout on disk: 466 of 2,667 visible message records carry no
        // `payload.id`. The membrane refused the whole 2.1 GB container on their account until
        // 2026-08-10. An absent identity is a condition of the container, not a corruption, and
        // the record address is exact and already retained.
        let path = temporary();
        let material = concat!(
            "{\"timestamp\":\"t0\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"id\":\"user-1\",\"content\":[{\"type\":\"input_text\",\"text\":\"How does current return?\"}]}}\n",
            "{\"timestamp\":\"t1\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"assistant\",\"phase\":\"final_answer\",\"content\":[{\"type\":\"output_text\",\"text\":\"The returned current changes standing.\"}]}}\n",
            "{\"timestamp\":\"t2\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"content\":[{\"type\":\"input_text\",\"text\":\"Apply that correction.\"}]}}\n"
        );
        std::fs::write(&path, material).unwrap();
        let lineage =
            ExactDialogueLineage::import_codex_rollout(&path, &CodexDialogueImportSpec::default())
                .unwrap();

        assert_eq!(lineage.occurrences.len(), 3);
        assert_eq!(lineage.receipt.founded_identity_occurrences, 2);
        assert_eq!(
            lineage.occurrences[0].identity_species,
            DialogueIdentitySpecies::Supplied
        );
        assert_eq!(lineage.occurrences[0].identity, "user-1");
        for founded in &lineage.occurrences[1..] {
            assert_eq!(
                founded.identity_species,
                DialogueIdentitySpecies::FoundedFromRecordRange
            );
            // The founded identity IS the record address, so it is reproducible from the container.
            assert_eq!(
                founded.identity,
                format!(
                    "codex-record/{}/{}-{}",
                    founded.raw_record, founded.raw_range.start, founded.raw_range.end
                )
            );
        }
        // Distinct records found distinct identities, so chronology and address remain exact.
        assert_ne!(lineage.occurrences[1].identity, lineage.occurrences[2].identity);
        assert_eq!(
            lineage.occurrences[2].addressed.as_deref(),
            Some(lineage.occurrences[1].identity.as_str()),
            "a founded identity carries the addressed lineage exactly as a supplied one does"
        );
        assert_eq!(lineage.passages()[2].text, "Apply that correction.");
        std::fs::remove_file(path).unwrap();
    }
}
