//! Exterior discovery and visible-face projection for one complete laboratory exchange aperture.
//!
//! Paths and provider faces authorize the captured occurrence. They never enter the contact law.
//! Every admitted file extent is captured together by the mount owner before its first record is
//! read. The visible projection then factors through the already-mounted richer record addresses.

use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::dialogue_lineage::{
    CodexDialogueImportSpec, DialoguePhase, DialogueSpeaker, ExactDialogueLineage,
    import_claude_visible_prefix,
};

use super::{Digest32, ExchangeContainerSpec, ExchangeWorldTube, VisibleMessageFace};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompleteExchangeSource {
    pub schema: String,
    pub workspace: PathBuf,
    pub codex_root: PathBuf,
    pub claude_root: PathBuf,
    pub specs: Vec<ExchangeContainerSpec>,
    pub excluded_codex_other_workspace: u64,
    pub excluded_non_jsonl: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VisibleProjectionReceipt {
    pub schema: String,
    pub visible_messages: usize,
    pub excluded_visible_controls: u64,
    pub every_face_factors_through_one_richer_record: bool,
    pub record_lookup_probes: u64,
}

/// Discover every complete JSONL container in the authorized workspace exchange roots. A Codex
/// rollout is admitted only when its own `session_meta` record declares the exact workspace.
pub fn discover_complete_exchange_aperture(
    codex_root: &Path,
    claude_root: &Path,
    workspace: &Path,
) -> Result<CompleteExchangeSource, String> {
    let workspace = workspace
        .canonicalize()
        .map_err(|error| format!("resolve workspace {}: {error}", workspace.display()))?;
    let codex_root = codex_root
        .canonicalize()
        .map_err(|error| format!("resolve Codex root {}: {error}", codex_root.display()))?;
    let claude_root = claude_root
        .canonicalize()
        .map_err(|error| format!("resolve Claude root {}: {error}", claude_root.display()))?;

    let mut codex_files = Vec::new();
    let mut codex_non_jsonl = 0u64;
    discover_jsonl(&codex_root, &mut codex_files, &mut codex_non_jsonl)?;
    codex_files.retain(|path| {
        path.file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with("rollout-") && name.ends_with(".jsonl"))
    });
    codex_files.sort();
    codex_files.dedup();

    let mut specs = Vec::new();
    let mut excluded_codex_other_workspace = 0u64;
    for path in codex_files {
        if codex_workspace(&path)?.as_deref() == Some(workspace.as_path()) {
            specs.push(ExchangeContainerSpec {
                locator: path,
                provider_face: "codex".to_owned(),
                material_kind_face: "exchange-rollout".to_owned(),
            });
        } else {
            excluded_codex_other_workspace = excluded_codex_other_workspace.saturating_add(1);
        }
    }

    let mut claude_files = Vec::new();
    let mut claude_non_jsonl = 0u64;
    discover_jsonl(&claude_root, &mut claude_files, &mut claude_non_jsonl)?;
    claude_files.sort();
    claude_files.dedup();
    for path in claude_files {
        let material_kind_face =
            if path.file_name().and_then(|name| name.to_str()) == Some("journal.jsonl") {
                "workflow-journal"
            } else if path
                .components()
                .any(|part| part.as_os_str() == "subagents")
            {
                "agent-branch"
            } else {
                "exchange-main"
            };
        specs.push(ExchangeContainerSpec {
            locator: path,
            provider_face: "claude-code".to_owned(),
            material_kind_face: material_kind_face.to_owned(),
        });
    }
    specs.sort_by(|left, right| left.locator.cmp(&right.locator));
    if specs.is_empty() {
        return Err(
            "the complete exchange discovery returned no authorized JSONL container".into(),
        );
    }
    Ok(CompleteExchangeSource {
        schema: "soma-life.complete-exchange-source.v1".to_owned(),
        workspace,
        codex_root,
        claude_root,
        specs,
        excluded_codex_other_workspace,
        excluded_non_jsonl: codex_non_jsonl.saturating_add(claude_non_jsonl),
    })
}

/// Project visible user/assistant faces through exact `(container, raw range)` incidence. The
/// lookup is formed once; it does not rescan every richer record for every message.
pub fn attach_visible_exchange_faces(
    world: &mut ExchangeWorldTube,
) -> Result<VisibleProjectionReceipt, String> {
    let record_lookup = world
        .records
        .iter()
        .enumerate()
        .map(|(at, record)| {
            (
                (
                    record.container,
                    record.raw_range.start,
                    record.raw_range.end,
                ),
                at as u64,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut faces = Vec::new();
    let mut controls = 0u64;
    let mut probes = 0u64;
    for container in &world.containers {
        if container.lineage.provider == "codex" {
            let dialogue = ExactDialogueLineage::import_codex_rollout_prefix(
                &container.lineage.locator,
                container.captured_extent,
                &CodexDialogueImportSpec::default(),
            )?;
            controls =
                controls.saturating_add(dialogue.receipt().excluded_control_occurrences as u64);
            for occurrence in dialogue.occurrences() {
                probes = probes.saturating_add(1);
                let record = record_lookup
                    .get(&(
                        container.ordinal,
                        occurrence.raw_range.start,
                        occurrence.raw_range.end,
                    ))
                    .copied()
                    .ok_or_else(|| missing_record(container.ordinal, &occurrence.raw_range))?;
                faces.push(VisibleMessageFace {
                    container: container.ordinal,
                    record,
                    raw_range: occurrence.raw_range.clone(),
                    occurrence: occurrence.identity.clone(),
                    text_sha256: Digest32::of(occurrence.text.as_bytes()),
                    text: occurrence.text.clone(),
                    provider_face: "codex".to_owned(),
                    speaker_face: speaker(occurrence.speaker).to_owned(),
                    phase_face: match &occurrence.phase {
                        DialoguePhase::Received => "received",
                        DialoguePhase::Commentary => "commentary",
                        DialoguePhase::FinalAnswer => "final-answer",
                        DialoguePhase::Other(_) => "other",
                    }
                    .to_owned(),
                });
            }
        } else {
            let (visible, receipt) = import_claude_visible_prefix(
                &container.lineage.locator,
                container.captured_extent,
            )?;
            controls = controls.saturating_add(receipt.excluded_control_occurrences as u64);
            for occurrence in visible {
                probes = probes.saturating_add(1);
                let record = record_lookup
                    .get(&(
                        container.ordinal,
                        occurrence.raw_range.start,
                        occurrence.raw_range.end,
                    ))
                    .copied()
                    .ok_or_else(|| missing_record(container.ordinal, &occurrence.raw_range))?;
                faces.push(VisibleMessageFace {
                    container: container.ordinal,
                    record,
                    raw_range: occurrence.raw_range,
                    occurrence: occurrence.identity,
                    text_sha256: Digest32::of(occurrence.text.as_bytes()),
                    text: occurrence.text,
                    provider_face: "claude-code".to_owned(),
                    speaker_face: speaker(occurrence.speaker).to_owned(),
                    phase_face: "visible".to_owned(),
                });
            }
        }
    }
    let population = faces.len();
    world.attach_visible_messages(faces, controls)?;
    let factored = world.visible_messages.iter().all(|face| {
        world
            .records
            .get(face.record as usize)
            .is_some_and(|record| {
                record.container == face.container && record.raw_range == face.raw_range
            })
    });
    Ok(VisibleProjectionReceipt {
        schema: "soma-life.complete-exchange-visible-projection.v1".to_owned(),
        visible_messages: population,
        excluded_visible_controls: controls,
        every_face_factors_through_one_richer_record: factored,
        record_lookup_probes: probes,
    })
}

fn codex_workspace(path: &Path) -> Result<Option<PathBuf>, String> {
    let input = File::open(path).map_err(|error| format!("open {}: {error}", path.display()))?;
    for (record, line) in BufReader::new(input).lines().enumerate() {
        let line =
            line.map_err(|error| format!("read {} record {record}: {error}", path.display()))?;
        if line.trim().is_empty() {
            continue;
        }
        let value: Value = serde_json::from_str(&line)
            .map_err(|error| format!("parse {} record {record}: {error}", path.display()))?;
        if value.get("type").and_then(Value::as_str) != Some("session_meta") {
            continue;
        }
        return Ok(value
            .pointer("/payload/cwd")
            .and_then(Value::as_str)
            .map(PathBuf::from));
    }
    Ok(None)
}

fn discover_jsonl(
    root: &Path,
    out: &mut Vec<PathBuf>,
    excluded_non_jsonl: &mut u64,
) -> Result<(), String> {
    for entry in fs::read_dir(root).map_err(|error| format!("read {}: {error}", root.display()))? {
        let entry = entry.map_err(|error| format!("read {} entry: {error}", root.display()))?;
        let kind = entry
            .file_type()
            .map_err(|error| format!("inspect {}: {error}", entry.path().display()))?;
        if kind.is_dir() {
            discover_jsonl(&entry.path(), out, excluded_non_jsonl)?;
        } else if kind.is_file()
            && entry.path().extension().and_then(|value| value.to_str()) == Some("jsonl")
        {
            out.push(entry.path());
        } else if kind.is_file() {
            *excluded_non_jsonl = excluded_non_jsonl.saturating_add(1);
        }
    }
    Ok(())
}

fn missing_record(container: u32, range: &std::ops::Range<u64>) -> String {
    format!(
        "container {container} has no richer record at {}..{}",
        range.start, range.end
    )
}

fn speaker(speaker: DialogueSpeaker) -> &'static str {
    match speaker {
        DialogueSpeaker::User => "user",
        DialogueSpeaker::Assistant => "assistant",
    }
}
