use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    ops::Bound::{Excluded, Unbounded},
    path::{Path, PathBuf},
};

use holonic_engine::{CpuExecutionError, CpuExecutor};
use holonic_structure::{LocalSequence, LocalSet};
use serde::Serialize;

use crate::causal_language::{lexical_tokens, render_tokens};

use super::{
    text_features, LaboratoryInformantPort, LaboratoryLanguageError, LaboratoryResearchLeader,
    LaboratoryReturnedSection, LaboratorySourceKind, LaboratoryWorldContactAttempt,
    LaboratoryWorldContactOutcome, LaboratoryWorldContactRequest, LaboratoryWorldContactReturn,
    LaboratoryWorldReturn,
};

const THEORY_RECEIVER_BASE: u64 = 10_000;
const CODE_RECEIVER_BASE: u64 = 1_000_000;

#[derive(Debug)]
pub(super) struct LaboratorySourceSection {
    pub(super) identity: String,
    pub(super) source: String,
    pub(super) receiver: u64,
    pub(super) line: usize,
    pub(super) kind: LaboratorySourceKind,
    pub(super) text: String,
    pub(super) features: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryAtlasReceipt {
    pub source_files: usize,
    /// Source inscriptions deliberately outside this atlas' causal boundary.  This is part of
    /// the receipt so a grading transcript cannot silently condition the rerun which grades it.
    pub excluded_sources: BTreeSet<String>,
    pub theory_sections: usize,
    pub rust_source_sections: usize,
    pub indexed_features: usize,
}

#[derive(Debug)]
pub struct LaboratorySourceAtlas {
    pub(super) sections: Vec<LaboratorySourceSection>,
    pub(super) feature_incidence: BTreeMap<String, BTreeSet<usize>>,
    pub(super) receipt: LaboratoryAtlasReceipt,
}

impl LaboratorySourceAtlas {
    /// Mount every research/paper inscription and every Rust source beneath the repository's
    /// production roots. Build output, observations, and run artifacts are not source receivers.
    pub fn mount_repository(root: &Path) -> Result<Self, LaboratoryLanguageError> {
        Self::mount_repository_excluding(root, &BTreeSet::new())
    }

    /// Mount the repository beneath an explicit source boundary.
    ///
    /// Exclusion is causal lineage, not a lexical filter: the named files never become atlas
    /// sections.  The grading instrument uses this to keep its own after-the-fact transcript from
    /// becoming inherited testimony on a later rerun.
    pub fn mount_repository_excluding(
        root: &Path,
        excluded_sources: &BTreeSet<String>,
    ) -> Result<Self, LaboratoryLanguageError> {
        let mut theory_paths = Vec::new();
        receive_paths(&root.join("src/soma/RESEARCH"), &["md"], &mut theory_paths)?;
        receive_paths(
            &root.join("src/soma/PAPERS"),
            &["md", "typ"],
            &mut theory_paths,
        )?;
        theory_paths.sort();
        theory_paths.dedup();

        let mut rust_paths = Vec::new();
        receive_paths(&root.join("crates"), &["rs"], &mut rust_paths)?;
        receive_paths(&root.join("src/soma"), &["rs"], &mut rust_paths)?;
        rust_paths.retain(|path| !path.components().any(|part| part.as_os_str() == "target"));
        rust_paths.sort();
        rust_paths.dedup();

        let mut sections = Vec::new();
        let mut source_files = 0usize;
        for (source_at, path) in theory_paths.iter().enumerate() {
            let receiver = THEORY_RECEIVER_BASE
                .checked_add(
                    u64::try_from(source_at).map_err(|_| LaboratoryLanguageError::CarrierExtent)?,
                )
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            let source = relative_source(root, path);
            if excluded_sources.contains(&source) {
                continue;
            }
            source_files = source_files
                .checked_add(1)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            let text = fs::read_to_string(path).map_err(|error| {
                LaboratoryLanguageError::Io(format!("read {}: {error}", path.display()))
            })?;
            receive_theory_sections(&source, receiver, &text, &mut sections)?;
        }

        for (source_at, path) in rust_paths.iter().enumerate() {
            let receiver = CODE_RECEIVER_BASE
                .checked_add(
                    u64::try_from(source_at).map_err(|_| LaboratoryLanguageError::CarrierExtent)?,
                )
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            let source = relative_source(root, path);
            if excluded_sources.contains(&source) {
                continue;
            }
            source_files = source_files
                .checked_add(1)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            let text = fs::read_to_string(path).map_err(|error| {
                LaboratoryLanguageError::Io(format!("read {}: {error}", path.display()))
            })?;
            receive_native_code_sections(&source, receiver, &text, &mut sections)?;
        }

        sections.sort_by(|left, right| {
            (
                left.receiver,
                left.source.as_str(),
                left.line,
                left.identity.as_str(),
            )
                .cmp(&(
                    right.receiver,
                    right.source.as_str(),
                    right.line,
                    right.identity.as_str(),
                ))
        });
        sections.dedup_by(|left, right| left.identity == right.identity);
        let mut feature_incidence = BTreeMap::<String, BTreeSet<usize>>::new();
        for (section_at, section) in sections.iter().enumerate() {
            for feature in &section.features {
                feature_incidence
                    .entry(feature.clone())
                    .or_default()
                    .insert(section_at);
            }
        }
        let receipt = LaboratoryAtlasReceipt {
            source_files,
            excluded_sources: excluded_sources.clone(),
            theory_sections: sections
                .iter()
                .filter(|section| section.kind == LaboratorySourceKind::Theory)
                .count(),
            rust_source_sections: sections
                .iter()
                .filter(|section| section.kind == LaboratorySourceKind::RustSource)
                .count(),
            indexed_features: feature_incidence.len(),
        };
        Ok(Self {
            sections,
            feature_incidence,
            receipt,
        })
    }

    pub const fn receipt(&self) -> &LaboratoryAtlasReceipt {
        &self.receipt
    }

    pub fn enact(
        &self,
        leader: &LaboratoryResearchLeader,
    ) -> Result<LaboratoryWorldReturn, LaboratoryLanguageError> {
        // Merge the already-sorted local feature incidences without constructing a candidate
        // population.  The retained frontier is bounded by the receiver aperture plus one cursor
        // per requested feature; source population and query result remain distinct.
        let mut cursors = LocalSequence::<(String, Option<usize>)>::new();
        for feature in &leader.region {
            if self.feature_incidence.contains_key(feature) {
                cursors.push((feature.to_owned(), None));
            }
        }
        let mut selected = LocalSequence::<(usize, LocalSet<String>)>::new();
        let mut complete_population = 0usize;
        loop {
            let mut next_section = None;
            for (feature, prior) in &cursors {
                let incidence = self
                    .feature_incidence
                    .get(feature)
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?;
                let next = match prior {
                    Some(prior) => incidence
                        .range((Excluded(*prior), Unbounded))
                        .next()
                        .copied(),
                    None => incidence.iter().next().copied(),
                };
                if let Some(next) = next {
                    next_section =
                        Some(next_section.map_or(next, |current: usize| current.min(next)));
                }
            }
            let Some(section_at) = next_section else {
                break;
            };
            complete_population = complete_population
                .checked_add(1)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            let section = self
                .sections
                .get(section_at)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            let mut matched = LocalSet::new();
            for feature in &leader.region {
                if section.features.contains(feature) {
                    matched.insert(feature.to_owned());
                }
            }
            selected.push((section_at, matched));
            if selected.len() > leader.aperture {
                return Err(LaboratoryLanguageError::ReceiverAperture {
                    leader: leader.identity.clone(),
                    encountered_population: selected.len(),
                    aperture: leader.aperture,
                });
            }
            for (feature, prior) in &mut cursors {
                let incidence = self
                    .feature_incidence
                    .get(feature)
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?;
                let next = match prior {
                    Some(prior) => incidence
                        .range((Excluded(*prior), Unbounded))
                        .next()
                        .copied(),
                    None => incidence.iter().next().copied(),
                };
                if next == Some(section_at) {
                    *prior = Some(section_at);
                }
            }
        }
        let selected_population = selected.len();
        let mut sections = Vec::with_capacity(selected_population);
        for (section_at, matched_features) in selected {
            let section = self
                .sections
                .get(section_at)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            sections.push(LaboratoryReturnedSection {
                identity: format!("{}/{}", leader.identity, section.identity),
                source_identity: section.identity.to_owned(),
                source: section.source.to_owned(),
                receiver: section.receiver,
                line: section.line,
                kind: section.kind,
                text: section.text.to_owned(),
                matched_features: matched_features.into_iter().collect(),
            });
        }
        Ok(LaboratoryWorldReturn {
            leader: leader.identity.clone(),
            sections,
            complete_population,
            omitted_population: complete_population.saturating_sub(selected_population),
        })
    }

    /// Enact one immutable repository contact for every co-present leader through the existing
    /// deterministic CPU owner. Each task reads the same mounted source atlas; results return in
    /// stable leader order and no worker completion order enters source chronology.
    pub fn enact_contact_front_with_cpu(
        &self,
        requests: &[LaboratoryWorldContactRequest],
        executor: &CpuExecutor,
    ) -> LaboratoryWorldContactAttempt {
        let execution = executor.execute_indexed(requests, |_request_at, request| {
            if request.port != LaboratoryInformantPort::RepositorySource {
                return Ok::<_, std::convert::Infallible>(
                    LaboratoryWorldContactOutcome::Obstructed {
                        identity: request.identity.to_owned(),
                        obstruction: format!("repository atlas cannot enact {:?}", request.port),
                    },
                );
            }
            Ok(match self.enact(&request.leader) {
                Ok(returned) => {
                    LaboratoryWorldContactOutcome::Returned(LaboratoryWorldContactReturn {
                        identity: request.identity.clone(),
                        leader: request.leader.identity.clone(),
                        port: request.port,
                        returned,
                    })
                }
                Err(error) => LaboratoryWorldContactOutcome::Obstructed {
                    identity: request.identity.to_owned(),
                    obstruction: format!("{error:?}"),
                },
            })
        });
        match execution {
            Ok((outcomes, receipt)) => LaboratoryWorldContactAttempt {
                outcomes: LocalSequence::from_iter(outcomes),
                execution: Some(receipt),
            },
            Err(CpuExecutionError::WorkerPanicked) => LaboratoryWorldContactAttempt {
                outcomes: requests
                    .iter()
                    .map(|request| LaboratoryWorldContactOutcome::Obstructed {
                        identity: request.identity.to_owned(),
                        obstruction: "repository contact worker panicked".to_owned(),
                    })
                    .collect(),
                execution: None,
            },
            Err(CpuExecutionError::Operation(never)) => match never {},
        }
    }
}

fn receive_paths(
    root: &Path,
    extensions: &[&str],
    paths: &mut Vec<PathBuf>,
) -> Result<(), LaboratoryLanguageError> {
    if !root.exists() {
        return Ok(());
    }
    let mut entries = fs::read_dir(root)
        .map_err(|error| LaboratoryLanguageError::Io(format!("read {}: {error}", root.display())))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| {
            LaboratoryLanguageError::Io(format!("read {}: {error}", root.display()))
        })?;
    entries.sort_by_key(|entry| entry.path());
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            receive_paths(&path, extensions, paths)?;
        } else if path
            .extension()
            .and_then(|extension| extension.to_str())
            .is_some_and(|extension| extensions.contains(&extension))
        {
            paths.push(path);
        }
    }
    Ok(())
}

fn relative_source(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}

fn receive_theory_sections(
    source: &str,
    receiver: u64,
    text: &str,
    sections: &mut Vec<LaboratorySourceSection>,
) -> Result<(), LaboratoryLanguageError> {
    let mut paragraph = String::new();
    let mut paragraph_line = 1usize;
    for (line_at, line) in text.lines().enumerate() {
        let line_number = line_at
            .checked_add(1)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        let trimmed = line.trim();
        let boundary = trimmed.is_empty()
            || trimmed.starts_with('#')
            || trimmed.starts_with("```")
            || trimmed.starts_with('|')
            || trimmed.starts_with("http://")
            || trimmed.starts_with("https://")
            || trimmed.starts_with("#let ")
            || trimmed.starts_with("#show ")
            || trimmed.starts_with('$');
        if boundary {
            receive_paragraph_sections(source, receiver, paragraph_line, &paragraph, sections)?;
            paragraph.clear();
            paragraph_line = line_number.saturating_add(1);
            continue;
        }
        let prose = trimmed
            .strip_prefix("- ")
            .or_else(|| trimmed.strip_prefix("* "))
            .unwrap_or(trimmed);
        if paragraph.is_empty() {
            paragraph_line = line_number;
        } else {
            paragraph.push(' ');
        }
        paragraph.push_str(prose);
    }
    receive_paragraph_sections(source, receiver, paragraph_line, &paragraph, sections)
}

fn receive_paragraph_sections(
    source: &str,
    receiver: u64,
    line: usize,
    paragraph: &str,
    sections: &mut Vec<LaboratorySourceSection>,
) -> Result<(), LaboratoryLanguageError> {
    let mut current = Vec::<String>::new();
    let mut sentence_at = 0usize;
    for token in lexical_tokens(paragraph) {
        current.push(token.clone());
        if matches!(token.as_str(), "." | "!" | "?") {
            receive_theory_sentence(source, receiver, line, sentence_at, &current, sections)?;
            sentence_at = sentence_at
                .checked_add(1)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            current.clear();
        }
    }
    if !current.is_empty() {
        receive_theory_sentence(source, receiver, line, sentence_at, &current, sections)?;
    }
    Ok(())
}

fn receive_theory_sentence(
    source: &str,
    receiver: u64,
    line: usize,
    sentence_at: usize,
    tokens: &[String],
    sections: &mut Vec<LaboratorySourceSection>,
) -> Result<(), LaboratoryLanguageError> {
    let words = tokens
        .iter()
        .filter(|token| token.chars().any(char::is_alphanumeric))
        .count();
    if !(5..=96).contains(&words) {
        return Ok(());
    }
    let text = render_tokens(tokens.iter().map(String::as_str));
    receive_section(
        format!("{}::theory::{line}:{sentence_at}", source),
        source.to_owned(),
        receiver,
        line,
        LaboratorySourceKind::Theory,
        text,
        sections,
    )
}

/// Retain Rust as source-native code sections. The atlas does not translate ownership, calls, or
/// constructor syntax into authored English conclusions; those relations must be enacted by a
/// receiving codec/current if they matter to a later deed.
fn receive_native_code_sections(
    source: &str,
    receiver: u64,
    text: &str,
    sections: &mut Vec<LaboratorySourceSection>,
) -> Result<(), LaboratoryLanguageError> {
    const BLOCK_LINES: usize = 24;
    let mut block = String::new();
    let mut block_start = 1usize;
    let mut block_lines = 0usize;
    for (line_at, line) in text.lines().enumerate() {
        let line_number = line_at
            .checked_add(1)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        let boundary = line.trim().is_empty() || block_lines == BLOCK_LINES;
        if boundary && !block.is_empty() {
            receive_section(
                format!("{source}::rust-source::{block_start}"),
                source.to_owned(),
                receiver,
                block_start,
                LaboratorySourceKind::RustSource,
                std::mem::take(&mut block),
                sections,
            )?;
            block_lines = 0;
        }
        if line.trim().is_empty() {
            continue;
        }
        if block.is_empty() {
            block_start = line_number;
        } else {
            block.push('\n');
        }
        block.push_str(line);
        block_lines = block_lines
            .checked_add(1)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
    }
    if !block.is_empty() {
        receive_section(
            format!("{source}::rust-source::{block_start}"),
            source.to_owned(),
            receiver,
            block_start,
            LaboratorySourceKind::RustSource,
            block,
            sections,
        )?;
    }
    Ok(())
}

fn receive_section(
    identity: String,
    source: String,
    receiver: u64,
    line: usize,
    kind: LaboratorySourceKind,
    text: String,
    sections: &mut Vec<LaboratorySourceSection>,
) -> Result<(), LaboratoryLanguageError> {
    if text.is_empty() {
        return Ok(());
    }
    let mut features = text_features(&text);
    features.extend(text_features(&source));
    sections.push(LaboratorySourceSection {
        identity,
        source,
        receiver,
        line,
        kind,
        text,
        features,
    });
    Ok(())
}
