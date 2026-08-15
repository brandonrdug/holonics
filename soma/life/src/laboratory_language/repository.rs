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

/// One borrowed source-native reading exposed by the mounted atlas.
///
/// This is the atlas's inherited material, not a research return.  Exposing it lets another
/// existing mouth compose the exact readings without reopening the repository or guessing the
/// atlas's section law.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaboratorySourceReading<'a> {
    pub identity: &'a str,
    pub source: &'a str,
    pub receiver: u64,
    pub line: usize,
    pub kind: LaboratorySourceKind,
    pub text: &'a str,
}

/// Which roots beneath a repository this atlas mounts, and under which extensions.
///
/// **These are the caller's declaration, not the organ's.** They were authored inside
/// `mount_repository_excluding` as `src/soma/RESEARCH`, `src/soma/PAPERS` and `src/soma` until
/// 2026-08-10 — the archived laboratory's directory layout, which resolves to nothing in this
/// body. The measured consequence was silent rather than loud: the atlas mounted `crates/` (which
/// both layouts happen to share), reported **220 source files and 15,102 Rust sections**, and
/// returned `theory_sections: 0` while the whole `soma/` tree and every research record went
/// unseen. A blind atlas that returns a large number reads exactly like a working one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaboratorySourceRoots {
    /// Roots whose `md`/`typ` inscriptions become theory sections.
    pub theory: Vec<PathBuf>,
    /// Roots whose `rs` sources become code sections.
    pub code: Vec<PathBuf>,
}

impl Default for LaboratorySourceRoots {
    /// This body's layout.
    fn default() -> Self {
        Self {
            theory: vec![PathBuf::from("research/records"), PathBuf::from("papers")],
            code: vec![PathBuf::from("crates"), PathBuf::from("soma")],
        }
    }
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
        Self::mount_repository_roots(root, &LaboratorySourceRoots::default(), excluded_sources)
    }

    /// Mount the repository beneath roots the caller declares.
    pub fn mount_repository_roots(
        root: &Path,
        roots: &LaboratorySourceRoots,
        excluded_sources: &BTreeSet<String>,
    ) -> Result<Self, LaboratoryLanguageError> {
        if roots.theory.is_empty() && roots.code.is_empty() {
            return Err(LaboratoryLanguageError::Io(
                "an atlas mounted over no declared root receives nothing".to_owned(),
            ));
        }
        let mut theory_paths = Vec::new();
        // Every declared root must resolve. A root that does not exist is a caller error and it is
        // refused by name; silently indexing nothing is how a mount reports a path defect as a
        // failure of the question.
        for relative in roots.theory.iter().chain(roots.code.iter()) {
            if !root.join(relative).exists() {
                return Err(LaboratoryLanguageError::DeclaredRootIsAbsent {
                    root: relative.display().to_string(),
                    beneath: root.display().to_string(),
                });
            }
        }
        for relative in &roots.theory {
            receive_paths(&root.join(relative), &["md", "typ"], &mut theory_paths)?;
        }
        theory_paths.sort();
        theory_paths.dedup();

        let mut rust_paths = Vec::new();
        for relative in &roots.code {
            receive_paths(&root.join(relative), &["rs"], &mut rust_paths)?;
        }
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

    /// Read every inherited section in the atlas's deterministic receiver/source order.
    pub fn source_readings(&self) -> impl ExactSizeIterator<Item = LaboratorySourceReading<'_>> {
        self.sections.iter().map(|section| LaboratorySourceReading {
            identity: &section.identity,
            source: &section.source,
            receiver: section.receiver,
            line: section.line,
            kind: section.kind,
            text: &section.text,
        })
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
    if root.is_file() {
        if root
            .extension()
            .and_then(|extension| extension.to_str())
            .is_some_and(|extension| extensions.contains(&extension))
        {
            paths.push(root.to_owned());
        }
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
    // A sentence is received when it carries a word.  This is a predicate on the material, not a
    // length: the retired form was `if !(5..=96).contains(&words) { return Ok(()) }`, two authored
    // levels that SILENTLY DELETED every theory sentence below five or above ninety-six
    // alphanumeric tokens.  Nothing derived either bound, and a deletion that returns no receipt is
    // the species `CLAUDE.md` §9 forbids outright — the artifact is the return.  The sentence
    // boundary itself is already the source's own (`receive_paragraph_sections`: `.`, `!`, `?`).
    let carries_a_word = tokens
        .iter()
        .any(|token| token.chars().any(char::is_alphanumeric));
    if !carries_a_word {
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
///
/// The section boundary is read off the source's own delimiters, never counted: a blank line, or
/// **the brace depth returning to zero**. Both are lexical facts about the file, in the same sense
/// that `.`/`!`/`?` are the theory sentence's boundary; neither is an authored English conclusion
/// about what the code means.
///
/// Stated exactly, because the code governs the name: the second boundary fires on the line where a
/// brace group that was opened during or before it closes and leaves the depth at zero. That is a
/// multi-line item body ending, and it is equally `use a::{b, c};`, whose braces open and close on
/// one line. No attempt is made to tell those apart — telling them apart is parsing, and the atlas
/// does not parse.
///
/// The retired form carried `const BLOCK_LINES: usize = 24` and cut a blank-line-free run at
/// twenty-four lines. Nothing derived twenty-four, and it decided the section population and so the
/// feature incidence a leader recruits over.
fn receive_native_code_sections(
    source: &str,
    receiver: u64,
    text: &str,
    sections: &mut Vec<LaboratorySourceSection>,
) -> Result<(), LaboratoryLanguageError> {
    let closings = rust_item_closings(text);
    let mut block = String::new();
    let mut block_start = 1usize;
    for (line_at, line) in text.lines().enumerate() {
        let line_number = line_at
            .checked_add(1)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        let boundary = line.trim().is_empty()
            || closings
                .get(line_at.wrapping_sub(1))
                .copied()
                .unwrap_or(false);
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

/// One entry per line of `text`: did the brace depth stand positive during this line and return to
/// zero by its end?
///
/// A `}` inside a string, a raw string, a character literal or a comment is not a delimiter, so
/// those four are consumed as such before any brace is counted — `'{'` and `'}'` are exactly the
/// case that separates this from a brace counter. The scanner is deliberately not a parser: it
/// reads the delimiters and nothing about what they enclose.
fn rust_item_closings(text: &str) -> Vec<bool> {
    #[derive(Clone, Copy)]
    enum Mode {
        Code,
        LineComment,
        BlockComment(usize),
        Str,
        RawStr(usize),
    }

    let bytes = text.as_bytes();
    let mut closings = Vec::new();
    let mut mode = Mode::Code;
    let mut depth = 0usize;
    let mut entered = false;
    let mut at = 0usize;
    while at < bytes.len() {
        let byte = bytes[at];
        if byte == b'\n' {
            if let Mode::LineComment = mode {
                mode = Mode::Code;
            }
            closings.push(entered && depth == 0);
            entered = depth > 0;
            at += 1;
            continue;
        }
        match mode {
            Mode::LineComment => at += 1,
            Mode::BlockComment(nesting) => {
                if bytes[at..].starts_with(b"*/") {
                    mode = if nesting <= 1 {
                        Mode::Code
                    } else {
                        Mode::BlockComment(nesting - 1)
                    };
                    at += 2;
                } else if bytes[at..].starts_with(b"/*") {
                    mode = Mode::BlockComment(nesting + 1);
                    at += 2;
                } else {
                    at += 1;
                }
            }
            Mode::Str => {
                // an escape consumes the next byte, EXCEPT a newline: a `\`-continued string still
                // crosses a line, and the line tally must not lose it.
                if byte == b'\\' && bytes.get(at + 1).is_some_and(|&next| next != b'\n') {
                    at += 2;
                } else {
                    if byte == b'"' {
                        mode = Mode::Code;
                    }
                    at += 1;
                }
            }
            Mode::RawStr(hashes) => {
                if byte == b'"'
                    && bytes.len() >= at + 1 + hashes
                    && bytes[at + 1..at + 1 + hashes].iter().all(|&h| h == b'#')
                {
                    mode = Mode::Code;
                    at += 1 + hashes;
                } else {
                    at += 1;
                }
            }
            Mode::Code => {
                if let Some((width, hashes)) = raw_string_opening(bytes, at) {
                    mode = Mode::RawStr(hashes);
                    at += width;
                } else if bytes[at..].starts_with(b"//") {
                    mode = Mode::LineComment;
                    at += 2;
                } else if bytes[at..].starts_with(b"/*") {
                    mode = Mode::BlockComment(1);
                    at += 2;
                } else if byte == b'"' {
                    mode = Mode::Str;
                    at += 1;
                } else if byte == b'\'' {
                    at += character_literal_width(bytes, at);
                } else if byte == b'{' {
                    depth += 1;
                    entered = true;
                    at += 1;
                } else if byte == b'}' {
                    depth = depth.saturating_sub(1);
                    at += 1;
                } else {
                    at += 1;
                }
            }
        }
    }
    if !bytes.is_empty() && bytes[bytes.len() - 1] != b'\n' {
        closings.push(entered && depth == 0);
    }
    closings
}

/// The width of a raw-string opening at `at` (`r"`, `r#"`, `br##"`, `cr"`, …) with its hash count,
/// or `None` where this is not one. A raw string's closing quote is only closing when followed by
/// as many hashes as it opened with, so the count travels with the mode.
fn raw_string_opening(bytes: &[u8], at: usize) -> Option<(usize, usize)> {
    fn is_identifier_byte(byte: u8) -> bool {
        byte.is_ascii_alphanumeric() || byte == b'_' || byte >= 0x80
    }
    if at > 0 && is_identifier_byte(bytes[at - 1]) {
        return None;
    }
    let mut cursor = at;
    if matches!(bytes.get(cursor), Some(b'b') | Some(b'c')) {
        cursor += 1;
    }
    if bytes.get(cursor) != Some(&b'r') {
        return None;
    }
    cursor += 1;
    let mut hashes = 0usize;
    while bytes.get(cursor) == Some(&b'#') {
        hashes += 1;
        cursor += 1;
    }
    if bytes.get(cursor) != Some(&b'"') {
        return None;
    }
    Some((cursor + 1 - at, hashes))
}

/// The width of a character literal opening at `at`, or `1` where the quote opens a lifetime
/// instead. `'{'` and `'}'` are exactly the case that matters here: a naive counter reads them as
/// delimiters, and `'a` in a signature is not a literal at all.
fn character_literal_width(bytes: &[u8], at: usize) -> usize {
    match bytes.get(at + 1) {
        Some(b'\\') => {
            let mut cursor = at + 2;
            while let Some(&byte) = bytes.get(cursor) {
                if byte == b'\n' {
                    return 1;
                }
                if byte == b'\'' {
                    return cursor + 1 - at;
                }
                cursor += 1;
            }
            1
        }
        Some(b'\n') => 1,
        Some(&lead) => {
            let width = if lead < 0x80 {
                1
            } else if lead >> 5 == 0b110 {
                2
            } else if lead >> 4 == 0b1110 {
                3
            } else {
                4
            };
            if bytes.get(at + 1 + width) == Some(&b'\'') {
                2 + width
            } else {
                1
            }
        }
        None => 1,
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The control the delimiter reader has to beat: every `{`/`}` byte, wherever it sits.
    fn naive_closings(text: &str) -> Vec<bool> {
        let mut out = Vec::new();
        let mut depth = 0usize;
        let mut entered = false;
        for line in text.split_inclusive('\n') {
            for byte in line.bytes() {
                if byte == b'{' {
                    depth += 1;
                    entered = true;
                } else if byte == b'}' {
                    depth = depth.saturating_sub(1);
                }
            }
            if line.ends_with('\n') {
                out.push(entered && depth == 0);
                entered = depth > 0;
            }
        }
        if !text.is_empty() && !text.ends_with('\n') {
            out.push(entered && depth == 0);
        }
        out
    }

    /// A `}` inside a string, a raw string, a character literal or a comment is not a delimiter.
    /// Each stanza below is written so a brace counter gets it WRONG — the disagreement is the
    /// distinguishing word, and it is asserted rather than assumed.
    #[test]
    fn a_brace_in_a_literal_or_a_comment_is_not_a_delimiter() {
        let material = concat!(
            "fn a() -> char { '{' }\n",             // 1: a char literal open brace
            "fn b() -> char { '}' }\n",             // 2: a char literal close brace
            "fn c() -> &'static str { \"}}}\" }\n", // 3: braces in a string, and a lifetime
            "fn d() { /* } } */ }\n",               // 4: braces in a block comment
            "fn e() { // }\n",                      // 5: a line comment opens, body continues
            "}\n",                                  // 6: and closes here
            "fn f() -> &'static str { r#\"a \" } is not a close\"# }\n", // 7: a raw string
            "fn g() { /* /* nested */ } */ }\n",    // 8: nested block comments
            "fn h() -> &'static str { r#\"\n",      // 9: a raw string opening
            "} not a close\n",                      // 10: whose brace crosses a line
            "\"# }\n",                              // 11: and closes with the item
        );
        let read = rust_item_closings(material);
        let counted = naive_closings(material);
        assert_eq!(
            read.len(),
            material.lines().count(),
            "one closing entry per line"
        );
        assert_eq!(
            read,
            vec![true, true, true, true, false, true, true, true, false, false, true],
            "every brace-delimited group closes on the line its delimiter closes on"
        );
        assert_ne!(
            read, counted,
            "CONTROL REFUSES ITSELF: a brace counter agreed, so this material does not separate them"
        );
        let parting = read
            .iter()
            .zip(counted.iter())
            .position(|(a, b)| a != b)
            .expect("the two readers part somewhere");
        assert_eq!(parting, 0, "they part on the first character literal");
    }

    /// A `\`-continued string crosses a line, and the per-line tally must not lose it.
    #[test]
    fn a_continued_string_does_not_lose_its_line() {
        let material = "fn a() -> &'static str {\n    \"one \\\n     two\"\n}\nfn b() {}\n";
        let read = rust_item_closings(material);
        assert_eq!(read.len(), material.lines().count());
        assert_eq!(read, vec![false, false, false, true, true]);
    }

    /// The retired `BLOCK_LINES = 24` cut a blank-line-free run at twenty-four lines. The live law
    /// runs to the source's own boundary, so a longer run returns whole.
    #[test]
    fn a_blank_line_free_run_is_not_cut_at_a_count() {
        let mut material = String::from("//! a header with no blank line in it\n");
        for at in 0..40 {
            material.push_str(&format!("//! line {at}\n"));
        }
        material.push('\n');
        material.push_str("fn a() {}\n");
        let mut sections = Vec::new();
        receive_native_code_sections("declared", 1, &material, &mut sections).expect("sections");
        assert_eq!(sections.len(), 2, "the header and the item");
        assert_eq!(
            sections[0].text.lines().count(),
            41,
            "the whole run, not twenty-four of it"
        );
    }

    /// The retired `(5..=96)` silently dropped every theory sentence outside it. A sentence is now
    /// received when it carries a word.
    #[test]
    fn a_short_sentence_is_received_and_a_wordless_one_is_not() {
        let mut sections = Vec::new();
        receive_theory_sections("declared", 1, "Git is the log.\n", &mut sections)
            .expect("sections");
        assert_eq!(sections.len(), 1, "four words is a sentence");
        assert_eq!(sections[0].text, "Git is the log.");

        let mut wordless = Vec::new();
        receive_theory_sections("declared", 1, "... !\n", &mut wordless).expect("sections");
        assert!(
            wordless.is_empty(),
            "a sentence with no word in it is not a sentence"
        );
    }

    #[test]
    fn an_explicit_file_root_is_received_without_inventing_a_directory() {
        let serial = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "soma-laboratory-explicit-root-{}-{serial}",
            std::process::id()
        ));
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(
            root.join("authority.md"),
            "The declared file is material.\n",
        )
        .unwrap();
        let atlas = LaboratorySourceAtlas::mount_repository_roots(
            &root,
            &LaboratorySourceRoots {
                theory: vec![PathBuf::from("authority.md")],
                code: Default::default(),
            },
            &Default::default(),
        )
        .unwrap();
        assert_eq!(atlas.receipt().source_files, 1);
        assert_eq!(atlas.receipt().theory_sections, 1);
        let reading = atlas.source_readings().next().unwrap();
        assert_eq!(reading.source, "authority.md");
        assert_eq!(reading.text, "The declared file is material.");
        std::fs::remove_dir_all(root).unwrap();
    }
}
