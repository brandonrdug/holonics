//! Assemble the declared linguistic body, seal it at the form mouth, detach every source, and
//! return one actual reading through the resident CUDA chart.
//!
//! The construction composes three existing mouths: `text_material` for visible dialogue,
//! `LaboratorySourceAtlas` for declared repository roots, and `lean_development` for every Lean
//! source below `formal`.  The seal is the text body's own exact native rest.  A detached
//! child is run inside a mount namespace where the repository and both dialogue stores are empty;
//! it must reproduce the rest address and every aggregate Lean reading before the GPU deed counts.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufRead, BufReader, Read},
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::lean_development::{read_development, DeclarationGrain};
use life::{
    form_mouth::{content_address, deposit_form_or_message},
    laboratory_language::{
        LaboratoryAtlasReceipt, LaboratoryResearchLeader, LaboratorySourceAtlas,
        LaboratorySourceRoots,
    },
    text_material::{
        ExactTextMaterialAtlas, ExactTextMaterialCorpus, ParsedTextDocument, TextMaterialInput,
    },
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const DRIVER: &str = "the_material_mouth_seals_the_declared_body";
const REST_FORM: &str = "declared-corpus-native-rest";
const SEMANTIC_FORM: &str = "source-detached-semantic-return";
const APPARATUS_FORM: &str = "source-detached-apparatus-receipt";
const GRADE_FORM: &str = "material-mouth-grade";
const RECEIVER_FEATURE: &str = "exacttextmaterialatlas";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct LeanReadingReceipt {
    files: usize,
    source_bytes: u64,
    declarations: usize,
    unopened: usize,
    commentary_terms: usize,
    preamble_terms: usize,
    scoping_terms: usize,
    ambiguous_short_names: usize,
    reading_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct DetachedExpectation {
    rest_address: String,
    lean: LeanReadingReceipt,
    source_roots: Vec<PathBuf>,
}

#[derive(Debug, Serialize)]
struct SourceSnapshotReceipt {
    codex_main_rollouts: usize,
    codex_delegated_rollouts_excluded: usize,
    codex_rollout_bytes: u64,
    claude_main_sessions: usize,
    claude_session_bytes: u64,
    laboratory: LaboratoryAtlasReceipt,
    lean: LeanReadingReceipt,
}

enum Mode {
    Build {
        workspace: PathBuf,
        codex_root: PathBuf,
        claude_root: PathBuf,
    },
    Detached {
        form: PathBuf,
        expectation: DetachedExpectation,
    },
}

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    match arguments()? {
        Mode::Build {
            workspace,
            codex_root,
            claude_root,
        } => build(&workspace, &codex_root, &claude_root),
        Mode::Detached { form, expectation } => detached(&form, &expectation),
    }
}

fn arguments() -> Result<Mode, String> {
    let mut arguments = std::env::args().skip(1);
    let Some(first) = arguments.next() else {
        return Err("usage: --workspace PATH --codex-root PATH --claude-root PATH".to_owned());
    };
    if first == "--detached" {
        let form = arguments
            .next()
            .map(PathBuf::from)
            .ok_or_else(|| "--detached requires a form".to_owned())?;
        let encoded = arguments
            .next()
            .ok_or_else(|| "--detached requires its expectation".to_owned())?;
        if arguments.next().is_some() {
            return Err("unexpected detached argument".to_owned());
        }
        let expectation = serde_json::from_str(&encoded)
            .map_err(|error| format!("read detached expectation: {error}"))?;
        return Ok(Mode::Detached { form, expectation });
    }
    let mut workspace = None;
    let mut codex_root = None;
    let mut claude_root = None;
    let mut flag = Some(first);
    while let Some(named) = flag.take().or_else(|| arguments.next()) {
        let value = arguments
            .next()
            .map(PathBuf::from)
            .ok_or_else(|| format!("{named} requires a path"))?;
        match named.as_str() {
            "--workspace" => workspace = Some(value),
            "--codex-root" => codex_root = Some(value),
            "--claude-root" => claude_root = Some(value),
            _ => return Err(format!("unknown argument {named}")),
        }
    }
    Ok(Mode::Build {
        workspace: workspace.ok_or_else(|| "missing --workspace".to_owned())?,
        codex_root: codex_root.ok_or_else(|| "missing --codex-root".to_owned())?,
        claude_root: claude_root.ok_or_else(|| "missing --claude-root".to_owned())?,
    })
}

fn build(workspace: &Path, codex_root: &Path, claude_root: &Path) -> Result<(), String> {
    let workspace = workspace
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", workspace.display()))?;
    let codex_root = codex_root
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", codex_root.display()))?;
    let claude_root = claude_root
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", claude_root.display()))?;

    let all_rollouts = files_below(&codex_root.join("sessions"), |path| {
        path.file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with("rollout-") && name.ends_with(".jsonl"))
    })?;
    let mut codex_rollouts = Vec::new();
    for path in &all_rollouts {
        if is_main_codex_rollout(path)? {
            codex_rollouts.push(path.to_owned());
        }
    }
    let claude_sessions = claude_main_sessions(&claude_root.join("projects"))?;
    let codex_history = codex_root.join("history.jsonl");
    let claude_history = claude_root.join("history.jsonl");
    if codex_rollouts.is_empty()
        || claude_sessions.is_empty()
        || !codex_history.is_file()
        || !claude_history.is_file()
    {
        return Err("one or more declared dialogue populations are absent".to_owned());
    }

    let mut inputs = Vec::new();
    for path in &codex_rollouts {
        inputs.push(TextMaterialInput::CodexRollout(path.to_owned()));
    }
    inputs.push(TextMaterialInput::CodexHistory(codex_history));
    for path in &claude_sessions {
        inputs.push(TextMaterialInput::ClaudeCode(path.to_owned()));
    }
    inputs.push(TextMaterialInput::ClaudeHistory(claude_history));

    let roots = LaboratorySourceRoots {
        theory: vec![
            PathBuf::from("AGENTS.md"),
            PathBuf::from("CLAUDE.md"),
            PathBuf::from("CONSTRUCTION_STATE.md"),
            PathBuf::from("canon"),
            PathBuf::from("blueprint"),
            PathBuf::from("research/records"),
            PathBuf::from("papers"),
        ],
        code: vec![PathBuf::from("crates"), PathBuf::from("soma")],
    };
    let laboratory =
        LaboratorySourceAtlas::mount_repository_roots(&workspace, &roots, &BTreeSet::new())
            .map_err(|error| format!("mount declared repository atlas: {error:?}"))?;
    let laboratory_receipt = laboratory.receipt().to_owned();
    let mut laboratory_documents = BTreeMap::<String, Vec<String>>::new();
    for reading in laboratory.source_readings() {
        laboratory_documents
            .entry(reading.source.to_owned())
            .or_default()
            .push(reading.text.to_owned());
    }
    let mut documents = Vec::with_capacity(laboratory_documents.len());
    for (source, sections) in laboratory_documents {
        documents.push(ParsedTextDocument {
            identity: format!("laboratory:{source}"),
            source,
            sections,
        });
    }
    drop(laboratory);

    let (lean_documents, lean_receipt) = lean_documents(&workspace.join("formal"))?;
    documents.extend(lean_documents);
    let snapshot = SourceSnapshotReceipt {
        codex_main_rollouts: codex_rollouts.len(),
        codex_delegated_rollouts_excluded: all_rollouts.len() - codex_rollouts.len(),
        codex_rollout_bytes: file_extent(&codex_rollouts)?,
        claude_main_sessions: claude_sessions.len(),
        claude_session_bytes: file_extent(&claude_sessions)?,
        laboratory: laboratory_receipt,
        lean: lean_receipt.to_owned(),
    };

    println!("MATERIAL MOUTH — declared source snapshot");
    println!(
        "{}",
        serde_json::to_string_pretty(&snapshot)
            .map_err(|error| format!("render source receipt: {error}"))?
    );
    let corpus =
        ExactTextMaterialCorpus::import(inputs, &documents, usize::from(!documents.is_empty()))
            .map_err(|error| format!("assemble exact text corpus: {error:?}"))?;
    drop(documents);
    let corpus_receipt = corpus.receipt().to_owned();
    println!(
        "corpus receipt\n{}",
        serde_json::to_string_pretty(&corpus_receipt)
            .map_err(|error| format!("render corpus receipt: {error}"))?
    );
    let atlas = ExactTextMaterialAtlas::condition(corpus)
        .map_err(|error| format!("condition exact text atlas: {error:?}"))?;
    let atlas_receipt = atlas.receipt().to_owned();
    println!(
        "atlas receipt\n{}",
        serde_json::to_string_pretty(&atlas_receipt)
            .map_err(|error| format!("render atlas receipt: {error}"))?
    );

    let native = atlas
        .encode_native_bytes()
        .map_err(|error| format!("encode native text rest: {error:?}"))?;
    let deposited = deposit_form_or_message(DRIVER, REST_FORM, &native)?;
    if deposited.octets != native {
        return Err("form mouth returned different native octets".to_owned());
    }
    let reopened = ExactTextMaterialAtlas::from_native_bytes(&deposited.octets)
        .map_err(|error| format!("reopen deposited native rest: {error:?}"))?;
    if reopened != atlas {
        return Err("deposited rest did not reproduce every text reading".to_owned());
    }
    drop(reopened);
    drop(atlas);
    drop(native);
    let rest_path = deposited
        .path
        .canonicalize()
        .map_err(|error| format!("resolve deposited rest: {error}"))?;
    let rest_address = deposited.address;
    drop(deposited.octets);

    let expectation = DetachedExpectation {
        rest_address: rest_address.to_owned(),
        lean: lean_receipt,
        source_roots: vec![workspace, codex_root, claude_root],
    };
    let returned = run_detached(&rest_path, &expectation)?;
    inspect_detached_return(&returned)?;
    let semantic = returned
        .get("semantic")
        .ok_or_else(|| "detached return omitted semantics".to_owned())?;
    let apparatus = returned
        .get("apparatus")
        .ok_or_else(|| "detached return omitted apparatus".to_owned())?;
    let semantic_bytes = serde_json::to_vec_pretty(semantic)
        .map_err(|error| format!("encode semantic return: {error}"))?;
    let semantic_form = deposit_form_or_message(DRIVER, SEMANTIC_FORM, &semantic_bytes)?;
    let apparatus_bytes = serde_json::to_vec_pretty(apparatus)
        .map_err(|error| format!("encode apparatus receipt: {error}"))?;
    let apparatus_form = deposit_form_or_message(DRIVER, APPARATUS_FORM, &apparatus_bytes)?;
    let grade = json!({
        "truth_status": "established-bounded",
        "evidence_tags": ["implemented-exact", "computational-witness", "measured"],
        "receiver_family": RECEIVER_FEATURE,
        "source_snapshot": snapshot,
        "corpus_receipt": corpus_receipt,
        "atlas_receipt": atlas_receipt,
        "native_rest": {"path": rest_path, "address": rest_address},
        "source_detached": true,
        "semantic_return": {"path": semantic_form.path, "address": semantic_form.address},
        "apparatus_receipt": {"path": apparatus_form.path, "address": apparatus_form.address},
        "detached_grade": returned.get("grade"),
    });
    let grade_bytes = serde_json::to_vec_pretty(&grade)
        .map_err(|error| format!("encode material-mouth grade: {error}"))?;
    let grade_form = deposit_form_or_message(DRIVER, GRADE_FORM, &grade_bytes)?;
    println!("\nRETURNED SEMANTIC ARTIFACT");
    println!(
        "{}",
        serde_json::to_string_pretty(semantic)
            .map_err(|error| format!("render semantic return: {error}"))?
    );
    println!("\nNATIVE REST       {}", rest_path.display());
    println!("SEMANTIC RETURN   {}", semantic_form.path.display());
    println!("APPARATUS RECEIPT {}", apparatus_form.path.display());
    println!("PASSING GRADE     {}", grade_form.path.display());
    Ok(())
}

fn detached(form: &Path, expectation: &DetachedExpectation) -> Result<(), String> {
    // An unreadable root is not a masked root. Until 2026-08-11 a `read_dir` error here was folded
    // into `empty: true`, so the one condition the detachment falsifier exists to detect — a root
    // this child cannot account for — would have been reported as a passing mask. The plan-2
    // driver's `masked_roots` already propagated it; this is the same law, written twice and
    // agreeing only on the happy path.
    let mut masked = Vec::with_capacity(expectation.source_roots.len());
    for path in &expectation.source_roots {
        let empty = std::fs::read_dir(path)
            .map_err(|error| format!("inspect masked source root {}: {error}", path.display()))?
            .next()
            .is_none();
        masked.push((path.display().to_string(), empty));
    }
    if masked.iter().any(|(_, empty)| !empty) {
        return Err("a declared source root remained reachable after detachment".to_owned());
    }
    if sha256_file(form)? != expectation.rest_address {
        return Err("the detached form's raw content address moved".to_owned());
    }
    let file = File::open(form).map_err(|error| format!("open detached rest: {error}"))?;
    let atlas = ExactTextMaterialAtlas::from_native_reader(BufReader::new(file))
        .map_err(|error| format!("decode detached rest: {error:?}"))?;
    let reencoded = atlas
        .encode_native_bytes()
        .map_err(|error| format!("re-encode detached rest: {error:?}"))?;
    if content_address(&reencoded) != expectation.rest_address {
        return Err("the remounted readings do not reproduce the native address".to_owned());
    }
    drop(reencoded);
    let lean = lean_receipt_from_atlas(&atlas)?;
    if lean != expectation.lean {
        return Err(format!(
            "the source-detached Lean readings moved: expected {:?}, returned {:?}",
            expectation.lean, lean
        ));
    }
    let mut resident = atlas.mount_cuda(0).map_err(|refusal| {
        format!(
            "mount source-detached text body on CUDA: {:?}",
            refusal.error()
        )
    })?;
    let horizon = u64::MAX;
    let leader = LaboratoryResearchLeader {
        identity: "material-mouth/source-detached-receiver".to_owned(),
        question: RECEIVER_FEATURE.to_owned(),
        region: BTreeSet::from([RECEIVER_FEATURE.to_owned()]),
        horizon,
        generation: 0,
        caused_by_clauses: BTreeSet::new(),
    };
    let (semantic, apparatus) = resident
        .enact(&leader)
        .map_err(|error| format!("enact resident source-detached reading: {error:?}"))?;
    if semantic.sections.is_empty() || apparatus.launch.is_none() || !apparatus.bounded_delta_equal
    {
        return Err("the resident GPU deed returned no exact semantic artifact".to_owned());
    }
    let returned = json!({
        "grade": {
            "truth_status": "established-bounded",
            "evidence_tags": ["implemented-exact", "computational-witness", "measured"],
            "source_roots_masked": masked,
            "native_rest_address": expectation.rest_address,
            "lean_reading": lean,
            "device": resident.device_name(),
            "launches": resident.launches(),
        },
        "semantic": semantic,
        "apparatus": apparatus,
    });
    println!(
        "{}",
        serde_json::to_string(&returned)
            .map_err(|error| format!("encode detached return: {error}"))?
    );
    Ok(())
}

fn run_detached(form: &Path, expectation: &DetachedExpectation) -> Result<Value, String> {
    let executable = std::env::current_exe()
        .and_then(|path| path.canonicalize())
        .map_err(|error| format!("resolve material-mouth executable: {error}"))?;
    let encoded = serde_json::to_string(expectation)
        .map_err(|error| format!("encode detached expectation: {error}"))?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--new-session", "--unshare-net"])
        .args(["--ro-bind", "/", "/"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"])
        .args(["--dir", "/tmp/material-mouth"])
        .arg("--ro-bind")
        .arg(&executable)
        .arg("/tmp/material-mouth/deed")
        .arg("--ro-bind")
        .arg(form)
        .arg("/tmp/material-mouth/corpus.form");
    for source in &expectation.source_roots {
        command.arg("--tmpfs").arg(source);
    }
    let output = command
        .args(["--chdir", "/tmp"])
        .arg("--")
        .arg("/tmp/material-mouth/deed")
        .arg("--detached")
        .arg("/tmp/material-mouth/corpus.form")
        .arg(encoded)
        .output()
        .map_err(|error| format!("start source-detached remount: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "source-detached remount failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    serde_json::from_slice(&output.stdout)
        .map_err(|error| format!("read source-detached return: {error}"))
}

fn inspect_detached_return(returned: &Value) -> Result<(), String> {
    let sections = returned
        .pointer("/semantic/sections")
        .and_then(Value::as_array)
        .ok_or_else(|| "detached semantics carry no section population".to_owned())?;
    let launch = returned.pointer("/apparatus/launch");
    let masked = returned
        .pointer("/grade/source_roots_masked")
        .and_then(Value::as_array)
        .is_some_and(|roots| {
            !roots.is_empty()
                && roots
                    .iter()
                    .all(|entry| entry.get(1).and_then(Value::as_bool) == Some(true))
        });
    if sections.is_empty() || launch.is_none_or(Value::is_null) || !masked {
        return Err("detached return failed semantic, CUDA, or source-mask inspection".to_owned());
    }
    Ok(())
}

fn lean_documents(root: &Path) -> Result<(Vec<ParsedTextDocument>, LeanReadingReceipt), String> {
    let paths = files_below(root, |path| {
        path.extension().and_then(|value| value.to_str()) == Some("lean")
    })?;
    let mut documents = Vec::with_capacity(paths.len());
    let mut accumulator = LeanAccumulator::new();
    for path in paths {
        let text = std::fs::read_to_string(&path)
            .map_err(|error| format!("read Lean source {}: {error}", path.display()))?;
        let relative = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        let identity = format!("lean:{relative}");
        accumulator.receive(&identity, &text)?;
        documents.push(ParsedTextDocument {
            identity,
            source: format!("formal/{relative}"),
            sections: vec![text],
        });
    }
    Ok((documents, accumulator.finish()))
}

fn lean_receipt_from_atlas(atlas: &ExactTextMaterialAtlas) -> Result<LeanReadingReceipt, String> {
    let mut accumulator = LeanAccumulator::new();
    for occurrence in atlas.corpus().occurrences() {
        let Some(identity) = occurrence
            .native_identity
            .strip_prefix("document:")
            .and_then(|identity| identity.strip_suffix(":0"))
            .filter(|identity| identity.starts_with("lean:"))
        else {
            continue;
        };
        accumulator.receive(identity, &occurrence.text)?;
    }
    Ok(accumulator.finish())
}

struct LeanAccumulator {
    files: usize,
    source_bytes: u64,
    declarations: usize,
    unopened: usize,
    commentary_terms: usize,
    preamble_terms: usize,
    scoping_terms: usize,
    ambiguous_short_names: usize,
    readings: BTreeMap<String, String>,
}

impl LeanAccumulator {
    fn new() -> Self {
        Self {
            files: 0,
            source_bytes: 0,
            declarations: 0,
            unopened: 0,
            commentary_terms: 0,
            preamble_terms: 0,
            scoping_terms: 0,
            ambiguous_short_names: 0,
            readings: BTreeMap::new(),
        }
    }

    fn receive(&mut self, identity: &str, text: &str) -> Result<(), String> {
        let reading = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        let encoded = serde_json::to_vec(&reading)
            .map_err(|error| format!("encode Lean reading {identity}: {error}"))?;
        if self
            .readings
            .insert(identity.to_owned(), hex(&Sha256::digest(&encoded)))
            .is_some()
        {
            return Err(format!("duplicate Lean source identity {identity}"));
        }
        self.files = checked(self.files, 1, "Lean file population")?;
        self.source_bytes = self
            .source_bytes
            .checked_add(u64::try_from(text.len()).map_err(|_| "Lean source extent".to_owned())?)
            .ok_or_else(|| "Lean source extent".to_owned())?;
        self.declarations = checked(
            self.declarations,
            reading.declarations.len(),
            "Lean declarations",
        )?;
        self.unopened = checked(self.unopened, reading.unopened.len(), "Lean unopened")?;
        self.commentary_terms = checked(
            self.commentary_terms,
            reading.commentary.len(),
            "Lean commentary",
        )?;
        self.preamble_terms =
            checked(self.preamble_terms, reading.preamble.len(), "Lean preamble")?;
        self.scoping_terms = checked(self.scoping_terms, reading.scoping.len(), "Lean scoping")?;
        self.ambiguous_short_names = checked(
            self.ambiguous_short_names,
            reading.ambiguous_short_names.len(),
            "Lean ambiguous names",
        )?;
        Ok(())
    }

    fn finish(self) -> LeanReadingReceipt {
        let mut digest = Sha256::new();
        for (identity, reading) in self.readings {
            digest.update(identity.as_bytes());
            digest.update([0]);
            digest.update(reading.as_bytes());
        }
        LeanReadingReceipt {
            files: self.files,
            source_bytes: self.source_bytes,
            declarations: self.declarations,
            unopened: self.unopened,
            commentary_terms: self.commentary_terms,
            preamble_terms: self.preamble_terms,
            scoping_terms: self.scoping_terms,
            ambiguous_short_names: self.ambiguous_short_names,
            reading_sha256: hex(&digest.finalize()),
        }
    }
}

fn checked(left: usize, right: usize, label: &str) -> Result<usize, String> {
    left.checked_add(right).ok_or_else(|| label.to_owned())
}

fn files_below(root: &Path, accepts: impl Fn(&Path) -> bool) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    let mut frontier = vec![root.to_owned()];
    while let Some(at) = frontier.pop() {
        let mut entries = std::fs::read_dir(&at)
            .map_err(|error| format!("read {}: {error}", at.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("read {}: {error}", at.display()))?;
        entries.sort_by_key(|entry| entry.path());
        for entry in entries.into_iter().rev() {
            let path = entry.path();
            let file_type = entry
                .file_type()
                .map_err(|error| format!("inspect {}: {error}", path.display()))?;
            if file_type.is_dir() {
                frontier.push(path);
            } else if file_type.is_file() && accepts(&path) {
                files.push(path);
            }
        }
    }
    files.sort();
    Ok(files)
}

fn claude_main_sessions(root: &Path) -> Result<Vec<PathBuf>, String> {
    let mut sessions = Vec::new();
    let mut projects = std::fs::read_dir(root)
        .map_err(|error| format!("read {}: {error}", root.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("read {}: {error}", root.display()))?;
    projects.sort_by_key(|entry| entry.path());
    for project in projects {
        if !project
            .file_type()
            .map_err(|error| format!("inspect {}: {error}", project.path().display()))?
            .is_dir()
        {
            continue;
        }
        let mut entries = std::fs::read_dir(project.path())
            .map_err(|error| format!("read {}: {error}", project.path().display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("read {}: {error}", project.path().display()))?;
        entries.sort_by_key(|entry| entry.path());
        for entry in entries {
            let path = entry.path();
            if entry
                .file_type()
                .map_err(|error| format!("inspect {}: {error}", path.display()))?
                .is_file()
                && path.extension().and_then(|value| value.to_str()) == Some("jsonl")
            {
                sessions.push(path);
            }
        }
    }
    sessions.sort();
    sessions.dedup();
    Ok(sessions)
}

fn is_main_codex_rollout(path: &Path) -> Result<bool, String> {
    let file = File::open(path).map_err(|error| format!("open {}: {error}", path.display()))?;
    for line in BufReader::new(file).lines() {
        let line = line.map_err(|error| format!("read {}: {error}", path.display()))?;
        if line.trim().is_empty() {
            continue;
        }
        let value: Value = serde_json::from_str(&line)
            .map_err(|error| format!("read session metadata {}: {error}", path.display()))?;
        let payload = value.get("payload");
        return Ok(
            value.get("type").and_then(Value::as_str) == Some("session_meta")
                && payload
                    .and_then(|value| value.get("originator"))
                    .and_then(Value::as_str)
                    == Some("codex-tui")
                && payload
                    .and_then(|value| value.get("source"))
                    .and_then(Value::as_str)
                    == Some("cli"),
        );
    }
    Ok(false)
}

fn file_extent(paths: &[PathBuf]) -> Result<u64, String> {
    let mut extent = 0u64;
    for path in paths {
        extent = extent
            .checked_add(
                path.metadata()
                    .map_err(|error| format!("inspect {}: {error}", path.display()))?
                    .len(),
            )
            .ok_or_else(|| "source population extent".to_owned())?;
    }
    Ok(extent)
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let mut file = File::open(path).map_err(|error| format!("open {}: {error}", path.display()))?;
    let mut digest = Sha256::new();
    let mut buffer = [0u8; 1 << 20];
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|error| format!("read {}: {error}", path.display()))?;
        if read == 0 {
            break;
        }
        digest.update(&buffer[..read]);
    }
    Ok(hex(&digest.finalize()))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
