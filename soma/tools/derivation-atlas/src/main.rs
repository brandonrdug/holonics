use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const SCHEMA: &str = "holonics.derivation-atlas.v1";
const USAGE: &str = "usage: soma-derivation-atlas <extract|validate|inspect|corpus> ...

  extract  --project DIR --source FILE --out FILE [--module-prefix MODULE]
  validate --bundle FILE
  inspect  --bundle FILE [--top N]
  corpus   --bundle FILE --bundle FILE ... [--top N]";

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ExpressionFace {
    rendered_exterior: String,
    lean_structural_hash_exterior: String,
    root_node: usize,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ExpressionNode {
    index: usize,
    kind_exterior: String,
    face_exterior: String,
    children: Vec<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct LocalStanding {
    index: usize,
    free_occurrence_exterior: String,
    user_face_exterior: String,
    binder_face_exterior: String,
    kind_face_exterior: String,
    #[serde(rename = "type")]
    type_face: ExpressionFace,
    value: Option<ExpressionFace>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct GoalFace {
    goal_occurrence_exterior: String,
    user_face_exterior: String,
    local_standing: Vec<LocalStanding>,
    target: ExpressionFace,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct TermOccurrence {
    sequence: usize,
    parent_declaration_exterior: String,
    start_byte: usize,
    stop_byte: usize,
    elaborator_exterior: String,
    syntax_exterior: String,
    expression: ExpressionFace,
    expected_type: Option<ExpressionFace>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ProofEvent {
    sequence: usize,
    parent_declaration_exterior: String,
    start_byte: usize,
    stop_byte: usize,
    elaborator_exterior: String,
    syntax_exterior: String,
    before: Vec<GoalFace>,
    after: Vec<GoalFace>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct DeclarationOperation {
    declaration_exterior: String,
    module_exterior: String,
    kind_exterior: String,
    #[serde(rename = "type")]
    type_face: ExpressionFace,
    defining_value: Option<ExpressionFace>,
    body_references_exterior: Vec<String>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AtlasBundle {
    schema: String,
    source_path_exterior: String,
    module_exterior: String,
    declaration_module_prefix_exterior: String,
    expression_nodes: Vec<ExpressionNode>,
    declaration_operations: Vec<DeclarationOperation>,
    term_occurrences: Vec<TermOccurrence>,
    proof_events: Vec<ProofEvent>,
    syntax_and_names_are_exterior: bool,
    kernel_checked: bool,
    truth_status: String,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct CountFace {
    face: String,
    count: usize,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct AtlasReport {
    schema: String,
    source_path_exterior: String,
    module_exterior: String,
    truth_status: String,
    expression_nodes: usize,
    declaration_operations: usize,
    theorem_bodies: usize,
    term_occurrences: usize,
    proof_events: usize,
    goal_faces: usize,
    distinct_declarations_used: usize,
    expression_kinds: Vec<CountFace>,
    recurring_expression_faces: Vec<CountFace>,
    recurring_goal_targets: Vec<CountFace>,
    proof_event_elaborators: Vec<CountFace>,
    theorem_body_roots: Vec<CountFace>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct CorpusReport {
    schema: String,
    bundles: usize,
    expression_nodes: usize,
    declaration_operations: usize,
    theorem_bodies: usize,
    term_occurrences: usize,
    proof_events: usize,
    modules: Vec<String>,
    recurring_expression_faces: Vec<CountFace>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct AtlasManifest {
    schema: String,
    bundle_path_exterior: String,
    bundle_sha256: String,
    source_path_exterior: String,
    source_sha256: String,
    module_exterior: String,
    expression_nodes: usize,
    declaration_operations: usize,
    theorem_bodies: usize,
    proof_events: usize,
    truth_status: String,
}

#[derive(Clone, Copy)]
enum CommandKind {
    Extract,
    Validate,
    Inspect,
    Corpus,
}

struct Args {
    command: CommandKind,
    project: Option<PathBuf>,
    source: Option<PathBuf>,
    output: Option<PathBuf>,
    bundles: Vec<PathBuf>,
    module_prefix: Option<String>,
    top: usize,
}

fn next_path<I>(raw: &mut I, flag: &str) -> Result<PathBuf, String>
where
    I: Iterator<Item = OsString>,
{
    raw.next()
        .map(PathBuf::from)
        .ok_or_else(|| format!("{flag} requires a value"))
}

fn parse_args() -> Result<Option<Args>, String> {
    let mut raw = env::args_os().skip(1);
    let Some(command) = raw.next() else {
        return Err(USAGE.to_owned());
    };
    if command == "--help" || command == "-h" {
        return Ok(None);
    }
    let command = match command.to_str() {
        Some("extract") => CommandKind::Extract,
        Some("validate") => CommandKind::Validate,
        Some("inspect") => CommandKind::Inspect,
        Some("corpus") => CommandKind::Corpus,
        _ => return Err(USAGE.to_owned()),
    };
    let mut args = Args {
        command,
        project: None,
        source: None,
        output: None,
        bundles: Vec::new(),
        module_prefix: None,
        top: 20,
    };
    while let Some(flag) = raw.next() {
        let flag = flag.to_string_lossy();
        match flag.as_ref() {
            "--project" => args.project = Some(next_path(&mut raw, &flag)?),
            "--source" => args.source = Some(next_path(&mut raw, &flag)?),
            "--out" => args.output = Some(next_path(&mut raw, &flag)?),
            "--bundle" => args.bundles.push(next_path(&mut raw, &flag)?),
            "--module-prefix" => {
                let next = raw
                    .next()
                    .ok_or_else(|| "--module-prefix requires a value".to_owned())?;
                args.module_prefix = Some(next.to_string_lossy().into_owned());
            }
            "--top" => {
                let next = raw
                    .next()
                    .ok_or_else(|| "--top requires a value".to_owned())?;
                args.top = next
                    .to_string_lossy()
                    .parse()
                    .map_err(|_| "--top must be a positive integer".to_owned())?;
            }
            "--help" | "-h" => return Ok(None),
            _ => return Err(format!("unknown flag {flag}\n\n{USAGE}")),
        }
    }
    Ok(Some(args))
}

fn read_bundle(path: &Path) -> Result<AtlasBundle, String> {
    let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    serde_json::from_slice(&bytes).map_err(|error| format!("decode {}: {error}", path.display()))
}

fn sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn face_root(
    face: &ExpressionFace,
    expression_nodes: &[ExpressionNode],
    context: &str,
) -> Result<(), String> {
    if face.root_node >= expression_nodes.len() {
        return Err(format!(
            "{context} points to expression node {}, but the population has {} nodes",
            face.root_node,
            expression_nodes.len()
        ));
    }
    Ok(())
}

fn validate_goal(
    goal: &GoalFace,
    expression_nodes: &[ExpressionNode],
    context: &str,
) -> Result<usize, String> {
    face_root(&goal.target, expression_nodes, &format!("{context}.target"))?;
    let mut local_count = 0;
    for local in &goal.local_standing {
        face_root(
            &local.type_face,
            expression_nodes,
            &format!("{context}.local.type"),
        )?;
        if let Some(value) = &local.value {
            face_root(value, expression_nodes, &format!("{context}.local.value"))?;
        }
        local_count += 1;
    }
    Ok(local_count)
}

fn validate(bundle: &AtlasBundle) -> Result<(), String> {
    if bundle.schema != SCHEMA {
        return Err(format!(
            "unsupported schema {:?}, expected {SCHEMA:?}",
            bundle.schema
        ));
    }
    if !bundle.syntax_and_names_are_exterior {
        return Err("bundle did not mark syntax and names as exterior lineage".to_owned());
    }
    if !bundle.kernel_checked {
        return Err("bundle is not marked kernel-checked".to_owned());
    }
    if bundle.expression_nodes.is_empty() {
        return Err("expression population is empty".to_owned());
    }
    for (position, node) in bundle.expression_nodes.iter().enumerate() {
        if node.index != position {
            return Err(format!(
                "expression node position {position} carries index {}",
                node.index
            ));
        }
        for child in &node.children {
            if *child >= node.index {
                return Err(format!(
                    "expression node {} has child {child}; expected a previously interned child",
                    node.index
                ));
            }
        }
    }
    let mut declarations = BTreeSet::new();
    let mut theorem_bodies = 0;
    for declaration in &bundle.declaration_operations {
        if !declarations.insert(&declaration.declaration_exterior) {
            return Err(format!(
                "duplicate declaration {}",
                declaration.declaration_exterior
            ));
        }
        face_root(
            &declaration.type_face,
            &bundle.expression_nodes,
            &format!("{}.type", declaration.declaration_exterior),
        )?;
        if let Some(value) = &declaration.defining_value {
            face_root(
                value,
                &bundle.expression_nodes,
                &format!("{}.definingValue", declaration.declaration_exterior),
            )?;
            if declaration.kind_exterior == "theorem" {
                theorem_bodies += 1;
            }
        }
    }
    for term in &bundle.term_occurrences {
        face_root(
            &term.expression,
            &bundle.expression_nodes,
            "term.expression",
        )?;
        if let Some(expected) = &term.expected_type {
            face_root(expected, &bundle.expression_nodes, "term.expectedType")?;
        }
        if term.stop_byte < term.start_byte {
            return Err(format!(
                "term {} has a reversed source range",
                term.sequence
            ));
        }
    }
    for (sequence, event) in bundle.proof_events.iter().enumerate() {
        if event.sequence != sequence {
            return Err(format!(
                "proof event position {sequence} carries sequence {}",
                event.sequence
            ));
        }
        if event.stop_byte < event.start_byte {
            return Err(format!(
                "proof event {} has a reversed source range",
                event.sequence
            ));
        }
        for (index, goal) in event.before.iter().enumerate() {
            validate_goal(
                goal,
                &bundle.expression_nodes,
                &format!("event {} before[{index}]", event.sequence),
            )?;
        }
        for (index, goal) in event.after.iter().enumerate() {
            validate_goal(
                goal,
                &bundle.expression_nodes,
                &format!("event {} after[{index}]", event.sequence),
            )?;
        }
    }
    if theorem_bodies == 0
        && bundle
            .declaration_operations
            .iter()
            .any(|d| d.kind_exterior == "theorem")
    {
        return Err("theorem declarations are present but no theorem body was exported".to_owned());
    }
    Ok(())
}

fn increment(map: &mut BTreeMap<String, usize>, key: impl Into<String>) {
    *map.entry(key.into()).or_default() += 1;
}

fn top_faces(map: BTreeMap<String, usize>, top: usize) -> Vec<CountFace> {
    let mut faces = map
        .into_iter()
        .map(|(face, count)| CountFace { face, count })
        .collect::<Vec<_>>();
    faces.sort_by(|left, right| {
        right
            .count
            .cmp(&left.count)
            .then_with(|| left.face.cmp(&right.face))
    });
    faces.truncate(top);
    faces
}

fn report(bundle: &AtlasBundle, top: usize) -> AtlasReport {
    let mut expression_kinds = BTreeMap::new();
    let mut recurring_expression_faces = BTreeMap::new();
    for node in &bundle.expression_nodes {
        increment(&mut expression_kinds, &node.kind_exterior);
        increment(
            &mut recurring_expression_faces,
            format!("{}|{}", node.kind_exterior, node.face_exterior),
        );
    }
    let mut recurring_goal_targets = BTreeMap::new();
    let mut goal_faces = 0;
    for event in &bundle.proof_events {
        for goal in event.before.iter().chain(event.after.iter()) {
            goal_faces += 1;
            let node = &bundle.expression_nodes[goal.target.root_node];
            increment(
                &mut recurring_goal_targets,
                format!("{}|{}", node.kind_exterior, node.face_exterior),
            );
        }
    }
    let mut proof_event_elaborators = BTreeMap::new();
    for event in &bundle.proof_events {
        increment(&mut proof_event_elaborators, &event.elaborator_exterior);
    }
    let mut theorem_body_roots = BTreeMap::new();
    let mut theorem_bodies = 0;
    let mut distinct_declarations_used = BTreeSet::new();
    for declaration in &bundle.declaration_operations {
        distinct_declarations_used.extend(declaration.body_references_exterior.iter().cloned());
        if declaration.kind_exterior == "theorem" {
            if let Some(value) = &declaration.defining_value {
                theorem_bodies += 1;
                let node = &bundle.expression_nodes[value.root_node];
                increment(
                    &mut theorem_body_roots,
                    format!("{}|{}", node.kind_exterior, node.face_exterior),
                );
            }
        }
    }
    AtlasReport {
        schema: bundle.schema.clone(),
        source_path_exterior: bundle.source_path_exterior.clone(),
        module_exterior: bundle.module_exterior.clone(),
        truth_status: bundle.truth_status.clone(),
        expression_nodes: bundle.expression_nodes.len(),
        declaration_operations: bundle.declaration_operations.len(),
        theorem_bodies,
        term_occurrences: bundle.term_occurrences.len(),
        proof_events: bundle.proof_events.len(),
        goal_faces,
        distinct_declarations_used: distinct_declarations_used.len(),
        expression_kinds: top_faces(expression_kinds, top),
        recurring_expression_faces: top_faces(recurring_expression_faces, top),
        recurring_goal_targets: top_faces(recurring_goal_targets, top),
        proof_event_elaborators: top_faces(proof_event_elaborators, top),
        theorem_body_roots: top_faces(theorem_body_roots, top),
    }
}

fn corpus_report(bundles: &[AtlasBundle], top: usize) -> CorpusReport {
    let mut recurring_expression_faces = BTreeMap::new();
    let mut expression_nodes = 0;
    let mut declaration_operations = 0;
    let mut theorem_bodies = 0;
    let mut term_occurrences = 0;
    let mut proof_events = 0;
    let mut modules = Vec::new();
    for bundle in bundles {
        expression_nodes += bundle.expression_nodes.len();
        declaration_operations += bundle.declaration_operations.len();
        theorem_bodies += bundle
            .declaration_operations
            .iter()
            .filter(|declaration| {
                declaration.kind_exterior == "theorem" && declaration.defining_value.is_some()
            })
            .count();
        term_occurrences += bundle.term_occurrences.len();
        proof_events += bundle.proof_events.len();
        modules.push(bundle.module_exterior.clone());
        for node in &bundle.expression_nodes {
            increment(
                &mut recurring_expression_faces,
                format!("{}|{}", node.kind_exterior, node.face_exterior),
            );
        }
    }
    modules.sort();
    CorpusReport {
        schema: SCHEMA.to_owned(),
        bundles: bundles.len(),
        expression_nodes,
        declaration_operations,
        theorem_bodies,
        term_occurrences,
        proof_events,
        modules,
        recurring_expression_faces: top_faces(recurring_expression_faces, top),
    }
}

fn extract(args: &Args) -> Result<(), String> {
    let project = args
        .project
        .as_deref()
        .ok_or_else(|| "extract requires --project".to_owned())
        .and_then(|path| {
            fs::canonicalize(path)
                .map_err(|error| format!("resolve project {}: {error}", path.display()))
        })?;
    let source = args
        .source
        .as_deref()
        .ok_or_else(|| "extract requires --source".to_owned())?
        .to_owned();
    let output = args
        .output
        .as_deref()
        .ok_or_else(|| "extract requires --out".to_owned())
        .and_then(|path| {
            if path.is_absolute() {
                Ok(path.to_owned())
            } else {
                env::current_dir()
                    .map(|directory| directory.join(path))
                    .map_err(|error| format!("resolve output {}: {error}", path.display()))
            }
        })?;
    let build = Command::new("lake")
        .args(["build", "derivation_atlas"])
        .current_dir(&project)
        .status()
        .map_err(|error| format!("build derivation_atlas: {error}"))?;
    if !build.success() {
        return Err(format!("lake build derivation_atlas exited with {build}"));
    }
    let executable = project.join(".lake/build/bin/derivation_atlas");
    if !executable.is_file() {
        return Err(format!("Lean exporter is absent: {}", executable.display()));
    }
    let mut command = Command::new(executable);
    command.arg("--input").arg(&source);
    if let Some(prefix) = &args.module_prefix {
        command.args(["--module-prefix", prefix]);
    }
    command.arg("--output").arg(&output);
    let status = command
        .current_dir(&project)
        .status()
        .map_err(|error| format!("run Lean derivation exporter: {error}"))?;
    if !status.success() {
        return Err(format!("Lean derivation exporter exited with {status}"));
    }
    let bundle = read_bundle(&output)?;
    validate(&bundle)?;
    let source_path = if source.is_absolute() {
        source
    } else {
        project.join(source)
    };
    let source_bytes = fs::read(&source_path)
        .map_err(|error| format!("read source {}: {error}", source_path.display()))?;
    let bundle_bytes =
        fs::read(&output).map_err(|error| format!("read bundle {}: {error}", output.display()))?;
    let manifest = AtlasManifest {
        schema: "holonics.derivation-atlas-manifest.v1".to_owned(),
        bundle_path_exterior: output.display().to_string(),
        bundle_sha256: sha256(&bundle_bytes),
        source_path_exterior: source_path.display().to_string(),
        source_sha256: sha256(&source_bytes),
        module_exterior: bundle.module_exterior.clone(),
        expression_nodes: bundle.expression_nodes.len(),
        declaration_operations: bundle.declaration_operations.len(),
        theorem_bodies: bundle
            .declaration_operations
            .iter()
            .filter(|declaration| {
                declaration.kind_exterior == "theorem" && declaration.defining_value.is_some()
            })
            .count(),
        proof_events: bundle.proof_events.len(),
        truth_status: bundle.truth_status.clone(),
    };
    let manifest_path = output.with_extension("manifest.json");
    let manifest_bytes = serde_json::to_vec_pretty(&manifest)
        .map_err(|error| format!("encode atlas manifest: {error}"))?;
    fs::write(&manifest_path, manifest_bytes)
        .map_err(|error| format!("write atlas manifest {}: {error}", manifest_path.display()))?;
    println!(
        "extracted and validated {}: {} expression nodes, {} declarations, {} proof events; manifest {}",
        output.display(),
        bundle.expression_nodes.len(),
        bundle.declaration_operations.len(),
        bundle.proof_events.len(),
        manifest_path.display()
    );
    Ok(())
}

fn run() -> Result<(), String> {
    let Some(args) = parse_args()? else {
        println!("{USAGE}");
        return Ok(());
    };
    match args.command {
        CommandKind::Extract => extract(&args),
        CommandKind::Validate | CommandKind::Inspect => {
            if args.bundles.len() != 1 {
                return Err("this command requires exactly one --bundle".to_owned());
            }
            let path = &args.bundles[0];
            let bundle = read_bundle(path)?;
            validate(&bundle)?;
            if matches!(args.command, CommandKind::Inspect) {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&report(&bundle, args.top))
                        .map_err(|error| format!("encode report: {error}"))?
                );
            } else {
                println!(
                    "validated {}: {} expression nodes, {} declarations, {} theorem bodies, {} proof events",
                    path.display(),
                    bundle.expression_nodes.len(),
                    bundle.declaration_operations.len(),
                    bundle
                        .declaration_operations
                        .iter()
                        .filter(|d| d.kind_exterior == "theorem" && d.defining_value.is_some())
                        .count(),
                    bundle.proof_events.len()
                );
            }
            Ok(())
        }
        CommandKind::Corpus => {
            if args.bundles.is_empty() {
                return Err("corpus requires at least one --bundle".to_owned());
            }
            let mut bundles = Vec::new();
            for path in &args.bundles {
                let bundle = read_bundle(path)?;
                validate(&bundle)?;
                bundles.push(bundle);
            }
            println!(
                "{}",
                serde_json::to_string_pretty(&corpus_report(&bundles, args.top))
                    .map_err(|error| format!("encode corpus report: {error}"))?
            );
            Ok(())
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("soma-derivation-atlas: {error}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_is_stable() {
        assert_eq!(
            sha256(b"holonics"),
            "916895528cd0616e9a3742f39cab46c770f6afe92ea4218df5a023388ad67c51"
        );
    }

    #[test]
    fn top_faces_orders_by_count_then_face() {
        let mut counts = BTreeMap::new();
        increment(&mut counts, "b");
        increment(&mut counts, "a");
        increment(&mut counts, "a");
        let returned = top_faces(counts, 2);
        assert_eq!(returned[0].face, "a");
        assert_eq!(returned[0].count, 2);
        assert_eq!(returned[1].face, "b");
    }
}
