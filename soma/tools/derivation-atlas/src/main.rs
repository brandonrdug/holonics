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

const SCHEMA: &str = "holonics.derivation-atlas.v2";
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

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ExpressionUse {
    node: usize,
    parent_node: Option<usize>,
    child_position: Option<usize>,
    count: usize,
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
    expression_uses: Vec<ExpressionUse>,
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
struct UsageFace {
    face: String,
    distinct_nodes: usize,
    occurrence_uses: usize,
    root_occurrences: usize,
    child_occurrences: usize,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct IntegerFace {
    module_exterior: String,
    literal_node: usize,
    literal_kind: String,
    value_exterior: String,
    occurrence_uses: usize,
    root_occurrences: usize,
    type_face_candidates: Vec<String>,
    parent_operations: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct FactorFace {
    module_exterior: String,
    operation: String,
    left_face: String,
    right_face: String,
    candidate_nodes: usize,
    occurrence_uses: usize,
    witness_nodes: Vec<usize>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct FigureFace {
    module_exterior: String,
    family: String,
    operation: String,
    distinct_nodes: usize,
    occurrence_uses: usize,
    witness_nodes: Vec<usize>,
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
    expression_use_edges: usize,
    expression_use_multiplicity: usize,
    root_expression_occurrences: usize,
    distinct_declarations_used: usize,
    expression_kinds: Vec<CountFace>,
    recurring_expression_faces: Vec<CountFace>,
    recurring_expression_usage: Vec<UsageFace>,
    literal_integer_faces: Vec<IntegerFace>,
    factor_candidates: Vec<FactorFace>,
    algebraic_figures: Vec<FigureFace>,
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
    expression_use_edges: usize,
    expression_use_multiplicity: usize,
    root_expression_occurrences: usize,
    modules: Vec<String>,
    recurring_expression_faces: Vec<CountFace>,
    recurring_expression_usage: Vec<UsageFace>,
    literal_integer_faces: Vec<IntegerFace>,
    factor_candidates: Vec<FactorFace>,
    algebraic_figures: Vec<FigureFace>,
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
    if bundle.expression_uses.is_empty() {
        return Err("expression-use population is empty".to_owned());
    }
    for (position, usage) in bundle.expression_uses.iter().enumerate() {
        if usage.count == 0 {
            return Err(format!("expression use {position} has zero multiplicity"));
        }
        if usage.node >= bundle.expression_nodes.len() {
            return Err(format!(
                "expression use {position} points to node {} outside the population",
                usage.node
            ));
        }
        match (usage.parent_node, usage.child_position) {
            (None, None) => {}
            (Some(parent), Some(child_position)) => {
                if parent >= bundle.expression_nodes.len() {
                    return Err(format!(
                        "expression use {position} points to parent {parent} outside the population"
                    ));
                }
                let parent_node = &bundle.expression_nodes[parent];
                if parent_node.children.get(child_position) != Some(&usage.node) {
                    return Err(format!(
                        "expression use {position} does not match parent {} child position {}",
                        parent, child_position
                    ));
                }
            }
            _ => {
                return Err(format!(
                    "expression use {position} has only one of parent and child position"
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

#[derive(Default)]
struct UsageAccumulator {
    distinct_nodes: usize,
    occurrence_uses: usize,
    root_occurrences: usize,
    child_occurrences: usize,
}

fn usage_counts(bundle: &AtlasBundle) -> (Vec<usize>, Vec<usize>, Vec<BTreeSet<usize>>) {
    let mut uses = vec![0; bundle.expression_nodes.len()];
    let mut roots = vec![0; bundle.expression_nodes.len()];
    let mut parents = vec![BTreeSet::new(); bundle.expression_nodes.len()];
    for usage in &bundle.expression_uses {
        uses[usage.node] += usage.count;
        if let Some(parent) = usage.parent_node {
            parents[usage.node].insert(parent);
        } else {
            roots[usage.node] += usage.count;
        }
    }
    (uses, roots, parents)
}

fn recurring_usage(bundle: &AtlasBundle, top: usize) -> Vec<UsageFace> {
    let (uses, roots, _) = usage_counts(bundle);
    let mut grouped = BTreeMap::<String, UsageAccumulator>::new();
    for (index, node) in bundle.expression_nodes.iter().enumerate() {
        let entry = grouped
            .entry(format!("{}|{}", node.kind_exterior, node.face_exterior))
            .or_default();
        entry.distinct_nodes += 1;
        entry.occurrence_uses += uses[index];
        entry.root_occurrences += roots[index];
        entry.child_occurrences += uses[index] - roots[index];
    }
    top_usage(grouped, top)
}

fn top_usage(grouped: BTreeMap<String, UsageAccumulator>, top: usize) -> Vec<UsageFace> {
    let mut returned = grouped
        .into_iter()
        .map(|(face, value)| UsageFace {
            face,
            distinct_nodes: value.distinct_nodes,
            occurrence_uses: value.occurrence_uses,
            root_occurrences: value.root_occurrences,
            child_occurrences: value.child_occurrences,
        })
        .collect::<Vec<_>>();
    returned.sort_by(|left, right| {
        right
            .occurrence_uses
            .cmp(&left.occurrence_uses)
            .then_with(|| left.face.cmp(&right.face))
    });
    returned.truncate(top);
    returned
}

fn parse_literal(face: &str) -> Option<(&'static str, String)> {
    face.strip_prefix("Lean.Literal.natVal ")
        .map(|value| ("natural", value.to_owned()))
        .or_else(|| {
            face.strip_prefix("Lean.Literal.intVal ")
                .map(|value| ("integer", value.to_owned()))
        })
}

fn type_faces_below_of_nat(
    node_index: usize,
    nodes: &[ExpressionNode],
    visited: &mut BTreeSet<usize>,
    returned: &mut BTreeSet<String>,
) {
    if !visited.insert(node_index) {
        return;
    }
    let node = &nodes[node_index];
    if node.face_exterior == "OfNat.ofNat" {
        if let Some((_, arguments)) = application_spine(node_index, nodes) {
            if let Some(type_node) = arguments.first() {
                returned.insert(format!(
                    "{}|{}",
                    nodes[*type_node].kind_exterior, nodes[*type_node].face_exterior
                ));
            }
        }
        return;
    }
    for child in &node.children {
        type_faces_below_of_nat(*child, nodes, visited, returned);
    }
}

fn literal_integer_faces(bundle: &AtlasBundle, top: usize) -> Vec<IntegerFace> {
    let (uses, roots, parents) = usage_counts(bundle);
    let mut returned = Vec::new();
    for node in &bundle.expression_nodes {
        let Some((literal_kind, value_exterior)) = parse_literal(&node.face_exterior) else {
            continue;
        };
        let mut type_faces = BTreeSet::new();
        let mut frontier = parents[node.index].iter().copied().collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(parent) = frontier.pop() {
            if !visited.insert(parent) {
                continue;
            }
            let parent_node = &bundle.expression_nodes[parent];
            if parent_node.face_exterior == "OfNat.ofNat" {
                let mut below_visited = BTreeSet::new();
                type_faces_below_of_nat(
                    parent,
                    &bundle.expression_nodes,
                    &mut below_visited,
                    &mut type_faces,
                );
                continue;
            }
            frontier.extend(parents[parent].iter().copied());
        }
        let parent_operations = parents[node.index]
            .iter()
            .map(|parent| {
                let parent_node = &bundle.expression_nodes[*parent];
                format!(
                    "{}|{}",
                    parent_node.kind_exterior, parent_node.face_exterior
                )
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        returned.push(IntegerFace {
            module_exterior: bundle.module_exterior.clone(),
            literal_node: node.index,
            literal_kind: literal_kind.to_owned(),
            value_exterior,
            occurrence_uses: uses[node.index],
            root_occurrences: roots[node.index],
            type_face_candidates: type_faces.into_iter().collect(),
            parent_operations,
        });
    }
    returned.sort_by(|left, right| {
        right
            .occurrence_uses
            .cmp(&left.occurrence_uses)
            .then_with(|| left.literal_node.cmp(&right.literal_node))
    });
    returned.truncate(top);
    returned
}

fn application_spine(node_index: usize, nodes: &[ExpressionNode]) -> Option<(String, Vec<usize>)> {
    if nodes[node_index].kind_exterior != "application" {
        return None;
    }
    let operation = nodes[node_index].face_exterior.clone();
    let mut current = node_index;
    let mut reversed_arguments = Vec::new();
    loop {
        let node = &nodes[current];
        if node.kind_exterior != "application" || node.children.len() != 2 {
            break;
        }
        reversed_arguments.push(node.children[1]);
        current = node.children[0];
    }
    if nodes[current].kind_exterior != "constant" {
        return None;
    }
    reversed_arguments.reverse();
    Some((operation, reversed_arguments))
}

fn figure_family(operation: &str) -> Option<&'static str> {
    match operation {
        "Eq" => Some("equality-cell"),
        "Eq.trans" => Some("equality-transport"),
        "congrArg" => Some("congruence-cell"),
        "HAdd.hAdd" => Some("addition-cell"),
        "HSub.hSub" => Some("difference-cell"),
        "HMul.hMul" => Some("multiplication-cell"),
        "HPow.hPow" => Some("power-cell"),
        "Finset.sum" => Some("finite-accumulation-cell"),
        "Matrix.mulVec" => Some("matrix-action-cell"),
        _ => None,
    }
}

fn factor_candidates(bundle: &AtlasBundle, top: usize) -> Vec<FactorFace> {
    let (uses, _, _) = usage_counts(bundle);
    let mut grouped = BTreeMap::<(String, String, String), (usize, usize, Vec<usize>)>::new();
    for node in &bundle.expression_nodes {
        let Some((operation, arguments)) = application_spine(node.index, &bundle.expression_nodes)
        else {
            continue;
        };
        if operation != "HMul.hMul" || arguments.len() < 6 {
            continue;
        }
        let left = arguments[arguments.len() - 2];
        let right = arguments[arguments.len() - 1];
        let left_face = format!(
            "{}|{}",
            bundle.expression_nodes[left].kind_exterior,
            bundle.expression_nodes[left].face_exterior
        );
        let right_face = format!(
            "{}|{}",
            bundle.expression_nodes[right].kind_exterior,
            bundle.expression_nodes[right].face_exterior
        );
        if left_face.contains("inst")
            || right_face.contains("inst")
            || left_face.contains(".to")
            || right_face.contains(".to")
        {
            continue;
        }
        let entry = grouped
            .entry((operation, left_face, right_face))
            .or_insert_with(|| (0, 0, Vec::new()));
        entry.0 += 1;
        entry.1 += uses[node.index];
        if entry.2.len() < 8 {
            entry.2.push(node.index);
        }
    }
    let mut returned = grouped
        .into_iter()
        .map(
            |(
                (operation, left_face, right_face),
                (candidate_nodes, occurrence_uses, witness_nodes),
            )| {
                FactorFace {
                    module_exterior: bundle.module_exterior.clone(),
                    operation,
                    left_face,
                    right_face,
                    candidate_nodes,
                    occurrence_uses,
                    witness_nodes,
                }
            },
        )
        .collect::<Vec<_>>();
    returned.sort_by(|left, right| {
        right
            .occurrence_uses
            .cmp(&left.occurrence_uses)
            .then_with(|| left.operation.cmp(&right.operation))
    });
    returned.truncate(top);
    returned
}

fn algebraic_figures(bundle: &AtlasBundle, top: usize) -> Vec<FigureFace> {
    let (uses, _, _) = usage_counts(bundle);
    let mut grouped = BTreeMap::<(String, String), (usize, usize, Vec<usize>)>::new();
    for node in &bundle.expression_nodes {
        let Some((operation, _)) = application_spine(node.index, &bundle.expression_nodes) else {
            continue;
        };
        let Some(family) = figure_family(&operation) else {
            continue;
        };
        let entry = grouped
            .entry((family.to_owned(), operation))
            .or_insert_with(|| (0, 0, Vec::new()));
        entry.0 += 1;
        entry.1 += uses[node.index];
        if entry.2.len() < 8 {
            entry.2.push(node.index);
        }
    }
    let mut returned = grouped
        .into_iter()
        .map(
            |((family, operation), (distinct_nodes, occurrence_uses, witness_nodes))| FigureFace {
                module_exterior: bundle.module_exterior.clone(),
                family,
                operation,
                distinct_nodes,
                occurrence_uses,
                witness_nodes,
            },
        )
        .collect::<Vec<_>>();
    returned.sort_by(|left, right| {
        right
            .occurrence_uses
            .cmp(&left.occurrence_uses)
            .then_with(|| left.operation.cmp(&right.operation))
    });
    returned.truncate(top);
    returned
}

fn report(bundle: &AtlasBundle, top: usize) -> AtlasReport {
    let (uses, roots, _) = usage_counts(bundle);
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
        expression_use_edges: bundle.expression_uses.len(),
        expression_use_multiplicity: uses.into_iter().sum(),
        root_expression_occurrences: roots.into_iter().sum(),
        distinct_declarations_used: distinct_declarations_used.len(),
        expression_kinds: top_faces(expression_kinds, top),
        recurring_expression_faces: top_faces(recurring_expression_faces, top),
        recurring_expression_usage: recurring_usage(bundle, top),
        literal_integer_faces: literal_integer_faces(bundle, top),
        factor_candidates: factor_candidates(bundle, top),
        algebraic_figures: algebraic_figures(bundle, top),
        recurring_goal_targets: top_faces(recurring_goal_targets, top),
        proof_event_elaborators: top_faces(proof_event_elaborators, top),
        theorem_body_roots: top_faces(theorem_body_roots, top),
    }
}

fn corpus_report(bundles: &[AtlasBundle], top: usize) -> CorpusReport {
    let mut recurring_expression_faces = BTreeMap::new();
    let mut usage_grouped = BTreeMap::<String, UsageAccumulator>::new();
    let mut corpus_literals = Vec::new();
    let mut corpus_factors = Vec::new();
    let mut corpus_figures = Vec::new();
    let mut expression_nodes = 0;
    let mut declaration_operations = 0;
    let mut theorem_bodies = 0;
    let mut term_occurrences = 0;
    let mut proof_events = 0;
    let mut expression_use_edges = 0;
    let mut expression_use_multiplicity = 0;
    let mut root_expression_occurrences = 0;
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
        expression_use_edges += bundle.expression_uses.len();
        let (uses, roots, _) = usage_counts(bundle);
        expression_use_multiplicity += uses.into_iter().sum::<usize>();
        root_expression_occurrences += roots.into_iter().sum::<usize>();
        modules.push(bundle.module_exterior.clone());
        for node in &bundle.expression_nodes {
            increment(
                &mut recurring_expression_faces,
                format!("{}|{}", node.kind_exterior, node.face_exterior),
            );
        }
        for usage in recurring_usage(bundle, usize::MAX) {
            let entry = usage_grouped.entry(usage.face).or_default();
            entry.distinct_nodes += usage.distinct_nodes;
            entry.occurrence_uses += usage.occurrence_uses;
            entry.root_occurrences += usage.root_occurrences;
            entry.child_occurrences += usage.child_occurrences;
        }
        corpus_literals.extend(literal_integer_faces(bundle, usize::MAX));
        corpus_factors.extend(factor_candidates(bundle, usize::MAX));
        corpus_figures.extend(algebraic_figures(bundle, usize::MAX));
    }
    modules.sort();
    let recurring_expression_usage = top_usage(usage_grouped, top);
    corpus_literals.sort_by(|left, right| {
        right
            .occurrence_uses
            .cmp(&left.occurrence_uses)
            .then_with(|| left.module_exterior.cmp(&right.module_exterior))
    });
    corpus_literals.truncate(top);
    corpus_factors.sort_by(|left, right| {
        right
            .occurrence_uses
            .cmp(&left.occurrence_uses)
            .then_with(|| left.module_exterior.cmp(&right.module_exterior))
    });
    corpus_factors.truncate(top);
    corpus_figures.sort_by(|left, right| {
        right
            .occurrence_uses
            .cmp(&left.occurrence_uses)
            .then_with(|| left.operation.cmp(&right.operation))
    });
    corpus_figures.truncate(top);
    CorpusReport {
        schema: SCHEMA.to_owned(),
        bundles: bundles.len(),
        expression_nodes,
        declaration_operations,
        theorem_bodies,
        term_occurrences,
        proof_events,
        expression_use_edges,
        expression_use_multiplicity,
        root_expression_occurrences,
        modules,
        recurring_expression_faces: top_faces(recurring_expression_faces, top),
        recurring_expression_usage,
        literal_integer_faces: corpus_literals,
        factor_candidates: corpus_factors,
        algebraic_figures: corpus_figures,
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
        schema: "holonics.derivation-atlas-manifest.v2".to_owned(),
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

    #[test]
    fn literal_faces_keep_the_elaborated_kind_and_value() {
        assert_eq!(
            parse_literal("Lean.Literal.natVal 17"),
            Some(("natural", "17".to_owned()))
        );
        assert_eq!(
            parse_literal("Lean.Literal.intVal (Int.negSucc 2)"),
            Some(("integer", "(Int.negSucc 2)".to_owned()))
        );
    }
}
