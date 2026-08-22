//! Exact exterior Lean return for the M6 source occurrence.
//!
//! Lean elaborates and checks the addressed S0 tree outside the productive body.  This owner
//! condenses repeated expression standing into addressed faces, resolves declaration references
//! into occurrence contacts, derives the transition-source population from those contacts, and
//! mounts only the resulting causal return into Athena's private namespace.  Names, source paths,
//! syntax and tactic elaborator labels remain exterior realization testimony; none is handed to
//! the route selector as a semantic category.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    os::unix::fs::symlink,
    path::{Component, Path},
    process::Command,
    time::Instant,
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::source::{self, SourceManifest};

pub const MANIFEST: &str = "causal-return-manifest.json";
const DECLARATIONS: &str = "declaration-operation-return.json";
const TRACE_ROOT: &str = "apparatus/lean-s0";
const CURRENT_FORMAL_ROOT: &str = "soma/formal/elementary-holonics";
const EXTRACTOR: &str = ".lake/build/bin/m6_lean_causal_return";
const TARGET_DECLARATION_EXTERIOR: &str =
    "Soma.Holonics.Millennium.Descent.TheFaceIsAHomomorphismEverywhere";

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RawExpressionFace {
    rendered_exterior: String,
    lean_structural_hash_exterior: String,
    ordered_transport_root: usize,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RawExpressionNode {
    index: usize,
    node_face_exterior: String,
    children: Vec<usize>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RawLocalStanding {
    index: usize,
    free_occurrence_exterior: String,
    user_face_exterior: String,
    binder_face_exterior: String,
    kind_face_exterior: String,
    #[serde(rename = "type")]
    type_face: RawExpressionFace,
    value: Option<RawExpressionFace>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RawGoalFace {
    goal_occurrence_exterior: String,
    user_face_exterior: String,
    local_standing: Vec<RawLocalStanding>,
    target: RawExpressionFace,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RawTermOccurrence {
    parent_declaration_exterior: String,
    elaborator_exterior: String,
    start_byte: usize,
    stop_byte: usize,
    syntax_exterior: String,
    expression: RawExpressionFace,
    expected_type: Option<RawExpressionFace>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RawTacticTransition {
    parent_declaration_exterior: String,
    elaborator_exterior: String,
    start_byte: usize,
    stop_byte: usize,
    syntax_exterior: String,
    before: Vec<RawGoalFace>,
    after: Vec<RawGoalFace>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RawDeclarationOperation {
    declaration_exterior: String,
    module_exterior: String,
    kind_exterior: String,
    #[serde(rename = "type")]
    type_face: RawExpressionFace,
    defining_value: Option<RawExpressionFace>,
    body_references_exterior: Vec<String>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RawCausalReceipt {
    schema: String,
    source_path_exterior: String,
    expression_nodes: Vec<RawExpressionNode>,
    declaration_operations: Vec<RawDeclarationOperation>,
    term_occurrences: Vec<RawTermOccurrence>,
    tactic_transitions: Vec<RawTacticTransition>,
    syntax_and_names_are_exterior: bool,
    truth_status: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExpressionFace {
    pub occurrence: String,
    pub structural_face: String,
    pub lean_hashes_exterior: BTreeSet<String>,
    pub rendered_faces_exterior: BTreeSet<String>,
    pub root_transport_node: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TransportNode {
    pub occurrence: String,
    pub structural_face: String,
    pub node_face_exterior: String,
    pub children: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DeclarationOperation {
    pub occurrence: String,
    pub declaration_exterior: String,
    pub module_exterior: String,
    pub kind_exterior: String,
    pub type_face: String,
    pub defining_value: Option<String>,
    pub referenced_operations: BTreeSet<String>,
    pub unresolved_operation_faces_exterior: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalStanding {
    pub index: usize,
    pub free_occurrence_exterior: String,
    pub user_face_exterior: String,
    pub binder_face_exterior: String,
    pub kind_face_exterior: String,
    pub type_face: String,
    pub value_face: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GoalFace {
    pub occurrence: String,
    pub structural_face: String,
    pub goal_occurrence_exterior: String,
    pub user_face_exterior: String,
    pub local_standing: Vec<LocalStanding>,
    pub target_face: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TermOccurrence {
    pub occurrence: String,
    pub parent_operation: Option<String>,
    pub parent_declaration_exterior: String,
    pub elaborator_exterior: String,
    pub start_byte: usize,
    pub stop_byte: usize,
    pub syntax_sha256_exterior: String,
    pub expression_face: String,
    pub expected_type_face: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TacticTransition {
    pub occurrence: String,
    pub parent_operation: Option<String>,
    pub parent_declaration_exterior: String,
    pub elaborator_exterior: String,
    pub start_byte: usize,
    pub stop_byte: usize,
    pub syntax_sha256_exterior: String,
    pub before: Vec<GoalFace>,
    pub after: Vec<GoalFace>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DeclarationReturn {
    pub schema: String,
    pub source_occurrence: String,
    pub root_source_path_exterior: String,
    pub expression_faces: BTreeMap<String, ExpressionFace>,
    pub transport_nodes: BTreeMap<String, TransportNode>,
    pub declaration_operations: Vec<DeclarationOperation>,
    pub operation_contacts: Vec<OperationContact>,
    pub target_operation: String,
    pub target_seed_operations: BTreeSet<String>,
    pub carrier_operations: BTreeSet<String>,
    pub transition_source_modules: BTreeSet<String>,
    pub transition_source_paths: BTreeSet<String>,
    pub selection_law: String,
    pub exterior_faces_do_not_route: bool,
    pub truth_status: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OperationContact {
    pub occurrence: String,
    pub from_operation: String,
    pub to_operation: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TransitionReturn {
    pub schema: String,
    pub source_occurrence: String,
    pub source_path_exterior: String,
    pub expression_faces: BTreeMap<String, ExpressionFace>,
    pub transport_nodes: BTreeMap<String, TransportNode>,
    pub term_occurrences: Vec<TermOccurrence>,
    pub tactic_transitions: Vec<TacticTransition>,
    pub syntax_and_names_are_exterior: bool,
    pub truth_status: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnFace {
    pub relative_path: String,
    pub source_path_exterior: String,
    pub octets: u64,
    pub sha256: String,
    pub term_occurrences: usize,
    pub tactic_transitions: usize,
    pub expression_faces: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExpensiveInvocation {
    pub command_exterior: Vec<String>,
    pub purpose: String,
    pub code_closure: Vec<String>,
    pub elapsed_milliseconds: u128,
    pub exit_status: i32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CausalReturnManifest {
    pub schema: String,
    pub source_occurrence: String,
    pub source_content_sha256: String,
    pub s0_trace_root_lineage: String,
    pub declaration_return: ReturnFace,
    pub transition_returns: Vec<ReturnFace>,
    pub target_operation: String,
    pub selected_source_paths: BTreeSet<String>,
    pub invocations: Vec<ExpensiveInvocation>,
    pub productive_mount_contains_lean: bool,
    pub productive_mount_contains_source_build_cache: bool,
    pub truth_status: String,
}

#[derive(Debug)]
pub struct MountedCausalReturn {
    pub manifest: CausalReturnManifest,
    pub declarations: DeclarationReturn,
    pub transitions: Vec<TransitionReturn>,
    pub opened_paths: Vec<String>,
}

pub fn prepare(
    workspace: &Path,
    source_root: &Path,
    source_manifest: &SourceManifest,
    destination: &Path,
) -> Result<CausalReturnManifest, String> {
    if destination.exists() {
        return Err(format!(
            "causal-return destination exists: {}",
            destination.display()
        ));
    }
    let trace_root = destination
        .parent()
        .ok_or_else(|| "causal-return destination has no apparatus parent".to_owned())?
        .join("lean-s0");
    if trace_root.exists() {
        return Err(format!(
            "S0 Lean trace root exists: {}",
            trace_root.display()
        ));
    }
    copy_source_occurrence(source_root, source_manifest, &trace_root)?;
    let packages = workspace.join(CURRENT_FORMAL_ROOT).join(".lake/packages");
    if !packages.is_dir() {
        return Err(format!(
            "the admitted Mathlib package cache is absent: {}",
            packages.display()
        ));
    }
    fs::create_dir_all(trace_root.join(".lake"))
        .map_err(|error| format!("create S0 Lake boundary: {error}"))?;
    symlink(&packages, trace_root.join(".lake/packages"))
        .map_err(|error| format!("bind admitted Mathlib packages into S0: {error}"))?;

    let mut invocations = Vec::new();
    let build_started = Instant::now();
    let build = Command::new("lake")
        .args(["build", "ElementaryHolonics"])
        .current_dir(&trace_root)
        .output()
        .map_err(|error| format!("build addressed S0 occurrence: {error}"))?;
    let build_status = build.status.code().unwrap_or(-1);
    invocations.push(ExpensiveInvocation {
        command_exterior: vec!["lake".to_owned(), "build".to_owned(), "ElementaryHolonics".to_owned()],
        purpose: "elaborate the exact S0 occurrence so its typed operation/state return can be observed; T0 is absent".to_owned(),
        code_closure: vec![source_manifest.occurrence.clone(), source_manifest.content_sha256.clone()],
        elapsed_milliseconds: build_started.elapsed().as_millis(),
        exit_status: build_status,
    });
    if !build.status.success() {
        return Err(format!(
            "S0 elaboration refused (status {build_status}):\n{}\n{}",
            String::from_utf8_lossy(&build.stdout),
            String::from_utf8_lossy(&build.stderr)
        ));
    }
    eprintln!(
        "M6 exterior apparatus: exact S0 elaboration returned in {} ms",
        build_started.elapsed().as_millis()
    );

    let extractor = workspace.join(CURRENT_FORMAL_ROOT).join(EXTRACTOR);
    if !extractor.is_file() {
        return Err(format!(
            "the project-owned Lean causal-return apparatus is absent: {}",
            extractor.display()
        ));
    }
    let declaration_started = Instant::now();
    let raw_declarations = invoke_extractor(
        &extractor,
        &trace_root,
        "--declarations",
        "ElementaryHolonics.lean",
    )?;
    invocations.push(ExpensiveInvocation {
        command_exterior: vec![EXTRACTOR.to_owned(), "--declarations".to_owned(), "ElementaryHolonics.lean".to_owned()],
        purpose: "return every S0 declaration operation once and derive the receiver-compatible source population".to_owned(),
        code_closure: vec![source_manifest.occurrence.clone(), source::sha256(&fs::read(&extractor).map_err(|error| format!("read extractor: {error}"))?)],
        elapsed_milliseconds: declaration_started.elapsed().as_millis(),
        exit_status: 0,
    });
    let raw: RawCausalReceipt = serde_json::from_slice(&raw_declarations)
        .map_err(|error| format!("decode S0 declaration return: {error}"))?;
    let declarations = condense_declarations(source_manifest, raw)?;
    eprintln!(
        "M6 exterior apparatus: {} declaration operations selected {} transition source faces",
        declarations.declaration_operations.len(),
        declarations.transition_source_paths.len()
    );

    fs::create_dir_all(destination)
        .map_err(|error| format!("create {}: {error}", destination.display()))?;
    let declaration_bytes = serde_json::to_vec(&declarations)
        .map_err(|error| format!("encode declaration return: {error}"))?;
    fs::write(destination.join(DECLARATIONS), &declaration_bytes)
        .map_err(|error| format!("write declaration return: {error}"))?;
    let declaration_face = ReturnFace {
        relative_path: DECLARATIONS.to_owned(),
        source_path_exterior: "ElementaryHolonics.lean".to_owned(),
        octets: u64::try_from(declaration_bytes.len())
            .map_err(|_| "declaration return extent".to_owned())?,
        sha256: source::sha256(&declaration_bytes),
        term_occurrences: 0,
        tactic_transitions: 0,
        expression_faces: declarations.expression_faces.len(),
    };

    let mut transition_returns = Vec::new();
    for (at, path) in declarations.transition_source_paths.iter().enumerate() {
        eprintln!(
            "M6 exterior apparatus: transition face {}/{} {}",
            at + 1,
            declarations.transition_source_paths.len(),
            path
        );
        let started = Instant::now();
        let bytes = invoke_extractor(&extractor, &trace_root, "--transitions", path)?;
        invocations.push(ExpensiveInvocation {
            command_exterior: vec![EXTRACTOR.to_owned(), "--transitions".to_owned(), path.clone()],
            purpose: "return caused term occurrences and before/after proof states for one receiver-compatible S0 source face".to_owned(),
            code_closure: vec![source_manifest.occurrence.clone(), path.clone()],
            elapsed_milliseconds: started.elapsed().as_millis(),
            exit_status: 0,
        });
        let raw: RawCausalReceipt = serde_json::from_slice(&bytes)
            .map_err(|error| format!("decode S0 transition return for {path}: {error}"))?;
        let compact = condense_transitions(source_manifest, &declarations, raw)?;
        let relative_path = format!("transition-return-{at:04}.json");
        let compact_bytes = serde_json::to_vec(&compact)
            .map_err(|error| format!("encode transition return for {path}: {error}"))?;
        fs::write(destination.join(&relative_path), &compact_bytes)
            .map_err(|error| format!("write transition return for {path}: {error}"))?;
        transition_returns.push(ReturnFace {
            relative_path,
            source_path_exterior: path.clone(),
            octets: u64::try_from(compact_bytes.len())
                .map_err(|_| "transition return extent".to_owned())?,
            sha256: source::sha256(&compact_bytes),
            term_occurrences: compact.term_occurrences.len(),
            tactic_transitions: compact.tactic_transitions.len(),
            expression_faces: compact.expression_faces.len(),
        });
    }

    let manifest = CausalReturnManifest {
        schema: "holonics.m6.causal-return-manifest.v1".to_owned(),
        source_occurrence: source_manifest.occurrence.clone(),
        source_content_sha256: source_manifest.content_sha256.clone(),
        s0_trace_root_lineage: TRACE_ROOT.to_owned(),
        declaration_return: declaration_face,
        transition_returns,
        target_operation: declarations.target_operation.clone(),
        selected_source_paths: declarations.transition_source_paths.clone(),
        invocations,
        productive_mount_contains_lean: false,
        productive_mount_contains_source_build_cache: false,
        truth_status: "established-bounded".to_owned(),
    };
    source::write_json(&destination.join(MANIFEST), &manifest)?;
    Ok(manifest)
}

pub fn mount(root: &Path) -> Result<MountedCausalReturn, String> {
    let manifest_bytes = fs::read(root.join(MANIFEST))
        .map_err(|error| format!("read causal-return manifest: {error}"))?;
    let manifest: CausalReturnManifest = serde_json::from_slice(&manifest_bytes)
        .map_err(|error| format!("decode causal-return manifest: {error}"))?;
    if manifest.schema != "holonics.m6.causal-return-manifest.v1"
        || manifest.productive_mount_contains_lean
        || manifest.productive_mount_contains_source_build_cache
    {
        return Err("the mounted causal return is not the admitted M6 exterior return".to_owned());
    }
    let mut expected = BTreeSet::from([MANIFEST.to_owned()]);
    expected.insert(manifest.declaration_return.relative_path.clone());
    expected.extend(
        manifest
            .transition_returns
            .iter()
            .map(|face| face.relative_path.clone()),
    );
    let actual = relative_files(root)?;
    if actual != expected {
        return Err(format!(
            "causal-return population moved: expected {expected:?}, actual {actual:?}"
        ));
    }
    let declaration_bytes = verified_face(root, &manifest.declaration_return)?;
    let declarations: DeclarationReturn = serde_json::from_slice(&declaration_bytes)
        .map_err(|error| format!("decode declaration return: {error}"))?;
    if declarations.source_occurrence != manifest.source_occurrence
        || declarations.target_operation != manifest.target_operation
    {
        return Err("declaration return moved from its causal manifest".to_owned());
    }
    let mut transitions = Vec::new();
    for face in &manifest.transition_returns {
        let bytes = verified_face(root, face)?;
        let returned: TransitionReturn = serde_json::from_slice(&bytes)
            .map_err(|error| format!("decode {}: {error}", face.relative_path))?;
        if returned.source_occurrence != manifest.source_occurrence
            || returned.source_path_exterior != face.source_path_exterior
        {
            return Err(format!("transition return moved: {}", face.relative_path));
        }
        transitions.push(returned);
    }
    let mut opened_paths = vec![
        MANIFEST.to_owned(),
        manifest.declaration_return.relative_path.clone(),
    ];
    opened_paths.extend(
        manifest
            .transition_returns
            .iter()
            .map(|face| face.relative_path.clone()),
    );
    Ok(MountedCausalReturn {
        manifest,
        declarations,
        transitions,
        opened_paths,
    })
}

fn condense_declarations(
    source_manifest: &SourceManifest,
    raw: RawCausalReceipt,
) -> Result<DeclarationReturn, String> {
    if raw.schema != "holonics.m6.lean-causal-return.v1"
        || raw.source_path_exterior != "ElementaryHolonics.lean"
        || !raw.syntax_and_names_are_exterior
        || raw.declaration_operations.is_empty()
        || !raw.term_occurrences.is_empty()
        || !raw.tactic_transitions.is_empty()
    {
        return Err("the S0 root did not return a declaration-only causal face".to_owned());
    }
    let mut condenser = ExpressionCondenser::new(raw.expression_nodes.clone())?;
    let mut preliminary = Vec::new();
    for operation in raw.declaration_operations {
        let type_face = condenser.expression(operation.type_face.clone())?;
        let defining_value = operation
            .defining_value
            .clone()
            .map(|face| condenser.expression(face))
            .transpose()?;
        let occurrence = address(&[
            source_manifest.occurrence.as_bytes(),
            operation.declaration_exterior.as_bytes(),
            type_face.as_bytes(),
            defining_value.as_deref().unwrap_or("").as_bytes(),
        ]);
        preliminary.push((operation, occurrence, type_face, defining_value));
    }
    let by_name = preliminary
        .iter()
        .map(|(operation, occurrence, _, _)| {
            (operation.declaration_exterior.clone(), occurrence.clone())
        })
        .collect::<BTreeMap<_, _>>();
    if by_name.len() != preliminary.len() {
        return Err("S0 returned plural declarations under one exterior identity".to_owned());
    }
    let mut declaration_operations = Vec::new();
    let mut operation_contacts = Vec::new();
    for (operation, occurrence, type_face, defining_value) in preliminary {
        let mut referenced_operations = BTreeSet::new();
        let mut unresolved = BTreeSet::new();
        for face in std::iter::once(&type_face).chain(defining_value.iter()) {
            for reference in condenser.expression_references(face)? {
                if let Some(target) = by_name.get(&reference) {
                    if target != &occurrence && referenced_operations.insert(target.clone()) {
                        operation_contacts.push(OperationContact {
                            occurrence: address(&[occurrence.as_bytes(), target.as_bytes()]),
                            from_operation: occurrence.clone(),
                            to_operation: target.clone(),
                        });
                    }
                } else {
                    unresolved.insert(reference);
                }
            }
        }
        for reference in &operation.body_references_exterior {
            if let Some(target) = by_name.get(reference) {
                if target != &occurrence && referenced_operations.insert(target.clone()) {
                    operation_contacts.push(OperationContact {
                        occurrence: address(&[occurrence.as_bytes(), target.as_bytes()]),
                        from_operation: occurrence.clone(),
                        to_operation: target.clone(),
                    });
                }
            }
        }
        declaration_operations.push(DeclarationOperation {
            occurrence,
            declaration_exterior: operation.declaration_exterior,
            module_exterior: operation.module_exterior,
            kind_exterior: operation.kind_exterior,
            type_face,
            defining_value,
            referenced_operations,
            unresolved_operation_faces_exterior: unresolved,
        });
    }
    declaration_operations.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    operation_contacts.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    let target = by_name
        .get(TARGET_DECLARATION_EXTERIOR)
        .cloned()
        .ok_or_else(|| "the declared M6 target operation is absent from S0".to_owned())?;
    let by_occurrence = declaration_operations
        .iter()
        .map(|operation| (operation.occurrence.clone(), operation))
        .collect::<BTreeMap<_, _>>();
    let target_operation = by_occurrence[&target];
    let target_seed_operations = target_operation.referenced_operations.clone();
    if target_seed_operations.is_empty() {
        return Err("the M6 target returned no founded source-operation contacts".to_owned());
    }
    // A carrier enters exactly when its declared type/direct proposition body makes contact with
    // one of the target's founded source operations.  The criterion is incidence, not a score,
    // name substring, file kind, tactic kind or caller-selected population.
    let mut carrier_operations = BTreeSet::from([target.clone()]);
    carrier_operations.extend(target_seed_operations.iter().cloned());
    for operation in &declaration_operations {
        if !operation
            .referenced_operations
            .is_disjoint(&target_seed_operations)
        {
            carrier_operations.insert(operation.occurrence.clone());
        }
    }
    // Carry every dependency required by an admitted carrier.  This is a least fixed point, not a
    // depth or capacity constant.
    let mut front = carrier_operations.iter().cloned().collect::<VecDeque<_>>();
    while let Some(at) = front.pop_front() {
        if let Some(operation) = by_occurrence.get(&at) {
            for dependency in &operation.referenced_operations {
                if carrier_operations.insert(dependency.clone()) {
                    front.push_back(dependency.clone());
                }
            }
        }
    }
    let transition_source_modules = carrier_operations
        .iter()
        .filter_map(|occurrence| {
            by_occurrence
                .get(occurrence)
                .map(|operation| operation.module_exterior.clone())
        })
        .collect::<BTreeSet<_>>();
    let transition_source_paths = transition_source_modules
        .iter()
        .map(|module| module_to_path(module))
        .collect::<Result<BTreeSet<_>, _>>()?;
    let admitted_paths = source_manifest
        .files
        .iter()
        .map(|face| face.relative_path.as_str())
        .collect::<BTreeSet<_>>();
    for path in &transition_source_paths {
        if !admitted_paths.contains(path.as_str()) {
            return Err(format!(
                "an operation-derived source face is absent from S0: {path}"
            ));
        }
    }
    Ok(DeclarationReturn {
        schema: "holonics.m6.declaration-operation-return.v3".to_owned(),
        source_occurrence: source_manifest.occurrence.clone(),
        root_source_path_exterior: raw.source_path_exterior,
        expression_faces: condenser.expressions,
        transport_nodes: condenser.nodes,
        declaration_operations,
        operation_contacts,
        target_operation: target,
        target_seed_operations,
        carrier_operations,
        transition_source_modules,
        transition_source_paths,
        selection_law: "least dependency-closed population containing the target and every declaration whose elaborated type, theorem body or direct-proposition body contacts a source operation carried by the target; exterior names resolve references once and are discarded before traversal".to_owned(),
        exterior_faces_do_not_route: true,
        truth_status: raw.truth_status,
    })
}

fn condense_transitions(
    source_manifest: &SourceManifest,
    declarations: &DeclarationReturn,
    raw: RawCausalReceipt,
) -> Result<TransitionReturn, String> {
    if raw.schema != "holonics.m6.lean-causal-return.v1"
        || !raw.syntax_and_names_are_exterior
        || !raw.declaration_operations.is_empty()
    {
        return Err(format!(
            "{} did not return a transition-only causal face",
            raw.source_path_exterior
        ));
    }
    let by_name = declarations
        .declaration_operations
        .iter()
        .map(|operation| {
            (
                operation.declaration_exterior.as_str(),
                operation.occurrence.as_str(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut condenser = ExpressionCondenser::new(raw.expression_nodes.clone())?;
    let mut terms = Vec::new();
    for term in raw.term_occurrences {
        let expression_face = condenser.expression(term.expression)?;
        let expected_type_face = term
            .expected_type
            .map(|face| condenser.expression(face))
            .transpose()?;
        let syntax_sha256_exterior = source::sha256(term.syntax_exterior.as_bytes());
        terms.push(TermOccurrence {
            occurrence: address(&[
                source_manifest.occurrence.as_bytes(),
                raw.source_path_exterior.as_bytes(),
                &term.start_byte.to_le_bytes(),
                &term.stop_byte.to_le_bytes(),
                expression_face.as_bytes(),
            ]),
            parent_operation: by_name
                .get(term.parent_declaration_exterior.as_str())
                .map(|value| (*value).to_owned()),
            parent_declaration_exterior: term.parent_declaration_exterior,
            elaborator_exterior: term.elaborator_exterior,
            start_byte: term.start_byte,
            stop_byte: term.stop_byte,
            syntax_sha256_exterior,
            expression_face,
            expected_type_face,
        });
    }
    let mut transitions = Vec::new();
    for transition in raw.tactic_transitions {
        let before = transition
            .before
            .into_iter()
            .map(|goal| condense_goal(&mut condenser, goal))
            .collect::<Result<Vec<_>, _>>()?;
        let after = transition
            .after
            .into_iter()
            .map(|goal| condense_goal(&mut condenser, goal))
            .collect::<Result<Vec<_>, _>>()?;
        let syntax_sha256_exterior = source::sha256(transition.syntax_exterior.as_bytes());
        let before_word = before
            .iter()
            .map(|goal| goal.occurrence.as_str())
            .collect::<Vec<_>>()
            .join("|");
        let after_word = after
            .iter()
            .map(|goal| goal.occurrence.as_str())
            .collect::<Vec<_>>()
            .join("|");
        transitions.push(TacticTransition {
            occurrence: address(&[
                source_manifest.occurrence.as_bytes(),
                raw.source_path_exterior.as_bytes(),
                &transition.start_byte.to_le_bytes(),
                &transition.stop_byte.to_le_bytes(),
                before_word.as_bytes(),
                after_word.as_bytes(),
            ]),
            parent_operation: by_name
                .get(transition.parent_declaration_exterior.as_str())
                .map(|value| (*value).to_owned()),
            parent_declaration_exterior: transition.parent_declaration_exterior,
            elaborator_exterior: transition.elaborator_exterior,
            start_byte: transition.start_byte,
            stop_byte: transition.stop_byte,
            syntax_sha256_exterior,
            before,
            after,
        });
    }
    Ok(TransitionReturn {
        schema: "holonics.m6.operation-state-transition-return.v2".to_owned(),
        source_occurrence: source_manifest.occurrence.clone(),
        source_path_exterior: raw.source_path_exterior,
        expression_faces: condenser.expressions,
        transport_nodes: condenser.nodes,
        term_occurrences: terms,
        tactic_transitions: transitions,
        syntax_and_names_are_exterior: true,
        truth_status: raw.truth_status,
    })
}

fn condense_goal(
    condenser: &mut ExpressionCondenser,
    raw: RawGoalFace,
) -> Result<GoalFace, String> {
    let mut local_standing = Vec::new();
    for standing in raw.local_standing {
        local_standing.push(LocalStanding {
            index: standing.index,
            free_occurrence_exterior: standing.free_occurrence_exterior,
            user_face_exterior: standing.user_face_exterior,
            binder_face_exterior: standing.binder_face_exterior,
            kind_face_exterior: standing.kind_face_exterior,
            type_face: condenser.expression(standing.type_face)?,
            value_face: standing
                .value
                .map(|face| condenser.expression(face))
                .transpose()?,
        });
    }
    let target_face = condenser.expression(raw.target)?;
    let mut exact = vec![target_face.clone()];
    let mut structural = vec![condenser.expressions[&target_face].structural_face.clone()];
    for standing in &local_standing {
        exact.push(standing.type_face.clone());
        structural.push(
            condenser.expressions[&standing.type_face]
                .structural_face
                .clone(),
        );
        if let Some(value) = &standing.value_face {
            exact.push(value.clone());
            structural.push(condenser.expressions[value].structural_face.clone());
        }
    }
    let structural_face = address(
        &structural
            .iter()
            .map(|member| member.as_bytes())
            .collect::<Vec<_>>(),
    );
    let exact_face = address(
        &exact
            .iter()
            .map(|member| member.as_bytes())
            .collect::<Vec<_>>(),
    );
    let occurrence = address(&[
        raw.goal_occurrence_exterior.as_bytes(),
        exact_face.as_bytes(),
    ]);
    Ok(GoalFace {
        occurrence,
        structural_face,
        goal_occurrence_exterior: raw.goal_occurrence_exterior,
        user_face_exterior: raw.user_face_exterior,
        local_standing,
        target_face,
    })
}

fn structural_node_face(member: &str) -> String {
    let mut parts = member.split('|');
    match parts.next().unwrap_or("") {
        "free" => "free".to_owned(),
        "open" => "open".to_owned(),
        "lambda" => format!("lambda|{}", parts.nth(1).unwrap_or("")),
        "forall" => format!("forall|{}", parts.nth(1).unwrap_or("")),
        "let" => "let".to_owned(),
        "have" => "have".to_owned(),
        "application" => "application".to_owned(),
        other => format!("{other}|{}", parts.collect::<Vec<_>>().join("|")),
    }
}

struct ExpressionCondenser {
    raw_nodes: Vec<RawExpressionNode>,
    exact_addresses: Vec<Option<String>>,
    structural_addresses: Vec<Option<String>>,
    nodes: BTreeMap<String, TransportNode>,
    expressions: BTreeMap<String, ExpressionFace>,
}

impl ExpressionCondenser {
    fn new(raw_nodes: Vec<RawExpressionNode>) -> Result<Self, String> {
        for (at, node) in raw_nodes.iter().enumerate() {
            if node.index != at || node.children.iter().any(|child| *child >= at) {
                return Err(format!(
                    "Lean expression DAG is not child-first at node {at}"
                ));
            }
        }
        let extent = raw_nodes.len();
        Ok(Self {
            raw_nodes,
            exact_addresses: vec![None; extent],
            structural_addresses: vec![None; extent],
            nodes: BTreeMap::new(),
            expressions: BTreeMap::new(),
        })
    }

    fn expression(&mut self, raw: RawExpressionFace) -> Result<String, String> {
        let root = self.node(raw.ordered_transport_root)?;
        let structural_face = self.structural_addresses[raw.ordered_transport_root]
            .clone()
            .ok_or_else(|| "expression structural root was not founded".to_owned())?;
        let occurrence = root.clone();
        let held = self
            .expressions
            .entry(occurrence.clone())
            .or_insert_with(|| ExpressionFace {
                occurrence: occurrence.clone(),
                structural_face: structural_face.clone(),
                lean_hashes_exterior: BTreeSet::new(),
                rendered_faces_exterior: BTreeSet::new(),
                root_transport_node: root,
            });
        if held.structural_face != structural_face {
            return Err("one exact expression returned plural structural faces".to_owned());
        }
        held.lean_hashes_exterior
            .insert(raw.lean_structural_hash_exterior);
        held.rendered_faces_exterior.insert(raw.rendered_exterior);
        Ok(occurrence)
    }

    fn node(&mut self, index: usize) -> Result<String, String> {
        if let Some(address) = self.exact_addresses.get(index).and_then(Clone::clone) {
            return Ok(address);
        }
        let raw = self
            .raw_nodes
            .get(index)
            .ok_or_else(|| format!("expression root is absent: {index}"))?
            .clone();
        let mut children = Vec::new();
        let mut structural_children = Vec::new();
        for child in raw.children {
            children.push(self.node(child)?);
            structural_children.push(
                self.structural_addresses[child]
                    .clone()
                    .ok_or_else(|| "child structural address was not founded".to_owned())?,
            );
        }
        let occurrence = address(
            &std::iter::once(raw.node_face_exterior.as_bytes())
                .chain(children.iter().map(|child| child.as_bytes()))
                .collect::<Vec<_>>(),
        );
        let structural_node = structural_node_face(&raw.node_face_exterior);
        let structural_face = address(
            &std::iter::once(structural_node.as_bytes())
                .chain(structural_children.iter().map(|child| child.as_bytes()))
                .collect::<Vec<_>>(),
        );
        let node = TransportNode {
            occurrence: occurrence.clone(),
            structural_face: structural_face.clone(),
            node_face_exterior: raw.node_face_exterior,
            children,
        };
        if let Some(prior) = self.nodes.get(&occurrence) {
            if prior != &node {
                return Err("a transport-node address collision reopened its fibre".to_owned());
            }
        } else {
            self.nodes.insert(occurrence.clone(), node);
        }
        self.exact_addresses[index] = Some(occurrence.clone());
        self.structural_addresses[index] = Some(structural_face);
        Ok(occurrence)
    }

    fn expression_references(&self, expression: &str) -> Result<BTreeSet<String>, String> {
        let face = self
            .expressions
            .get(expression)
            .ok_or_else(|| format!("expression face is absent: {expression}"))?;
        let mut returned = BTreeSet::new();
        let mut reached = BTreeSet::new();
        let mut front = vec![face.root_transport_node.as_str()];
        while let Some(at) = front.pop() {
            if !reached.insert(at) {
                continue;
            }
            let node = self
                .nodes
                .get(at)
                .ok_or_else(|| format!("transport node is absent: {at}"))?;
            let mut parts = node.node_face_exterior.split('|');
            if parts.next() == Some("constant") {
                if let Some(name) = parts.next() {
                    returned.insert(name.to_owned());
                }
            }
            front.extend(node.children.iter().map(String::as_str));
        }
        Ok(returned)
    }
}

fn module_to_path(module: &str) -> Result<String, String> {
    let relative = module
        .strip_prefix("ElementaryHolonics")
        .ok_or_else(|| format!("foreign module entered S0 declaration population: {module}"))?;
    if relative.is_empty() {
        return Ok("ElementaryHolonics.lean".to_owned());
    }
    Ok(format!(
        "ElementaryHolonics{}.lean",
        relative.replace('.', "/")
    ))
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExteriorPassageProfile {
    pub schema: String,
    pub source_sha256: String,
    pub source_octets: u64,
    pub expression_nodes: usize,
    pub declaration_operations: usize,
    pub theorem_declarations: usize,
    pub term_occurrences: usize,
    pub tactic_transitions: usize,
    pub before_goal_population: usize,
    pub after_goal_population: usize,
    pub closed_transitions: usize,
    pub widened_transitions: usize,
    pub narrowed_transitions: usize,
    pub unchanged_width_transitions: usize,
    pub maximum_goal_width: usize,
    pub state_transition_operation_word_sha256: String,
    pub declared_proposition_types: BTreeSet<String>,
    pub target_receiver_declarations: BTreeMap<String, String>,
    pub invocations: Vec<ExpensiveInvocation>,
    pub truth_status: String,
}

/// Profile an emitted or withheld Lean passage after productive emission.  Declaration names,
/// syntax and tactic elaborators remain exterior testimony; the operation word is formed from the
/// ordered before/after proof-state shapes with constant names erased.
pub fn profile_exterior_passage(
    extractor: &Path,
    root: &Path,
    file: &Path,
) -> Result<ExteriorPassageProfile, String> {
    let source_bytes = fs::read(file).map_err(|error| {
        format!(
            "read exterior comparison passage {}: {error}",
            file.display()
        )
    })?;
    let file_face = file
        .to_str()
        .ok_or_else(|| format!("comparison passage path is not UTF-8: {}", file.display()))?;
    let mut invocations = Vec::new();
    let started = Instant::now();
    let declaration_bytes = invoke_extractor(extractor, root, "--declarations", file_face)?;
    invocations.push(ExpensiveInvocation {
        command_exterior: vec![
            extractor.display().to_string(),
            "--declarations".to_owned(),
            file.display().to_string(),
        ],
        purpose: "return the post-emission declaration operation face".to_owned(),
        code_closure: vec![source::sha256(&source_bytes)],
        elapsed_milliseconds: started.elapsed().as_millis(),
        exit_status: 0,
    });
    let declarations = decode_raw_receipt(&declaration_bytes, "declaration")?;
    let started = Instant::now();
    let transition_bytes = invoke_extractor(extractor, root, "--transitions", file_face)?;
    invocations.push(ExpensiveInvocation {
        command_exterior: vec![
            extractor.display().to_string(),
            "--transitions".to_owned(),
            file.display().to_string(),
        ],
        purpose: "return the post-emission proof-state transition passage".to_owned(),
        code_closure: vec![source::sha256(&source_bytes)],
        elapsed_milliseconds: started.elapsed().as_millis(),
        exit_status: 0,
    });
    let transitions = decode_raw_receipt(&transition_bytes, "transition")?;
    for returned in [&declarations, &transitions] {
        if returned.schema != "holonics.m6.lean-causal-return.v1"
            || !returned.syntax_and_names_are_exterior
        {
            return Err("the exterior passage profiler returned another schema".to_owned());
        }
    }

    let declared_proposition_types = declarations
        .declaration_operations
        .iter()
        .filter(|operation| operation.kind_exterior == "theorem")
        .map(|operation| operation.type_face.rendered_exterior.clone())
        .collect::<BTreeSet<_>>();
    let target_receiver_declarations = declarations
        .declaration_operations
        .iter()
        .filter(|operation| {
            operation
                .type_face
                .rendered_exterior
                .contains("TheFaceIsAHomomorphismEverywhere")
                || operation
                    .declaration_exterior
                    .ends_with("heldOutCommutedFace")
                || operation
                    .declaration_exterior
                    .ends_with("generatedFaceHomomorphism")
        })
        .map(|operation| {
            (
                operation.declaration_exterior.clone(),
                operation.type_face.rendered_exterior.clone(),
            )
        })
        .collect();

    let before_goal_population = transitions
        .tactic_transitions
        .iter()
        .map(|transition| transition.before.len())
        .sum();
    let after_goal_population = transitions
        .tactic_transitions
        .iter()
        .map(|transition| transition.after.len())
        .sum();
    let mut operation_word = Sha256::new();
    let mut shape_memo = BTreeMap::new();
    for transition in &transitions.tactic_transitions {
        operation_word.update((transition.before.len() as u64).to_le_bytes());
        for goal in &transition.before {
            let shape = expression_shape(
                &transitions.expression_nodes,
                goal.target.ordered_transport_root,
                &mut shape_memo,
            )?;
            framed(&mut operation_word, shape.as_bytes());
        }
        operation_word.update((transition.after.len() as u64).to_le_bytes());
        for goal in &transition.after {
            let shape = expression_shape(
                &transitions.expression_nodes,
                goal.target.ordered_transport_root,
                &mut shape_memo,
            )?;
            framed(&mut operation_word, shape.as_bytes());
        }
    }
    let closed_transitions = transitions
        .tactic_transitions
        .iter()
        .filter(|transition| !transition.before.is_empty() && transition.after.is_empty())
        .count();
    let widened_transitions = transitions
        .tactic_transitions
        .iter()
        .filter(|transition| transition.after.len() > transition.before.len())
        .count();
    let narrowed_transitions = transitions
        .tactic_transitions
        .iter()
        .filter(|transition| transition.after.len() < transition.before.len())
        .count();
    let unchanged_width_transitions =
        transitions.tactic_transitions.len() - widened_transitions - narrowed_transitions;
    let maximum_goal_width = transitions
        .tactic_transitions
        .iter()
        .flat_map(|transition| [transition.before.len(), transition.after.len()])
        .max()
        .unwrap_or(0);
    Ok(ExteriorPassageProfile {
        schema: "holonics.m6.exterior-operation-state-profile.v1".to_owned(),
        source_sha256: source::sha256(&source_bytes),
        source_octets: source_bytes.len() as u64,
        expression_nodes: transitions.expression_nodes.len(),
        declaration_operations: declarations.declaration_operations.len(),
        theorem_declarations: declarations
            .declaration_operations
            .iter()
            .filter(|operation| operation.kind_exterior == "theorem")
            .count(),
        term_occurrences: transitions.term_occurrences.len(),
        tactic_transitions: transitions.tactic_transitions.len(),
        before_goal_population,
        after_goal_population,
        closed_transitions,
        widened_transitions,
        narrowed_transitions,
        unchanged_width_transitions,
        maximum_goal_width,
        state_transition_operation_word_sha256: hex(&operation_word.finalize()),
        declared_proposition_types,
        target_receiver_declarations,
        invocations,
        truth_status: "established-bounded".to_owned(),
    })
}

fn decode_raw_receipt(bytes: &[u8], face: &str) -> Result<RawCausalReceipt, String> {
    let marker = b"{\"declarationOperations\"";
    let start = bytes
        .windows(marker.len())
        .position(|window| window == marker)
        .ok_or_else(|| format!("the {face} comparison return contains no JSON receipt"))?;
    serde_json::from_slice(&bytes[start..])
        .map_err(|error| format!("decode {face} comparison return: {error}"))
}

fn expression_shape(
    nodes: &[RawExpressionNode],
    at: usize,
    memo: &mut BTreeMap<usize, String>,
) -> Result<String, String> {
    if let Some(held) = memo.get(&at) {
        return Ok(held.clone());
    }
    let node = nodes
        .get(at)
        .ok_or_else(|| format!("proof-state transport node is absent: {at}"))?;
    if node.index != at {
        return Err(format!(
            "proof-state transport node moved: expected {at}, got {}",
            node.index
        ));
    }
    let kind = node.node_face_exterior.split('|').next().unwrap_or("");
    let mut digest = Sha256::new();
    framed(&mut digest, kind.as_bytes());
    for child in &node.children {
        let child = expression_shape(nodes, *child, memo)?;
        framed(&mut digest, child.as_bytes());
    }
    let returned = hex(&digest.finalize());
    memo.insert(at, returned.clone());
    Ok(returned)
}

fn invoke_extractor(
    extractor: &Path,
    root: &Path,
    mode: &str,
    file: &str,
) -> Result<Vec<u8>, String> {
    let returned = Command::new(extractor)
        .args([mode, file])
        .current_dir(root)
        .output()
        .map_err(|error| format!("invoke Lean causal return for {file}: {error}"))?;
    if !returned.status.success() {
        return Err(format!(
            "Lean causal return refused for {file}:\n{}\n{}",
            String::from_utf8_lossy(&returned.stdout),
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(returned.stdout)
}

fn copy_source_occurrence(
    source_root: &Path,
    manifest: &SourceManifest,
    target: &Path,
) -> Result<(), String> {
    fs::create_dir_all(target).map_err(|error| format!("create {}: {error}", target.display()))?;
    for face in &manifest.files {
        let source_path = source_root.join(&face.relative_path);
        let bytes = fs::read(&source_path)
            .map_err(|error| format!("read {}: {error}", source_path.display()))?;
        if source::sha256(&bytes) != face.sha256 {
            return Err(format!(
                "source face moved before S0 elaboration: {}",
                face.relative_path
            ));
        }
        let target_path = target.join(&face.relative_path);
        if let Some(parent) = target_path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create {}: {error}", parent.display()))?;
        }
        fs::write(&target_path, bytes)
            .map_err(|error| format!("write {}: {error}", target_path.display()))?;
    }
    Ok(())
}

fn verified_face(root: &Path, face: &ReturnFace) -> Result<Vec<u8>, String> {
    lawful_relative(&face.relative_path)?;
    let bytes = fs::read(root.join(&face.relative_path))
        .map_err(|error| format!("read {}: {error}", face.relative_path))?;
    let octets = u64::try_from(bytes.len()).map_err(|_| "causal return extent".to_owned())?;
    if octets != face.octets || source::sha256(&bytes) != face.sha256 {
        return Err(format!("causal return moved: {}", face.relative_path));
    }
    Ok(bytes)
}

fn relative_files(root: &Path) -> Result<BTreeSet<String>, String> {
    fn walk(root: &Path, at: &Path, returned: &mut BTreeSet<String>) -> Result<(), String> {
        let mut entries = fs::read_dir(at)
            .map_err(|error| format!("read {}: {error}", at.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("read {}: {error}", at.display()))?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let kind = entry
                .file_type()
                .map_err(|error| format!("read entry type: {error}"))?;
            if kind.is_dir() {
                walk(root, &entry.path(), returned)?;
            } else if kind.is_file() {
                let relative = entry
                    .path()
                    .strip_prefix(root)
                    .map_err(|error| format!("rebase causal return: {error}"))?
                    .to_string_lossy()
                    .replace('\\', "/");
                lawful_relative(&relative)?;
                returned.insert(relative);
            } else {
                return Err(format!(
                    "unsupported causal return entry: {}",
                    entry.path().display()
                ));
            }
        }
        Ok(())
    }
    let mut returned = BTreeSet::new();
    walk(root, root, &mut returned)?;
    Ok(returned)
}

fn lawful_relative(relative: &str) -> Result<(), String> {
    let path = Path::new(relative);
    if relative.is_empty()
        || path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(format!(
            "causal return path escapes its occurrence: {relative}"
        ));
    }
    Ok(())
}

fn address(parts: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    for part in parts {
        framed(&mut hasher, part);
    }
    hex(&hasher.finalize())
}

fn framed(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|octet| format!("{octet:02x}")).collect()
}
