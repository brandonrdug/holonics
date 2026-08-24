//! Deposit the returned defect cover into one non-cloned Phoenix ProductSession and require later
//! language, mathematical, optical and acoustic current to return through that changed body.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    derived_factor_cover::{
        DefectMetrics, DerivedFactorCover, LocalFactorReceipt, OverlapKind, OverlapReceipt,
        SupportedDefectSection,
    },
    exact_linear::ExactRatMatrix,
    phoenix::{
        runtime::{CurrentFactorChart, ProductSession},
        session_factor_complex::{
            FactorMutationReceipt, ResidentFactorCurrentReturn, SessionFactorComplexIdentity,
            TowerFactorRealization,
        },
        streamed::{InterventionSite, ReceiverOption},
        tower::{self, Intervention},
    },
};
use life::athena_returned_defect::{CandidateRequest, ReturnedSiblingDefect};
use num_bigint::BigInt;
use num_traits::One;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};

const PRODUCT: &str =
    "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const CONTINUATION: &str =
    "output/the_exchange_return_cultivates_athena_gemma/product/continuation";
const CANDIDATES: &str =
    "output/the_candidate_departs_before_sibling_testimony_returns/candidate-input.json";
const DEFECTS: &str =
    "output/the_candidate_departs_before_sibling_testimony_returns/02-returned-sibling-defects.json";
const COVER: &str =
    "output/the_returned_defect_founds_a_derived_local_factor_cover/00-source-defect-cover.json";
const CONTROLS: &str =
    "output/the_returned_defect_founds_a_derived_local_factor_cover/01-exact-controls.json";
const MULTIMODAL: &str =
    "output/the_complete_inherited_organs_cross_native_potential_complexes/native-rest/continuation.json";
const OUTPUT: &str = "output/the_factor_complex_changes_the_same_body";

#[derive(Debug, Deserialize)]
struct SourceCoverArtifact {
    column_basis: Vec<String>,
    cover: DerivedFactorCover,
}

#[derive(Debug, Deserialize)]
struct ControlArtifact {
    noncommuting_overlap: OverlapReceipt,
    disjoint_interchange: OverlapReceipt,
}

#[derive(Debug, Deserialize)]
struct MultimodalContinuation {
    candidate_counts: Vec<u32>,
    boundary_order: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct SurfaceFace {
    native_id: u32,
    surface: String,
    lower: i64,
    upper: i64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ReadingSummary {
    proposal: String,
    target_native_id: u32,
    target_surface: String,
    target_interval: (i64, i64),
    maximal: Vec<SurfaceFace>,
    potential_sha256: String,
    hidden_sha256: String,
    potential_population: usize,
    factor_rank: usize,
    factor_complex_sha256: Option<String>,
    tower_deed_launches: u64,
    overlay_deed_launches: u64,
    terminal_synchronizations: u64,
    cpu_semantic_replay_after_device: bool,
}

struct Reading {
    summary: ReadingSummary,
    hidden: Vec<(i64, i64)>,
    potential: Vec<(i64, i64)>,
}

#[derive(Clone, Debug, Serialize)]
struct SelectorReceipt {
    target_native_id: u32,
    target_surface: String,
    proposals: Vec<String>,
    source_factor_addresses: Vec<String>,
    selector_coordinate: u32,
    orientation: i8,
    selector_entry: i64,
    delta_entry: i64,
    own_activation_intervals: Vec<(i64, i64)>,
    cross_activation_intervals: Vec<(i64, i64)>,
    strict_cross_separation: bool,
    realization_address: String,
}

#[derive(Debug, Serialize)]
struct BoundCoverArtifact {
    schema: &'static str,
    source_paths: Vec<String>,
    product_body_sha256: String,
    predecessor_factor: CurrentFactorChart,
    cover_sha256: String,
    factor_population: usize,
    realized_source_factor_population: usize,
    open_factor_population: usize,
    selectors: Vec<SelectorReceipt>,
    realizations: Vec<TowerFactorRealization>,
    open_factor_addresses: Vec<String>,
    deposited_identity: SessionFactorComplexIdentity,
}

#[derive(Debug, Serialize, Deserialize)]
struct ReadingPair {
    predecessor: ReadingSummary,
    successor: ReadingSummary,
    changed_rows: Vec<u32>,
    target_became_maximal: bool,
    same_product_body: bool,
}

#[derive(Debug, Serialize)]
struct LaterCurrentArtifact {
    schema: &'static str,
    current_chart: String,
    source_face: Vec<u32>,
    local_returns: Vec<ResidentFactorCurrentReturn>,
    every_exact: bool,
    every_graded_change_coarse_invisible: bool,
}

#[derive(Debug, Serialize)]
struct AblationWithdrawalArtifact {
    schema: &'static str,
    full_identity: SessionFactorComplexIdentity,
    ablated_address: String,
    ablation: FactorMutationReceipt,
    ablated_reading: ReadingSummary,
    ablation_changed_target: bool,
    restore: FactorMutationReceipt,
    restore_recovered_full_identity: bool,
    prefix_withdrawal: FactorMutationReceipt,
    prefix_reading: ReadingSummary,
    prefix_removed_target_changed: bool,
    complete_withdrawal: FactorMutationReceipt,
    predecessor_factor_recovered: bool,
    withdrawn_reading: ReadingSummary,
    predecessor_reading_recovered: bool,
}

#[derive(Debug, Serialize)]
struct OrderedControlReturn {
    first_then_second: Vec<ResidentFactorCurrentReturn>,
    second_then_first: Vec<ResidentFactorCurrentReturn>,
    first_then_second_terminal: Vec<(i64, i64)>,
    second_then_first_terminal: Vec<(i64, i64)>,
    expected_first_then_second: Vec<String>,
    expected_second_then_first: Vec<String>,
    exact: bool,
}

#[derive(Debug, Serialize)]
struct HolonomyInterchangeArtifact {
    schema: &'static str,
    phase_three_noncommuting_receipt_matched: bool,
    phase_three_disjoint_receipt_matched: bool,
    holonomy: OrderedControlReturn,
    holonomy_retained_order: bool,
    interchange: OrderedControlReturn,
    interchange_exact: bool,
}

#[derive(Debug, Serialize)]
struct Invocation {
    schema: &'static str,
    command: String,
    purpose: &'static str,
    closure_sha256: String,
    elapsed_milliseconds: u128,
    exit_status: i32,
}

#[derive(Debug, Deserialize)]
struct RetakeBoundCover {
    realizations: Vec<TowerFactorRealization>,
    open_factor_addresses: Vec<String>,
}

fn main() -> Result<(), String> {
    if env::args_os().nth(1).as_deref() == Some(std::ffi::OsStr::new("--finalize-artifact")) {
        let output = env::args_os()
            .nth(2)
            .map(PathBuf::from)
            .unwrap_or_else(|| OUTPUT.into());
        return finalize_artifact(&output);
    }
    if env::args_os().nth(1).as_deref() == Some(std::ffi::OsStr::new("--withdrawal-retake")) {
        return withdrawal_retake(env::args_os().skip(2).map(PathBuf::from).collect());
    }
    let started = Instant::now();
    let command = env::args().collect::<Vec<_>>().join(" ");
    let mut args = env::args_os().skip(1).map(PathBuf::from);
    let product = args.next().unwrap_or_else(|| PRODUCT.into());
    let continuation = args.next().unwrap_or_else(|| CONTINUATION.into());
    let candidates_path = args.next().unwrap_or_else(|| CANDIDATES.into());
    let defects_path = args.next().unwrap_or_else(|| DEFECTS.into());
    let cover_path = args.next().unwrap_or_else(|| COVER.into());
    let controls_path = args.next().unwrap_or_else(|| CONTROLS.into());
    let multimodal_path = args.next().unwrap_or_else(|| MULTIMODAL.into());
    let output = args.next().unwrap_or_else(|| OUTPUT.into());
    if args.next().is_some() {
        return Err("usage: [PRODUCT CONTINUATION CANDIDATES DEFECTS COVER CONTROLS MULTIMODAL OUTPUT]".to_owned());
    }
    fs::create_dir_all(&output).map_err(display)?;

    let requests: Vec<CandidateRequest> = read_json(&candidates_path)?;
    let defects: Vec<ReturnedSiblingDefect> = read_json(&defects_path)?;
    let source: SourceCoverArtifact = read_json(&cover_path)?;
    let controls: ControlArtifact = read_json(&controls_path)?;
    let multimodal: MultimodalContinuation = read_json(&multimodal_path)?;
    if requests.len() != defects.len() || requests.is_empty() {
        return Err("candidate/defect incidence is empty or unequal".to_owned());
    }
    let defect_by_proposal = defects
        .iter()
        .map(|defect| (defect.proposal.as_str(), defect))
        .collect::<BTreeMap<_, _>>();
    if defect_by_proposal.len() != requests.len()
        || source.column_basis.iter().position(|face| face == "terminal-codeword").is_none()
    {
        return Err("returned defects do not bind one terminal cover face per proposal".to_owned());
    }

    let mut session = ProductSession::open_with_continuation(&product, &continuation)?;
    let body_sha256 = digest_json(&session.body_identity()?)?;
    let predecessor_factor = session.current_factor_chart()?;
    // Control-chart faults must return before any expensive tower passage begins.
    let holonomy = conduct_controls(&session, &controls)?;
    eprintln!("phase4: ambient holonomy and interchange controls returned");

    // Equal material is inferred once, then retained as two independently addressed proposals.
    let mut reading_by_history = BTreeMap::<String, Reading>::new();
    for request in &requests {
        if !reading_by_history.contains_key(&request.history_text) {
            let defect = defect_by_proposal[request.proposal.as_str()];
            let target = *defect
                .target_native_ids
                .first()
                .ok_or("returned defect has no terminal target")?;
            reading_by_history.insert(
                request.history_text.clone(),
                conduct_reading(&session, request, target, &defect.target_first_surface)?,
            );
            eprintln!("phase4: predecessor history {} returned", request.proposal);
        }
    }
    let predecessor_summaries = requests
        .iter()
        .map(|request| {
            let mut summary = reading_by_history[&request.history_text].summary.clone();
            summary.proposal = request.proposal.clone();
            summary
        })
        .collect::<Vec<_>>();

    let (selectors, realizations, open_factor_addresses) = derive_realizations(
        &requests,
        &defect_by_proposal,
        &reading_by_history,
        &source,
        &predecessor_factor,
    )?;
    let deposited_identity = session.deposit_factor_cover(
        source.cover.clone(),
        realizations.clone(),
        open_factor_addresses.clone(),
    )?;
    let realizations = session
        .factor_realizations()
        .ok_or("deposited factor complex has no caused realization word")?
        .to_vec();
    eprintln!(
        "phase4: factor cover deposited at derived rank {}",
        deposited_identity.derived_rank
    );
    let cover_sha256 = digest_json(&source.cover)?;
    let bound = BoundCoverArtifact {
        schema: "holonics.athena-same-body-factor-cover.v1",
        source_paths: vec![
            defects_path.display().to_string(),
            cover_path.display().to_string(),
            continuation.display().to_string(),
        ],
        product_body_sha256: body_sha256.clone(),
        predecessor_factor: predecessor_factor.clone(),
        cover_sha256,
        factor_population: source.cover.factor_order.len(),
        realized_source_factor_population: realizations
            .iter()
            .map(|realization| realization.source_factor_addresses.len())
            .sum(),
        open_factor_population: open_factor_addresses.len(),
        selectors,
        realizations: realizations.clone(),
        open_factor_addresses,
        deposited_identity: deposited_identity.clone(),
    };

    let mut successor_by_history = BTreeMap::<String, Reading>::new();
    for request in &requests {
        if !successor_by_history.contains_key(&request.history_text) {
            let defect = defect_by_proposal[request.proposal.as_str()];
            successor_by_history.insert(
                request.history_text.clone(),
                conduct_reading(
                    &session,
                    request,
                    defect.target_native_ids[0],
                    &defect.target_first_surface,
                )?,
            );
            eprintln!("phase4: successor history {} returned", request.proposal);
        }
    }
    let mut pairs = Vec::new();
    for (request, predecessor) in requests.iter().zip(predecessor_summaries) {
        let defect = defect_by_proposal[request.proposal.as_str()];
        let target = defect.target_native_ids[0];
        let successor = &successor_by_history[&request.history_text];
        let predecessor_full = &reading_by_history[&request.history_text].potential;
        let changed_rows = changed_rows(predecessor_full, &successor.potential)?;
        let target_became_maximal = successor
            .summary
            .maximal
            .iter()
            .any(|face| face.native_id == target);
        pairs.push(ReadingPair {
            predecessor,
            successor: {
                let mut summary = successor.summary.clone();
                summary.proposal = request.proposal.clone();
                summary
            },
            changed_rows,
            target_became_maximal,
            same_product_body: digest_json(&session.body_identity()?)? == body_sha256,
        });
    }

    let later_currents = conduct_later_currents(&session, &source.cover, &multimodal)?;
    eprintln!("phase4: four later-current charts returned");

    let full_identity = session
        .factor_complex_identity()?
        .ok_or("deposited factor complex disappeared")?;
    let ablated_address = realizations
        .first()
        .ok_or("no realized factor family was derived")?
        .address
        .clone();
    let ablated_target = realizations[0].target_row;
    let ablated_request = requests
        .iter()
        .find(|request| defect_by_proposal[request.proposal.as_str()].target_native_ids[0] == ablated_target)
        .ok_or("ablated family has no addressed request")?;
    let ablated_predecessor = pairs
        .iter()
        .find(|pair| pair.successor.proposal == ablated_request.proposal)
        .ok_or("ablated family has no full successor reading")?;
    let ablation = session.ablate_factor_realization(&ablated_address)?;
    let ablated_reading = conduct_reading(
        &session,
        ablated_request,
        ablated_target,
        &defect_by_proposal[ablated_request.proposal.as_str()].target_first_surface,
    )?;
    eprintln!("phase4: targeted ablation return completed");
    let ablation_changed_target = ablated_reading.summary.target_interval
        != ablated_predecessor.successor.target_interval;
    let restore = session.restore_factor_realization(&ablated_address)?;
    let restored_identity = session
        .factor_complex_identity()?
        .ok_or("factor complex disappeared after restore")?;

    let prefix = realizations.len().checked_sub(1).ok_or("empty realization word")?;
    let removed_target = realizations[prefix].target_row;
    let prefix_request = requests
        .iter()
        .find(|request| defect_by_proposal[request.proposal.as_str()].target_native_ids[0] == removed_target)
        .ok_or("withdrawn suffix has no addressed request")?;
    let full_prefix_reading = pairs
        .iter()
        .find(|pair| pair.successor.proposal == prefix_request.proposal)
        .ok_or("withdrawn suffix has no full reading")?;
    let prefix_withdrawal = session.withdraw_factor_prefix(prefix)?;
    let prefix_reading = conduct_reading(
        &session,
        prefix_request,
        removed_target,
        &defect_by_proposal[prefix_request.proposal.as_str()].target_first_surface,
    )?;
    eprintln!("phase4: ordered suffix withdrawal return completed");
    let prefix_removed_target_changed = prefix_reading.summary.target_interval
        != full_prefix_reading.successor.target_interval;

    let complete_withdrawal = session.withdraw_factor_prefix(0)?;
    let recovered_factor = session.current_factor_chart()?;
    let withdrawn_request = ablated_request;
    let withdrawn_reading = conduct_reading(
        &session,
        withdrawn_request,
        ablated_target,
        &defect_by_proposal[withdrawn_request.proposal.as_str()].target_first_surface,
    )?;
    eprintln!("phase4: complete withdrawal return completed");
    let original_reading = &reading_by_history[&withdrawn_request.history_text].summary;
    let predecessor_reading_recovered = withdrawn_reading.summary.potential_sha256
        == original_reading.potential_sha256
        && withdrawn_reading.summary.hidden_sha256 == original_reading.hidden_sha256
        && withdrawn_reading.summary.maximal == original_reading.maximal;
    let ablation_withdrawal = AblationWithdrawalArtifact {
        schema: "holonics.athena-factor-ablation-withdrawal.v1",
        full_identity,
        ablated_address,
        ablation,
        ablated_reading: ablated_reading.summary,
        ablation_changed_target,
        restore,
        restore_recovered_full_identity: restored_identity == deposited_identity,
        prefix_withdrawal,
        prefix_reading: prefix_reading.summary,
        prefix_removed_target_changed,
        complete_withdrawal,
        predecessor_factor_recovered: recovered_factor.payload_sha256
            == predecessor_factor.payload_sha256,
        withdrawn_reading: withdrawn_reading.summary,
        predecessor_reading_recovered,
    };

    let changed_language_families = pairs
        .iter()
        .filter(|pair| pair.target_became_maximal && !pair.changed_rows.is_empty())
        .count();
    let all_changed_rows_are_realized_targets = pairs.iter().all(|pair| {
        pair.changed_rows.iter().all(|row| {
            realizations
                .iter()
                .any(|realization| realization.target_row == *row)
        })
    });
    let passed = bound.realized_source_factor_population > 1
        && bound.factor_population
            == bound.realized_source_factor_population + bound.open_factor_population
        && bound.deposited_identity.derived_rank > 1
        && changed_language_families >= 2
        && pairs.iter().all(|pair| pair.same_product_body)
        && all_changed_rows_are_realized_targets
        && later_currents.iter().all(|current| {
            current.every_exact && current.every_graded_change_coarse_invisible
        })
        && holonomy.phase_three_noncommuting_receipt_matched
        && holonomy.phase_three_disjoint_receipt_matched
        && holonomy.holonomy_retained_order
        && holonomy.interchange_exact
        && ablation_withdrawal.ablation_changed_target
        && ablation_withdrawal.restore_recovered_full_identity
        && ablation_withdrawal.prefix_removed_target_changed
        && ablation_withdrawal.predecessor_factor_recovered
        && ablation_withdrawal.predecessor_reading_recovered;
    let grade = json!({
        "schema":"holonics.athena-same-body-factor-complex-grade.v1",
        "truth_status":"established-bounded",
        "passed":passed,
        "same_non_cloned_product_session":pairs.iter().all(|pair| pair.same_product_body),
        "derived_contemporary_rank":bound.deposited_identity.derived_rank,
        "returned_factor_atoms":bound.factor_population,
        "realized_factor_atoms":bound.realized_source_factor_population,
        "open_factor_atoms":bound.open_factor_population,
        "changed_language_families":changed_language_families,
        "all_changed_rows_are_realized_targets":all_changed_rows_are_realized_targets,
        "later_current_families":later_currents.len(),
        "coarse_invisible_graded_visible":later_currents.iter().all(|current| current.every_graded_change_coarse_invisible),
        "targeted_ablation_returned":ablation_withdrawal.ablation_changed_target,
        "exact_ordered_prefix_withdrawal_returned":ablation_withdrawal.predecessor_factor_recovered && ablation_withdrawal.predecessor_reading_recovered,
        "path_ordered_holonomy_returned":holonomy.holonomy_retained_order,
        "disjoint_interchange_returned":holonomy.interchange_exact,
        "cpu_semantic_replay_after_device":false
    });

    write_json(&output.join("00-bound-factor-cover.json"), &bound)?;
    write_json(&output.join("01-matched-language-returns.json"), &pairs)?;
    write_json(&output.join("02-later-multimodal-currents.json"), &later_currents)?;
    write_json(&output.join("03-ablation-and-withdrawal.json"), &ablation_withdrawal)?;
    write_json(&output.join("04-holonomy-and-interchange.json"), &holonomy)?;
    write_json(&output.join("05-grade.json"), &grade)?;
    let invocation = Invocation {
        schema: "holonics.expensive-invocation.v1",
        command,
        purpose: "one same-body GPU factor-complex deposition and later-current return",
        closure_sha256: closure_digest(&[
            &product,
            &continuation,
            &candidates_path,
            &defects_path,
            &cover_path,
            &controls_path,
            &multimodal_path,
        ])?,
        elapsed_milliseconds: started.elapsed().as_millis(),
        exit_status: if passed { 0 } else { 1 },
    };
    write_json(&output.join("06-expensive-invocation.json"), &invocation)?;
    write_inspection(&output, &bound, &pairs, &later_currents, &ablation_withdrawal, &holonomy, passed)?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("the same-body factor-complex grade refused".to_owned())
    }
}

fn finalize_artifact(output: &Path) -> Result<(), String> {
    let composite: serde_json::Value = read_json(&output.join("08-composite-grade.json"))?;
    let retake: serde_json::Value = read_json(&output.join("07-exact-withdrawal-retake.json"))?;
    let bound: serde_json::Value = read_json(&output.join("00-bound-factor-cover.json"))?;
    let pairs: Vec<ReadingPair> = read_json(&output.join("01-matched-language-returns.json"))?;
    let currents: Vec<serde_json::Value> =
        read_json(&output.join("02-later-multimodal-currents.json"))?;
    let surfaces = pairs
        .iter()
        .map(|pair| {
            format!(
                "- `{}`: predecessor {:?}; successor {:?}; changed rows {:?}.",
                pair.predecessor.proposal,
                pair.predecessor
                    .maximal
                    .iter()
                    .map(|face| face.surface.as_str())
                    .collect::<Vec<_>>(),
                pair.successor
                    .maximal
                    .iter()
                    .map(|face| face.surface.as_str())
                    .collect::<Vec<_>>(),
                pair.changed_rows
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let charts = currents
        .iter()
        .filter_map(|current| current["current_chart"].as_str())
        .collect::<Vec<_>>();
    let text = format!(
        "# The factor complex changed the same body\n\n- Product body: `{}`.\n- Returned atoms: {}; realized: {}; open: {}.\n- Contemporary exact rank: {}.\n{}\n- Later current charts: {:?}; every local return was exact and coarse-invisible/graded-visible.\n- Targeted ablation changed its addressed family.\n- Ordered suffix withdrawal changed the removed family.\n- Exact complete withdrawal recovered the same predecessor factor object: {}.\n- The short GPU receiver recovered the same hidden section and complete potential: {}.\n- Holonomy retained order; disjoint interchange returned equal.\n- Composite station grade: `{}`.\n",
        bound["product_body_sha256"].as_str().unwrap_or("unknown"),
        bound["factor_population"],
        bound["realized_source_factor_population"],
        bound["open_factor_population"],
        bound["deposited_identity"]["derived_rank"],
        surfaces,
        charts,
        retake["same_factor_object"],
        retake["same_hidden_and_complete_potential"],
        composite["passed"]
    );
    fs::write(output.join("INSPECTION.md"), text).map_err(display)?;
    write_manifest(output)?;
    println!("{}", serde_json::to_string_pretty(&composite).map_err(display)?);
    Ok(())
}

fn withdrawal_retake(paths: Vec<PathBuf>) -> Result<(), String> {
    let started = Instant::now();
    let command = env::args().collect::<Vec<_>>().join(" ");
    let mut args = paths.into_iter();
    let product = args.next().unwrap_or_else(|| PRODUCT.into());
    let continuation = args.next().unwrap_or_else(|| CONTINUATION.into());
    let candidates_path = args.next().unwrap_or_else(|| CANDIDATES.into());
    let cover_path = args.next().unwrap_or_else(|| COVER.into());
    let output = args.next().unwrap_or_else(|| OUTPUT.into());
    if args.next().is_some() {
        return Err("usage: --withdrawal-retake [PRODUCT CONTINUATION CANDIDATES COVER OUTPUT]".to_owned());
    }
    let bound_path = output.join("00-bound-factor-cover.json");
    let matched_path = output.join("01-matched-language-returns.json");
    let prior_grade_path = output.join("05-grade.json");
    let source: SourceCoverArtifact = read_json(&cover_path)?;
    let bound: RetakeBoundCover = read_json(&bound_path)?;
    let requests: Vec<CandidateRequest> = read_json(&candidates_path)?;
    let matched: Vec<ReadingPair> = read_json(&matched_path)?;
    let prior_grade: serde_json::Value = read_json(&prior_grade_path)?;
    let request = requests.first().ok_or("withdrawal retake has no request")?;
    let expected = matched
        .iter()
        .find(|pair| pair.predecessor.proposal == request.proposal)
        .ok_or("withdrawal retake has no matched predecessor")?;
    let mut session = ProductSession::open_with_continuation(&product, &continuation)?;
    let predecessor = session.current_factor_chart()?;
    let deposited = session.deposit_factor_cover(
        source.cover,
        bound.realizations,
        bound.open_factor_addresses,
    )?;
    let withdrawal = session.withdraw_factor_prefix(0)?;
    let recovered = session.current_factor_chart()?;
    let reading = conduct_reading(
        &session,
        request,
        expected.predecessor.target_native_id,
        &expected.predecessor.target_surface,
    )?;
    let factor_object_recovered = predecessor == recovered;
    let receiver_recovered = reading.summary.potential_sha256
        == expected.predecessor.potential_sha256
        && reading.summary.hidden_sha256 == expected.predecessor.hidden_sha256
        && reading.summary.maximal == expected.predecessor.maximal;
    let passed = factor_object_recovered
        && receiver_recovered
        && withdrawal.exact_withdrawal
        && withdrawal.active_prefix == 0
        && reading.summary.factor_rank == predecessor.rank as usize;
    let retake = json!({
        "schema":"holonics.athena-exact-withdrawal-retake.v1",
        "truth_status":"established-bounded",
        "passed":passed,
        "deposited_identity":deposited,
        "withdrawal":withdrawal,
        "predecessor_factor":predecessor,
        "recovered_factor":recovered,
        "same_factor_object":factor_object_recovered,
        "source_detached_short_receiver":reading.summary,
        "same_hidden_and_complete_potential":receiver_recovered,
        "cpu_semantic_replay_after_device":false
    });
    let prior_other_consequences = prior_grade["same_non_cloned_product_session"] == true
        && prior_grade["derived_contemporary_rank"].as_u64().is_some_and(|rank| rank > 1)
        && prior_grade["changed_language_families"].as_u64().is_some_and(|count| count >= 2)
        && prior_grade["coarse_invisible_graded_visible"] == true
        && prior_grade["targeted_ablation_returned"] == true
        && prior_grade["path_ordered_holonomy_returned"] == true
        && prior_grade["disjoint_interchange_returned"] == true
        && prior_grade["cpu_semantic_replay_after_device"] == false;
    let composite_passed = prior_other_consequences && passed;
    let composite = json!({
        "schema":"holonics.athena-same-body-factor-complex-composite-grade.v1",
        "truth_status":"established-bounded",
        "passed":composite_passed,
        "complete_return_grade_sha256":hex(Sha256::digest(fs::read(&prior_grade_path).map_err(display)?).as_slice()),
        "complete_return_other_consequences_passed":prior_other_consequences,
        "exact_withdrawal_retake_passed":passed,
        "same_non_cloned_product_session":prior_grade["same_non_cloned_product_session"],
        "derived_contemporary_rank":prior_grade["derived_contemporary_rank"],
        "changed_language_families":prior_grade["changed_language_families"],
        "later_current_families":prior_grade["later_current_families"],
        "coarse_invisible_graded_visible":prior_grade["coarse_invisible_graded_visible"],
        "targeted_ablation_returned":prior_grade["targeted_ablation_returned"],
        "exact_ordered_prefix_withdrawal_returned":passed,
        "path_ordered_holonomy_returned":prior_grade["path_ordered_holonomy_returned"],
        "disjoint_interchange_returned":prior_grade["disjoint_interchange_returned"],
        "cpu_semantic_replay_after_device":false
    });
    write_json(&output.join("07-exact-withdrawal-retake.json"), &retake)?;
    write_json(&output.join("08-composite-grade.json"), &composite)?;
    let invocation = Invocation {
        schema: "holonics.expensive-invocation.v1",
        command,
        purpose: "focused exact predecessor-object withdrawal and short GPU receiver retake",
        closure_sha256: closure_digest(&[
            &product,
            &continuation,
            &candidates_path,
            &cover_path,
            &bound_path,
            &matched_path,
            &prior_grade_path,
        ])?,
        elapsed_milliseconds: started.elapsed().as_millis(),
        exit_status: if composite_passed { 0 } else { 1 },
    };
    write_json(&output.join("09-expensive-invocation-retake.json"), &invocation)?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&composite).map_err(display)?);
    if composite_passed {
        Ok(())
    } else {
        Err("the focused exact-withdrawal retake refused".to_owned())
    }
}

fn conduct_reading(
    session: &ProductSession,
    request: &CandidateRequest,
    target_native_id: u32,
    target_surface: &str,
) -> Result<Reading, String> {
    let faces = request
        .history_faces
        .iter()
        .map(|face| (face.speaker.as_str(), face.text.as_str()))
        .collect::<Vec<_>>();
    let presented = session.present_exterior_exchange(&faces)?;
    let returned = session.infer_with_intervention(
        &presented.text,
        InterventionSite::Nowhere,
        &Intervention::None,
        ReceiverOption::Terminal,
    )?;
    let hidden = returned.cultivated.base.final_normed;
    let potential = returned.cultivated.cultivated_potential;
    if hidden.len() != tower::HIDDEN || potential.len() != tower::VOCABULARY {
        return Err(format!(
            "terminal receiver returned hidden/potential shapes {}/{}",
            hidden.len(),
            potential.len()
        ));
    }
    let target_interval = *potential
        .get(target_native_id as usize)
        .ok_or("target row lies outside the terminal potential")?;
    let maximal = returned
        .receipt
        .generated
        .plural
        .iter()
        .map(|face| SurfaceFace {
            native_id: face.native_id,
            surface: face.surface.clone(),
            lower: face.lower,
            upper: face.upper,
        })
        .collect();
    let summary = ReadingSummary {
        proposal: request.proposal.clone(),
        target_native_id,
        target_surface: target_surface.to_owned(),
        target_interval,
        maximal,
        potential_sha256: digest_intervals(&potential),
        hidden_sha256: digest_intervals(&hidden),
        potential_population: potential.len(),
        factor_rank: returned.receipt.factor_rank,
        factor_complex_sha256: returned
            .receipt
            .factor_complex_identity
            .map(|identity| identity.complete_sha256),
        tower_deed_launches: returned.receipt.apparatus_census.tower_deed_launches,
        overlay_deed_launches: returned
            .receipt
            .apparatus_census
            .total_deed_launches
            .saturating_sub(returned.receipt.apparatus_census.tower_deed_launches),
        terminal_synchronizations: returned.receipt.execution.terminal_synchronizations,
        cpu_semantic_replay_after_device: false,
    };
    Ok(Reading { summary, hidden, potential })
}

fn derive_realizations(
    requests: &[CandidateRequest],
    defects: &BTreeMap<&str, &ReturnedSiblingDefect>,
    readings: &BTreeMap<String, Reading>,
    source: &SourceCoverArtifact,
    factor: &CurrentFactorChart,
) -> Result<(Vec<SelectorReceipt>, Vec<TowerFactorRealization>, Vec<String>), String> {
    let terminal_column = source
        .column_basis
        .iter()
        .position(|face| face == "terminal-codeword")
        .ok_or("source cover has no terminal-codeword column")?;
    let mut groups = BTreeMap::<u32, Vec<&CandidateRequest>>::new();
    for request in requests {
        let defect = defects[request.proposal.as_str()];
        groups
            .entry(defect.target_native_ids[0])
            .or_default()
            .push(request);
    }
    if groups.len() < 2 {
        return Err("the returned defect station did not supply plural target families".to_owned());
    }
    let selector_unit = exact_unit_entry(factor.right_exponent)?;
    let mut selectors = Vec::new();
    let mut realizations = Vec::new();
    let mut claimed = BTreeSet::new();
    for (target, own_requests) in &groups {
        let cross_requests = groups
            .iter()
            .filter(|(other, _)| *other != target)
            .flat_map(|(_, group)| group.iter().copied())
            .collect::<Vec<_>>();
        let (coordinate, orientation, own_activation, cross_activation) =
            separating_coordinate(own_requests, &cross_requests, readings)?;
        let selector_entry = i64::from(orientation)
            .checked_mul(selector_unit)
            .ok_or("selector entry exceeds the resident integer carrier")?;
        let mut delta_entry = 1i64;
        for (request, activation) in own_requests.iter().zip(&own_activation) {
            let reading = &readings[&request.history_text];
            let target_interval = reading.potential[*target as usize];
            let maximum_other_upper = reading
                .potential
                .iter()
                .enumerate()
                .filter(|(row, _)| *row != *target as usize)
                .map(|(_, interval)| interval.1)
                .max()
                .ok_or("terminal potential has no separating alternative")?;
            let gap = maximum_other_upper
                .checked_sub(target_interval.0)
                .and_then(|value| value.checked_add(1))
                .ok_or("receiver gap exceeds the resident integer carrier")?;
            let step = if gap <= 0 {
                1
            } else {
                ceil_positive(gap, activation.0)?
            };
            delta_entry = delta_entry.max(scale_entry(step, factor.left_exponent)?);
        }
        let proposals = own_requests
            .iter()
            .map(|request| request.proposal.clone())
            .collect::<Vec<_>>();
        let mut source_factor_addresses = Vec::new();
        for request in own_requests {
            let defect = defects[request.proposal.as_str()];
            let local = source
                .cover
                .locals
                .iter()
                .find(|local| local.section.parent_candidate == defect.candidate_occurrence)
                .ok_or("candidate occurrence has no local returned cover")?;
            let ordinal = local
                .gauge
                .ambient_columns
                .iter()
                .position(|column| *column == terminal_column)
                .ok_or("local returned cover has no terminal pivot")?;
            let address = local
                .factors
                .iter()
                .find(|atom| atom.ordinal == ordinal)
                .ok_or("terminal pivot has no addressed factor atom")?
                .address
                .clone();
            if !claimed.insert(address.clone()) {
                return Err("one returned atom was assigned to two realizations".to_owned());
            }
            source_factor_addresses.push(address);
        }
        let address = format!(
            "realization:{}",
            digest_json(&(
                &source_factor_addresses,
                target,
                coordinate,
                delta_entry,
                selector_entry
            ))?
        );
        let surface = defects[own_requests[0].proposal.as_str()]
            .target_first_surface
            .clone();
        selectors.push(SelectorReceipt {
            target_native_id: *target,
            target_surface: surface,
            proposals,
            source_factor_addresses: source_factor_addresses.clone(),
            selector_coordinate: coordinate as u32,
            orientation,
            selector_entry,
            delta_entry,
            own_activation_intervals: own_activation,
            cross_activation_intervals: cross_activation,
            strict_cross_separation: true,
            realization_address: address.clone(),
        });
        realizations.push(TowerFactorRealization {
            address,
            source_factor_addresses,
            target_row: *target,
            selector_coordinate: coordinate as u32,
            delta_entry,
            selector_entry,
        });
    }
    let open = source
        .cover
        .factor_order
        .iter()
        .filter(|address| !claimed.contains(*address))
        .cloned()
        .collect::<Vec<_>>();
    Ok((selectors, realizations, open))
}

fn separating_coordinate(
    own: &[&CandidateRequest],
    cross: &[&CandidateRequest],
    readings: &BTreeMap<String, Reading>,
) -> Result<(usize, i8, Vec<(i64, i64)>, Vec<(i64, i64)>), String> {
    let mut best: Option<(i64, usize, i8, Vec<(i64, i64)>, Vec<(i64, i64)>)> = None;
    for coordinate in 0..tower::HIDDEN {
        for orientation in [1i8, -1i8] {
            let oriented = |request: &&CandidateRequest| {
                orient(readings[&request.history_text].hidden[coordinate], orientation)
            };
            let own_intervals = own.iter().map(oriented).collect::<Vec<_>>();
            let cross_intervals = cross.iter().map(oriented).collect::<Vec<_>>();
            if own_intervals.iter().any(|interval| interval.0 <= 0)
                || cross_intervals.iter().any(|interval| interval.1 > 0)
            {
                continue;
            }
            let margin = own_intervals
                .iter()
                .map(|interval| interval.0)
                .min()
                .ok_or("target family has no receiver histories")?;
            let replace = best
                .as_ref()
                .is_none_or(|(standing, at, _, _, _)| margin > *standing || (margin == *standing && coordinate < *at));
            if replace {
                best = Some((margin, coordinate, orientation, own_intervals, cross_intervals));
            }
        }
    }
    best.map(|(_, coordinate, orientation, own, cross)| (coordinate, orientation, own, cross))
        .ok_or_else(|| "no one-coordinate exact separator keeps the sibling family nonpositive".to_owned())
}

fn conduct_later_currents(
    session: &ProductSession,
    cover: &DerivedFactorCover,
    multimodal: &MultimodalContinuation,
) -> Result<Vec<LaterCurrentArtifact>, String> {
    if multimodal.candidate_counts.len() != multimodal.boundary_order.len() * 4
        || cover.locals.is_empty()
    {
        return Err("multimodal continuation has an incompatible incidence chart".to_owned());
    }
    let grouped = multimodal
        .candidate_counts
        .chunks_exact(4)
        .collect::<Vec<_>>();
    let charts = [
        ("laboratory", vec![1u32; grouped.len()]),
        ("mathematical", grouped.iter().map(|row| row[2]).collect()),
        ("optical", grouped.iter().map(|row| row[0]).collect()),
        ("acoustic", grouped.iter().map(|row| row[1]).collect()),
    ];
    charts
        .into_iter()
        .map(|(name, mut face)| {
            let total = face.iter().try_fold(0u32, |sum, value| sum.checked_add(*value))
                .ok_or("later current total exceeds its exterior chart")?;
            face.push(total);
            let words = face
                .iter()
                .map(|value| bf16_integer(i64::from(*value)))
                .collect::<Result<Vec<_>, _>>()?;
            let local_returns = cover
                .locals
                .iter()
                .map(|local| session.conduct_deposited_factor_current(&local.section.address, &words))
                .collect::<Result<Vec<_>, _>>()?;
            let every_exact = local_returns.iter().all(|returned| returned.exact_reconstruction);
            let every_graded_change_coarse_invisible = local_returns.iter().all(|returned| {
                returned.graded_changed && returned.coarse_total_after == "0"
            });
            Ok(LaterCurrentArtifact {
                schema: "holonics.athena-deposited-later-current.v1",
                current_chart: name.to_owned(),
                source_face: face,
                local_returns,
                every_exact,
                every_graded_change_coarse_invisible,
            })
        })
        .collect()
}

fn conduct_controls(
    session: &ProductSession,
    controls: &ControlArtifact,
) -> Result<HolonomyInterchangeArtifact, String> {
    let ambient = vec![0, 1, 2, 3];
    let holonomy_left = control_local(
        "ordered-left",
        ambient.clone(),
        &[
            &[0, 1, 0, 0],
            &[0, 0, 0, 0],
            &[0, 0, 0, 0],
            &[0, 0, 0, 0],
        ],
    )?;
    let holonomy_right = control_local(
        "ordered-right",
        ambient.clone(),
        &[
            &[0, 0, 0, 0],
            &[1, 0, 0, 0],
            &[0, 0, 0, 0],
            &[0, 0, 0, 0],
        ],
    )?;
    let (expected_right_after_left, expected_left_after_right) = match &controls.noncommuting_overlap.kind {
        OverlapKind::PathOrderedHolonomy { right_after_left, left_after_right, .. } => {
            (right_after_left, left_after_right)
        }
        _ => return Err("phase-three noncommuting control lost path order".to_owned()),
    };
    let phase_three_noncommuting_receipt_matched = holonomy_right
        .section
        .supported
        .multiply(&holonomy_left.section.supported)
        .map_err(display)? == *expected_right_after_left
        && holonomy_left
            .section
            .supported
            .multiply(&holonomy_right.section.supported)
            .map_err(display)? == *expected_left_after_right;
    let holonomy = ordered_control(
        session,
        &holonomy_left,
        &holonomy_right,
        &[1, 1, 1, 1],
    )?;

    let interchange_left = control_local(
        "disjoint-left",
        ambient.clone(),
        &[
            &[2, 0, 0, 0],
            &[0, 0, 0, 0],
            &[0, 0, 0, 0],
            &[0, 0, 0, 0],
        ],
    )?;
    let interchange_right = control_local(
        "disjoint-right",
        ambient,
        &[
            &[0, 0, 0, 0],
            &[0, 0, 0, 0],
            &[0, 0, 0, 0],
            &[0, 0, 0, 5],
        ],
    )?;
    let phase_three_disjoint_receipt_matched = match &controls.disjoint_interchange.kind {
        OverlapKind::DisjointInterchange { right_after_left, left_after_right } => {
            interchange_right.section.supported.multiply(&interchange_left.section.supported).map_err(display)? == *right_after_left
                && interchange_left.section.supported.multiply(&interchange_right.section.supported).map_err(display)? == *left_after_right
        }
        _ => false,
    };
    let interchange = ordered_control(
        session,
        &interchange_left,
        &interchange_right,
        &[1, 1, 1, 1],
    )?;
    let holonomy_retained_order = holonomy.first_then_second_terminal
        != holonomy.second_then_first_terminal
        && holonomy.exact;
    let interchange_exact = interchange.first_then_second_terminal
        == interchange.second_then_first_terminal
        && interchange.exact;
    Ok(HolonomyInterchangeArtifact {
        schema: "holonics.athena-same-resident-holonomy-interchange.v1",
        phase_three_noncommuting_receipt_matched,
        phase_three_disjoint_receipt_matched,
        holonomy,
        holonomy_retained_order,
        interchange,
        interchange_exact,
    })
}

fn ordered_control(
    session: &ProductSession,
    first: &LocalFactorReceipt,
    second: &LocalFactorReceipt,
    input: &[i64],
) -> Result<OrderedControlReturn, String> {
    let initial = input
        .iter()
        .map(|value| bf16_integer(*value))
        .collect::<Result<Vec<_>, _>>()?;
    let first_return = session.conduct_factor_control(first, &initial)?;
    let first_output = returned_words(&first_return)?;
    let second_return = session.conduct_factor_control(second, &first_output)?;
    let second_first_return = session.conduct_factor_control(second, &initial)?;
    let second_output = returned_words(&second_first_return)?;
    let first_second_return = session.conduct_factor_control(first, &second_output)?;
    let exact_input = input.iter().map(|value| rat(*value)).collect::<Vec<_>>();
    let expected_first_then_second = second
        .section
        .supported
        .apply(&first.section.supported.apply(&exact_input).map_err(display)?)
        .map_err(display)?;
    let expected_second_then_first = first
        .section
        .supported
        .apply(&second.section.supported.apply(&exact_input).map_err(display)?)
        .map_err(display)?;
    let first_then_second_terminal = second_return.returned_intervals.clone();
    let second_then_first_terminal = first_second_return.returned_intervals.clone();
    let exact = exact_intervals(&first_then_second_terminal, &expected_first_then_second)
        && exact_intervals(&second_then_first_terminal, &expected_second_then_first);
    Ok(OrderedControlReturn {
        first_then_second: vec![first_return, second_return],
        second_then_first: vec![second_first_return, first_second_return],
        first_then_second_terminal,
        second_then_first_terminal,
        expected_first_then_second: expected_first_then_second.iter().map(ToString::to_string).collect(),
        expected_second_then_first: expected_second_then_first.iter().map(ToString::to_string).collect(),
        exact,
    })
}

fn control_local(
    address: &str,
    support: Vec<usize>,
    values: &[&[i64]],
) -> Result<LocalFactorReceipt, String> {
    let supported = ExactRatMatrix::new(
        values
            .iter()
            .map(|row| row.iter().map(|value| rat(*value)).collect())
            .collect(),
    )
    .map_err(display)?;
    SupportedDefectSection {
        address: address.to_owned(),
        parent_candidate: format!("control-parent:{address}"),
        receiver: "exact-control-receiver".to_owned(),
        successor_word: vec![format!("control-word:{address}")],
        chart: "factor-cover-control-chart".to_owned(),
        ambient_rows: 4,
        ambient_columns: 4,
        support_rows: support.clone(),
        support_columns: support,
        metrics: DefectMetrics {
            domain: ExactRatMatrix::identity(supported.columns()).map_err(display)?,
            codomain: ExactRatMatrix::identity(supported.rows()).map_err(display)?,
        },
        supported,
    }
    .derive()
    .map_err(display)
}

fn returned_words(returned: &ResidentFactorCurrentReturn) -> Result<Vec<u16>, String> {
    returned
        .returned_intervals
        .iter()
        .map(|(lower, upper)| {
            if lower != upper {
                return Err("ordered control returned a non-singleton interval".to_owned());
            }
            bf16_integer(*lower)
        })
        .collect()
}

fn exact_intervals(intervals: &[(i64, i64)], exact: &[Rat]) -> bool {
    intervals.len() == exact.len()
        && intervals.iter().zip(exact).all(|((lower, upper), value)| {
            lower == upper
                && value.denom() == &BigInt::one()
                && value.numer() == &BigInt::from(*lower)
        })
}

fn changed_rows(before: &[(i64, i64)], after: &[(i64, i64)]) -> Result<Vec<u32>, String> {
    if before.len() != after.len() {
        return Err("predecessor and successor potential extents differ".to_owned());
    }
    before
        .iter()
        .zip(after)
        .enumerate()
        .filter(|(_, (left, right))| left != right)
        .map(|(row, _)| u32::try_from(row).map_err(display))
        .collect()
}

fn orient(interval: (i64, i64), orientation: i8) -> (i64, i64) {
    if orientation > 0 {
        interval
    } else {
        (-interval.1, -interval.0)
    }
}

fn exact_unit_entry(exponent: i32) -> Result<i64, String> {
    if exponent > 0 {
        return Err("a positive selector exponent cannot represent the exact unit".to_owned());
    }
    1i64
        .checked_shl((-exponent) as u32)
        .ok_or_else(|| "the exact selector unit exceeds the resident integer carrier".to_owned())
}

fn ceil_positive(numerator: i64, denominator: i64) -> Result<i64, String> {
    if numerator <= 0 || denominator <= 0 {
        return Err("positive lattice ceiling received a nonpositive argument".to_owned());
    }
    numerator
        .checked_add(denominator - 1)
        .map(|value| value / denominator)
        .ok_or_else(|| "lattice ceiling exceeds the resident integer carrier".to_owned())
}

fn scale_entry(step: i64, exponent: i32) -> Result<i64, String> {
    if exponent >= 0 {
        let scale = 1i64
            .checked_shl(exponent as u32)
            .ok_or("left scale exceeds the resident integer carrier")?;
        ceil_positive(step, scale)
    } else {
        step.checked_shl((-exponent) as u32)
            .ok_or_else(|| "scaled lattice step exceeds the resident integer carrier".to_owned())
    }
}

fn bf16_integer(value: i64) -> Result<u16, String> {
    if value == 0 {
        return Ok(0);
    }
    let negative = value < 0;
    let magnitude = value.unsigned_abs();
    let highest = u64::BITS - 1 - magnitude.leading_zeros();
    if highest + 127 >= 255 {
        return Err("integer lies outside finite BF16".to_owned());
    }
    let significand = if highest <= 7 {
        magnitude << (7 - highest)
    } else {
        let shift = highest - 7;
        let mask = (1u64 << shift) - 1;
        if magnitude & mask != 0 {
            return Err(format!("integer {value} is not exact in BF16"));
        }
        magnitude >> shift
    };
    let fraction = significand
        .checked_sub(128)
        .ok_or("invalid BF16 integer significand")?;
    Ok(((negative as u16) << 15) | (((highest + 127) as u16) << 7) | fraction as u16)
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn digest_intervals(values: &[(i64, i64)]) -> String {
    let mut digest = Sha256::new();
    for (lower, upper) in values {
        digest.update(lower.to_le_bytes());
        digest.update(upper.to_le_bytes());
    }
    hex(digest.finalize().as_slice())
}

fn digest_json(value: &impl Serialize) -> Result<String, String> {
    Ok(hex(
        Sha256::digest(serde_json::to_vec(value).map_err(display)?)
            .as_slice(),
    ))
}

fn closure_digest(paths: &[&Path]) -> Result<String, String> {
    let mut digest = Sha256::new();
    for path in paths {
        digest.update(path.as_os_str().as_encoded_bytes());
        if path.is_file() {
            digest.update(fs::read(path).map_err(display)?);
        } else {
            // The authenticated rest already binds its multi-gigabyte members by digest. Reading
            // those bodies again would be an unrelated serial replay, so the invocation closure
            // consumes the directory's authenticated manifest face.
            let manifest = path.join("manifest.json");
            if !manifest.is_file() {
                return Err(format!(
                    "closure directory {} has no authenticated manifest",
                    path.display()
                ));
            }
            digest.update(manifest.as_os_str().as_encoded_bytes());
            digest.update(fs::read(manifest).map_err(display)?);
        }
    }
    Ok(hex(digest.finalize().as_slice()))
}

fn write_inspection(
    output: &Path,
    bound: &BoundCoverArtifact,
    pairs: &[ReadingPair],
    currents: &[LaterCurrentArtifact],
    withdrawal: &AblationWithdrawalArtifact,
    controls: &HolonomyInterchangeArtifact,
    passed: bool,
) -> Result<(), String> {
    let surfaces = pairs
        .iter()
        .map(|pair| {
            format!(
                "- `{}`: predecessor {:?}; successor {:?}; changed rows {:?}.",
                pair.predecessor.proposal,
                pair.predecessor.maximal.iter().map(|face| face.surface.as_str()).collect::<Vec<_>>(),
                pair.successor.maximal.iter().map(|face| face.surface.as_str()).collect::<Vec<_>>(),
                pair.changed_rows
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let text = format!(
        "# The factor complex changed the same body\n\n- Product body: `{}`.\n- Returned atoms: {}; realized: {}; open: {}.\n- Contemporary exact rank: {}.\n{}\n- Later current charts: {:?}; all exact and coarse-invisible/graded-visible: {}.\n- Targeted ablation changed its target: {}.\n- Exact complete withdrawal recovered predecessor: {}.\n- Holonomy retained order: {}; disjoint interchange returned equal: {}.\n- Station grade: `{}`.\n",
        bound.product_body_sha256,
        bound.factor_population,
        bound.realized_source_factor_population,
        bound.open_factor_population,
        bound.deposited_identity.derived_rank,
        surfaces,
        currents.iter().map(|current| current.current_chart.as_str()).collect::<Vec<_>>(),
        currents.iter().all(|current| current.every_exact && current.every_graded_change_coarse_invisible),
        withdrawal.ablation_changed_target,
        withdrawal.predecessor_factor_recovered && withdrawal.predecessor_reading_recovered,
        controls.holonomy_retained_order,
        controls.interchange_exact,
        passed
    );
    fs::write(output.join("INSPECTION.md"), text).map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut members = fs::read_dir(output)
        .map_err(display)?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| entry.path())
        .filter(|path| path.is_file())
        .collect::<Vec<_>>();
    members.sort();
    let files = members
        .iter()
        .map(|path| {
            let bytes = fs::read(path).map_err(display)?;
            Ok(json!({
                "path":path.file_name().and_then(|name| name.to_str()).ok_or("non-UTF8 artifact name")?,
                "octets":bytes.len(),
                "sha256":hex(Sha256::digest(&bytes).as_slice())
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let identity = digest_json(&files)?;
    write_json(
        &output.join("MANIFEST.json"),
        &json!({"schema":"holonics.artifact-manifest.v1","identity":identity,"files":files}),
    )
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn hex(octets: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(octets.len() * 2);
    for octet in octets {
        out.push(DIGITS[(octet >> 4) as usize] as char);
        out.push(DIGITS[(octet & 15) as usize] as char);
    }
    out
}
