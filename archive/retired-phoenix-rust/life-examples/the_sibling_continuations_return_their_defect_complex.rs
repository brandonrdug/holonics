//! A2: fixed-rest sibling continuations return a receiver-indexed defect complex.
//!
//! The cohort is not a prompt list. A1's exact repeated-content fibres determine every admitted
//! history cut and their shortest content-history separators. One authenticated Phoenix product
//! remains mounted while each distinct history occurrence crosses it. The output front retains all
//! interval-compatible candidates; it never samples a winner. Recorded continuation text, tool
//! returns and later operator current remain exterior sibling testimony.

#[path = "a2/cohort.rs"]
mod cohort;
#[path = "a2/defect.rs"]
mod defect;

use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

use cohort::{provider_neutral_digest, SiblingCohort, SiblingHistoryCut};
use defect::{fixed_body, FixedBodyIdentity, HistoryDefectReturn};
use holonic_engine::phoenix::{
    runtime::{ProductSession, RuntimeReceipt},
    streamed::{InterventionSite, ReceiverOption},
    tower::Intervention,
};
use life::exchange_world_tube::{exchange_world_tube_rest_digest, remount_exchange_world_tube};
use serde::Serialize;
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Mode {
    Plan,
    Produce,
}

struct Args {
    mode: Mode,
    exchange_rest: PathBuf,
    phoenix_product: Option<PathBuf>,
    output: Option<PathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct PlanReceipt {
    schema: String,
    exchange_rest_sha256: String,
    repeated_content_classes: usize,
    repeated_content_occurrences: usize,
    admitted_history_cuts: usize,
    excluded_history_cuts: usize,
    unique_content_histories: usize,
    unresolved_content_histories: usize,
    history_message_population: usize,
    maximum_shortest_history_messages: usize,
    history_presentation_octets: usize,
    maximum_history_presentation_octets: usize,
    sibling_presentation_octets: usize,
    input_native_token_population: usize,
    maximum_input_native_tokens: usize,
    input_receiver_row_population: usize,
    maximum_input_receiver_rows: usize,
    terminal_receiver_rows_per_deed: usize,
    terminal_potential_coordinates_per_deed: usize,
    whole_potential_coordinates_not_materialized: u128,
    history_token_closure: Vec<HistoryTokenClosure>,
    resident_deed_order: Vec<String>,
    history_deeds_interchange_exact: bool,
    interchange_basis: String,
    resident_deeds_required: usize,
    provider_neutral_cohort_sha256: String,
    truth_status: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct HistoryTokenClosure {
    occurrence: String,
    native_tokens: usize,
    receiver_rows: usize,
    presentation_octets: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct PresentationControl {
    schema: String,
    history_cut_occurrence: String,
    base_presentation: String,
    rebased_presentation: String,
    fixed_body_preserved: bool,
    base_input_sha256: String,
    rebased_input_sha256: String,
    base_candidate_ids: Vec<u32>,
    rebased_candidate_ids: Vec<u32>,
    candidate_fibre_preserved: bool,
    shortest_candidate_separator: Option<u32>,
    scalar_winner_selected: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ProviderRemovalControl {
    schema: String,
    provider_faces_removed: usize,
    speaker_faces_removed: usize,
    native_cohort_before: String,
    native_cohort_after: String,
    runtime_input_population_unchanged: bool,
    native_cohort_preserved: bool,
    inference_replayed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct A2DefectComplex {
    schema: String,
    exchange_source_occurrence_sha256: String,
    exchange_rest_sha256: String,
    fixed_body: FixedBodyIdentity,
    histories: Vec<HistoryDefectReturn>,
    presentation_control: PresentationControl,
    provider_removal_control: ProviderRemovalControl,
    complete_candidate_population: usize,
    complete_defect_population: usize,
    histories_with_recorded_tool_world_returns: usize,
    histories_with_later_operator_return: usize,
    histories_whose_sibling_first_front_survives: usize,
    open_fibre_population: usize,
    teacher_interior_invented: bool,
    response_text_substituted_for_world_consequence: bool,
    scalar_winner_selected: bool,
    provider_priority_rule: bool,
    truth_status: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct A2Grade {
    schema: String,
    fixed_rest_and_history_receipts: bool,
    activity_cuts_separate: bool,
    complete_plural_candidate_and_open_fibres: bool,
    recorded_world_and_later_returns_retained: bool,
    complete_receiver_indexed_defect_complex: bool,
    shortest_separators_or_open_fibres_retained: bool,
    presentation_rebase_control_returned: bool,
    provider_removal_preserves_native_cohort: bool,
    no_scalar_winner_probability_or_provider_priority: bool,
    frozen_members_and_source_access_audit_pass: bool,
    passed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct InvocationReceipt {
    command: Vec<String>,
    purpose: String,
    code_closure: String,
    elapsed_milliseconds: u128,
    exit_status: i32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ProductManifest {
    schema: String,
    product: String,
    plan: PlanReceipt,
    fixed_body: FixedBodyIdentity,
    runtime_returns: usize,
    resident_deeds_enacted_in_this_invocation: usize,
    addressed_returns_reused: usize,
    candidate_population: usize,
    defect_population: usize,
    grade: String,
    defect_complex: String,
    cohort: String,
    runtime_receipts: String,
    invocations: Vec<InvocationReceipt>,
    open_exterior: Vec<String>,
    inference_entry: String,
}

fn main() -> Result<(), String> {
    let args = args()?;
    let world = remount_exchange_world_tube(&args.exchange_rest)?;
    let exchange_rest_sha256 = exchange_world_tube_rest_digest(&world)?.render();
    let cohort = cohort::derive(&world)?;
    let product = args
        .phoenix_product
        .as_ref()
        .ok_or_else(|| "A2 requires a Phoenix product directory".to_owned())?;
    let session = ProductSession::open(product)?;
    let plan = plan(&cohort, exchange_rest_sha256, &session)?;
    if args.mode == Mode::Plan {
        println!(
            "{}",
            serde_json::to_string_pretty(&plan).map_err(|error| error.to_string())?
        );
        return Ok(());
    }
    let output = args
        .output
        .as_ref()
        .ok_or_else(|| "--produce requires an output directory".to_owned())?;
    produce(&session, output, world, cohort, plan)
}

fn produce(
    session: &ProductSession,
    output: &Path,
    world: life::exchange_world_tube::ExchangeWorldTube,
    cohort: SiblingCohort,
    plan: PlanReceipt,
) -> Result<(), String> {
    if output.join("MANIFEST.json").exists() {
        return Err(format!(
            "the completed A2 product already stands at {}",
            output.display()
        ));
    }
    fs::create_dir_all(output.join("runtime")).map_err(|error| error.to_string())?;
    fs::create_dir_all(output.join("histories")).map_err(|error| error.to_string())?;
    let cohort_path = output.join("00-sibling-cohort.json");
    let expected_cohort = json_bytes(&cohort)?;
    if cohort_path.exists() {
        let retained = fs::read(&cohort_path).map_err(|error| error.to_string())?;
        if retained != expected_cohort {
            return Err(
                "the retained A2 cohort disagrees with the current addressed rest".to_owned(),
            );
        }
    } else {
        write_bytes(cohort_path, &expected_cohort)?;
    }
    let code_closure = code_closure();
    let mut invocations = Vec::new();
    let mut histories = Vec::new();
    let mut base_candidates = BTreeMap::<String, (FixedBodyIdentity, Vec<u32>, String)>::new();
    let mut fixed = None::<FixedBodyIdentity>;

    let cut_by_occurrence = cohort
        .cuts
        .iter()
        .map(|cut| (cut.occurrence.as_str(), cut))
        .collect::<BTreeMap<_, _>>();
    for occurrence in &plan.resident_deed_order {
        let cut = cut_by_occurrence
            .get(occurrence.as_str())
            .copied()
            .ok_or_else(|| format!("planned A2 occurrence {occurrence} is absent"))?;
        let input = present(cut, Presentation::JsonLineBoundary);
        let history_path = output.join("histories").join(format!("{occurrence}.json"));
        if history_path.exists() {
            let history: HistoryDefectReturn = serde_json::from_slice(
                &fs::read(&history_path).map_err(|error| error.to_string())?,
            )
            .map_err(|error| format!("read retained A2 history {occurrence}: {error}"))?;
            let runtime_path = output.join(&history.runtime_receipt_artifact);
            let valid = history.history_cut_occurrence == cut.occurrence
                && history.history_sha256 == cut.native_history_sha256
                && history.presentation == "jsonl-record-boundary"
                && history.productive_code_closure == code_closure
                && history.runtime_input_sha256 == hex(&Sha256::digest(input.text.as_bytes()))
                && runtime_path.exists()
                && sha256_file(&runtime_path)? == history.runtime_receipt_sha256
                && history.frozen_members_verified
                && history.source_access_forbidden_population == 0;
            if !valid {
                return Err(format!(
                    "retained A2 history {occurrence} does not bind the current body/history closure"
                ));
            }
            if fixed
                .as_ref()
                .is_some_and(|held| held != &history.fixed_body)
            {
                return Err(
                    "the retained Athena product identity moved between histories".to_owned(),
                );
            }
            fixed.get_or_insert_with(|| history.fixed_body.clone());
            base_candidates.insert(
                cut.occurrence.clone(),
                (
                    history.fixed_body.clone(),
                    history
                        .defects
                        .iter()
                        .map(|entry| entry.candidate.native_id)
                        .collect(),
                    history.runtime_input_sha256.clone(),
                ),
            );
            invocations.push(InvocationReceipt {
                command: vec![
                    "addressed-runtime-return-reused".to_owned(),
                    cut.occurrence.clone(),
                ],
                purpose:
                    "reuse the inspected same-closure local return; no resident deed was replayed"
                        .to_owned(),
                code_closure: code_closure.clone(),
                elapsed_milliseconds: 0,
                exit_status: 0,
            });
            histories.push(history);
            continue;
        }
        let begun = Instant::now();
        let returned = session.infer_partitioned_with_intervention(
            &input.text,
            &input.byte_boundaries,
            InterventionSite::Nowhere,
            &Intervention::None,
            ReceiverOption::Terminal,
        )?;
        invocations.push(InvocationReceipt {
            command: vec![
                "ProductSession::infer_partitioned_with_intervention".to_owned(),
                cut.occurrence.clone(),
                "jsonl-record-boundary".to_owned(),
            ],
            purpose: "return the complete fixed-body next-front and causal/apparatus cuts for one addressed A1 history".to_owned(),
            code_closure: code_closure.clone(),
            elapsed_milliseconds: begun.elapsed().as_millis(),
            exit_status: 0,
        });
        validate_runtime(&returned.receipt, cut.history.len())?;
        let body = fixed_body(&returned.receipt)?;
        if fixed.as_ref().is_some_and(|held| held != &body) {
            return Err("the Athena product identity moved between A2 histories".to_owned());
        }
        fixed.get_or_insert_with(|| body.clone());
        let runtime_path = format!("runtime/{}.json", cut.occurrence);
        write_json(output.join(&runtime_path), &returned.receipt)?;
        let runtime_receipt_sha256 = sha256_file(&output.join(&runtime_path))?;
        let sibling_ids = session.encode(&cut.sibling.text)?;
        let sibling_id = *sibling_ids
            .first()
            .ok_or_else(|| format!("sibling {} encoded to no codewords", cut.sibling.occurrence))?;
        let sibling_surface = session
            .predecessor()
            .codebook()
            .native_surface(sibling_id)
            .map_err(|error| error.to_string())?
            .to_owned();
        let sibling_interval = terminal_interval(
            &returned.cultivated.cultivated_potential,
            returned.receipt.generated.vocabulary_extent,
            sibling_id,
        )?;
        let analyzed = defect::analyze(
            cut,
            "jsonl-record-boundary",
            runtime_path,
            runtime_receipt_sha256,
            code_closure.clone(),
            &returned.receipt,
            sibling_ids,
            sibling_surface,
            sibling_interval,
        )?;
        let candidate_ids = analyzed
            .defects
            .iter()
            .map(|entry| entry.candidate.native_id)
            .collect::<Vec<_>>();
        base_candidates.insert(
            cut.occurrence.clone(),
            (
                body,
                candidate_ids,
                returned.receipt.input.text_sha256.clone(),
            ),
        );
        write_json(history_path, &analyzed)?;
        histories.push(analyzed);
    }

    let control_cut = cohort
        .cuts
        .iter()
        .max_by(|left, right| {
            (left.history.len(), left.occurrence.as_str())
                .cmp(&(right.history.len(), right.occurrence.as_str()))
        })
        .ok_or_else(|| "A1 returned no admitted repeated-history cut".to_owned())?;
    let rebased_input = present(control_cut, Presentation::BoundaryWithdrawn);
    let begun = Instant::now();
    let rebased = session.infer_partitioned_with_intervention(
        &rebased_input.text,
        &rebased_input.byte_boundaries,
        InterventionSite::Nowhere,
        &Intervention::None,
        ReceiverOption::Terminal,
    )?;
    invocations.push(InvocationReceipt {
        command: vec![
            "ProductSession::infer_partitioned_with_intervention".to_owned(),
            control_cut.occurrence.clone(),
            "boundary-withdrawn".to_owned(),
        ],
        purpose: "return the presentation-boundary intervention on the richest founded A2 history"
            .to_owned(),
        code_closure: code_closure.clone(),
        elapsed_milliseconds: begun.elapsed().as_millis(),
        exit_status: 0,
    });
    validate_runtime(&rebased.receipt, control_cut.history.len())?;
    let rebased_body = fixed_body(&rebased.receipt)?;
    let (base_body, base_ids, base_input_sha256) = &base_candidates[&control_cut.occurrence];
    let rebased_ids = rebased
        .receipt
        .generated
        .plural
        .iter()
        .map(|candidate| candidate.native_id)
        .collect::<Vec<_>>();
    let presentation_control = PresentationControl {
        schema: "holonics.athena-a2-presentation-control.v1".to_owned(),
        history_cut_occurrence: control_cut.occurrence.clone(),
        base_presentation: "JSONL's admitted single record-boundary LF".to_owned(),
        rebased_presentation:
            "the same ordered message occurrences with that exterior LF boundary withdrawn"
                .to_owned(),
        fixed_body_preserved: *base_body == rebased_body,
        base_input_sha256: base_input_sha256.clone(),
        rebased_input_sha256: rebased.receipt.input.text_sha256.clone(),
        base_candidate_ids: base_ids.clone(),
        rebased_candidate_ids: rebased_ids.clone(),
        candidate_fibre_preserved: *base_ids == rebased_ids,
        shortest_candidate_separator: first_set_separator(base_ids, &rebased_ids),
        scalar_winner_selected: false,
    };

    let neutral_before = provider_neutral_digest(&cohort);
    let mut ablated = cohort.clone();
    let mut provider_faces_removed = 0usize;
    let mut speaker_faces_removed = 0usize;
    for cut in &mut ablated.cuts {
        for message in cut
            .history
            .iter_mut()
            .chain([&mut cut.prompt, &mut cut.sibling])
        {
            provider_faces_removed += usize::from(!message.provider_face.is_empty());
            speaker_faces_removed += usize::from(!message.speaker_face.is_empty());
            message.provider_face.clear();
            message.speaker_face.clear();
            message.phase_face.clear();
        }
        if let Some(later) = &mut cut.world.later_operator_return {
            provider_faces_removed += usize::from(!later.provider_face.is_empty());
            speaker_faces_removed += usize::from(!later.speaker_face.is_empty());
            later.provider_face.clear();
            later.speaker_face.clear();
            later.phase_face.clear();
        }
    }
    let neutral_after = provider_neutral_digest(&ablated);
    let runtime_input_population_unchanged =
        cohort
            .cuts
            .iter()
            .zip(&ablated.cuts)
            .all(|(before, after)| {
                present(before, Presentation::JsonLineBoundary)
                    == present(after, Presentation::JsonLineBoundary)
            });
    let provider_control = ProviderRemovalControl {
        schema: "holonics.athena-a2-provider-removal-control.v1".to_owned(),
        provider_faces_removed,
        speaker_faces_removed,
        native_cohort_before: neutral_before,
        native_cohort_after: neutral_after,
        runtime_input_population_unchanged,
        native_cohort_preserved: provider_neutral_digest(&cohort)
            == provider_neutral_digest(&ablated),
        inference_replayed: false,
    };

    let fixed_body = fixed.ok_or_else(|| "A2 returned no fixed body receipt".to_owned())?;
    if fixed_body != rebased_body {
        return Err("the fixed body moved under presentation rebase".to_owned());
    }
    let complete_candidate_population = histories
        .iter()
        .map(|history| history.generated_candidate_population)
        .sum();
    let complete_defect_population = histories.iter().map(|history| history.defects.len()).sum();
    let histories_with_recorded_tool_world_returns = histories
        .iter()
        .filter(|history| history.tool_world_pair_population > 0)
        .count();
    let histories_with_later_operator_return = histories
        .iter()
        .filter(|history| history.later_operator_return_present)
        .count();
    let histories_whose_sibling_first_front_survives = histories
        .iter()
        .filter(|history| history.recorded_sibling_in_candidate_fibre)
        .count();
    let open_fibre_population = histories
        .iter()
        .map(|history| {
            history.open_fibres.len()
                + history
                    .defects
                    .iter()
                    .map(|defect| defect.open_successor_fibres.len())
                    .sum::<usize>()
        })
        .sum();
    let complex = A2DefectComplex {
        schema: "holonics.athena-a2-defect-complex.v1".to_owned(),
        exchange_source_occurrence_sha256: world.source_occurrence_sha256.render(),
        exchange_rest_sha256: plan.exchange_rest_sha256.clone(),
        fixed_body: fixed_body.clone(),
        histories,
        presentation_control,
        provider_removal_control: provider_control,
        complete_candidate_population,
        complete_defect_population,
        histories_with_recorded_tool_world_returns,
        histories_with_later_operator_return,
        histories_whose_sibling_first_front_survives,
        open_fibre_population,
        teacher_interior_invented: false,
        response_text_substituted_for_world_consequence: false,
        scalar_winner_selected: false,
        provider_priority_rule: false,
        truth_status: "established-bounded".to_owned(),
    };
    let grade = grade(&complex, &cohort);
    write_json(output.join("01-defect-complex.json"), &complex)?;
    write_json(output.join("02-grade.json"), &grade)?;
    let manifest = ProductManifest {
        schema: "holonics.athena-a2-product-manifest.v1".to_owned(),
        product: "Athena-Gemma sibling continuation defect atlas".to_owned(),
        plan,
        fixed_body,
        runtime_returns: invocations.len(),
        resident_deeds_enacted_in_this_invocation: invocations
            .iter()
            .filter(|invocation| invocation.command.first().is_some_and(|command| {
                command == "ProductSession::infer_partitioned_with_intervention"
            }))
            .count(),
        addressed_returns_reused: invocations
            .iter()
            .filter(|invocation| {
                invocation
                    .command
                    .first()
                    .is_some_and(|command| command == "addressed-runtime-return-reused")
            })
            .count(),
        candidate_population: complex.complete_candidate_population,
        defect_population: complex.complete_defect_population,
        grade: "02-grade.json".to_owned(),
        defect_complex: "01-defect-complex.json".to_owned(),
        cohort: "00-sibling-cohort.json".to_owned(),
        runtime_receipts: "runtime/*.json".to_owned(),
        invocations,
        open_exterior: vec![
            "A2 returns one exact next-token frontier per history; complete response suffixes remain open".to_owned(),
            "recorded world returns are exterior sibling testimony and are not attributed to un-enacted Athena candidates".to_owned(),
            "A3 cultivation has not occurred; the fixed body is unchanged".to_owned(),
        ],
        inference_entry: "the_sibling_continuations_return_their_defect_complex --produce EXCHANGE_REST PHOENIX_PRODUCT DESTINATION".to_owned(),
    };
    write_json(output.join("MANIFEST.json"), &manifest)?;
    inspect(output, &grade, &complex)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&manifest).map_err(|error| error.to_string())?
    );
    if grade.passed {
        Ok(())
    } else {
        Err("A2 grade refused the sibling defect complex".to_owned())
    }
}

fn grade(complex: &A2DefectComplex, cohort: &SiblingCohort) -> A2Grade {
    let fixed_rest_and_history_receipts = !complex.histories.is_empty()
        && complex.histories.iter().all(|history| {
            history.fixed_body == complex.fixed_body && history.history_messages > 0
        });
    let activity_cuts_separate = complex
        .histories
        .iter()
        .all(|history| history.activity.cuts_are_separate);
    let complete_plural_candidate_and_open_fibres = complex
        .histories
        .iter()
        .all(|history| !history.defects.is_empty() && !history.open_fibres.is_empty());
    let recorded_world_and_later_returns_retained = complex.histories.len() == cohort.cuts.len()
        && complex.histories_with_later_operator_return > 0;
    let complete_receiver_indexed_defect_complex = complex.complete_candidate_population
        == complex.complete_defect_population
        && complex.complete_defect_population > 0;
    let shortest_separators_or_open_fibres_retained = complex.histories.iter().all(|history| {
        history.defects.iter().all(|defect| {
            defect.shortest_separator.is_some() || !defect.open_successor_fibres.is_empty()
        })
    });
    let presentation_rebase_control_returned = complex.presentation_control.fixed_body_preserved
        && complex.presentation_control.base_input_sha256
            != complex.presentation_control.rebased_input_sha256;
    let provider_removal_preserves_native_cohort =
        complex.provider_removal_control.native_cohort_preserved
            && complex
                .provider_removal_control
                .runtime_input_population_unchanged
            && !complex.provider_removal_control.inference_replayed;
    let no_scalar_winner_probability_or_provider_priority = !complex.scalar_winner_selected
        && !complex.provider_priority_rule
        && !complex.teacher_interior_invented
        && !complex.response_text_substituted_for_world_consequence
        && complex.histories.iter().all(|history| {
            !history.scalar_winner_selected
                && !history.probability_substituted_for_causal_return
                && !history.provider_priority_rule
        });
    let frozen_members_and_source_access_audit_pass = complex.histories.iter().all(|history| {
        history.fixed_body == complex.fixed_body
            && history.frozen_members_verified
            && history.source_access_forbidden_population == 0
    });
    let passed = fixed_rest_and_history_receipts
        && activity_cuts_separate
        && complete_plural_candidate_and_open_fibres
        && recorded_world_and_later_returns_retained
        && complete_receiver_indexed_defect_complex
        && shortest_separators_or_open_fibres_retained
        && presentation_rebase_control_returned
        && provider_removal_preserves_native_cohort
        && no_scalar_winner_probability_or_provider_priority
        && frozen_members_and_source_access_audit_pass;
    A2Grade {
        schema: "holonics.athena-a2-grade.v1".to_owned(),
        fixed_rest_and_history_receipts,
        activity_cuts_separate,
        complete_plural_candidate_and_open_fibres,
        recorded_world_and_later_returns_retained,
        complete_receiver_indexed_defect_complex,
        shortest_separators_or_open_fibres_retained,
        presentation_rebase_control_returned,
        provider_removal_preserves_native_cohort,
        no_scalar_winner_probability_or_provider_priority,
        frozen_members_and_source_access_audit_pass,
        passed,
    }
}

fn validate_runtime(receipt: &RuntimeReceipt, expected_receiver_rows: usize) -> Result<(), String> {
    if !receipt.frozen_members_verified
        || !receipt.source_access.forbidden.is_empty()
        || receipt.generated.plural.is_empty()
        || receipt.generated.separated == 0
        || receipt.generated.plural.len() + receipt.generated.separated
            != receipt.generated.vocabulary_extent
        || receipt.input.presentation.schema != "holonic-engine.phoenix.input-presentation.v1"
        || receipt.input.presentation.kind != "addressed-partition-directed-mean"
        || !receipt.input.presentation.source_rows_retained
        || receipt.input.presentation.source_rows != receipt.input.native_ids.len()
        || receipt.input.presentation.received_rows != expected_receiver_rows
        || receipt.input.presentation.partition_boundaries.first() != Some(&0)
        || receipt
            .input
            .presentation
            .partition_boundaries
            .last()
            .copied()
            != Some(receipt.input.native_ids.len() as u32)
        || receipt
            .input
            .presentation
            .partition_boundaries
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        || receipt.generated.plural.iter().any(|candidate| {
            candidate.lower > receipt.generated.top_lower
                || candidate.upper < receipt.generated.top_lower
        })
    {
        return Err(
            "the Phoenix runtime did not return the complete fixed-body candidate fibre".to_owned(),
        );
    }
    Ok(())
}

fn terminal_interval(
    potential: &[(i64, i64)],
    vocabulary: usize,
    native_id: u32,
) -> Result<(i64, i64), String> {
    if vocabulary == 0 || potential.is_empty() || potential.len() % vocabulary != 0 {
        return Err("the runtime potential is not a complete row population".to_owned());
    }
    let terminal = &potential[potential.len() - vocabulary..];
    terminal
        .get(native_id as usize)
        .copied()
        .ok_or_else(|| format!("sibling native id {native_id} left the terminal vocabulary"))
}

#[derive(Clone, Copy)]
enum Presentation {
    JsonLineBoundary,
    BoundaryWithdrawn,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PresentedHistory {
    text: String,
    byte_boundaries: Vec<usize>,
}

fn present(cut: &SiblingHistoryCut, presentation: Presentation) -> PresentedHistory {
    let separator = match presentation {
        Presentation::JsonLineBoundary => "\n",
        Presentation::BoundaryWithdrawn => "",
    };
    let mut text = String::new();
    let mut byte_boundaries = Vec::with_capacity(cut.history.len() + 1);
    byte_boundaries.push(0);
    for (index, message) in cut.history.iter().enumerate() {
        if index > 0 {
            text.push_str(separator);
        }
        text.push_str(&message.text);
        byte_boundaries.push(text.len());
    }
    PresentedHistory {
        text,
        byte_boundaries,
    }
}

fn first_set_separator(left: &[u32], right: &[u32]) -> Option<u32> {
    left.iter()
        .copied()
        .find(|candidate| right.binary_search(candidate).is_err())
        .or_else(|| {
            right
                .iter()
                .copied()
                .find(|candidate| left.binary_search(candidate).is_err())
        })
}

fn plan(
    cohort: &SiblingCohort,
    exchange_rest_sha256: String,
    session: &ProductSession,
) -> Result<PlanReceipt, String> {
    let history_token_closure = cohort
        .cuts
        .iter()
        .map(|cut| {
            let presentation = present(cut, Presentation::JsonLineBoundary);
            session
                .encode(&presentation.text)
                .map(|ids| HistoryTokenClosure {
                    occurrence: cut.occurrence.clone(),
                    native_tokens: ids.len(),
                    receiver_rows: cut.history.len(),
                    presentation_octets: presentation.text.len(),
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let vocabulary = session.runtime_law().vocabulary_extent as usize;
    let whole_potential_coordinates_not_materialized = history_token_closure
        .iter()
        .map(|entry| entry.receiver_rows.saturating_sub(1) as u128 * vocabulary as u128)
        .sum();
    let mut resident_deed_order = history_token_closure.clone();
    resident_deed_order.sort_by(|left, right| {
        right
            .native_tokens
            .cmp(&left.native_tokens)
            .then_with(|| left.occurrence.cmp(&right.occurrence))
    });
    Ok(PlanReceipt {
        schema: "holonics.athena-a2-plan-receipt.v1".to_owned(),
        exchange_rest_sha256,
        repeated_content_classes: cohort.repeated_content_classes,
        repeated_content_occurrences: cohort.repeated_content_occurrences,
        admitted_history_cuts: cohort.cuts.len(),
        excluded_history_cuts: cohort.exclusions.len(),
        unique_content_histories: cohort
            .cuts
            .iter()
            .filter(|cut| cut.content_history_is_unique)
            .count(),
        unresolved_content_histories: cohort
            .cuts
            .iter()
            .filter(|cut| !cut.content_history_is_unique)
            .count(),
        history_message_population: cohort.cuts.iter().map(|cut| cut.history.len()).sum(),
        maximum_shortest_history_messages: cohort
            .cuts
            .iter()
            .map(|cut| cut.history.len())
            .max()
            .unwrap_or(0),
        history_presentation_octets: cohort
            .cuts
            .iter()
            .map(|cut| present(cut, Presentation::JsonLineBoundary).text.len())
            .sum(),
        maximum_history_presentation_octets: cohort
            .cuts
            .iter()
            .map(|cut| present(cut, Presentation::JsonLineBoundary).text.len())
            .max()
            .unwrap_or(0),
        sibling_presentation_octets: cohort.cuts.iter().map(|cut| cut.sibling.text.len()).sum(),
        input_native_token_population: history_token_closure
            .iter()
            .map(|entry| entry.native_tokens)
            .sum(),
        maximum_input_native_tokens: history_token_closure
            .iter()
            .map(|entry| entry.native_tokens)
            .max()
            .unwrap_or(0),
        input_receiver_row_population: history_token_closure
            .iter()
            .map(|entry| entry.receiver_rows)
            .sum(),
        maximum_input_receiver_rows: history_token_closure
            .iter()
            .map(|entry| entry.receiver_rows)
            .max()
            .unwrap_or(0),
        terminal_receiver_rows_per_deed: usize::from(!cohort.cuts.is_empty()),
        terminal_potential_coordinates_per_deed: vocabulary,
        whole_potential_coordinates_not_materialized,
        history_token_closure,
        resident_deed_order: resident_deed_order
            .into_iter()
            .map(|entry| entry.occurrence)
            .collect(),
        history_deeds_interchange_exact: true,
        interchange_basis: "each deed reads one immutable authenticated product identity and owns only its addressed input, resident surface, obstruction lineage, return and artifact path; no deed changes a successor, obstruction, lineage or logical resource state read by another deed; the descending native-token work order asks the dominating apparatus falsifier first and is therefore an apparatus chart over an exact independent family"
            .to_owned(),
        resident_deeds_required: cohort.cuts.len() + usize::from(!cohort.cuts.is_empty()),
        provider_neutral_cohort_sha256: provider_neutral_digest(cohort),
        truth_status: "established-bounded".to_owned(),
    })
}

fn inspect(output: &Path, grade: &A2Grade, complex: &A2DefectComplex) -> Result<(), String> {
    let grade_again: serde_json::Value = serde_json::from_slice(
        &fs::read(output.join("02-grade.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let complex_again: serde_json::Value = serde_json::from_slice(
        &fs::read(output.join("01-defect-complex.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    if grade_again.get("passed") != Some(&serde_json::Value::Bool(grade.passed))
        || complex_again
            .get("complete_defect_population")
            .and_then(serde_json::Value::as_u64)
            != Some(complex.complete_defect_population as u64)
    {
        return Err(
            "A2 emitted artifact inspection disagreed with the in-memory return".to_owned(),
        );
    }
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# Athena A2 sibling defect complex\n\n- grade: {}\n- histories: {}\n- candidate/defect cells: {}\n- tool/world-bearing histories: {}\n- sibling first fronts retained: {}\n- scalar winner: false\n- provider priority: false\n",
            if grade.passed { "PASS" } else { "REFUSED" },
            complex.histories.len(),
            complex.complete_defect_population,
            complex.histories_with_recorded_tool_world_returns,
            complex.histories_whose_sibling_first_front_survives,
        ),
    )
    .map_err(|error| error.to_string())
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    write_bytes(path, &json_bytes(value)?)
}

fn json_bytes(value: &impl Serialize) -> Result<Vec<u8>, String> {
    serde_json::to_vec_pretty(value).map_err(|error| error.to_string())
}

fn write_bytes(path: PathBuf, bytes: &[u8]) -> Result<(), String> {
    let temporary = path.with_extension("a2-staged");
    fs::write(&temporary, bytes).map_err(|error| error.to_string())?;
    fs::rename(&temporary, &path).map_err(|error| error.to_string())
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let bytes = fs::read(path).map_err(|error| error.to_string())?;
    Ok(hex(&Sha256::digest(bytes)))
}

fn code_closure() -> String {
    let mut digest = Sha256::new();
    for bytes in [
        include_bytes!("the_sibling_continuations_return_their_defect_complex.rs").as_slice(),
        include_bytes!("a2/cohort.rs").as_slice(),
        include_bytes!("a2/defect.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/runtime.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/streamed.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/streamed_cultivation.rs")
            .as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/tower.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/front_passage.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/resident_law.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/resident_section.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/streamed_standing.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/kernels/exact_resident_section.cu")
            .as_slice(),
    ] {
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }
    hex(&digest.finalize())
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}

fn args() -> Result<Args, String> {
    let mut values = env::args().skip(1);
    match values.next().as_deref() {
        Some("--plan") => {
            let exchange_rest = values
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--plan requires EXCHANGE_REST PHOENIX_PRODUCT".to_owned())?;
            let phoenix_product = values
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--plan requires EXCHANGE_REST PHOENIX_PRODUCT".to_owned())?;
            if values.next().is_some() {
                return Err("--plan accepts exactly two paths".to_owned());
            }
            Ok(Args {
                mode: Mode::Plan,
                exchange_rest,
                phoenix_product: Some(phoenix_product),
                output: None,
            })
        }
        Some("--produce") => {
            let exchange_rest = values.next().map(PathBuf::from).ok_or_else(|| {
                "--produce requires EXCHANGE_REST PHOENIX_PRODUCT OUTPUT".to_owned()
            })?;
            let phoenix_product = values.next().map(PathBuf::from).ok_or_else(|| {
                "--produce requires EXCHANGE_REST PHOENIX_PRODUCT OUTPUT".to_owned()
            })?;
            let output = values.next().map(PathBuf::from).ok_or_else(|| {
                "--produce requires EXCHANGE_REST PHOENIX_PRODUCT OUTPUT".to_owned()
            })?;
            if values.next().is_some() {
                return Err("--produce accepts exactly three paths".to_owned());
            }
            Ok(Args {
                mode: Mode::Produce,
                exchange_rest,
                phoenix_product: Some(phoenix_product),
                output: Some(output),
            })
        }
        _ => Err(
            "usage: --plan EXCHANGE_REST PHOENIX_PRODUCT | --produce EXCHANGE_REST PHOENIX_PRODUCT OUTPUT"
                .to_owned(),
        ),
    }
}
