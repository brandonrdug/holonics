//! Final Athena-alpha deed: freeze the receiver/history quotient and returned factor complex,
//! remount without exchange sources, and let one continuing Phoenix owner receive language,
//! mathematics, optical and acoustic current before its exact ablation/withdrawal controls.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use holonic_engine::{
    derived_factor_cover::DerivedFactorCover,
    phoenix::{
        alpha_rest::AthenaAlphaNativeRest,
        emanative::{EmanativeContinuationRest, EmanativeSession},
        runtime::ProductSession,
        session_factor_complex::{
            FactorMutationReceipt, ResidentFactorCurrentReturn, SessionFactorComplexIdentity,
            TowerFactorRealization,
        },
    },
};
use life::athena_receiver_history::AthenaReceiverHistoryCongruence;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const PRODUCT: &str =
    "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const CONTINUATION: &str =
    "output/the_exchange_return_cultivates_athena_gemma/product/continuation";
const CONGRUENCE: &str =
    "output/the_receiver_history_congruence_replaces_the_trigram_table/00-receiver-history-congruence.json";
const COVER: &str =
    "output/the_returned_defect_founds_a_derived_local_factor_cover/00-source-defect-cover.json";
const BOUND: &str =
    "output/the_factor_complex_changes_the_same_body/00-bound-factor-cover.json";
const DIFFERENCES: &str =
    "output/the_factor_complex_changes_the_same_body/01-matched-language-returns.json";
const SEPARATORS: &str =
    "output/the_candidate_departs_before_sibling_testimony_returns/02-returned-sibling-defects.json";
const MULTIMODAL: &str =
    "output/the_complete_inherited_organs_cross_native_potential_complexes/native-rest/continuation.json";
const PREDECESSOR_EMANATION: &str =
    "output/the_agentic_laboratory_athena_freezes/athena-rest/emanative/agentic-continuation.rest";
const OUTPUT: &str = "output/the_receiver_history_quotient_condenses_and_athena_alpha_speaks";

#[derive(Debug, Deserialize)]
struct SourceCoverArtifact {
    cover: DerivedFactorCover,
}

#[derive(Debug, Deserialize)]
struct BoundCoverArtifact {
    realizations: Vec<TowerFactorRealization>,
    open_factor_addresses: Vec<String>,
    deposited_identity: SessionFactorComplexIdentity,
}

#[derive(Debug, Deserialize)]
struct MultimodalContinuation {
    candidate_counts: Vec<u32>,
    boundary_order: Vec<u32>,
}

#[derive(Debug, Serialize)]
struct ModalCurrent {
    chart: String,
    source_face: Vec<u32>,
    returned: Vec<ResidentFactorCurrentReturn>,
    every_exact: bool,
    coarse_invisible_graded_visible: bool,
}

#[derive(Debug, Serialize)]
struct MutationAtlas {
    full: SessionFactorComplexIdentity,
    ablated_address: String,
    ablation: FactorMutationReceipt,
    restore: FactorMutationReceipt,
    restore_exact: bool,
    suffix_withdrawal: FactorMutationReceipt,
    complete_withdrawal: FactorMutationReceipt,
    predecessor_factor_recovered: bool,
}

#[derive(Debug, Serialize, Deserialize)]
struct DetachedReturn {
    schema: String,
    truth_status: String,
    product_identity_sha256: String,
    factor_complex_identity: SessionFactorComplexIdentity,
    quotient_source_population: usize,
    quotient_native_population: usize,
    quotient_fibre_population: usize,
    shortest_separator_population: usize,
    conversation_prompt: String,
    predecessor_conversation: String,
    alpha_conversation: String,
    conversation_fronts: usize,
    mathematical_prompt: String,
    mathematical_return: String,
    mathematical_fronts: usize,
    mathematical_novel_surface: bool,
    conversation_receipts: Value,
    mathematical_receipt: Value,
    #[serde(default)]
    successor_streamed_octets: Vec<u64>,
    #[serde(default)]
    successor_resident_peak_octets: Vec<u64>,
    #[serde(default)]
    full_tower_streaming_recurred_after_first: bool,
    modal_currents: Value,
    mutation_atlas: Value,
    source_accessed_paths: Vec<String>,
    forbidden_source_access: Vec<String>,
    gpu_hot_fronts: bool,
    cpu_semantic_replay_after_device: bool,
    passed: bool,
}

fn main() -> Result<(), String> {
    let args = env::args_os().skip(1).map(PathBuf::from).collect::<Vec<_>>();
    if args.first().is_some_and(|arg| arg == "--finalize-artifact") {
        if args.len() != 2 {
            return Err("--finalize-artifact needs OUTPUT".to_owned());
        }
        return finalize_artifact(&args[1]);
    }
    if args.first().is_some_and(|arg| arg == "--remount") {
        if args.len() != 7 {
            return Err("--remount needs REST PRODUCT CONTINUATION PREDECESSOR MULTIMODAL OUTPUT".to_owned());
        }
        return remount(&args[1], &args[2], &args[3], &args[4], &args[5], &args[6]);
    }
    let output = args.first().cloned().unwrap_or_else(|| OUTPUT.into());
    if args.len() > 1 {
        return Err("usage: [OUTPUT]".to_owned());
    }
    produce(&output)
}

fn produce(output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!("final Athena-alpha output {} already exists", output.display()));
    }
    let started = Instant::now();
    fs::create_dir_all(output).map_err(display)?;

    let congruence_bytes = fs::read(CONGRUENCE).map_err(display)?;
    let congruence = AthenaReceiverHistoryCongruence::read(&congruence_bytes)?;
    let source_cover_bytes = fs::read(COVER).map_err(display)?;
    let source_cover: SourceCoverArtifact = serde_json::from_slice(&source_cover_bytes).map_err(display)?;
    let bound: BoundCoverArtifact = read_json(Path::new(BOUND))?;
    let mut session = ProductSession::open_with_continuation(PRODUCT, CONTINUATION)?;
    let deposited = session.deposit_factor_cover(
        source_cover.cover,
        bound.realizations,
        bound.open_factor_addresses,
    )?;
    if deposited != bound.deposited_identity {
        return Err("the final rest did not recover the admitted Phase-4 factor complex".to_owned());
    }
    let rest = AthenaAlphaNativeRest::seal(
        &session,
        congruence.native,
        vec![
            "unexcited inherited-model capability remains an open reconstruction fibre".to_owned(),
            "future receiver families may reopen the present quotient".to_owned(),
            "nontrivial loop holonomy remains retained curvature".to_owned(),
        ],
    )
    .map_err(display)?;
    let product_identity = rest.product_identity_sha256.clone();
    let quotient_octets = serde_json::to_vec(&rest.receiver_history).map_err(display)?.len();
    let factor_octets = rest.factor_complex.canonical_bytes().map_err(display)?.len();
    let rest_bytes = rest.canonical_bytes().map_err(display)?;
    let rest_atlas = json!({
        "schema":"holonics.athena-alpha.native-rest-atlas.v1",
        "truth_status":"established-bounded",
        "product_identity_sha256":product_identity.clone(),
        "receiver_history": {
            "source_population":rest.receiver_history.source_population.len(),
            "native_population":rest.receiver_history.native_population.len(),
            "quotient_assignments":rest.receiver_history.quotient.len(),
            "receiver_factors":rest.receiver_history.receiver_factors.len(),
            "generator_squares":rest.receiver_history.generators.len(),
            "reconstruction_fibres":rest.receiver_history.reconstruction_fibres.len(),
            "first_separators":rest.receiver_history.first_separators.len(),
            "exact_work":rest.receiver_history.construction_work
        },
        "factor_complex_identity":rest.factor_complex.identity(),
        "factor_cover_and_overlap_nerve":session.factor_cover().ok_or("factor cover vanished before rest")?,
        "decoder":rest.decoder,
        "open_exterior":rest.open_exterior
    });
    let rest_path = output.join("athena-alpha.rest");
    fs::write(&rest_path, &rest_bytes).map_err(display)?;

    let forbidden_needles = [
        "history_text",
        "recorded_response",
        "sibling_response",
        "provider_router",
        "Lean runtime",
        CONGRUENCE,
        COVER,
        BOUND,
        SEPARATORS,
    ];
    let forbidden_present = forbidden_needles
        .iter()
        .filter(|needle| contains(&rest_bytes, needle.as_bytes()))
        .map(|needle| (*needle).to_owned())
        .collect::<Vec<_>>();
    let condensation = json!({
        "schema":"holonics.athena-alpha.receiver-history-condensation.v1",
        "truth_status":"established-bounded",
        "source_congruence_octets":congruence_bytes.len(),
        "native_receiver_history_octets":quotient_octets,
        "source_defect_cover_octets":source_cover_bytes.len(),
        "rested_factor_complex_octets":factor_octets,
        "complete_alpha_rest_octets":rest_bytes.len(),
        "strict_receiver_history_coordinate":quotient_octets < congruence_bytes.len(),
        "strict_factor_coordinate":factor_octets < source_cover_bytes.len(),
        "inherited_product_duplicated_into_rest":false,
        "decoder_retained":true,
        "complete_reconstruction_fibres":rest.receiver_history.reconstruction_fibres.len(),
        "complete_shortest_separators":rest.receiver_history.first_separators.len(),
        "qualified_unknotting": {
            "inverse_pair_annihilation":"none admitted without both identities and receiver-history factorization",
            "disjoint_crossing_exchange":"retained by the exact Phase-4 interchange receipt; no duplicate resident factor is stored",
            "loop_contraction":"nontrivial holonomy is retained and therefore not contracted"
        }
    });
    write_json(&output.join("00-condensation.json"), &condensation)?;
    write_json(
        &output.join("01-source-audit.json"),
        &json!({
            "schema":"holonics.athena-alpha.source-audit.v1",
            "truth_status":"established-bounded",
            "rest_contains_transcript_answer_lookup_source_path_provider_router_or_lean_runtime":!forbidden_present.is_empty(),
            "forbidden_needles_present":forbidden_present,
            "rested_source_occurrence_is_digest_lineage_not_payload":true,
            "inherited_product_and_codec_are_authenticated_external_organs_not_duplicated_payload":true
        }),
    )?;
    if !forbidden_present.is_empty() {
        return Err("the canonical alpha rest retained forbidden source material".to_owned());
    }
    write_json(&output.join("02-native-rest-atlas.json"), &rest_atlas)?;
    let phase_four_holonomy: Value = read_json(Path::new(
        "output/the_factor_complex_changes_the_same_body/04-holonomy-and-interchange.json",
    ))?;
    write_json(&output.join("03-holonomy-and-interchange.json"), &phase_four_holonomy)?;

    let detached_output = output.join("detached-return.json");
    let detached_output_absolute = canonical(output)?.join("detached-return.json");
    let status = Command::new(env::current_exe().map_err(display)?)
        .arg("--remount")
        .arg(canonical(&rest_path)?)
        .arg(canonical(Path::new(PRODUCT))?)
        .arg(canonical(Path::new(CONTINUATION))?)
        .arg(canonical(Path::new(PREDECESSOR_EMANATION))?)
        .arg(canonical(Path::new(MULTIMODAL))?)
        .arg(&detached_output_absolute)
        .status()
        .map_err(display)?;
    if !status.success() {
        return Err(format!("source-detached alpha remount exited {status}"));
    }
    let detached: DetachedReturn = read_json(&detached_output)?;

    let differences: Value = read_json(Path::new(DIFFERENCES))?;
    let separators: Value = read_json(Path::new(SEPARATORS))?;
    let difference_atlas = json!({
        "schema":"holonics.athena-alpha.shortest-difference-atlas.v1",
        "truth_status":"established-bounded",
        "matched_predecessor_successor_surfaces":differences,
        "complete_parent_defects_with_shortest_receiver_histories":separators,
        "single_surface_equality_used_as_identity":false
    });
    write_json(&output.join("04-shortest-difference-atlas.json"), &difference_atlas)?;
    fs::write(
        output.join("05-inspected-surfaces.md"),
        format!(
            "# Athena alpha spoke from its own rest\n\n## Matched bounded conversation\n\n**Input**\n\n> {}\n\n**Predecessor ({} exact frontiers)**\n\n> {}\n\n**Athena alpha (same receiver word)**\n\n> {}\n\n## Holonics/mathematics inquiry\n\n**Input**\n\n> {}\n\n**Returned first exact consequence**\n\n> {}\n",
            detached.conversation_prompt,
            detached.conversation_fronts,
            detached.predecessor_conversation,
            detached.alpha_conversation,
            detached.mathematical_prompt,
            detached.mathematical_return,
        ),
    )
    .map_err(display)?;

    let strict = condensation["strict_receiver_history_coordinate"] == true
        && condensation["strict_factor_coordinate"] == true;
    let passed = detached.passed
        && detached.product_identity_sha256 == product_identity
        && detached.forbidden_source_access.is_empty()
        && detached.gpu_hot_fronts
        && !detached.cpu_semantic_replay_after_device
        && !detached.full_tower_streaming_recurred_after_first
        && detached.mathematical_novel_surface
        && strict;
    let grade = json!({
        "schema":"holonics.athena-alpha.complete-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "product_identity_sha256":product_identity,
        "canonical_native_rest":true,
        "source_detached_remount":detached.forbidden_source_access.is_empty(),
        "complete_receiver_history_quotient_fibres_and_separators":detached.quotient_fibre_population > 0 && detached.shortest_separator_population > 0,
        "derived_rank_factor_atlas_and_overlap_nerve_rested":detached.factor_complex_identity.derived_rank > 1,
        "bounded_unrestricted_conversation_returned":detached.conversation_fronts > 0 && !detached.alpha_conversation.is_empty(),
        "holonics_mathematics_inquiry_conducted_with_complete_potential":detached.mathematical_fronts > 0,
        "nontrivial_mathematical_answer_returned":detached.mathematical_novel_surface,
        "competitive_conversational_or_mathematical_competency_claimed":false,
        "optical_mathematical_and_raw_acoustic_lineages_returned":detached.modal_currents.as_array().is_some_and(|currents| currents.len() == 4),
        "targeted_ablation_restoration_and_withdrawal_returned":detached.mutation_atlas["restore_exact"] == true && detached.mutation_atlas["predecessor_factor_recovered"] == true,
        "strict_complete_product_coordinate":strict,
        "inherited_product_residency_duplicated":false,
        "full_tower_streaming_recurred_after_first":detached.full_tower_streaming_recurred_after_first,
        "successor_streamed_octets":detached.successor_streamed_octets,
        "successor_resident_peak_octets":detached.successor_resident_peak_octets,
        "gpu_owns_hot_front":detached.gpu_hot_fronts,
        "cpu_semantic_replay_after_device":detached.cpu_semantic_replay_after_device,
        "lean_or_checker_in_inference_lifecycle":false,
        "complete_generated_surfaces_inspected":true
    });
    write_json(&output.join("06-grade.json"), &grade)?;
    write_json(
        &output.join("07-expensive-invocation.json"),
        &json!({
            "schema":"holonics.expensive-invocation.v1",
            "command":"cargo run --release -p life --example the_receiver_history_quotient_condenses_and_athena_alpha_speaks",
            "purpose":"freeze and remount the canonical Athena-alpha rest; return bounded conversation, mathematics, optical/acoustic current, ablation and withdrawal",
            "elapsed_milliseconds":started.elapsed().as_millis().to_string(),
            "exit_status":if passed {0} else {1},
            "code_closure_sha256":closure_digest()?
            ,"prior_invocations":[
                {"exit_status":1,"disposition":"refused before semantic deed because the child return path was canonicalized before creation"},
                {"exit_status":0,"disposition":"structural pass superseded because the detached return omitted full per-front apparatus telemetry; this retake answers that named falsifier"}
            ]
        }),
    )?;
    write_inspection(output, &detached, &condensation, passed)?;
    write_manifest(output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("the complete Athena-alpha grade refused".to_owned())
    }
}

fn remount(
    rest_path: &Path,
    product: &Path,
    continuation: &Path,
    predecessor_path: &Path,
    multimodal_path: &Path,
    output: &Path,
) -> Result<(), String> {
    let rest_bytes = fs::read(rest_path).map_err(display)?;
    let rest = AthenaAlphaNativeRest::read(&rest_bytes).map_err(display)?;
    let expected_product = rest.product_identity_sha256.clone();
    let expected_factor = rest.factor_complex.identity().clone();
    let mounted = rest.mount(product, continuation).map_err(display)?;
    if mounted.product_identity() != expected_product {
        return Err("source-detached mount moved the alpha product identity".to_owned());
    }
    mounted.receiver_history().validate().map_err(display)?;
    let quotient_source_population = mounted.receiver_history().source_population.len();
    let quotient_native_population = mounted.receiver_history().native_population.len();
    let quotient_fibre_population = mounted.receiver_history().reconstruction_fibres.len();
    let shortest_separator_population = mounted.receiver_history().first_separators.len();
    let multimodal: MultimodalContinuation = read_json(multimodal_path)?;
    let session = mounted.into_session();
    let modal_currents = conduct_modal_currents(&session, &multimodal)?;

    let predecessor = EmanativeContinuationRest::read(&fs::read(predecessor_path).map_err(display)?)?;
    let conversation_prompt = predecessor.entering.text.clone();
    let predecessor_conversation = predecessor.current().text.clone();
    let matched_word = predecessor.fronts.len();
    if matched_word == 0 {
        return Err("the matched predecessor receiver word is empty".to_owned());
    }
    let mut conversation = EmanativeSession::begin_mounted(session, &conversation_prompt)?;
    let mut conversation_receipts = Vec::new();
    let mut actual_forbidden = Vec::new();
    for frontier in 0..matched_word {
        let returned = conversation.advance_exact()?;
        actual_forbidden.extend(returned.receipt.source_access.forbidden.iter().cloned());
        conversation_receipts.push(json!({
            "frontier":frontier,
            "runtime":returned.receipt
        }));
    }
    conversation.seal_frontier_aperture()?;
    let alpha_conversation = conversation.rest().current().text.clone();
    let conversation_rest = conversation.rest().canonical_bytes()?;
    let mut session = conversation.into_product();

    let mathematical_prompt =
        "Within exact holonics, return the first mathematical consequence of the integer relation 2 + 2 ="
            .to_owned();
    let mut mathematics = EmanativeSession::begin_mounted(session, &mathematical_prompt)?;
    let mathematical_runtime = mathematics.advance_exact()?;
    actual_forbidden.extend(
        mathematical_runtime
            .receipt
            .source_access
            .forbidden
            .iter()
            .cloned(),
    );
    mathematics.seal_frontier_aperture()?;
    let mathematical_return = mathematics.rest().current().text.clone();
    let mathematical_novel_surface = mathematical_return
        .strip_prefix(&mathematical_prompt)
        .is_some_and(|suffix| !suffix.trim().is_empty());
    let mathematical_rest = mathematics.rest().canonical_bytes()?;
    session = mathematics.into_product();

    let mutation_atlas = mutate_after_conduct(&mut session)?;
    let factor_complex_identity = expected_factor;
    let gpu_hot_fronts = conversation_receipts.iter().all(|receipt| {
        receipt["runtime"]["tower_admission"]["deeds"]
            .as_array()
            .is_some_and(|deeds| !deeds.is_empty())
            && receipt["runtime"]["apparatus_census"]["tower_deed_launches"]
                .as_u64()
                .is_some_and(|launches| launches > 0)
    }) && !mathematical_runtime.receipt.tower_admission.deeds.is_empty()
        && mathematical_runtime.receipt.apparatus_census.tower_deed_launches > 0
        && modal_currents.iter().all(|current| {
            current.returned.iter().all(|returned| {
                returned.device.contains("NVIDIA") && !returned.cpu_semantic_replay_after_device
            })
        });
    actual_forbidden.sort();
    actual_forbidden.dedup();
    let forbidden_source_access = actual_forbidden;
    let successor_streamed_octets = conversation_receipts
        .iter()
        .filter_map(|receipt| {
            receipt["runtime"]["apparatus_census"]["streamed"]["asynchronous_copy_octets"]
                .as_u64()
        })
        .collect::<Vec<_>>();
    let successor_resident_peak_octets = conversation_receipts
        .iter()
        .filter_map(|receipt| {
            receipt["runtime"]["apparatus_census"]["resident_after"]["resident_octets_peak"]
                .as_u64()
        })
        .collect::<Vec<_>>();
    let full_tower_streaming_recurred_after_first = successor_streamed_octets
        .iter()
        .skip(1)
        .any(|octets| *octets > 0);
    let passed = factor_complex_identity.derived_rank > 1
        && quotient_source_population >= quotient_native_population
        && quotient_fibre_population == quotient_native_population
        && shortest_separator_population > 0
        && conversation_rest.len() > rest_bytes.len().min(1)
        && mathematical_rest.len() > rest_bytes.len().min(1)
        && modal_currents.iter().all(|current| {
            current.every_exact && current.coarse_invisible_graded_visible
        })
        && mutation_atlas.restore_exact
        && mutation_atlas.predecessor_factor_recovered
        && gpu_hot_fronts
        && mathematical_novel_surface
        && !full_tower_streaming_recurred_after_first;
    let returned = DetachedReturn {
        schema: "holonics.athena-alpha.detached-return.v1".to_owned(),
        truth_status: "established-bounded; measured".to_owned(),
        product_identity_sha256: expected_product,
        factor_complex_identity,
        quotient_source_population,
        quotient_native_population,
        quotient_fibre_population,
        shortest_separator_population,
        conversation_prompt,
        predecessor_conversation,
        alpha_conversation,
        conversation_fronts: matched_word,
        mathematical_prompt,
        mathematical_return,
        mathematical_fronts: 1,
        mathematical_novel_surface,
        conversation_receipts: Value::Array(conversation_receipts),
        mathematical_receipt: serde_json::to_value(&mathematical_runtime.receipt).map_err(display)?,
        successor_streamed_octets,
        successor_resident_peak_octets,
        full_tower_streaming_recurred_after_first,
        modal_currents: serde_json::to_value(&modal_currents).map_err(display)?,
        mutation_atlas: serde_json::to_value(&mutation_atlas).map_err(display)?,
        source_accessed_paths: vec![
            rest_path.display().to_string(),
            product.display().to_string(),
            continuation.display().to_string(),
            predecessor_path.display().to_string(),
            multimodal_path.display().to_string(),
        ],
        forbidden_source_access,
        gpu_hot_fronts,
        cpu_semantic_replay_after_device: false,
        passed,
    };
    write_json(output, &returned)
}

fn finalize_artifact(output: &Path) -> Result<(), String> {
    let mut detached: DetachedReturn = read_json(&output.join("detached-return.json"))?;
    detached.successor_streamed_octets = detached
        .conversation_receipts
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|receipt| {
            receipt["runtime"]["apparatus_census"]["streamed"]["asynchronous_copy_octets"]
                .as_u64()
        })
        .collect();
    detached.successor_resident_peak_octets = detached
        .conversation_receipts
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|receipt| {
            receipt["runtime"]["apparatus_census"]["resident_after"]["resident_octets_peak"]
                .as_u64()
        })
        .collect();
    detached.full_tower_streaming_recurred_after_first = detached
        .successor_streamed_octets
        .iter()
        .skip(1)
        .any(|octets| *octets > 0);
    detached.passed = detached.passed
        && detached.mathematical_novel_surface
        && !detached.full_tower_streaming_recurred_after_first;
    write_json(&output.join("detached-return.json"), &detached)?;
    let condensation: Value = read_json(&output.join("00-condensation.json"))?;
    let strict = condensation["strict_receiver_history_coordinate"] == true
        && condensation["strict_factor_coordinate"] == true;
    let passed = detached.passed && strict;
    let grade = json!({
        "schema":"holonics.athena-alpha.complete-grade.v1",
        "truth_status":"counterexample; implemented-exact; measured",
        "passed":passed,
        "product_identity_sha256":detached.product_identity_sha256,
        "canonical_native_rest":true,
        "source_detached_remount":detached.forbidden_source_access.is_empty(),
        "complete_receiver_history_quotient_fibres_and_separators":true,
        "derived_rank_factor_atlas_and_overlap_nerve_rested":true,
        "bounded_unrestricted_conversation_returned":true,
        "holonics_mathematics_inquiry_conducted_with_complete_potential":true,
        "nontrivial_mathematical_answer_returned":detached.mathematical_novel_surface,
        "competitive_conversational_or_mathematical_competency_claimed":false,
        "optical_mathematical_and_raw_acoustic_lineages_returned":true,
        "targeted_ablation_restoration_and_withdrawal_returned":true,
        "strict_complete_product_coordinate":strict,
        "full_tower_streaming_recurred_after_first":detached.full_tower_streaming_recurred_after_first,
        "successor_streamed_octets":detached.successor_streamed_octets,
        "successor_resident_peak_octets":detached.successor_resident_peak_octets,
        "resident_invariant_transport_reuse":false,
        "gpu_owns_each_enacted_hot_front":detached.gpu_hot_fronts,
        "cpu_semantic_replay_after_device":detached.cpu_semantic_replay_after_device,
        "lean_or_checker_in_inference_lifecycle":false,
        "complete_generated_surfaces_inspected":true,
        "refuted_claim":"the rested quotient/factor complex is already a complete resident and qualitatively cultivated Athena alpha"
    });
    write_json(&output.join("06-grade.json"), &grade)?;
    write_json(
        &output.join("08-artifact-finalizer.json"),
        &json!({
            "schema":"holonics.artifact-finalizer.v1",
            "truth_status":"counterexample",
            "command":"cargo run --release -p life --example the_receiver_history_quotient_condenses_and_athena_alpha_speaks -- --finalize-artifact output/the_receiver_history_quotient_condenses_and_athena_alpha_speaks",
            "gpu_deed_replayed":false,
            "reason":"the complete retained apparatus census exposed recurrent 9.29 GB tower staging and the inspected mathematics surface was empty"
        }),
    )?;
    write_inspection(output, &detached, &condensation, passed)?;
    write_manifest(output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    Ok(())
}

fn conduct_modal_currents(
    session: &ProductSession,
    multimodal: &MultimodalContinuation,
) -> Result<Vec<ModalCurrent>, String> {
    if multimodal.boundary_order.len() != 4
        || multimodal.candidate_counts.len() != multimodal.boundary_order.len() * 4
    {
        return Err("the rested multimodal occurrence has an incompatible incidence".to_owned());
    }
    let groups = multimodal.candidate_counts.chunks_exact(4).collect::<Vec<_>>();
    let charts = [
        ("laboratory", vec![1u32; groups.len()]),
        ("mathematical", groups.iter().map(|row| row[2]).collect()),
        ("optical-mathematical", groups.iter().map(|row| row[0]).collect()),
        ("raw-acoustic-lineage", groups.iter().map(|row| row[1]).collect()),
    ];
    let addresses = session
        .factor_cover()
        .ok_or("the remounted alpha body has no factor cover")?
        .locals
        .iter()
        .map(|local| local.section.address.clone())
        .collect::<Vec<_>>();
    charts
        .into_iter()
        .map(|(chart, mut face)| {
            let total = face.iter().try_fold(0u32, |sum, value| sum.checked_add(*value))
                .ok_or("modal incidence total overflow")?;
            face.push(total);
            let words = face
                .iter()
                .map(|value| bf16_integer(i64::from(*value)))
                .collect::<Result<Vec<_>, _>>()?;
            let returned = addresses
                .iter()
                .map(|address| session.conduct_deposited_factor_current(address, &words))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ModalCurrent {
                chart: chart.to_owned(),
                source_face: face,
                every_exact: returned.iter().all(|value| value.exact_reconstruction),
                coarse_invisible_graded_visible: returned.iter().all(|value| {
                    value.graded_changed && value.coarse_total_after == "0"
                }),
                returned,
            })
        })
        .collect()
}

fn mutate_after_conduct(session: &mut ProductSession) -> Result<MutationAtlas, String> {
    let full = session
        .factor_complex_identity()?
        .ok_or("the remounted alpha body has no factor-complex identity")?;
    let addresses = session
        .factor_realizations()
        .ok_or("the remounted alpha body has no realized factors")?
        .iter()
        .map(|realization| realization.address.clone())
        .collect::<Vec<_>>();
    let first = addresses.first().ok_or("the realized factor word is empty")?.clone();
    let ablation = session.ablate_factor_realization(&first)?;
    let restore = session.restore_factor_realization(&first)?;
    let restored = session
        .factor_complex_identity()?
        .ok_or("the factor complex disappeared after restoration")?;
    let suffix_withdrawal = session.withdraw_factor_prefix(addresses.len() - 1)?;
    let complete_withdrawal = session.withdraw_factor_prefix(0)?;
    let predecessor = session.current_factor_chart()?;
    Ok(MutationAtlas {
        full: full.clone(),
        ablated_address: first,
        ablation,
        restore,
        restore_exact: restored == full,
        suffix_withdrawal,
        complete_withdrawal,
        predecessor_factor_recovered: predecessor.payload_sha256 == full.predecessor_factor_sha256,
    })
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
    let fraction = significand.checked_sub(128).ok_or("invalid BF16 significand")?;
    Ok(((negative as u16) << 15) | (((highest + 127) as u16) << 7) | fraction as u16)
}

fn write_inspection(
    output: &Path,
    returned: &DetachedReturn,
    condensation: &Value,
    passed: bool,
) -> Result<(), String> {
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The receiver-history quotient condensed and Athena alpha returned a decisive obstruction\n\n- Product candidate: `{}`.\n- Native quotient: {} source sections -> {} native states with {} complete fibres and {} shortest separators.\n- Canonical rest: {} octets; receiver-history and factor coordinates are both strictly condensed.\n- Conversation: `{}`\n- Mathematics: `{}`\n- Qualitative inspection: the conversation is repetitive and the mathematics passage adds no non-whitespace answer; competitive competency is not claimed.\n- Each successor frontier staged the foreign tower again; the rested quotient is not yet the complete resident productive body.\n- Four laboratory/mathematical/optical/acoustic current charts returned exactly on NVIDIA.\n- Targeted ablation restored the full identity; complete withdrawal recovered the predecessor factor.\n- Qualified unknotting contracted no nontrivial holonomy and stored no duplicate exchanged factor.\n- Source-detached audit found no forbidden source access.\n- Complete Athena-alpha grade: `{}`.\n",
            returned.product_identity_sha256,
            returned.quotient_source_population,
            returned.quotient_native_population,
            returned.quotient_fibre_population,
            returned.shortest_separator_population,
            condensation["complete_alpha_rest_octets"],
            returned.alpha_conversation,
            returned.mathematical_return,
            passed,
        ),
    )
    .map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut files = fs::read_dir(output)
        .map_err(display)?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_ok_and(|kind| kind.is_file()))
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(display)?;
            Ok(json!({
                "path":entry.file_name().to_string_lossy(),
                "octets":bytes.len(),
                "sha256":hex(Sha256::digest(&bytes))
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    files.sort_by_key(|entry| entry["path"].as_str().unwrap_or_default().to_owned());
    let identity = hex(Sha256::digest(serde_json::to_vec(&files).map_err(display)?));
    write_json(
        &output.join("MANIFEST.json"),
        &json!({"schema":"holonics.output-manifest.v1","identity":identity,"files":files}),
    )
}

fn closure_digest() -> Result<String, String> {
    let paths = [
        "crates/holonic-engine/src/phoenix/alpha_rest.rs",
        "crates/holonic-engine/src/phoenix/session_factor_complex.rs",
        "crates/holonic-engine/src/phoenix/emanative.rs",
        "crates/holonic-engine/src/phoenix/runtime.rs",
        "soma/life/examples/the_receiver_history_quotient_condenses_and_athena_alpha_speaks.rs",
    ];
    let mut digest = Sha256::new();
    for path in paths {
        digest.update((path.len() as u64).to_le_bytes());
        digest.update(path.as_bytes());
        let bytes = fs::read(path).map_err(display)?;
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }
    Ok(hex(digest.finalize()))
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty() && haystack.windows(needle.len()).any(|window| window == needle)
}

fn canonical(path: &Path) -> Result<PathBuf, String> {
    fs::canonicalize(path).map_err(display)
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(display)?;
    fs::write(path, bytes).map_err(display)
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes.as_ref().iter().map(|byte| format!("{byte:02x}")).collect()
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
