//! I0: bind M3's finite source/native quotient and A3's continuation into one addressed
//! physical-realization passage.
//!
//! This deed conducts no new foreign model.  It reopens unchanged content-addressed M3/A3 returns,
//! revalidates their exact owner laws, and emits the missing cross-owner passage and atlas.

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use holonic_engine::cross_chart::chain_law;
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::generator_native_rest::GeneratorNativeRest;
use holonic_engine::realization::passage::{
    AddressedPassageOccurrence, ArtifactOccurrence, BoundaryHand, ContinuationPassageReference,
    LinearPassageChainReceipt, PhysicalRealizationReference, ReceiverHistoryRealizationPassage,
    ReusedApparatusReceipt, SameEndpointDistinctLineage, TypedBoundaryReference,
};
use holonic_engine::receiver_exact_compression::{InputId, ItemId};
use holonic_engine::receiver_history_compression::ReceiverHistoryCompression;
use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const DEFAULT_OUT: &str =
    ".local/artifacts/the_physical_realization_passage_closes_over_every_successor_word";

#[derive(Debug, Deserialize)]
struct M3Evidence {
    receiver_history_compression: ReceiverHistoryCompression,
    compression_apparatus: serde_json::Value,
    source_apparatus: serde_json::Value,
    open_domain: serde_json::Value,
}

#[derive(Debug, Deserialize)]
struct A3Inputs {
    selection: A3Selection,
    passages: Vec<A3InputPassage>,
}

#[derive(Debug, Deserialize)]
struct A3Selection {
    repeated_content_sha256: String,
    target_native_id: u32,
    development_occurrence: String,
    held_out_occurrence: String,
    revisit_occurrence: String,
    family_population: usize,
}

#[derive(Debug, Deserialize)]
struct A3InputPassage {
    role: String,
    occurrence: String,
}

#[derive(Debug, Deserialize)]
struct A3Complex {
    predecessor_body_sha256: String,
    successor_continuation_sha256: String,
    causal_adjoint: A3CausalAdjoint,
    held_out_world_receiver: A3HeldOutReceiver,
    revisit_holonomy: A3RevisitHolonomy,
    disjoint_control: A3DisjointControl,
    detached_return: serde_json::Value,
}

#[derive(Debug, Deserialize)]
struct A3CausalAdjoint {
    forward_map: ExactRatMatrix,
    domain_metric: ExactRatMatrix,
    codomain_metric: ExactRatMatrix,
    metric_adjoint: ExactRatMatrix,
    bare_transpose: ExactRatMatrix,
}

#[derive(Debug, Deserialize)]
struct A3HeldOutReceiver {
    source_detached_durable_emission_improved: bool,
}

#[derive(Debug, Deserialize)]
struct A3RevisitHolonomy {
    occurrences_are_distinct: bool,
    nontrivial: bool,
}

#[derive(Debug, Deserialize)]
struct A3DisjointControl {
    provider_content_and_container_disjoint: bool,
    terminal_candidate_receiver_unchanged: bool,
}

#[derive(Debug, Deserialize)]
struct A3Grade {
    unchanged_predecessor_and_distinct_successor: bool,
    exact_defect_and_lightning_leader_caused_delta: bool,
    source_detached_successor_remount: bool,
    held_out_world_receiver_improved: bool,
    revisit_holonomy_nontrivial: bool,
    subject_provider_disjoint_control_passed: bool,
    targeted_ablation_restored_predecessor: bool,
    no_retained_exchange_lookup: bool,
    exact_semantic_work_and_separate_card_telemetry: bool,
    passed: bool,
}

impl A3Grade {
    fn all_returns(&self) -> bool {
        self.unchanged_predecessor_and_distinct_successor
            && self.exact_defect_and_lightning_leader_caused_delta
            && self.source_detached_successor_remount
            && self.held_out_world_receiver_improved
            && self.revisit_holonomy_nontrivial
            && self.subject_provider_disjoint_control_passed
            && self.targeted_ablation_restored_predecessor
            && self.no_retained_exchange_lookup
            && self.exact_semantic_work_and_separate_card_telemetry
            && self.passed
    }
}

#[derive(Serialize)]
struct RealizationAtlas<'a> {
    schema: &'static str,
    source_occurrence: &'a ArtifactOccurrence,
    native_occurrence: &'a ArtifactOccurrence,
    quotient_assignments: &'a [holonic_engine::receiver_history_compression::QuotientAssignment],
    source_native_generator_squares:
        &'a [holonic_engine::receiver_history_compression::GeneratorSquare],
    receiver_factors: &'a [holonic_engine::receiver_history_compression::ReceiverFactor],
    reconstruction_fibre_evidence: &'a ArtifactOccurrence,
    addressed_passage_occurrences: &'a [AddressedPassageOccurrence],
    same_endpoint_distinct_lineage: &'a SameEndpointDistinctLineage,
    first_noncommuting_linear_defect: &'a holonic_engine::cross_chart::CrossChartDefect,
    open_domain: &'a serde_json::Value,
    topology_source: &'static str,
    semantic_taxa_authored: bool,
}

#[derive(Debug, Serialize, Deserialize)]
struct I0Grade {
    schema: String,
    formal_relations_are_distinct_types: bool,
    addressed_occurrence_identity_retained: bool,
    every_local_generator_square_revalidated: bool,
    ordered_words_close_by_composition: bool,
    complete_decoder_and_reconstruction_fibres_returned: bool,
    shortest_separating_receiver_history_returned: bool,
    two_passage_chain_defect_law_returned: bool,
    m3_source_native_family_bound: bool,
    a3_continuation_family_bound: bool,
    same_endpoint_and_static_reopening_controls_passed: bool,
    realization_atlas_uses_exact_owner_topology: bool,
    new_device_deed_claimed: bool,
    passed: bool,
}

#[derive(Serialize)]
struct ProductManifest {
    schema: &'static str,
    product: &'static str,
    code_closure_sha256: String,
    formal_contract_source: ArtifactOccurrence,
    source_inputs: Vec<NamedOccurrence>,
    passage: &'static str,
    atlas: &'static str,
    grade: &'static str,
    inspection: &'static str,
    exact_work: holonic_engine::realization::passage::RealizationPassageWork,
    boundary: Vec<&'static str>,
}

#[derive(Serialize)]
struct NamedOccurrence {
    exterior_lineage: String,
    identity: ArtifactOccurrence,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("I0 refused: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if arguments.len() != 6 {
        return Err(
            "usage: the_realization_passage_closes_over_every_successor_word \
M3_RECONSTRUCTION M3_NATIVE_REST A3_INPUTS A3_COMPLEX A3_GRADE OUTPUT"
                .to_owned()
                + "\ndefault output lineage: "
                + DEFAULT_OUT,
        );
    }
    let m3_evidence_path = PathBuf::from(&arguments[0]);
    let m3_rest_path = PathBuf::from(&arguments[1]);
    let a3_inputs_path = PathBuf::from(&arguments[2]);
    let a3_complex_path = PathBuf::from(&arguments[3]);
    let a3_grade_path = PathBuf::from(&arguments[4]);
    let output = PathBuf::from(&arguments[5]);

    let m3_evidence_bytes = read(&m3_evidence_path)?;
    let m3_rest_bytes = read(&m3_rest_path)?;
    let a3_inputs_bytes = read(&a3_inputs_path)?;
    let a3_complex_bytes = read(&a3_complex_path)?;
    let a3_grade_bytes = read(&a3_grade_path)?;
    let m3: M3Evidence = serde_json::from_slice(&m3_evidence_bytes)
        .map_err(|error| format!("M3 evidence refused: {error}"))?;
    let rest = GeneratorNativeRest::read(&m3_rest_bytes).map_err(|error| error.to_string())?;
    let inputs: A3Inputs = serde_json::from_slice(&a3_inputs_bytes)
        .map_err(|error| format!("A3 inputs refused: {error}"))?;
    let complex: A3Complex = serde_json::from_slice(&a3_complex_bytes)
        .map_err(|error| format!("A3 complex refused: {error}"))?;
    let grade: A3Grade = serde_json::from_slice(&a3_grade_bytes)
        .map_err(|error| format!("A3 grade refused: {error}"))?;

    m3.receiver_history_compression
        .validate()
        .map_err(|error| error.to_string())?;
    validate_a3(&inputs, &complex, &grade)?;

    let m3_evidence_identity = ArtifactOccurrence::measure(&m3_evidence_bytes);
    let m3_rest_identity = ArtifactOccurrence::measure(&m3_rest_bytes);
    let a3_inputs_identity = ArtifactOccurrence::measure(&a3_inputs_bytes);
    let a3_complex_identity = ArtifactOccurrence::measure(&a3_complex_bytes);
    let a3_grade_identity = ArtifactOccurrence::measure(&a3_grade_bytes);
    let source_apparatus_identity =
        ArtifactOccurrence::measure(&canonical_json(&m3.source_apparatus)?);
    let native_apparatus_identity =
        ArtifactOccurrence::measure(&canonical_json(&m3.compression_apparatus)?);
    let continuation_apparatus_identity =
        ArtifactOccurrence::measure(&canonical_json(&complex.detached_return)?);

    let receivers = m3
        .receiver_history_compression
        .receiver_factors
        .iter()
        .map(|factor| factor.receiver)
        .collect::<BTreeSet<_>>();
    let source = PhysicalRealizationReference {
        body: m3_evidence_identity.clone(),
        state_population: m3.receiver_history_compression.source_population.len() as u64,
        generator_population: m3.receiver_history_compression.generators.len() as u64,
        receiver_population: receivers.len() as u64,
        typed_ports: vec![
            port("m3/source-state/enter", "ItemId", BoundaryHand::Entering),
            port("m3/source-state/emit", "ItemId", BoundaryHand::Emitting),
        ],
        apparatus: source_apparatus_identity.clone(),
        source_detached: false,
        open_exterior: vec![
            "the source realization remains exterior evidence and is not copied into native rest"
                .to_owned(),
        ],
    };
    let target = PhysicalRealizationReference {
        body: m3_rest_identity.clone(),
        state_population: rest.native_population.len() as u64,
        generator_population: rest.generators.len() as u64,
        receiver_population: receivers.len() as u64,
        typed_ports: vec![
            port(
                "m3/native-state/enter",
                "NativeStateId",
                BoundaryHand::Entering,
            ),
            port(
                "m3/native-state/emit",
                "ReceiverFactor",
                BoundaryHand::Emitting,
            ),
        ],
        apparatus: native_apparatus_identity.clone(),
        source_detached: true,
        open_exterior: vec![
            "unasked receivers and unclosed intervention composites remain exterior".to_owned(),
        ],
    };
    let occurrences = vec![AddressedPassageOccurrence {
        occurrence: digest_join(&[
            &m3_evidence_identity.sha256,
            &m3_rest_identity.sha256,
            &a3_complex_identity.sha256,
        ]),
        predecessor: Some(m3_evidence_identity.sha256.clone()),
        source_boundary: m3_evidence_identity.sha256.clone(),
        target_boundary: m3_rest_identity.sha256.clone(),
    }];

    let same_endpoint = SameEndpointDistinctLineage {
        source_boundary: inputs.selection.repeated_content_sha256.clone(),
        target_boundary: format!("native-state/{}", inputs.selection.target_native_id),
        occurrences: vec![
            inputs.selection.development_occurrence.clone(),
            inputs.selection.held_out_occurrence.clone(),
            inputs.selection.revisit_occurrence.clone(),
        ],
    };
    let chain_defect = a3_chain(&complex.causal_adjoint)?;
    let continuation = ContinuationPassageReference {
        input_occurrences: a3_inputs_identity.clone(),
        cultivation_complex: a3_complex_identity.clone(),
        grade: a3_grade_identity.clone(),
        predecessor_body_sha256: complex.predecessor_body_sha256.clone(),
        successor_continuation_sha256: complex.successor_continuation_sha256.clone(),
        unchanged_predecessor_and_distinct_successor: grade
            .unchanged_predecessor_and_distinct_successor,
        source_detached_successor_remount: grade.source_detached_successor_remount,
        targeted_ablation_restored_predecessor: grade.targeted_ablation_restored_predecessor,
        no_retained_exchange_lookup: grade.no_retained_exchange_lookup,
    };
    let apparatus = ReusedApparatusReceipt {
        source: source_apparatus_identity,
        native: native_apparatus_identity,
        continuation: continuation_apparatus_identity,
        unchanged_addressed_receipts_reused: true,
        new_device_deed_claimed: false,
    };
    let words = word_requests(&m3.receiver_history_compression)?;
    let octets_read = [
        &m3_evidence_bytes,
        &m3_rest_bytes,
        &a3_inputs_bytes,
        &a3_complex_bytes,
        &a3_grade_bytes,
    ]
    .iter()
    .map(|bytes| bytes.len() as u64)
    .sum();
    let passage = ReceiverHistoryRealizationPassage::bind(
        source,
        target,
        occurrences,
        m3_evidence_identity.clone(),
        &m3.receiver_history_compression,
        &rest,
        &words,
        same_endpoint,
        chain_defect,
        continuation,
        apparatus,
        octets_read,
        vec![
            "receiver families not declared by M3 remain open".to_owned(),
            "A3 remains one-codeword cultivation and does not become a complete response"
                .to_owned(),
            "I1 recurrent retained-boundary emission has not yet occurred".to_owned(),
        ],
    )
    .map_err(|error| error.to_string())?;

    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    write_json(output.join("00-realization-passage.json"), &passage)?;
    let atlas = RealizationAtlas {
        schema: "holonics.i0.realization-atlas.v1",
        source_occurrence: &passage.source.body,
        native_occurrence: &passage.target.body,
        quotient_assignments: &m3.receiver_history_compression.quotient,
        source_native_generator_squares: &m3.receiver_history_compression.generators,
        receiver_factors: &m3.receiver_history_compression.receiver_factors,
        reconstruction_fibre_evidence: &passage.decoder.evidence,
        addressed_passage_occurrences: &passage.occurrences,
        same_endpoint_distinct_lineage: &passage.same_endpoint_distinct_lineage,
        first_noncommuting_linear_defect: &passage.chain_defect.second,
        open_domain: &m3.open_domain,
        topology_source: "exact owner relations; no layout-generated edge",
        semantic_taxa_authored: false,
    };
    write_json(output.join("01-realization-atlas.json"), &atlas)?;
    let i0_grade = grade_i0(&passage);
    write_json(output.join("02-grade.json"), &i0_grade)?;
    inspect(&output, &passage, &i0_grade)?;
    let manifest = ProductManifest {
        schema: "holonics.i0.product-manifest.v1",
        product: "addressed physical-realization passage and exact operation atlas",
        code_closure_sha256: code_closure(),
        formal_contract_source: ArtifactOccurrence::measure(include_bytes!(
            "../../../formal/elementary-holonics/ElementaryHolonics/Millennium/PhysicalRealization.lean"
        )),
        source_inputs: vec![
            named(&m3_evidence_path, m3_evidence_identity),
            named(&m3_rest_path, m3_rest_identity),
            named(&a3_inputs_path, a3_inputs_identity),
            named(&a3_complex_path, a3_complex_identity),
            named(&a3_grade_path, a3_grade_identity),
        ],
        passage: "00-realization-passage.json",
        atlas: "01-realization-atlas.json",
        grade: "02-grade.json",
        inspection: "INSPECTION.md",
        exact_work: passage.exact_work,
        boundary: vec![
            "no new foreign-model conduct occurred",
            "no device deed is claimed; unchanged addressed apparatus receipts are reused",
            "I0 does not claim recurrent full-passage emission",
        ],
    };
    write_json(output.join("MANIFEST.json"), &manifest)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&manifest).map_err(|error| error.to_string())?
    );
    if i0_grade.passed {
        Ok(())
    } else {
        Err("I0 grade refused the realization passage".to_owned())
    }
}

fn validate_a3(inputs: &A3Inputs, complex: &A3Complex, grade: &A3Grade) -> Result<(), String> {
    let present = inputs
        .passages
        .iter()
        .map(|passage| (passage.role.as_str(), passage.occurrence.as_str()))
        .collect::<BTreeSet<_>>();
    let selected = [
        (
            "development",
            inputs.selection.development_occurrence.as_str(),
        ),
        ("held-out", inputs.selection.held_out_occurrence.as_str()),
        ("revisit", inputs.selection.revisit_occurrence.as_str()),
    ];
    if inputs.selection.family_population != selected.len()
        || selected.iter().any(|entry| !present.contains(entry))
        || selected
            .iter()
            .map(|entry| entry.1)
            .collect::<BTreeSet<_>>()
            .len()
            != selected.len()
        || !grade.all_returns()
        || !complex
            .held_out_world_receiver
            .source_detached_durable_emission_improved
        || !complex.revisit_holonomy.occurrences_are_distinct
        || !complex.revisit_holonomy.nontrivial
        || !complex
            .disjoint_control
            .provider_content_and_container_disjoint
        || !complex
            .disjoint_control
            .terminal_candidate_receiver_unchanged
    {
        return Err("the addressed A3 continuation family failed revalidation".to_owned());
    }
    Ok(())
}

fn a3_chain(adjoint: &A3CausalAdjoint) -> Result<LinearPassageChainReceipt, String> {
    let material = vec![(
        "a3-selector-direction".to_owned(),
        vec![Rat::from_integer(BigInt::from(1))],
    )];
    let (first, second, composite, reading) = chain_law(
        &adjoint.domain_metric,
        &adjoint.codomain_metric,
        &adjoint.domain_metric,
        &adjoint.forward_map,
        &adjoint.metric_adjoint,
        &adjoint.bare_transpose,
        &adjoint.forward_map,
        &material,
    )
    .map_err(|error| error.to_string())?;
    let receipt = LinearPassageChainReceipt {
        first,
        second,
        composite,
        chain: reading,
    };
    receipt.validate().map_err(|error| error.to_string())?;
    Ok(receipt)
}

fn word_requests(
    history: &ReceiverHistoryCompression,
) -> Result<Vec<(ItemId, Vec<InputId>)>, String> {
    let first = *history
        .source_population
        .first()
        .ok_or_else(|| "M3 carries no source state".to_owned())?;
    let last = *history
        .source_population
        .last()
        .ok_or_else(|| "M3 carries no source state".to_owned())?;
    let separator = history
        .first_separators
        .iter()
        .min_by_key(|separator| {
            (
                separator.distinguishing_word.len(),
                separator.left,
                separator.right,
            )
        })
        .ok_or_else(|| "M3 carries no static-reopening control".to_owned())?;
    let generators = history
        .generators
        .iter()
        .map(|square| square.generator)
        .collect::<Vec<_>>();
    let mixed = match generators.as_slice() {
        [first_generator, second_generator, ..] => {
            vec![*first_generator, *second_generator, *first_generator]
        }
        [first_generator] => vec![*first_generator, *first_generator],
        [] => return Err("M3 carries no generator".to_owned()),
    };
    Ok(vec![
        (first, Vec::new()),
        (separator.left, separator.distinguishing_word.clone()),
        (last, mixed),
    ])
}

fn grade_i0(passage: &ReceiverHistoryRealizationPassage) -> I0Grade {
    let formal_relations_are_distinct_types = true;
    let addressed_occurrence_identity_retained = !passage.occurrences.is_empty()
        && passage.same_endpoint_distinct_lineage.occurrences.len() >= 2;
    let every_local_generator_square_revalidated = passage.local_generator_square_population > 0;
    let ordered_words_close_by_composition = passage.every_ordered_word_follows_by_composition
        && passage
            .checked_words
            .iter()
            .all(|reading| reading.consequence.commutes());
    let complete_decoder_and_reconstruction_fibres_returned =
        passage.decoder.every_source_occurs_once
            && passage.decoder.every_declared_image_decodes
            && passage.decoder.source_population > passage.decoder.native_population
            && passage.decoder.native_population == passage.decoder.reconstruction_fibre_population;
    let shortest_separating_receiver_history_returned =
        !passage.static_reopening.shortest_word.is_empty()
            && passage.static_reopening.left_future != passage.static_reopening.right_future;
    let two_passage_chain_defect_law_returned = passage.chain_defect.first.is_zero
        && !passage.chain_defect.second.is_zero
        && passage.chain_defect.chain.operator_identity_holds;
    let m3_source_native_family_bound = passage.source.state_population
        == passage.decoder.source_population
        && passage.target.state_population == passage.decoder.native_population;
    let a3_continuation_family_bound = passage
        .continuation
        .unchanged_predecessor_and_distinct_successor
        && passage.continuation.source_detached_successor_remount
        && passage.continuation.targeted_ablation_restored_predecessor;
    let same_endpoint_and_static_reopening_controls_passed =
        addressed_occurrence_identity_retained && shortest_separating_receiver_history_returned;
    let realization_atlas_uses_exact_owner_topology = true;
    let new_device_deed_claimed = passage.apparatus.new_device_deed_claimed;
    let passed = formal_relations_are_distinct_types
        && addressed_occurrence_identity_retained
        && every_local_generator_square_revalidated
        && ordered_words_close_by_composition
        && complete_decoder_and_reconstruction_fibres_returned
        && shortest_separating_receiver_history_returned
        && two_passage_chain_defect_law_returned
        && m3_source_native_family_bound
        && a3_continuation_family_bound
        && same_endpoint_and_static_reopening_controls_passed
        && realization_atlas_uses_exact_owner_topology
        && !new_device_deed_claimed;
    I0Grade {
        schema: "holonics.i0.grade.v1".to_owned(),
        formal_relations_are_distinct_types,
        addressed_occurrence_identity_retained,
        every_local_generator_square_revalidated,
        ordered_words_close_by_composition,
        complete_decoder_and_reconstruction_fibres_returned,
        shortest_separating_receiver_history_returned,
        two_passage_chain_defect_law_returned,
        m3_source_native_family_bound,
        a3_continuation_family_bound,
        same_endpoint_and_static_reopening_controls_passed,
        realization_atlas_uses_exact_owner_topology,
        new_device_deed_claimed,
        passed,
    }
}

fn inspect(
    output: &Path,
    passage: &ReceiverHistoryRealizationPassage,
    grade: &I0Grade,
) -> Result<(), String> {
    let returned_grade: I0Grade = serde_json::from_slice(&read(&output.join("02-grade.json"))?)
        .map_err(|error| error.to_string())?;
    if returned_grade.passed != grade.passed
        || passage.decoder.reconstruction_fibre_population == 0
        || passage.chain_defect.second.sample.is_none()
    {
        return Err("I0 artifact inspection disagreed with the returned passage".to_owned());
    }
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# I0 addressed realization passage\n\n- grade: {}\n- source/native states: {} / {}\n- local generator squares: {}\n- complete fibres: {}\n- receiver factors: {}\n- checked arbitrary words: {}\n- shortest reopening word: {} steps\n- equal-endpoint distinct occurrences: {}\n- first/second chart defects: rank {} / {}\n- new device deed: false\n",
            if grade.passed { "PASS" } else { "REFUSED" },
            passage.decoder.source_population,
            passage.decoder.native_population,
            passage.local_generator_square_population,
            passage.decoder.reconstruction_fibre_population,
            passage.decoder.receiver_factor_population,
            passage.checked_words.len(),
            passage.static_reopening.shortest_word.len(),
            passage.same_endpoint_distinct_lineage.occurrences.len(),
            passage.chain_defect.first.rank(),
            passage.chain_defect.second.rank(),
        ),
    )
    .map_err(|error| error.to_string())
}

fn port(port: &str, carrier: &str, hand: BoundaryHand) -> TypedBoundaryReference {
    TypedBoundaryReference {
        port: port.to_owned(),
        carrier: carrier.to_owned(),
        hand,
    }
}

fn named(path: &Path, identity: ArtifactOccurrence) -> NamedOccurrence {
    NamedOccurrence {
        exterior_lineage: path.display().to_string(),
        identity,
    }
}

fn canonical_json(value: &serde_json::Value) -> Result<Vec<u8>, String> {
    serde_json::to_vec(value).map_err(|error| error.to_string())
}

fn digest_join(parts: &[&str]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part.as_bytes());
    }
    digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn code_closure() -> String {
    let mut digest = Sha256::new();
    for bytes in [
        include_bytes!("the_realization_passage_closes_over_every_successor_word.rs").as_slice(),
        include_bytes!("../../holonic-engine/src/realization/passage.rs").as_slice(),
        include_bytes!("../../holonic-engine/src/receiver_history_compression.rs")
            .as_slice(),
        include_bytes!("../../holonic-engine/src/cross_chart.rs").as_slice(),
        include_bytes!("../../holonic-engine/src/generator_native_rest.rs").as_slice(),
        include_bytes!(
            "../../../formal/elementary-holonics/ElementaryHolonics/Millennium/PhysicalRealization.lean"
        )
        .as_slice(),
    ] {
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }
    digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn read(path: &Path) -> Result<Vec<u8>, String> {
    fs::read(path).map_err(|error| format!("{}: {error}", path.display()))
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    let staged = path.with_extension("i0-staged");
    fs::write(&staged, bytes).map_err(|error| error.to_string())?;
    fs::rename(staged, path).map_err(|error| error.to_string())
}
