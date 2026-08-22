//! M3 rest, evidence, complete cost vector and source-detached remount grade.

use std::path::Path;

use holonic_engine::generator_native_rest::GeneratorNativeRest;
use holonic_engine::receiver_exact_compression::{InputId, ReceiverId};
use holonic_engine::receiver_history_compression::NativeStateId;
use num_bigint::BigUint;
use num_traits::Zero;
use serde::Serialize;
use sha2::{Digest, Sha256};

use super::active_cover::Recovery;
use super::native::M3Deed;
use super::swing::SwingCalibration;

const OUT: &str = "output/the_active_cover_condenses_into_a_generator_native_codec";

#[derive(Serialize)]
struct Evidence<'a> {
    schema: &'static str,
    truth_status: &'static str,
    source_chart: String,
    source_decoder: String,
    source_schema: &'a str,
    source_states: &'a [super::active_cover::StateAddress],
    generator_declarations: &'a [super::active_cover::GeneratorDeclaration],
    receiver_history_compression:
        &'a holonic_engine::receiver_history_compression::ReceiverHistoryCompression,
    recovered_transition_monoid: &'a super::native::TransitionMonoidReceipt,
    open_domain: &'a super::active_cover::OpenDomainReceipt,
    compression_apparatus: &'a super::native::CompressionApparatus,
    native_semantic_work: &'a super::native::NativeSemanticWork,
    source_exact_work: &'a holonic_engine::exact_work::ExactWork,
    source_apparatus: &'a super::active_cover::SourceApparatus,
    boundary: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CostSide {
    pub artifact_octets: u64,
    pub decoder_octets: u64,
    pub caused_relation_applications: String,
    pub dependency_span: String,
    pub resident_octets_peak: u64,
    pub transfer_octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CostComparison {
    pub schema: String,
    pub receiver: String,
    pub source: CostSide,
    pub native: CostSide,
    pub artifact_nonincreasing: bool,
    pub decoder_nonincreasing: bool,
    pub work_nonincreasing: bool,
    pub dependency_span_nonincreasing: bool,
    pub residency_nonincreasing: bool,
    pub transfer_nonincreasing: bool,
    pub at_least_one_strict_reduction: bool,
    pub complete_vector_strictly_reduced: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct RemountReceipt {
    first_endpoint: NativeStateId,
    first_receiver_image: holonic_engine::receiver_exact_compression::Observation,
    repeated_endpoint_identical: bool,
    repeated_receiver_image_identical: bool,
    source_material_opened_by_decoder: bool,
    withdrawn_generator: InputId,
    targeted_withdrawal_refused_the_same_word: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct Grade {
    schema: String,
    truth_status: String,
    source_population: usize,
    native_population: usize,
    quotient_strictly_reduces_population: bool,
    generator_squares: usize,
    first_separators: usize,
    complete_reconstruction_fibres: usize,
    transition_monoid_elements: usize,
    transition_relations: usize,
    unclosed_intervention_composites_retained: usize,
    card_quotient_launches: u64,
    card_native_word_launches: u64,
    native_rest_omits_foreign_matrices_and_source_items: bool,
    decoder_reopened_complete_declared_image: bool,
    source_detached_remount_held: bool,
    targeted_withdrawal_refused: bool,
    swing_conjugated_negation_held: bool,
    swing_word_normalization_held: bool,
    swing_lineage_receiver_reopened_word: bool,
    complete_cost_vector_strictly_reduced: bool,
    passed: bool,
    boundary: String,
}

pub fn write(
    root: &Path,
    recovery: &Recovery,
    deed: &M3Deed,
    swing: &SwingCalibration,
) -> Result<(), String> {
    let out = root.join(OUT);
    std::fs::create_dir_all(&out).map_err(|error| error.to_string())?;
    let rest_bytes = serde_json::to_vec(&deed.native_rest).map_err(|error| error.to_string())?;
    let rest_path = out.join("generator-native-rest.json");
    std::fs::write(&rest_path, &rest_bytes).map_err(|error| error.to_string())?;

    let evidence = Evidence {
        schema: "holonics.m3.receiver-history-evidence.v1",
        truth_status: "established-bounded",
        source_chart: relative(root, &recovery.source_path)?,
        source_decoder: relative(root, &recovery.source_decoder_path)?,
        source_schema: &recovery.source_schema,
        source_states: &deed.source_states,
        generator_declarations: &recovery.generators,
        receiver_history_compression: &deed.history,
        recovered_transition_monoid: &deed.monoid,
        open_domain: &recovery.open_domain,
        compression_apparatus: &deed.apparatus,
        native_semantic_work: &deed.semantic_work,
        source_exact_work: &recovery.source_exact_work,
        source_apparatus: &recovery.source_apparatus,
        boundary: "the declared M2 boundary/support/prefix receiver family under chronology and the witnessed baseline/reflow chart map; singleton intervention composites, finer grains, lineage identity and all unexcited foreign capability remain open",
    };
    let evidence_bytes = serde_json::to_vec(&evidence).map_err(|error| error.to_string())?;
    let evidence_path = out.join("reconstruction-evidence.json");
    std::fs::write(&evidence_path, &evidence_bytes).map_err(|error| error.to_string())?;
    let swing_bytes = serde_json::to_vec(swing).map_err(|error| error.to_string())?;
    let swing_path = out.join("swing-anti-vacuity.json");
    std::fs::write(&swing_path, &swing_bytes).map_err(|error| error.to_string())?;

    let cost = compare_cost(
        recovery,
        deed,
        (evidence_bytes.len() + swing_bytes.len()) as u64,
        rest_bytes.len() as u64,
    );
    let cost_bytes = serde_json::to_vec(&cost).map_err(|error| error.to_string())?;
    std::fs::write(out.join("complete-cost-vector.json"), &cost_bytes)
        .map_err(|error| error.to_string())?;

    // A fresh value built only from the detached rest bytes performs two identical conducts and a
    // decode. It receives no workspace path, M2 chart, W1 rest, source item or q-fibre.
    let remounted = GeneratorNativeRest::read(&rest_bytes).map_err(|error| error.to_string())?;
    let start = *remounted
        .native_population
        .first()
        .ok_or_else(|| "the native rest has no state".to_owned())?;
    let word = &deed.apparatus.native_word.word;
    let first_endpoint = remounted
        .conduct_word(start, word)
        .map_err(|error| error.to_string())?;
    let second_endpoint = remounted
        .conduct_word(start, word)
        .map_err(|error| error.to_string())?;
    let first_image = remounted
        .decode(first_endpoint, ReceiverId(0))
        .map_err(|error| error.to_string())?;
    let second_image = remounted
        .decode(second_endpoint, ReceiverId(0))
        .map_err(|error| error.to_string())?;
    let withdrawn_generator = *word
        .first()
        .ok_or_else(|| "the native conduct word is empty".to_owned())?;
    let mut ablated = remounted.clone();
    ablated
        .generators
        .retain(|generator| generator.generator != withdrawn_generator);
    let targeted_withdrawal_refused_the_same_word = ablated.conduct_word(start, word).is_err();
    let remount = RemountReceipt {
        first_endpoint,
        first_receiver_image: first_image,
        repeated_endpoint_identical: first_endpoint == second_endpoint,
        repeated_receiver_image_identical: first_image == second_image,
        source_material_opened_by_decoder: false,
        withdrawn_generator,
        targeted_withdrawal_refused_the_same_word,
    };
    std::fs::write(
        out.join("source-detached-remount.json"),
        serde_json::to_vec(&remount).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;

    let decoder_reopened_complete_declared_image = deed.semantic_work.complete_decoder_factor_reads
        == (deed.history.native_population.len() * 3) as u64;
    let source_detached_remount_held = remount.repeated_endpoint_identical
        && remount.repeated_receiver_image_identical
        && !remount.source_material_opened_by_decoder;
    let swing_lineage_receiver_reopened_word =
        swing.lineage_separator.left_word != swing.lineage_separator.right_word;
    let native_rest_omits_foreign_matrices_and_source_items = rest_bytes
        .windows(b"source_population".len())
        .all(|window| window != b"source_population")
        && rest_bytes
            .windows(b"matrix".len())
            .all(|window| window != b"matrix")
        && rest_bytes
            .windows(b"reconstruction_fibre".len())
            .all(|window| window != b"reconstruction_fibre");
    let passed = deed.history.native_population.len() < deed.history.source_population.len()
        && !deed.history.generators.is_empty()
        && !deed.history.first_separators.is_empty()
        && deed.history.reconstruction_fibres.len() == deed.history.native_population.len()
        && !deed.monoid.relations.is_empty()
        && !recovery.open_domain.unclosed_intervention_pairs.is_empty()
        && deed.apparatus.quotient_launches > 0
        && deed.apparatus.native_word.launches == 1
        && native_rest_omits_foreign_matrices_and_source_items
        && decoder_reopened_complete_declared_image
        && source_detached_remount_held
        && targeted_withdrawal_refused_the_same_word
        && swing.every_generator_is_conjugated_negation
        && swing.every_presented_word_factors_through_its_normal_form
        && swing_lineage_receiver_reopened_word
        && cost.complete_vector_strictly_reduced;
    let grade = Grade {
        schema: "holonics.m3.generator-native-codec-grade.v1".to_owned(),
        truth_status: if passed {
            "established-bounded".to_owned()
        } else {
            "refuted".to_owned()
        },
        source_population: deed.history.source_population.len(),
        native_population: deed.history.native_population.len(),
        quotient_strictly_reduces_population: deed.history.native_population.len()
            < deed.history.source_population.len(),
        generator_squares: deed.history.generators.len(),
        first_separators: deed.history.first_separators.len(),
        complete_reconstruction_fibres: deed.history.reconstruction_fibres.len(),
        transition_monoid_elements: deed.monoid.elements,
        transition_relations: deed.monoid.relations.len(),
        unclosed_intervention_composites_retained: recovery
            .open_domain
            .unclosed_intervention_pairs
            .len(),
        card_quotient_launches: deed.apparatus.quotient_launches,
        card_native_word_launches: deed.apparatus.native_word.launches,
        native_rest_omits_foreign_matrices_and_source_items,
        decoder_reopened_complete_declared_image,
        source_detached_remount_held,
        targeted_withdrawal_refused: targeted_withdrawal_refused_the_same_word,
        swing_conjugated_negation_held: swing.every_generator_is_conjugated_negation,
        swing_word_normalization_held: swing.every_presented_word_factors_through_its_normal_form,
        swing_lineage_receiver_reopened_word,
        complete_cost_vector_strictly_reduced: cost.complete_vector_strictly_reduced,
        passed,
        boundary: evidence.boundary.to_owned(),
    };
    let grade_bytes = serde_json::to_vec(&grade).map_err(|error| error.to_string())?;
    std::fs::write(out.join("grade.json"), &grade_bytes).map_err(|error| error.to_string())?;
    let manifest = format!(
        "M3 GENERATOR-NATIVE CODEC\ntruth-status: {}\nsource-population: {}\nnative-population: {}\nfirst-separators: {}\ntransition-monoid: {} elements, {} returned relations\nnative-rest: {} octets sha256 {}\nevidence: {} octets sha256 {}\nswing: {} octets sha256 {}\ncomplete-vector-strictly-reduced: {}\nsource-detached-remount: {}\ntargeted-withdrawal-refused: {}\nboundary: {}\n",
        grade.truth_status,
        grade.source_population,
        grade.native_population,
        grade.first_separators,
        grade.transition_monoid_elements,
        grade.transition_relations,
        rest_bytes.len(),
        digest(&rest_bytes),
        evidence_bytes.len(),
        digest(&evidence_bytes),
        swing_bytes.len(),
        digest(&swing_bytes),
        grade.complete_cost_vector_strictly_reduced,
        grade.source_detached_remount_held,
        grade.targeted_withdrawal_refused,
        grade.boundary,
    );
    std::fs::write(out.join("grade.form"), manifest.as_bytes())
        .map_err(|error| error.to_string())?;
    println!(
        "M3 {} — {} source states -> {} native states; {} first separators; {} monoid elements; complete vector reduced {}",
        if passed { "PASSED" } else { "REFUTED" },
        grade.source_population,
        grade.native_population,
        grade.first_separators,
        grade.transition_monoid_elements,
        grade.complete_cost_vector_strictly_reduced,
    );
    if passed {
        Ok(())
    } else {
        Err("M3 grade refused the returned generator-native codec".to_owned())
    }
}

fn compare_cost(
    recovery: &Recovery,
    deed: &M3Deed,
    native_artifact_octets: u64,
    native_decoder_octets: u64,
) -> CostComparison {
    let source_work = source_relation_applications(&recovery.source_exact_work);
    let native_work = native_relation_applications(&deed.semantic_work);
    let source_span = recovery.source_exact_work.dependency_span.clone();
    let native_span = BigUint::from(deed.semantic_work.dependency_span as u64);
    let source_transfer = recovery.source_apparatus.host_ingress_octets
        + recovery.source_apparatus.host_egress_octets
        + recovery.source_apparatus.device_copy_octets;
    let native_resident = deed
        .apparatus
        .quotient_resident_octets_peak
        .max(deed.apparatus.native_word.resident_octets);
    let native_transfer = deed.apparatus.quotient_host_ingress_octets
        + deed.apparatus.quotient_host_egress_octets
        + deed.apparatus.native_word.host_ingress_octets
        + deed.apparatus.native_word.host_egress_octets;
    let source = CostSide {
        artifact_octets: recovery.source_octets,
        decoder_octets: recovery.source_decoder_octets,
        caused_relation_applications: source_work.to_string(),
        dependency_span: source_span.to_string(),
        resident_octets_peak: recovery.source_apparatus.resident_octets_peak,
        transfer_octets: source_transfer,
    };
    let native = CostSide {
        artifact_octets: native_artifact_octets,
        decoder_octets: native_decoder_octets,
        caused_relation_applications: native_work.to_string(),
        dependency_span: native_span.to_string(),
        resident_octets_peak: native_resident,
        transfer_octets: native_transfer,
    };
    let comparisons = [
        native.artifact_octets <= source.artifact_octets,
        native.decoder_octets <= source.decoder_octets,
        native_work <= source_work,
        native_span <= source_span,
        native.resident_octets_peak <= source.resident_octets_peak,
        native.transfer_octets <= source.transfer_octets,
    ];
    let strict = native.artifact_octets < source.artifact_octets
        || native.decoder_octets < source.decoder_octets
        || native_work < source_work
        || native_span < source_span
        || native.resident_octets_peak < source.resident_octets_peak
        || native.transfer_octets < source.transfer_octets;
    CostComparison {
        schema: "holonics.m3.complete-compression-vector.v1".to_owned(),
        receiver: "product order over complete semantic artifact, executable declared-image decoder, caused local relation applications, dependency span, peak card residency and exact transfer testimony; no scalar ratio governs admission".to_owned(),
        source,
        native,
        artifact_nonincreasing: comparisons[0],
        decoder_nonincreasing: comparisons[1],
        work_nonincreasing: comparisons[2],
        dependency_span_nonincreasing: comparisons[3],
        residency_nonincreasing: comparisons[4],
        transfer_nonincreasing: comparisons[5],
        at_least_one_strict_reduction: strict,
        complete_vector_strictly_reduced: comparisons.into_iter().all(|held| held) && strict,
    }
}

fn source_relation_applications(work: &holonic_engine::exact_work::ExactWork) -> BigUint {
    &work.additions + &work.multiplications + &work.divisions + &work.entries_written
}

fn native_relation_applications(work: &super::native::NativeSemanticWork) -> BigUint {
    [
        work.quotient_assignments,
        work.receiver_factor_reads,
        work.source_transport_reads,
        work.native_transport_entries,
        work.generator_square_checks,
        work.transition_monoid_cell_reads,
        work.native_word_transport_reads,
        work.complete_decoder_factor_reads,
        work.complete_decoder_fibre_members_returned,
    ]
    .into_iter()
    .map(BigUint::from)
    .fold(BigUint::zero(), |sum, value| sum + value)
}

fn relative(root: &Path, path: &Path) -> Result<String, String> {
    path.strip_prefix(root)
        .map(|path| path.display().to_string())
        .map_err(|_| format!("{} left the workspace", path.display()))
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
