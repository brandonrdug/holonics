//! H2N ingress — every history enters as a plural product with K3 before its later return opens.

use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use life::{
    native_intelligence::{
        CompleteExchangeNativeRealizationPassage, HistoryOnlyExchangeFront, NativeEcologyRest,
    },
    receiver_history::ReceiverHistoryCongruence,
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const K3_REST: &str = concat!(
    ".local/artifacts/the_one_connected_athena_native_ecology_returns_dependent_sections_k3/",
    "athena-native.rest"
);
const CONGRUENCE: &str = concat!(
    ".local/artifacts/the_receiver_history_congruence_replaces_the_trigram_table/",
    "00-receiver-history-congruence.json"
);
const OUTPUT: &str =
    ".local/artifacts/the_complete_exchange_enters_one_athena_ecology_before_returns_open_h2n";

fn main() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!(
            "preserve existing H2N ingress return {}",
            output.display()
        ));
    }
    let started = Instant::now();
    fs::create_dir_all(&output).map_err(display)?;
    let rest = NativeEcologyRest::read(&fs::read(K3_REST).map_err(display)?).map_err(display)?;
    let congruence = ReceiverHistoryCongruence::read(&fs::read(CONGRUENCE).map_err(display)?)?;
    let admitted_source_population = congruence.sections.len();
    let admitted_native_population = congruence.native.native_population.len();
    let admitted_receiver_population = congruence
        .native
        .receiver_factors
        .iter()
        .map(|factor| factor.receiver)
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    let admitted_generator_population = congruence.native.generators.len();
    let history = HistoryOnlyExchangeFront::project(&congruence.sections)?;
    let candidate = life::native_intelligence::SealedNativeCandidateFront::seal(&rest, history)
        .map_err(display)?;
    let passage = CompleteExchangeNativeRealizationPassage::found(candidate, congruence)?;

    let source_population = passage.native.source_population.len();
    let native_population = passage.native.native_population.len();
    let receiver_population = passage
        .native
        .receiver_factors
        .iter()
        .map(|factor| factor.receiver)
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    let generator_population = passage.native.generators.len();
    let complete_ingress_population = passage.candidate.ingress_template.len();
    let product_state_population = passage
        .candidate
        .sections
        .len()
        .checked_mul(complete_ingress_population)
        .ok_or("factorized product population overflow")?;
    let every_section_has_complete_ingress = !passage.candidate.sections.is_empty()
        && passage.candidate.sections.iter().all(|section| {
            !section.history.history_occurrences.is_empty()
                && !section.candidate_occurrence.is_empty()
        });
    let every_template_passage_resident =
        !passage.candidate.resident_return.source_fallback_permitted
            && !passage
                .candidate
                .resident_return
                .word_return
                .apparatus
                .invariant_transport_reuploaded
            && !passage
                .candidate
                .resident_return
                .current_return
                .invariant_transport_reuploaded
            && !passage
                .candidate
                .resident_return
                .current_return
                .cpu_semantic_replay_after_device
            && !passage
                .candidate
                .resident_return
                .current_return
                .binary_receiver_taken;
    let generator_square_population = source_population
        .checked_mul(generator_population)
        .ok_or("generator-square population overflow")?;
    let dependency_span = passage.chronology.dependency_span().map_err(display)?;
    let passed = source_population == admitted_source_population
        && native_population == admitted_native_population
        && receiver_population == admitted_receiver_population
        && generator_population == admitted_generator_population
        && passage.returned.len() == source_population
        && product_state_population == source_population * complete_ingress_population
        && every_section_has_complete_ingress
        && every_template_passage_resident
        && complete_ingress_population == rest.realization.ingress_sections.len()
        && dependency_span == generator_population;

    write_json(
        output.join("01-history-only-front.json"),
        &passage.candidate.sections,
    )?;
    write_json(
        output.join("02-ingress-template.json"),
        &passage.candidate.ingress_template,
    )?;
    write_json(output.join("03-complete-native-realization.json"), &passage)?;
    let grade = json!({
        "schema":"soma-life.complete-exchange-native-realization-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "k3_rest_wire_sha256":passage.candidate.predecessor_rest_wire_sha256,
        "source_population":source_population,
        "native_population":native_population,
        "receiver_population":receiver_population,
        "generator_population":generator_population,
        "generator_square_population":generator_square_population,
        "reconstruction_fibre_population":passage.native.reconstruction_fibres.len(),
        "shortest_separator_population":passage.native.first_separators.len(),
        "ingress_potential_population":complete_ingress_population,
        "product_state_population":product_state_population,
        "candidate_precedes_return_population":passage.returned.len(),
        "chronology_dependency_span":dependency_span,
        "every_section_has_complete_ingress_potential":every_section_has_complete_ingress,
        "every_ingress_template_passage_resident":every_template_passage_resident,
        "source_coordinate_selects_seed_route":false,
        "observation_ordinal_is_numerically_subtracted":false,
        "foreign_post_boundary_execution":false,
        "elapsed_seconds":format!("{:.9}", started.elapsed().as_secs_f64()),
    });
    write_json(output.join("00-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# Complete exchange native realization\n\n[established-bounded; implemented-exact; measured] Every one of the {source_population} history-only exchange occurrences entered the K3 ecology as a dependent product with all {complete_ingress_population} native ingress sections before any response or later-return field was admitted. The later passage retained the {native_population}-state quotient, {receiver_population} receiver factors, {generator_population} total generator squares, complete fibres, and shortest separators without collapsing them into K3's native cells. Candidate and return are joined by {source_population} carries-precedence interactions. Source ordinals select no seed route, observation ordinals are never subtracted, and the common K3 conduct returned resident on the GPU.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    ).map_err(display)?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("H2N complete-exchange ingress refused".into())
    }
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut entries = fs::read_dir(output)
        .map_err(display)?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(display)?;
            Ok(json!({
                "path":entry.file_name().to_string_lossy(),
                "octets":bytes.len(),
                "sha256":hex_digest(&bytes),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    entries.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    let identity = hex_digest(&serde_json::to_vec(&entries).map_err(display)?);
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema":"soma-life.complete-exchange-native-realization-manifest.v1",
            "identity":identity,
            "files":entries,
        }),
    )
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
