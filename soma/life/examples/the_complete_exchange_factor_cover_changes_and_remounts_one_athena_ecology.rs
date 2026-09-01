//! H3N — deposit the H2N factors into one native Complex-Parametron current and prove actual
//! change, move-owned ablation, token-consuming restoration, detached remount, and preservation
//! away from the factor support.

use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use life::native_intelligence::{
    CompleteExchangeCultivationCover, CultivatedConductConsequence, CultivatedConductPassage,
    CultivatedEcologyRest, NativeConductConsequence, NativeCultivatedPotentialCoordinate,
    NativeEcologyRest, WithdrawnNativeFactor,
};
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const K3_REST: &str = concat!(
    "output/the_one_connected_athena_native_ecology_returns_dependent_sections_k3/",
    "athena-native.rest"
);
const H2N_COVER: &str = concat!(
    "output/the_returned_exchange_boundary_founds_one_compact_native_factor_cover_h2n/",
    "01-complete-exchange-cultivation-cover.json"
);
const OUTPUT: &str =
    "output/the_complete_exchange_factor_cover_changes_and_remounts_one_athena_ecology_h3n";

fn main() -> Result<(), String> {
    let arguments = env::args().collect::<Vec<_>>();
    if arguments
        .get(1)
        .is_some_and(|argument| argument == "--detached")
    {
        let output = arguments
            .get(2)
            .map(PathBuf::from)
            .ok_or("detached H3N has no output root")?;
        return detached(&output);
    }
    found()
}

fn found() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing H3N return {}", output.display()));
    }
    fs::create_dir_all(&output).map_err(display)?;
    let predecessor =
        NativeEcologyRest::read(&fs::read(K3_REST).map_err(display)?).map_err(display)?;
    let cover = CompleteExchangeCultivationCover::read(&fs::read(H2N_COVER).map_err(display)?)?;
    let cultivated = CultivatedEcologyRest::cultivate(predecessor, cover).map_err(display)?;
    let rest_bytes = cultivated.canonical_bytes().map_err(display)?;
    fs::write(output.join("athena-cultivated.rest"), &rest_bytes).map_err(display)?;
    drop(cultivated);

    // The source-addressed H2N cover and predecessor construction are absent from the child
    // process. Its only ingress is the sealed native rest path and its only output is this root.
    let executable = env::current_exe().map_err(display)?;
    let status = Command::new(executable)
        .arg("--detached")
        .arg(fs::canonicalize(&output).map_err(display)?)
        .status()
        .map_err(display)?;
    if !status.success() {
        return Err(format!("detached H3N returned {status}"));
    }
    write_manifest(&output)?;
    let grade = fs::read_to_string(output.join("00-grade.json")).map_err(display)?;
    println!("{grade}");
    Ok(())
}

fn detached(output: &Path) -> Result<(), String> {
    if output.join("00-grade.json").exists() {
        return Err("preserve existing detached H3N return".to_owned());
    }
    let started = Instant::now();
    let full_rest_bytes = fs::read(output.join("athena-cultivated.rest")).map_err(display)?;
    let full_rest = CultivatedEcologyRest::read(&full_rest_bytes).map_err(display)?;
    let full_identity = full_rest.identity().to_owned();
    let ingress = full_rest
        .predecessor()
        .realization
        .ingress_sections
        .first()
        .cloned()
        .ok_or("K3 has no native ingress")?;
    let unrelated = full_rest
        .predecessor()
        .realization
        .sections
        .iter()
        .find(|section| {
            !full_rest
                .predecessor()
                .realization
                .ingress_sections
                .contains(section)
        })
        .cloned()
        .ok_or("K3 has no support-disjoint section")?;
    let receiver = *full_rest
        .predecessor()
        .realization
        .receiver_family
        .iter()
        .next()
        .ok_or("K3 has no native receiver")?;
    let target = full_rest
        .morphology()
        .deposits
        .first()
        .map(|deposit| deposit.address.clone())
        .ok_or("cultivation has no factor")?;
    let predecessor_ingress = returned(
        full_rest
            .predecessor()
            .conduct(&ingress, receiver)
            .map_err(display)?,
    )?;
    let predecessor_unrelated = returned(
        full_rest
            .predecessor()
            .conduct(&unrelated, receiver)
            .map_err(display)?,
    )?;

    let mut full_resident = full_rest.mount().map_err(display)?;
    let full_ingress =
        cultivated_return(full_resident.conduct(&ingress, receiver).map_err(display)?)?;
    let full_unrelated = cultivated_return(
        full_resident
            .conduct(&unrelated, receiver)
            .map_err(display)?,
    )?;
    let full_rest = full_resident.into_rest();

    let (ablated, withdrawn, ablation) = full_rest.ablate(&target).map_err(display)?;
    let ablated_rest_bytes = ablated.canonical_bytes().map_err(display)?;
    let withdrawn_bytes = withdrawn.canonical_bytes().map_err(display)?;
    fs::write(
        output.join("athena-factor-ablated.rest"),
        &ablated_rest_bytes,
    )
    .map_err(display)?;
    fs::write(
        output.join("withdrawn-native-factor.delta"),
        &withdrawn_bytes,
    )
    .map_err(display)?;
    drop(ablated);
    drop(withdrawn);

    let mut ablated_resident = CultivatedEcologyRest::read(&ablated_rest_bytes)
        .map_err(display)?
        .mount()
        .map_err(display)?;
    let ablated_ingress = cultivated_return(
        ablated_resident
            .conduct(&ingress, receiver)
            .map_err(display)?,
    )?;
    let ablated_unrelated = cultivated_return(
        ablated_resident
            .conduct(&unrelated, receiver)
            .map_err(display)?,
    )?;
    let ablated = ablated_resident.into_rest();
    let withdrawn = WithdrawnNativeFactor::read(&withdrawn_bytes).map_err(display)?;
    let token_address_equal = withdrawn.deposit_address() == target;
    let (restored, restoration) = ablated.restore(withdrawn).map_err(display)?;
    let restored_identity_equal = restored.identity() == full_identity;
    let restored_rest_bytes = restored.canonical_bytes().map_err(display)?;
    let restored_bytes_equal = restored_rest_bytes == full_rest_bytes;
    fs::write(
        output.join("athena-factor-restored.rest"),
        &restored_rest_bytes,
    )
    .map_err(display)?;
    let mut restored_resident = CultivatedEcologyRest::read(&restored_rest_bytes)
        .map_err(display)?
        .mount()
        .map_err(display)?;
    let restored_ingress = cultivated_return(
        restored_resident
            .conduct(&ingress, receiver)
            .map_err(display)?,
    )?;
    let restored_unrelated = cultivated_return(
        restored_resident
            .conduct(&unrelated, receiver)
            .map_err(display)?,
    )?;

    let full_coordinates = coordinate_map(&full_ingress)?;
    let ablated_coordinates = coordinate_map(&ablated_ingress)?;
    let restored_coordinates = coordinate_map(&restored_ingress)?;
    let exact_target_withdrawal = full_coordinates.contains_key(target.as_str())
        && !ablated_coordinates.contains_key(target.as_str())
        && restored_coordinates.get(target.as_str()) == full_coordinates.get(target.as_str())
        && full_coordinates
            .iter()
            .filter(|(address, _)| **address != target)
            .all(|(address, coordinate)| ablated_coordinates.get(*address) == Some(coordinate))
        && full_coordinates == restored_coordinates;
    let changed_later_native_conduct = full_ingress.potential_complex.changed_on_this_section
        && full_ingress
            .potential_complex
            .coordinates
            .iter()
            .any(|coordinate| !coordinate.response.is_zero());
    let exact_complex_response_not_census =
        full_ingress
            .potential_complex
            .coordinates
            .iter()
            .all(|coordinate| {
                !coordinate.returned_limbs.is_empty()
                    && coordinate.candidate_coefficient.numer() != &0.into()
            });
    let unrelated_standing_preserved = [&full_unrelated, &ablated_unrelated, &restored_unrelated]
        .into_iter()
        .all(|passage| {
            !passage.potential_complex.changed_on_this_section
                && passage
                    .potential_complex
                    .coordinates
                    .iter()
                    .all(|coordinate| coordinate.response.is_zero())
                && passage.predecessor.section == predecessor_unrelated.section
                && passage.predecessor.word_return == predecessor_unrelated.word_return
                && passage.predecessor.current_return == predecessor_unrelated.current_return
        });
    let predecessor_summand_preserved = full_ingress.predecessor.section
        == predecessor_ingress.section
        && full_ingress.predecessor.word_return == predecessor_ingress.word_return
        && full_ingress.predecessor.current_return == predecessor_ingress.current_return;
    let every_hot_passage_resident = [
        &full_ingress,
        &full_unrelated,
        &ablated_ingress,
        &ablated_unrelated,
        &restored_ingress,
        &restored_unrelated,
    ]
    .into_iter()
    .all(resident_exact);
    let no_source_surface_in_rest = [
        "source_columns",
        "candidate_event",
        "return_event",
        "candidate_seal_sha256",
        "parent_defect",
        "support_columns",
        "response_occurrences",
        "response_text",
        "history_text",
        "soulkiller",
        "phoenix",
        "foreign_executor",
        "gemma",
    ]
    .iter()
    .all(|needle| !find_ascii_case_insensitive(&full_rest_bytes, needle.as_bytes()));
    let passed = full_coordinates.len() == 2_224
        && ablated_coordinates.len() + 1 == full_coordinates.len()
        && restored_coordinates.len() == full_coordinates.len()
        && changed_later_native_conduct
        && exact_complex_response_not_census
        && exact_target_withdrawal
        && token_address_equal
        && ablation.forward_then_inverse_zero
        && ablation.inverse_then_forward_zero
        && restoration.forward_then_inverse_zero
        && restoration.inverse_then_forward_zero
        && restored_identity_equal
        && restored_bytes_equal
        && predecessor_summand_preserved
        && unrelated_standing_preserved
        && every_hot_passage_resident
        && no_source_surface_in_rest;

    let controls = json!({
        "schema":"soma-life.athena-native-complex-cultivation-controls.v2",
        "cultivated_identity_sha256":full_identity,
        "cultivated_rest_octets":full_rest_bytes.len(),
        "target_factor_address":target,
        "withdrawn_delta_octets":withdrawn_bytes.len(),
        "ablation":ablation,
        "restoration":restoration,
        "ingress":ingress,
        "receiver":receiver,
        "support_disjoint_section":unrelated,
        "predecessor_summand_preserved":predecessor_summand_preserved,
        "unrelated_standing_preserved":unrelated_standing_preserved,
        "source_addressed_reconstruction_available_after_remount":!no_source_surface_in_rest,
    });
    write_json(output.join("01-cultivation-controls.json"), &controls)?;
    write_json(output.join("02-full-ingress-return.json"), &full_ingress)?;
    write_json(
        output.join("03-ablated-ingress-return.json"),
        &ablated_ingress,
    )?;
    write_json(
        output.join("04-restored-ingress-return.json"),
        &restored_ingress,
    )?;
    write_json(
        output.join("05-full-unrelated-return.json"),
        &full_unrelated,
    )?;
    write_json(
        output.join("06-ablated-unrelated-return.json"),
        &ablated_unrelated,
    )?;
    write_json(
        output.join("07-restored-unrelated-return.json"),
        &restored_unrelated,
    )?;
    let grade = json!({
        "schema":"soma-life.athena-native-complex-cultivation-grade.v2",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "fresh_process_remount":true,
        "full_native_factor_coordinates":full_coordinates.len(),
        "ablated_native_factor_coordinates":ablated_coordinates.len(),
        "restored_native_factor_coordinates":restored_coordinates.len(),
        "changed_later_native_conduct":changed_later_native_conduct,
        "exact_complex_response_not_census":exact_complex_response_not_census,
        "exact_move_owned_target_withdrawal":exact_target_withdrawal && token_address_equal,
        "restoration_recovered_full_identity":restored_identity_equal,
        "restoration_recovered_full_wire":restored_bytes_equal,
        "unrelated_standing_preserved":unrelated_standing_preserved,
        "source_addressed_reconstruction_available_after_remount":!no_source_surface_in_rest,
        "every_hot_passage_resident":every_hot_passage_resident,
        "elapsed_seconds":format!("{:.9}", started.elapsed().as_secs_f64()),
    });
    write_json(output.join("00-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# Same-owner Athena Complex-Parametron cultivation\n\n[established-bounded; implemented-exact; measured] The H2N factors descended once into source-neutral native morphology and the exchange cover then left the hot closure. In a fresh process, the addressed emitting current crossed all {} resident factor branches as an exact complex section. A move-owned inverse removed one complete coordinate; consuming that token restored the exact rest identity and wire. The support-disjoint native occurrence crossed the same resident law and returned zero cultivated current in all siblings.\n\n```json\n{}\n```\n",
            full_coordinates.len(),
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    if passed {
        Ok(())
    } else {
        Err("H3N exact native cultivation refused".to_owned())
    }
}

fn coordinate_map<'a>(
    passage: &'a CultivatedConductPassage,
) -> Result<BTreeMap<&'a str, &'a NativeCultivatedPotentialCoordinate>, String> {
    let map = passage
        .potential_complex
        .coordinates
        .iter()
        .map(|coordinate| (coordinate.deposit_address.as_str(), coordinate))
        .collect::<BTreeMap<_, _>>();
    if map.len() != passage.potential_complex.coordinates.len() {
        return Err("cultivated return duplicated a factor address".to_owned());
    }
    Ok(map)
}

fn resident_exact(passage: &CultivatedConductPassage) -> bool {
    passage.resident_return.device.contains("NVIDIA")
        && passage.resident_return.launches == 1
        && passage.resident_return.synchronizations == 1
        && !passage.resident_return.invariant_transport_reuploaded
        && !passage.resident_return.cpu_semantic_replay_after_device
        && !passage.resident_return.binary_receiver_taken
        && !passage.predecessor.source_fallback_permitted
        && !passage
            .predecessor
            .word_return
            .apparatus
            .invariant_transport_reuploaded
        && !passage
            .predecessor
            .current_return
            .invariant_transport_reuploaded
        && !passage
            .predecessor
            .current_return
            .cpu_semantic_replay_after_device
}

fn returned(
    consequence: NativeConductConsequence,
) -> Result<life::native_intelligence::NativeConductPassage, String> {
    match consequence {
        NativeConductConsequence::Returned(passage) => Ok(passage),
        NativeConductConsequence::Insufficient(insufficiency) => {
            Err(format!("native control returned {insufficiency:?}"))
        }
    }
}

fn cultivated_return(
    consequence: CultivatedConductConsequence,
) -> Result<CultivatedConductPassage, String> {
    match consequence {
        CultivatedConductConsequence::Returned(passage) => Ok(passage),
        CultivatedConductConsequence::Insufficient(insufficiency) => {
            Err(format!("cultivated control returned {insufficiency:?}"))
        }
    }
}

fn find_ascii_case_insensitive(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.windows(needle.len()).any(|window| {
        window
            .iter()
            .zip(needle)
            .all(|(left, right)| left.eq_ignore_ascii_case(right))
    })
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
        .collect::<Result<Vec<Value>, String>>()?;
    entries.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    let identity = hex_digest(&serde_json::to_vec(&entries).map_err(display)?);
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema":"soma-life.athena-native-complex-cultivation-manifest.v2",
            "identity":identity,
            "files":entries,
        }),
    )
}

fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
