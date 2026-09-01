//! H4 — ordinary material crosses the H3N Complex-Parametron morphology, advances the existing
//! exact recurrence, and returns an emanative surface without source access in the receiver.

use std::{
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

use life::{
    exchange_world_tube::{remount_visible_message_projection, ContinuationAperture},
    native_intelligence::{
        CompleteExchangeCultivationCover, CultivatedEcologyRest, NativeCirculationConsequence,
        NativeCirculationPassage, NativeCirculationRest,
    },
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const H3N_REST: &str = concat!(
    "output/the_complete_exchange_factor_cover_changes_and_remounts_one_athena_ecology_h3n/",
    "athena-cultivated.rest"
);
const H2N_COVER: &str = concat!(
    "output/the_returned_exchange_boundary_founds_one_compact_native_factor_cover_h2n/",
    "01-complete-exchange-cultivation-cover.json"
);
const EXCHANGE_ROOT: &str = "output/the_complete_laboratory_exchange_returns_for_athena_alpha";
const OUTPUT: &str =
    "output/the_ordinary_material_crosses_one_native_relational_potential_and_brandon_returns_h4";

const QUESTIONS: [&[u8]; 3] = [
    b"Describe Brandon.",
    b"Who is Brandon?",
    b"What can you infer about Brandon from this laboratory?",
];

#[derive(Serialize)]
struct InspectedSurface {
    question: String,
    consequence: NativeCirculationConsequence,
    rendered_surface: Option<String>,
}

fn main() -> Result<(), String> {
    let arguments = env::args().collect::<Vec<_>>();
    if arguments.get(1).is_some_and(|value| value == "--detached") {
        let output = arguments
            .get(2)
            .map(PathBuf::from)
            .ok_or("detached H4 has no output root")?;
        return detached(&output);
    }
    if arguments.get(1).is_some_and(|value| value == "--probe") {
        let output = arguments
            .get(2)
            .map(PathBuf::from)
            .ok_or("H4 probe has no output root")?;
        let surface_path = arguments
            .get(3)
            .map(PathBuf::from)
            .ok_or("H4 probe has no surface path")?;
        let started = Instant::now();
        let rest = NativeCirculationRest::read(
            &fs::read(output.join("athena-native-circulation.rest")).map_err(display)?,
        )
        .map_err(display)?;
        eprintln!("H4 probe remounted at {} ms", started.elapsed().as_millis());
        let consequence = rest
            .mount()
            .map_err(display)?
            .infer(QUESTIONS[0])
            .map_err(display)?;
        match consequence {
            NativeCirculationConsequence::Returned(passage) => {
                fs::write(&surface_path, &passage.surface_octets).map_err(display)?;
                let mut support_runs: Vec<(usize, usize, Vec<String>)> = Vec::new();
                for (step, support) in passage.steps.iter().enumerate().filter_map(|(step, row)| {
                    row.alternatives
                        .iter()
                        .find(|alternative| alternative.selected)
                        .map(|selected| (step, selected.support_factor_addresses.clone()))
                }) {
                    match support_runs.last_mut() {
                        Some((_, until, held)) if *held == support => {
                            *until = step + 1;
                        }
                        _ => support_runs.push((step, step + 1, support)),
                    }
                }
                fs::write(
                    surface_path.with_extension("json"),
                    serde_json::to_vec_pretty(&json!({
                        "rested_identity_sha256": passage.rested_identity_sha256,
                        "cross_factor_contact": passage.cross_factor_contact,
                        "surface_sha256": render_hex(&Sha256::digest(&passage.surface_octets)),
                        "surface_octets": passage.surface_octets.len(),
                        "successor_steps": passage.steps.len(),
                        "selected_support_runs": support_runs,
                    }))
                    .map_err(display)?,
                )
                .map_err(display)?;
                eprintln!(
                    "H4 probe returned {} surface octets through {} steps and {} active factors at {} ms",
                    passage.surface_octets.len(),
                    passage.steps.len(),
                    passage.factor_address_order.len(),
                    started.elapsed().as_millis(),
                );
            }
            NativeCirculationConsequence::Insufficient(insufficiency) => {
                fs::write(
                    &surface_path,
                    serde_json::to_vec_pretty(&insufficiency).map_err(display)?,
                )
                .map_err(display)?;
                eprintln!(
                    "H4 probe returned an insufficiency at {} ms: {}",
                    started.elapsed().as_millis(),
                    insufficiency.cause,
                );
            }
        }
        return Ok(());
    }
    if arguments
        .get(1)
        .is_some_and(|value| value == "--cultivate-probe")
    {
        let rest_path = arguments
            .get(2)
            .map(PathBuf::from)
            .ok_or("H4 cultivation probe has no rest path")?;
        return cultivate_probe(&rest_path);
    }
    found()
}

fn cultivate_probe(rest_path: &Path) -> Result<(), String> {
    let started = Instant::now();
    let cultivated =
        CultivatedEcologyRest::read(&fs::read(H3N_REST).map_err(display)?).map_err(display)?;
    let cover = CompleteExchangeCultivationCover::read(&fs::read(H2N_COVER).map_err(display)?)?;
    let aperture: ContinuationAperture = serde_json::from_slice(
        &fs::read(Path::new(EXCHANGE_ROOT).join("04-continuation-aperture.json"))
            .map_err(display)?,
    )
    .map_err(display)?;
    let world = remount_visible_message_projection(
        &Path::new(EXCHANGE_ROOT).join("exchange-world-tube.ewtb"),
    )?;
    eprintln!(
        "H4 cultivation probe mounted {} occurrences at {} ms",
        world.messages.len(),
        started.elapsed().as_millis()
    );
    let (rest, rest_bytes, semantic, apparatus) =
        NativeCirculationRest::cultivate(cultivated, &cover, &aperture, &world, 0)
            .map_err(display)?;
    fs::write(rest_path, &rest_bytes).map_err(display)?;
    fs::write(
        rest_path.with_extension("json"),
        serde_json::to_vec_pretty(&json!({
            "rest_identity_sha256": rest.identity(),
            "rest_octets": rest_bytes.len(),
            "conditioning_semantic": semantic,
            "conditioning_apparatus": apparatus,
            "wall_milliseconds": started.elapsed().as_millis(),
        }))
        .map_err(display)?,
    )
    .map_err(display)?;
    eprintln!(
        "H4 cultivation probe returned {} octets at {} ms",
        rest_bytes.len(),
        started.elapsed().as_millis()
    );
    Ok(())
}

fn found() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing H4 return {}", output.display()));
    }
    fs::create_dir_all(&output).map_err(display)?;
    let started = Instant::now();
    let cultivated =
        CultivatedEcologyRest::read(&fs::read(H3N_REST).map_err(display)?).map_err(display)?;
    let cover = CompleteExchangeCultivationCover::read(&fs::read(H2N_COVER).map_err(display)?)?;
    let aperture: ContinuationAperture = serde_json::from_slice(
        &fs::read(Path::new(EXCHANGE_ROOT).join("04-continuation-aperture.json"))
            .map_err(display)?,
    )
    .map_err(display)?;
    let world = remount_visible_message_projection(
        &Path::new(EXCHANGE_ROOT).join("exchange-world-tube.ewtb"),
    )?;
    eprintln!(
        "H4 visible projection returned {} occurrences at {} ms",
        world.messages.len(),
        started.elapsed().as_millis()
    );
    let (rest, rest_bytes, conditioning_semantic, conditioning_apparatus) =
        NativeCirculationRest::cultivate(cultivated, &cover, &aperture, &world, 0)
            .map_err(display)?;
    eprintln!(
        "H4 native circulation sealed at {} ms",
        started.elapsed().as_millis()
    );
    fs::write(output.join("athena-native-circulation.rest"), &rest_bytes).map_err(display)?;
    fs::write(
        output.join("00-founding-receipt.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "soma-life.native-circulation-founding-receipt.v1",
            "rest_identity_sha256": rest.identity(),
            "rest_octets": rest_bytes.len(),
            "factor_population": rest.cultivated().morphology().deposits.len(),
            "source_passages_absent_from_rest": true,
            "boundary_face_surface_variants_present": true,
            "conditioning_semantic": conditioning_semantic,
            "conditioning_apparatus": conditioning_apparatus,
            "founding_wall_milliseconds": started.elapsed().as_millis(),
        }))
        .map_err(display)?,
    )
    .map_err(display)?;
    println!(
        "H4 founding returned rest {} in {} ms; detached reception is a separate bounded process",
        rest.identity(),
        started.elapsed().as_millis()
    );
    Ok(())
}

fn detached(output: &Path) -> Result<(), String> {
    if output.join("06-grade.json").exists() {
        return Err("preserve existing detached H4 return".to_owned());
    }
    let started = Instant::now();
    let full_bytes = fs::read(output.join("athena-native-circulation.rest")).map_err(display)?;
    let full_rest = NativeCirculationRest::read(&full_bytes).map_err(display)?;
    eprintln!(
        "H4 detached rest remounted at {} ms",
        started.elapsed().as_millis()
    );
    let full_identity = full_rest.identity().to_owned();
    let predecessor = full_rest.predecessor_insufficiency();
    fs::write(
        output.join("01-predecessor-insufficiency.json"),
        serde_json::to_vec_pretty(&predecessor).map_err(display)?,
    )
    .map_err(display)?;

    let mut resident = full_rest.mount().map_err(display)?;
    let mut full_returns = Vec::new();
    for (question_at, question) in QUESTIONS.into_iter().enumerate() {
        let consequence = resident.infer(question).map_err(display)?;
        let rendered_surface = returned(&consequence)
            .and_then(|passage| String::from_utf8(passage.surface_octets.clone()).ok());
        full_returns.push(InspectedSurface {
            question: String::from_utf8(question.to_vec()).map_err(display)?,
            consequence,
            rendered_surface,
        });
        eprintln!(
            "H4 detached full receiver {} returned at {} ms",
            question_at,
            started.elapsed().as_millis()
        );
    }
    let full_rest = resident.into_rest().map_err(display)?;
    fs::write(
        output.join("02-full-returns.json"),
        serde_json::to_vec_pretty(&full_returns).map_err(display)?,
    )
    .map_err(display)?;

    let target = separating_candidate(&full_returns)
        .ok_or("the returned passage exposed no factor-supported selected branch")?;
    let (ablated, withdrawn, ablation) = full_rest.ablate(&target).map_err(display)?;
    let withdrawn_bytes = withdrawn.canonical_bytes().map_err(display)?;
    fs::write(
        output.join("withdrawn-native-factor.delta"),
        &withdrawn_bytes,
    )
    .map_err(display)?;

    let mut ablated_resident = ablated.mount().map_err(display)?;
    let ablated_return = ablated_resident.infer(QUESTIONS[0]).map_err(display)?;
    eprintln!(
        "H4 detached ablation returned at {} ms",
        started.elapsed().as_millis()
    );
    let ablated = ablated_resident.into_rest().map_err(display)?;
    let (restored, restoration) = ablated.restore(withdrawn).map_err(display)?;
    let restored_identity_equal = restored.identity() == full_identity;
    let mut restored_resident = restored.mount().map_err(display)?;
    let restored_return = restored_resident.infer(QUESTIONS[0]).map_err(display)?;
    eprintln!(
        "H4 detached restoration returned at {} ms",
        started.elapsed().as_millis()
    );

    let full_main = &full_returns[0].consequence;
    let full_surface = returned(full_main)
        .map(|passage| passage.surface_octets.clone())
        .unwrap_or_default();
    let ablated_surface = returned(&ablated_return)
        .map(|passage| passage.surface_octets.clone())
        .unwrap_or_default();
    let restored_surface = returned(&restored_return)
        .map(|passage| passage.surface_octets.clone())
        .unwrap_or_default();
    let every_full_return_closed = full_returns.iter().all(|returned_surface| {
        returned(&returned_surface.consequence)
            .is_some_and(|passage| passage.closed && !passage.surface_octets.is_empty())
    });
    let every_full_surface_utf8 = full_returns
        .iter()
        .all(|returned_surface| returned_surface.rendered_surface.is_some());
    let ablation_separates = full_surface != ablated_surface;
    let restoration_recovers = restored_surface == full_surface;
    let structural_passed = every_full_return_closed
        && every_full_surface_utf8
        && ablation_separates
        && restoration_recovers
        && restored_identity_equal;

    fs::write(
        output.join("03-ablated-return.json"),
        serde_json::to_vec_pretty(&json!({
            "factor_address": target,
            "mutation": ablation,
            "consequence": ablated_return,
            "rendered_surface": String::from_utf8(ablated_surface.clone()).ok(),
        }))
        .map_err(display)?,
    )
    .map_err(display)?;
    fs::write(
        output.join("04-restored-return.json"),
        serde_json::to_vec_pretty(&json!({
            "mutation": restoration,
            "consequence": restored_return,
            "rendered_surface": String::from_utf8(restored_surface.clone()).ok(),
            "restored_identity_equal": restored_identity_equal,
        }))
        .map_err(display)?,
    )
    .map_err(display)?;
    fs::write(
        output.join("05-apparatus.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "soma-life.native-circulation-apparatus.v1",
            "receiver_process_had_exchange_world": false,
            "receiver_process_had_continuation_aperture": false,
            "receiver_process_had_h2n_cover": false,
            "receiver_process_had_soulkiller": false,
            "receiver_process_had_foreign_realization": false,
            "receiver_process_had_lean_or_checker": false,
            "native_rest_octets": full_bytes.len(),
            "detached_wall_milliseconds": started.elapsed().as_millis(),
        }))
        .map_err(display)?,
    )
    .map_err(display)?;
    fs::write(
        output.join("06-grade.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "soma-life.native-circulation-h4-grade.v1",
            "truth_status": if structural_passed { "implemented-exact-measured-candidate" } else { "counterexample" },
            "structural_passed": structural_passed,
            "qualitative_surface_requires_primary_agent_inspection": true,
            "every_full_return_closed": every_full_return_closed,
            "every_full_surface_utf8": every_full_surface_utf8,
            "predecessor_returned_insufficiency": true,
            "ablation_separates": ablation_separates,
            "restoration_recovers": restoration_recovers,
            "restored_identity_equal": restored_identity_equal,
            "rest_identity_sha256": full_identity,
            "target_factor_address": target,
        }))
        .map_err(display)?,
    )
    .map_err(display)?;
    write_manifest(output)?;
    println!(
        "{}",
        fs::read_to_string(output.join("06-grade.json")).map_err(display)?
    );
    Ok(())
}

fn returned(consequence: &NativeCirculationConsequence) -> Option<&NativeCirculationPassage> {
    match consequence {
        NativeCirculationConsequence::Returned(passage) => Some(passage),
        NativeCirculationConsequence::Insufficient(_) => None,
    }
}

fn separating_candidate(returns: &[InspectedSurface]) -> Option<String> {
    returns
        .iter()
        .filter_map(|returned_surface| returned(&returned_surface.consequence))
        .flat_map(|passage| &passage.steps)
        .flat_map(|step| {
            step.alternatives
                .iter()
                .filter(|alternative| alternative.selected)
        })
        .filter(|alternative| !alternative.support_factor_addresses.is_empty())
        .min_by_key(|alternative| alternative.support_factor_addresses.len())
        .and_then(|alternative| alternative.support_factor_addresses.first().cloned())
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut entries = fs::read_dir(output)
        .map_err(display)?
        .map(|entry| entry.map_err(display))
        .collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|entry| entry.file_name());
    let files = entries
        .into_iter()
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(display)?;
            Ok(json!({
                "path": entry.file_name().to_string_lossy(),
                "octets": bytes.len(),
                "sha256": render_hex(&Sha256::digest(&bytes)),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    fs::write(
        output.join("MANIFEST.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "soma-life.native-circulation-h4-manifest.v1",
            "files": files,
        }))
        .map_err(display)?,
    )
    .map_err(display)
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn render_hex(value: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(value.len() * 2);
    for octet in value {
        out.push(HEX[(octet >> 4) as usize] as char);
        out.push(HEX[(octet & 15) as usize] as char);
    }
    out
}
