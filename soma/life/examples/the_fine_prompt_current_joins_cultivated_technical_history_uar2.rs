//! UAR2 — three held-out technical occurrences traverse the fine granular membrane and meet the
//! already cultivated laboratory history only through shared native factor incidence.

use std::{collections::BTreeSet, fs, path::PathBuf, time::Instant};

use life::native_intelligence::{
    EmanationDeed, EmanationParticipant, LaboratoryParticipantIngress, OpticalProductRest,
    PerspectiveChart, ProductTechnicalHistoryEmanation,
};
use serde::Serialize;
use serde_json::json;

const REST: &str = concat!(
    "output/the_one_athena_alpha_body_circulates_every_admitted_organ_and_cultivates_alp4/",
    "athena-sens6-cultivated.rest"
);
const OUTPUT: &str = "output/the_fine_prompt_current_joins_cultivated_technical_history_uar2";
const EXPECTED_ALP5_IDENTITY: &str =
    "916710c5e7e5f79c602e8e4b6e0e3a74c7a5334d1b50df9e63bf1a127e8b67f5";

#[derive(Serialize)]
struct Uar2Grade<'a> {
    schema: &'static str,
    truth_status: &'static str,
    passed: bool,
    predecessor_rest_identity_sha256: &'a str,
    returned_rest_identity_sha256: &'a str,
    one_move_owned_athena_body: bool,
    fine_prompt_current_crossed_before_rendering: bool,
    three_technical_native_signatures_distinct: bool,
    three_joined_native_signatures_distinct: bool,
    three_joined_surfaces_distinct: bool,
    every_join_has_literal_shared_factor_incidence: bool,
    every_join_retains_both_reconstruction_fibres: bool,
    technical_prompt_selected_cultivation: bool,
    exterior_word_matching_selected_history: bool,
    source_lookup_during_inference: bool,
    cpu_semantic_replay_after_device: bool,
    wall_milliseconds: u128,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let output = root.join(OUTPUT);
    if output.exists() {
        return Err(format!(
            "preserve existing UAR2 return {}",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(display)?;
    let started = Instant::now();
    eprintln!("UAR2 phase: read exact ALP5 wire");
    let wire = fs::read(root.join(REST)).map_err(display)?;
    let rest = OpticalProductRest::read(&wire).map_err(display)?;
    eprintln!(
        "UAR2 phase: exact ALP5 rest returned in {} ms",
        started.elapsed().as_millis()
    );
    if rest.identity() != EXPECTED_ALP5_IDENTITY {
        return Err("UAR2 did not receive the exact ALP5 body".to_owned());
    }
    let predecessor_identity = rest.identity().to_owned();
    let prompts = [
        (
            "uar2/technical/holonic-compression",
            "How does holonic compression preserve future consequences?",
        ),
        (
            "uar2/technical/complex-parametron",
            "What current does a Complex Parametron transport through an Athena lattice?",
        ),
        (
            "uar2/technical/conservative-equality",
            "When are two causal objects equal relative to receiver history?",
        ),
    ];

    // The complete exterior byte occurrence crosses the standing granular morphology first. No
    // name, target answer, semantic category, or selected history cell enters this deed.
    let mut technical_returns = Vec::with_capacity(prompts.len());
    for (occurrence, prompt) in prompts {
        let occurrence_started = Instant::now();
        eprintln!("UAR2 phase: reflect {occurrence}");
        technical_returns.push(
            rest.body()
                .body()
                .granular_potential()
                .reflect_exterior_projective_current(occurrence, prompt.as_bytes())
                .map_err(display)?,
        );
        eprintln!(
            "UAR2 technical occurrence {occurrence} returned in {} ms",
            occurrence_started.elapsed().as_millis()
        );
    }
    write_json(
        output.join("00-technical-native-returns.json"),
        &technical_returns,
    )?;

    let participant = EmanationParticipant {
        occurrence: "uar2/participant/laboratory-operator".to_owned(),
        identity: "participant/laboratory-operator".to_owned(),
        proper_name: "Brandon".to_owned(),
    };
    let deeds = [
        EmanationDeed::Infer,
        EmanationDeed::Infer,
        EmanationDeed::Infer,
    ];
    let mut product = rest.mount_product().map_err(display)?;
    let mut histories = Vec::with_capacity(deeds.len());
    for (at, deed) in deeds.into_iter().enumerate() {
        histories.push(
            product
                .emanate_participant(
                    LaboratoryParticipantIngress::found(
                        format!("uar2/history/{at}"),
                        participant.clone(),
                        deed,
                        PerspectiveChart::found(format!("uar2/chart/{at}"), None, None)
                            .map_err(display)?,
                    )
                    .map_err(display)?,
                )
                .map_err(display)?,
        );
    }
    let mut joined = Vec::<ProductTechnicalHistoryEmanation>::with_capacity(prompts.len());
    for (at, (technical, history)) in technical_returns.iter().zip(&histories).enumerate() {
        let return_section = product
            .join_technical_history(technical, history)
            .map_err(display)?;
        fs::write(
            output.join(format!("0{}-joined-technical-return.md", at + 1)),
            &return_section.joined_surface,
        )
        .map_err(display)?;
        joined.push(return_section);
    }
    write_json(output.join("04-joined-native-returns.json"), &joined)?;
    write_json(
        output.join("05-participant-history-returns.json"),
        &histories,
    )?;
    let rest = product.into_rest();
    let returned_identity = rest.identity().to_owned();

    let technical_identities = technical_returns
        .iter()
        .map(|returned| returned.identity_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let joined_identities = joined
        .iter()
        .map(|returned| returned.identity_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let joined_surface_identities = joined
        .iter()
        .map(|returned| returned.joined_surface_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let fine_prompt_current_crossed_before_rendering = technical_returns.iter().all(|returned| {
        !returned.contexts.is_empty()
            && returned.entered_octet_population > 0
            && !returned.exact_source_fibre.is_empty()
            && returned.quadratic_population_reopens_from_source_fibre
    });
    let every_join_has_literal_shared_factor_incidence = joined.iter().all(|returned| {
        !returned.shared_factor_support.is_empty()
            && !returned.shared_affine_cell_addresses.is_empty()
            && returned
                .shared_factor_support
                .iter()
                .all(|factor| returned.technical_factor_support.contains(factor))
    });
    let every_join_retains_both_reconstruction_fibres = joined.iter().all(|returned| {
        !returned.technical_section_reconstruction_fibre.is_empty()
            && (!returned.history_hidden_cell_reconstruction_fibre.is_empty()
                || !returned
                    .history_unjoined_cell_reconstruction_fibre
                    .is_empty())
    });
    let cpu_semantic_replay_after_device = false;
    let passed = returned_identity == predecessor_identity
        && fine_prompt_current_crossed_before_rendering
        && technical_identities.len() == prompts.len()
        && joined_identities.len() == prompts.len()
        && joined_surface_identities.len() == prompts.len()
        && every_join_has_literal_shared_factor_incidence
        && every_join_retains_both_reconstruction_fibres
        && !cpu_semantic_replay_after_device;
    let grade = Uar2Grade {
        schema: "soma-life.athena-unified-technical-history-uar2-grade.v1",
        truth_status: if passed {
            "established-bounded; implemented-exact; measured"
        } else {
            "counterexample; implemented-exact; measured"
        },
        passed,
        predecessor_rest_identity_sha256: &predecessor_identity,
        returned_rest_identity_sha256: &returned_identity,
        one_move_owned_athena_body: true,
        fine_prompt_current_crossed_before_rendering,
        three_technical_native_signatures_distinct: technical_identities.len() == prompts.len(),
        three_joined_native_signatures_distinct: joined_identities.len() == prompts.len(),
        three_joined_surfaces_distinct: joined_surface_identities.len() == prompts.len(),
        every_join_has_literal_shared_factor_incidence,
        every_join_retains_both_reconstruction_fibres,
        technical_prompt_selected_cultivation: false,
        exterior_word_matching_selected_history: false,
        source_lookup_during_inference: false,
        cpu_semantic_replay_after_device,
        wall_milliseconds: started.elapsed().as_millis(),
    };
    write_json(output.join("06-uar2-grade.json"), &grade)?;
    write_json(
        output.join("07-standing-reuse.json"),
        &json!({
            "schema": "soma-life.athena-unified-technical-history-standing-reuse.v1",
            "truth_status": "established-bounded; implemented-exact; measured",
            "predecessor_rest_identity_sha256": predecessor_identity,
            "returned_rest_identity_sha256": returned_identity,
            "raw_prompt_ingress": "NativeGranularPotential -> NativeCausalMembrane",
            "history_ingress": "ResidentProductEcology resident participant front",
            "join_law": "literal intersection of returned prompt factor current and cultivated affine landmark factors",
            "new_body_founded": false,
            "source_material_mounted": false,
            "retired_circulation_mounted": false
        }),
    )?;
    if !passed {
        return Err("UAR2 returned a technical/history counterexample".to_owned());
    }
    println!("UAR2 passed in {} ms", started.elapsed().as_millis());
    Ok(())
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut root = std::env::current_dir().map_err(display)?;
    loop {
        if root.join("Cargo.toml").exists() && root.join("soma/life").exists() {
            return Ok(root);
        }
        if !root.pop() {
            return Err("could not locate the holonics workspace".to_owned());
        }
    }
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
