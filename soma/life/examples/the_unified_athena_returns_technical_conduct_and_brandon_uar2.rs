//! UAR2 — fine exterior currents meet the complete cultivated affine history inside the one
//! resident Athena product.  Three technical and three participant receivers share one law; the
//! accepted UAR1 participant aperture returns afterward as an exact non-regression control.

use std::{collections::BTreeSet, fs, path::PathBuf, time::Instant};

use life::native_intelligence::{
    EmanationDeed, EmanationParticipant, LaboratoryParticipantIngress, OpticalProductRest,
    PerspectiveChart, ProductSituatedCurrentEmanation,
};
use serde::Serialize;

const REST: &str = concat!(
    "output/the_one_athena_alpha_body_circulates_every_admitted_organ_and_cultivates_alp4/",
    "athena-sens6-cultivated.rest"
);
const OUTPUT: &str =
    "output/the_unified_athena_returns_complete_current_technical_conduct_and_brandon_uar2";
const EXPECTED_REST: &str = "916710c5e7e5f79c602e8e4b6e0e3a74c7a5334d1b50df9e63bf1a127e8b67f5";
const UAR1_SURFACE_HASHES: [&str; 3] = [
    "bc276eb70250d8120ef21aaa1b1bcef3fc8732b445d673017fdd1b26dc6ad30c",
    "4f9d506c42adebaffe1c99b173134358cd738969f8020a43df5dc48e713b4829",
    "d0f42fa9e9d63a5f28a6b231bcd7e30d8201c7aac8202379e75fb6394601f914",
];

#[derive(Serialize)]
struct Uar2Grade<'a> {
    schema: &'static str,
    truth_status: &'static str,
    mechanism_passed: bool,
    qualitative_grade_pending_direct_inspection: bool,
    predecessor_rest_identity_sha256: &'a str,
    returned_rest_identity_sha256: &'a str,
    technical_current_identities_distinct: bool,
    technical_overlap_holons_distinct: bool,
    technical_native_fronts_distinct: bool,
    technical_surfaces_distinct: bool,
    technical_surfaces_nonempty: bool,
    brandon_current_identities_distinct: bool,
    brandon_native_fronts_distinct: bool,
    brandon_surfaces_distinct: bool,
    brandon_surfaces_nonempty: bool,
    accepted_uar1_brandon_surfaces_unchanged: bool,
    one_move_owned_athena_body: bool,
    full_cell_by_context_overlap_retained: bool,
    scalar_score_present: bool,
    authored_output_extent_present: bool,
    technical_prompt_selected_cultivation: bool,
    exterior_word_matching_selected_history: bool,
    source_lookup_during_inference: bool,
    invariant_transport_reuploaded: bool,
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
    let began = Instant::now();
    let rest =
        OpticalProductRest::read(&fs::read(root.join(REST)).map_err(display)?).map_err(display)?;
    if rest.identity() != EXPECTED_REST {
        return Err("UAR2 did not receive the exact ALP5 rest".to_owned());
    }
    let predecessor_identity = rest.identity().to_owned();

    let technical_prompts = [
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
    let brandon_prompts = [
        (
            "uar2/brandon/describe",
            "Describe Brandon.",
            EmanationDeed::Describe,
        ),
        (
            "uar2/brandon/identify",
            "Who is Brandon?",
            EmanationDeed::Identify,
        ),
        (
            "uar2/brandon/infer",
            "What does Brandon infer about holonic compression?",
            EmanationDeed::Infer,
        ),
    ];
    let technical_currents = technical_prompts
        .iter()
        .map(|(occurrence, surface)| {
            rest.body()
                .body()
                .granular_potential()
                .reflect_exterior_projective_current(*occurrence, surface.as_bytes())
                .map_err(display)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let brandon_currents = brandon_prompts
        .iter()
        .map(|(occurrence, surface, _)| {
            rest.body()
                .body()
                .granular_potential()
                .reflect_exterior_projective_current(*occurrence, surface.as_bytes())
                .map_err(display)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut product = rest.mount_product().map_err(display)?;

    let technical_returns = technical_currents
        .iter()
        .map(|current| product.emanate_situated_current(current, false, EmanationDeed::Infer, None))
        .collect::<Result<Vec<_>, _>>()
        .map_err(display)?;
    let brandon_returns = brandon_currents
        .iter()
        .zip(brandon_prompts.iter())
        .map(|(current, (_, _, deed))| {
            product.emanate_situated_current(current, true, *deed, Some("Brandon".to_owned()))
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(display)?;

    for (at, returned) in technical_returns.iter().enumerate() {
        fs::write(
            output.join(format!("0{}-technical-return.md", at + 1)),
            &returned.surface,
        )
        .map_err(display)?;
    }
    for (at, returned) in brandon_returns.iter().enumerate() {
        fs::write(
            output.join(format!("0{}-brandon-return.md", at + 4)),
            &returned.surface,
        )
        .map_err(display)?;
    }
    write_json(
        output.join("07-technical-native-returns.json"),
        &technical_returns,
    )?;
    write_json(
        output.join("08-brandon-native-returns.json"),
        &brandon_returns,
    )?;

    let participant = EmanationParticipant {
        occurrence: "uar2/control/participant".to_owned(),
        identity: "participant/laboratory-operator".to_owned(),
        proper_name: "Brandon".to_owned(),
    };
    let controls = [
        (EmanationDeed::Describe, None, None),
        (
            EmanationDeed::Identify,
            Some(participant.identity.clone()),
            None,
        ),
        (
            EmanationDeed::Infer,
            None,
            Some(participant.identity.clone()),
        ),
    ]
    .into_iter()
    .enumerate()
    .map(|(at, (deed, speaker, addressee))| {
        product
            .emanate_participant(
                LaboratoryParticipantIngress::found(
                    format!("uar2/control/{at}"),
                    participant.clone(),
                    deed,
                    PerspectiveChart::found(format!("uar2/control/chart/{at}"), speaker, addressee)
                        .map_err(display)?,
                )
                .map_err(display)?,
            )
            .map_err(display)
    })
    .collect::<Result<Vec<_>, _>>()?;
    write_json(output.join("09-uar1-non-regression.json"), &controls)?;
    let returned_rest = product.into_rest();
    let returned_identity = returned_rest.identity().to_owned();

    let technical_current_identities_distinct = distinct(
        technical_returns
            .iter()
            .map(|returned| returned.exterior_current_identity_sha256.as_str()),
    ) == technical_returns.len();
    let technical_overlap_holons_distinct = distinct(
        technical_returns
            .iter()
            .map(|returned| returned.apparatus.overlap_identity_sha256.as_str()),
    ) == technical_returns.len();
    let technical_native_fronts_distinct = distinct_fronts(&technical_returns);
    let technical_surfaces_distinct = distinct(
        technical_returns
            .iter()
            .map(|returned| returned.surface_sha256.as_str()),
    ) == technical_returns.len();
    let brandon_current_identities_distinct = distinct(
        brandon_returns
            .iter()
            .map(|returned| returned.exterior_current_identity_sha256.as_str()),
    ) == brandon_returns.len();
    let brandon_native_fronts_distinct = distinct_fronts(&brandon_returns);
    let brandon_surfaces_distinct = distinct(
        brandon_returns
            .iter()
            .map(|returned| returned.surface_sha256.as_str()),
    ) == brandon_returns.len();
    let mut all_returns = technical_returns.iter().chain(&brandon_returns);
    let full_cell_by_context_overlap_retained = all_returns.clone().all(|returned| {
        returned.apparatus.cell_context_overlaps.len() == returned.apparatus.cell_population
            && returned
                .apparatus
                .cell_context_overlaps
                .iter()
                .all(|cell| cell.len() == returned.apparatus.context_population)
    });
    let scalar_score_present = all_returns
        .clone()
        .any(|returned| returned.apparatus.scalar_score_present);
    let authored_output_extent_present = all_returns
        .clone()
        .any(|returned| returned.apparatus.authored_output_extent_present);
    let invariant_transport_reuploaded = all_returns
        .clone()
        .any(|returned| returned.apparatus.invariant_transport_reuploaded);
    let cpu_semantic_replay_after_device =
        all_returns.any(|returned| returned.apparatus.cpu_semantic_replay_after_device);
    let technical_surfaces_nonempty = technical_returns
        .iter()
        .all(|returned| !returned.surface.is_empty());
    let brandon_surfaces_nonempty = brandon_returns
        .iter()
        .all(|returned| !returned.surface.is_empty());
    let accepted_uar1_brandon_surfaces_unchanged = controls
        .iter()
        .map(|control| control.text_sha256.as_str())
        .eq(UAR1_SURFACE_HASHES);
    let mechanism_passed = returned_identity == predecessor_identity
        && technical_current_identities_distinct
        && technical_overlap_holons_distinct
        && technical_native_fronts_distinct
        && technical_surfaces_distinct
        && technical_surfaces_nonempty
        && brandon_current_identities_distinct
        && brandon_native_fronts_distinct
        && brandon_surfaces_distinct
        && brandon_surfaces_nonempty
        && accepted_uar1_brandon_surfaces_unchanged
        && full_cell_by_context_overlap_retained
        && !scalar_score_present
        && !authored_output_extent_present
        && !invariant_transport_reuploaded
        && !cpu_semantic_replay_after_device;
    let grade = Uar2Grade {
        schema: "soma-life.unified-athena-technical-brandon-uar2-grade.v1",
        truth_status: if mechanism_passed {
            "established-bounded; implemented-exact; measured"
        } else {
            "counterexample; implemented-exact; measured"
        },
        mechanism_passed,
        qualitative_grade_pending_direct_inspection: true,
        predecessor_rest_identity_sha256: &predecessor_identity,
        returned_rest_identity_sha256: &returned_identity,
        technical_current_identities_distinct,
        technical_overlap_holons_distinct,
        technical_native_fronts_distinct,
        technical_surfaces_distinct,
        technical_surfaces_nonempty,
        brandon_current_identities_distinct,
        brandon_native_fronts_distinct,
        brandon_surfaces_distinct,
        brandon_surfaces_nonempty,
        accepted_uar1_brandon_surfaces_unchanged,
        one_move_owned_athena_body: true,
        full_cell_by_context_overlap_retained,
        scalar_score_present,
        authored_output_extent_present,
        technical_prompt_selected_cultivation: false,
        exterior_word_matching_selected_history: false,
        source_lookup_during_inference: false,
        invariant_transport_reuploaded,
        cpu_semantic_replay_after_device,
        wall_milliseconds: began.elapsed().as_millis(),
    };
    write_json(output.join("10-uar2-grade.json"), &grade)?;
    if !mechanism_passed {
        return Err("UAR2 situated-current mechanism returned a counterexample".to_owned());
    }
    println!(
        "UAR2 mechanism passed: technical fronts {:?}; Brandon fronts {:?}; elapsed {} ms",
        technical_returns
            .iter()
            .map(|returned| returned.selected_cell_addresses.len())
            .collect::<Vec<_>>(),
        brandon_returns
            .iter()
            .map(|returned| returned.selected_cell_addresses.len())
            .collect::<Vec<_>>(),
        began.elapsed().as_millis(),
    );
    Ok(())
}

fn distinct<'a>(values: impl Iterator<Item = &'a str>) -> usize {
    values.collect::<BTreeSet<_>>().len()
}

fn distinct_fronts(returns: &[ProductSituatedCurrentEmanation]) -> bool {
    returns
        .iter()
        .map(|returned| &returned.selected_cell_addresses)
        .collect::<BTreeSet<_>>()
        .len()
        == returns.len()
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
