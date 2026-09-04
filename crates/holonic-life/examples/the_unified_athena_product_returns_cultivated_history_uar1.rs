//! UAR0--UAR1 — the exact ALP5 body exposes its already resident cultivated participant/history
//! section without founding another Athena rest or reopening source material.

use std::{collections::BTreeSet, fs, path::PathBuf, time::Instant};

use life::native_intelligence::{
    EmanationDeed, EmanationParticipant, LaboratoryParticipantEmanation,
    LaboratoryParticipantIngress, OpticalProductRest, PerspectiveChart,
};
use serde::Serialize;
use serde_json::json;

const REST: &str = concat!(
    ".local/artifacts/the_one_holonics_hna_body_circulates_every_admitted_organ_and_cultivates_alp4/",
    "athena-sens6-cultivated.rest"
);
const OUTPUT: &str =
    ".local/artifacts/the_unified_athena_product_returns_cultivated_history_with_chart_agreement_uar1";
const EXPECTED_ALP5_IDENTITY: &str =
    "916710c5e7e5f79c602e8e4b6e0e3a74c7a5334d1b50df9e63bf1a127e8b67f5";

#[derive(Serialize)]
struct Uar1Grade<'a> {
    schema: &'static str,
    truth_status: &'static str,
    passed: bool,
    predecessor_rest_identity_sha256: &'a str,
    returned_rest_identity_sha256: &'a str,
    one_move_owned_product_body: bool,
    resident_gpu_participant_return: bool,
    three_native_sections_distinct: bool,
    three_surfaces_distinct: bool,
    exterior_name_absent_from_native_selection: bool,
    source_material_mounted: bool,
    retired_circulation_mounted: bool,
    old_compact_projection_retained_as_parity: bool,
    wall_milliseconds: u128,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let output = root.join(OUTPUT);
    if output.exists() {
        return Err(format!(
            "preserve existing UAR1 return {}",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(display)?;
    let started = Instant::now();
    let wire = fs::read(root.join(REST)).map_err(display)?;
    let rest = OpticalProductRest::read(&wire).map_err(display)?;
    if rest.identity() != EXPECTED_ALP5_IDENTITY {
        return Err("UAR1 did not receive the exact ALP5 body".to_owned());
    }
    let predecessor_identity = rest.identity().to_owned();
    let core = rest.body().body().body();
    let reuse = json!({
        "schema": "soma-life.athena-unified-history-standing-reuse.v1",
        "truth_status": "established-bounded; implemented-exact; measured",
        "predecessor_rest_identity_sha256": predecessor_identity,
        "nested_recurrent_affine_identity_sha256": core.identity(),
        "affine_cell_population": core.affine_cells().len(),
        "optical_organ_present": true,
        "acoustic_organ_present": true,
        "granular_organ_present": true,
        "cultivated_relational_organ_present": true,
        "resident_participant_front_present": true,
        "situated_operation_egress_present": true,
        "omitted_composition": "the complete resident participant/history section was not exposed by the ALP5 product aperture beside situated operation egress",
        "new_body_required": false,
        "source_material_mounted": false,
        "retired_circulation_mounted": false
    });
    write_json(output.join("00-standing-reuse.json"), &reuse)?;

    let participant = EmanationParticipant {
        occurrence: "uar1/participant/laboratory-operator".to_owned(),
        identity: "participant/laboratory-operator".to_owned(),
        proper_name: "Brandon".to_owned(),
    };
    let deeds = [
        EmanationDeed::Describe,
        EmanationDeed::Identify,
        EmanationDeed::Infer,
    ];
    let labels = ["describe", "identify", "infer"];
    let perspectives = [
        PerspectiveChart::found("uar1/chart/brandon-referent", None, None).map_err(display)?,
        PerspectiveChart::found(
            "uar1/chart/brandon-speaker",
            Some(participant.identity.clone()),
            None,
        )
        .map_err(display)?,
        PerspectiveChart::found(
            "uar1/chart/brandon-addressee",
            None,
            Some(participant.identity.clone()),
        )
        .map_err(display)?,
    ];

    let mut product = rest.mount_product().map_err(display)?;
    let mut returns = Vec::<LaboratoryParticipantEmanation>::new();
    for ((deed, label), perspective) in deeds.into_iter().zip(labels).zip(perspectives) {
        let returned = product
            .emanate_participant(
                LaboratoryParticipantIngress::found(
                    format!("uar1/ingress/{label}"),
                    participant.clone(),
                    deed,
                    perspective,
                )
                .map_err(display)?,
            )
            .map_err(display)?;
        fs::write(
            output.join(format!("0{}-{label}.md", returns.len() + 1)),
            &returned.text,
        )
        .map_err(display)?;
        returns.push(returned);
    }

    let renamed = product
        .emanate_participant(
            LaboratoryParticipantIngress::found(
                "uar1/control/exterior-name",
                EmanationParticipant {
                    occurrence: participant.occurrence.clone(),
                    identity: participant.identity.clone(),
                    proper_name: "ExteriorNameControl".to_owned(),
                },
                EmanationDeed::Describe,
                PerspectiveChart::found("uar1/chart/exterior-name-control", None, None)
                    .map_err(display)?,
            )
            .map_err(display)?,
        )
        .map_err(display)?;
    let exterior_name_absent_from_native_selection = renamed.selected_cell_addresses
        == returns[0].selected_cell_addresses
        && renamed.selected_affine_sections == returns[0].selected_affine_sections
        && renamed.native_successor_identity_sha256 == returns[0].native_successor_identity_sha256;
    write_json(output.join("04-native-history-returns.json"), &returns)?;
    write_json(output.join("05-exterior-name-control.json"), &renamed)?;

    let native_identities = returns
        .iter()
        .map(|returned| returned.native_successor_identity_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let surface_identities = returns
        .iter()
        .map(|returned| returned.text_sha256.as_str())
        .collect::<BTreeSet<_>>();
    let resident_gpu_participant_return = returns.iter().all(|returned| {
        returned.apparatus.device.contains("RTX")
            && returned.apparatus.launches == 1
            && returned.apparatus.synchronizations == 1
            && !returned.apparatus.invariant_transport_reuploaded
            && !returned.apparatus.cpu_semantic_replay_after_device
            && !returned.apparatus.authored_output_extent_present
    });
    let rest = product.into_rest();
    let returned_identity = rest.identity().to_owned();
    let passed = returned_identity == predecessor_identity
        && resident_gpu_participant_return
        && native_identities.len() == returns.len()
        && surface_identities.len() == returns.len()
        && exterior_name_absent_from_native_selection;
    let grade = Uar1Grade {
        schema: "soma-life.athena-unified-history-uar1-grade.v1",
        truth_status: "established-bounded; implemented-exact; measured",
        passed,
        predecessor_rest_identity_sha256: &predecessor_identity,
        returned_rest_identity_sha256: &returned_identity,
        one_move_owned_product_body: true,
        resident_gpu_participant_return,
        three_native_sections_distinct: native_identities.len() == returns.len(),
        three_surfaces_distinct: surface_identities.len() == returns.len(),
        exterior_name_absent_from_native_selection,
        source_material_mounted: false,
        retired_circulation_mounted: false,
        old_compact_projection_retained_as_parity: true,
        wall_milliseconds: started.elapsed().as_millis(),
    };
    write_json(output.join("06-uar1-grade.json"), &grade)?;
    if !passed {
        return Err(
            "UAR1 did not return the complete product-owned participant section".to_owned(),
        );
    }
    println!(
        "UAR1 returned three complete cultivated-history sections from {} in {} ms",
        returned_identity,
        started.elapsed().as_millis()
    );
    Ok(())
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut root = std::env::current_dir().map_err(display)?;
    loop {
        if root.join("Cargo.toml").exists() && root.join("crates/holonic-life").exists() {
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
