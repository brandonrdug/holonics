//! Repaired L5 participant receiver over the already-cultivated affine rest.

use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use life::native_intelligence::{
    AffineLaboratoryCultivatedRest, EmanationDeed, EmanationParticipant,
    LaboratoryParticipantEmanation, LaboratoryParticipantIngress, PerspectiveChart,
};
use serde::Serialize;
use serde_json::json;

const REST: &str = concat!(
    ".local/artifacts/the_affine_laboratory_returns_one_relational_organ_over_four_cycle_fibres_l5_repair/",
    "athena-affine-laboratory-cultivated.rest"
);
const OUTPUT: &str =
    ".local/artifacts/the_direct_participant_returns_without_existential_alias_collapse_l5_repair";

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .ok_or("cannot locate repository root")?
        .to_path_buf();
    let output = root.join(OUTPUT);
    let grade_path = output.join("08-resident-participant-grade.json");
    if grade_path.exists() {
        return Err(format!(
            "preserve existing participant return {}",
            grade_path.display()
        ));
    }
    fs::create_dir_all(&output).map_err(display)?;
    let started = Instant::now();
    let rest_bytes = fs::read(root.join(REST)).map_err(display)?;
    let rest = AffineLaboratoryCultivatedRest::read(&rest_bytes).map_err(display)?;
    let rest_identity = rest.identity().to_owned();
    let mut resident = rest.mount().map_err(display)?;
    let participant = EmanationParticipant {
        occurrence: "laboratory-participant-occurrence".to_owned(),
        identity: "laboratory-addressed-participant".to_owned(),
        proper_name: "Brandon".to_owned(),
    };
    let perspective = PerspectiveChart::found(
        "participant-referent-chart",
        Some("athena-speaker".to_owned()),
        Some("laboratory-addressee".to_owned()),
    )
    .map_err(display)?;
    let mut returns = Vec::new();
    for (ordinal, deed) in [
        EmanationDeed::Describe,
        EmanationDeed::Identify,
        EmanationDeed::Infer,
    ]
    .into_iter()
    .enumerate()
    {
        let ingress = LaboratoryParticipantIngress::found(
            format!("participant-deed/{ordinal}"),
            participant.clone(),
            deed,
            perspective.clone(),
        )
        .map_err(display)?;
        returns.push(resident.emanate_participant(ingress).map_err(display)?);
    }

    // The proper-name chart changes only the exterior subject surface. It cannot change native
    // contact, selected causal sections, or the native successor identity.
    let renamed_participant = EmanationParticipant {
        proper_name: "the laboratory operator".to_owned(),
        ..participant.clone()
    };
    let renamed = resident
        .emanate_participant(
            LaboratoryParticipantIngress::found(
                "participant-deed/renamed-control",
                renamed_participant,
                EmanationDeed::Describe,
                perspective,
            )
            .map_err(display)?,
        )
        .map_err(display)?;
    let describe = &returns[0];
    let native_name_inert = describe.native_successor_identity_sha256
        == renamed.native_successor_identity_sha256
        && describe.selected_cell_addresses == renamed.selected_cell_addresses
        && describe.text != renamed.text;
    let signatures = returns
        .iter()
        .map(|returned| returned.native_successor_identity_sha256.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    let texts = returns
        .iter()
        .map(|returned| returned.text_sha256.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    let distinct_deeds = signatures.len() == returns.len() && texts.len() == returns.len();
    let resident_exact = returns.iter().all(|returned| {
        returned.rest_identity_sha256 == rest_identity
            && returned.apparatus.selected_population > 0
            && returned.apparatus.launches == 1
            && returned.apparatus.synchronizations == 1
            && !returned.apparatus.invariant_transport_reuploaded
            && !returned.apparatus.cpu_semantic_replay_after_device
            && !returned.apparatus.authored_output_extent_present
    });
    for returned in &returns {
        write_json(
            output.join(format!(
                "05-{}-participant-return.json",
                deed_name(returned.deed)
            )),
            returned,
        )?;
        write_text(
            output.join(format!(
                "05-{}-participant-surface.md",
                deed_name(returned.deed)
            )),
            &returned.text,
        )?;
    }
    write_json(output.join("06-renamed-perspective-control.json"), &renamed)?;
    write_text(
        output.join("06-renamed-perspective-surface.md"),
        &renamed.text,
    )?;
    let qualitative = returns
        .iter()
        .map(qualitative_projection)
        .collect::<Vec<_>>();
    write_json(
        output.join("07-participant-qualitative-projection.json"),
        &qualitative,
    )?;
    let passed = distinct_deeds && resident_exact && native_name_inert;
    write_json(
        grade_path,
        &json!({
            "schema": "soma-life.affine-laboratory-resident-participant-grade.v1",
            "truth_status": if passed { "established-bounded-implemented-exact-measured" } else { "counterexample" },
            "passed": passed,
            "rest_identity_sha256": rest_identity,
            "distinct_deed_native_successors": distinct_deeds,
            "resident_gpu_front_exact": resident_exact,
            "proper_name_is_native_inert": native_name_inert,
            "selected_populations": returns.iter().map(|returned| returned.selected_cell_addresses.len()).collect::<Vec<_>>(),
            "surface_octets": returns.iter().map(|returned| returned.text.len()).collect::<Vec<_>>(),
            "device": returns.first().map(|returned| returned.apparatus.device.clone()),
            "mount_host_ingress_octets": returns.first().map(|returned| returned.apparatus.mount_host_ingress_octets),
            "successor_invariant_reupload_population": returns.iter().filter(|returned| returned.apparatus.invariant_transport_reuploaded).count(),
            "cpu_semantic_replay_population": returns.iter().filter(|returned| returned.apparatus.cpu_semantic_replay_after_device).count(),
            "authored_output_extent_population": returns.iter().filter(|returned| returned.apparatus.authored_output_extent_present).count(),
            "wall_milliseconds": started.elapsed().as_millis(),
        }),
    )?;
    if !passed {
        return Err("the resident participant/deed receiver failed".to_owned());
    }
    println!(
        "resident participant receiver returned describe/identify/infer through {} in {} ms",
        returns[0].apparatus.device,
        started.elapsed().as_millis()
    );
    Ok(())
}

fn qualitative_projection(returned: &LaboratoryParticipantEmanation) -> serde_json::Value {
    json!({
        "deed": deed_name(returned.deed),
        "selected_cell_population": returned.selected_cell_addresses.len(),
        "hidden_reconstruction_fibre_population": returned.hidden_participant_cell_fibre.len(),
        "text_octets": returned.text.len(),
        "text_preview": returned.text.chars().take(1200).collect::<String>(),
        "native_successor_identity_sha256": returned.native_successor_identity_sha256,
    })
}

fn deed_name(deed: EmanationDeed) -> &'static str {
    match deed {
        EmanationDeed::Describe => "describe",
        EmanationDeed::Identify => "identify",
        EmanationDeed::Infer => "infer",
        EmanationDeed::Explain => "explain",
        EmanationDeed::Rewrite => "rewrite",
        EmanationDeed::Derive => "derive",
    }
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(display)?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(display)
}

fn write_text(path: PathBuf, value: &str) -> Result<(), String> {
    let mut value = value.as_bytes().to_vec();
    value.push(b'\n');
    fs::write(path, value).map_err(display)
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
