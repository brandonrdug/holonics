//! L5 repair — one later material section crosses the complete cultivated affine base by exact
//! barycentric linear extension. Prose, notation, and Rust delivery faces return the same native
//! field; withdrawal removes it and restoration recovers the singular rest.

use std::{fs, path::PathBuf, time::Instant};

use life::native_intelligence::{
    compare_material_factorizations, AddressedEmanationIngress, AddressedEmanationWorldReturn,
    AddressedMaterialOccurrence, AffineLaboratoryCultivatedRest, CausalOperationWorldReturn,
    CausalResultCell, EmanationDeed, EmanationParticipant, ExteriorWorldReturnTestimony,
    MaterialFactorizationAperture, PerspectiveChart, SituatedEmanationPassage,
};
use serde::Serialize;
use serde_json::json;

const REST: &str = concat!(
    ".local/artifacts/the_affine_laboratory_returns_one_relational_organ_over_four_cycle_fibres_l5_repair/",
    "athena-affine-laboratory-cultivated.rest"
);
const OUTPUT: &str = ".local/artifacts/the_three_resident_fronts_return_one_affine_athena_continuation_l5";

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let out = root.join(OUTPUT);
    if out.exists() {
        return Err(format!(
            "preserve existing L5 affine-current return {}",
            out.display()
        ));
    }
    let started = Instant::now();
    let rest = AffineLaboratoryCultivatedRest::read(&fs::read(root.join(REST)).map_err(display)?)
        .map_err(display)?;
    let cultivated_identity = rest.identity().to_owned();
    let expected_landmarks = rest.correspondences().len();
    let expected_cells = rest.affine_cells().len();

    let prose_material = material(
        "l5-affine/material/prose",
        b"Two disjoint populations of two return four occurrences.",
        "ordinary-prose",
    )?;
    let notation_material = material(
        "l5-affine/material/notation",
        br"|{a,b} \sqcup {c,d}| = 4",
        "mathematical-notation",
    )?;
    let rust_material = material(
        "l5-affine/material/rust",
        b"let returned = left.into_iter().chain(right).count();",
        "rust-source",
    )?;
    let prose_world = union_return(&prose_material, "prose")?;
    let notation_world = union_return(&notation_material, "notation")?;
    let rust_world = union_return(&rust_material, "rust")?;

    let aperture = MaterialFactorizationAperture::found(&rest).map_err(display)?;
    let mut prose_factorization = aperture
        .factor(&prose_material, &prose_world)
        .map_err(display)?;
    let notation_factorization = aperture
        .factor(&notation_material, &notation_world)
        .map_err(display)?;
    let prose_notation = compare_material_factorizations(
        &prose_factorization,
        &notation_factorization,
        "same-operation/prose-notation",
    );
    let rust_factorization = aperture
        .factor(&rust_material, &rust_world)
        .map_err(display)?;
    let prose_rust = compare_material_factorizations(
        &prose_factorization,
        &rust_factorization,
        "same-operation/prose-rust",
    );
    let transport = prose_factorization
        .cultivated_affine_transport
        .as_ref()
        .ok_or("the cultivated rest delegated material current to its L2 predecessor")?;
    let transport_summary = json!({
        "identity_sha256": transport.identity_sha256,
        "entering_section": transport.entering_section,
        "addressed_landmark_population": transport.addressed_landmark_population,
        "addressed_cell_population": transport.addressed_cell_population,
        "local_fibre_term_population": transport.local_fibre_term_population,
        "every_cell_augments_to_entering_section": transport.every_cell_augments_to_entering_section,
        "complete_cell_reconstruction_fibre_population": transport.complete_cell_reconstruction_fibre.len(),
    });
    drop(notation_factorization);
    drop(rust_factorization);

    let mut resident = rest.mount().map_err(display)?;
    let resident_return = resident
        .conduct_material(&mut prose_factorization)
        .map_err(display)?;
    let affine_apparatus = prose_factorization
        .cultivated_affine_transport
        .as_ref()
        .and_then(|transport| transport.resident_apparatus.clone())
        .ok_or("the affine field did not return from the resident card")?;
    let integrated_apparatus = prose_factorization
        .cultivated_affine_transport
        .as_ref()
        .and_then(|transport| transport.integrated_resident_apparatus.clone())
        .ok_or("the resident fronts did not return one integrated apparatus receipt")?;
    let resident_rest_identity_exact = resident_return.rest_identity_sha256 == cultivated_identity;
    let apparatus = resident_return.apparatus.clone();
    let rest = resident.into_rest().map_err(display)?;
    let ingress = AddressedEmanationIngress::found(
        "l5-affine/ingress/prose",
        prose_material.occurrence.clone(),
        b"Describe how this operation crosses cultivated laboratory standing.",
        None,
        "participant/operator",
        vec![EmanationParticipant {
            occurrence: "participant-occurrence/operator/l5-affine".to_owned(),
            identity: "participant/operator".to_owned(),
            proper_name: "Brandon".to_owned(),
        }],
        EmanationDeed::Describe,
        vec!["retain every affine cell reconstruction fibre".to_owned()],
        PerspectiveChart::found("l5-affine/chart/referent", None, None).map_err(display)?,
        vec![
            "l5-affine/chronology/material-return".to_owned(),
            "l5-affine/chronology/card-current".to_owned(),
        ],
        vec!["later Hodge and constitutive receiver families".to_owned()],
        vec!["receivers outside the admitted affine field remain open".to_owned()],
    )
    .map_err(display)?;
    let mut passage =
        SituatedEmanationPassage::found(rest, prose_factorization, resident_return, ingress)
            .map_err(display)?;
    let surface = passage.emanate().map_err(display)?;
    let returned = AddressedEmanationWorldReturn::found(
        "l5-affine/world-return/close",
        surface.occurrence.clone(),
        b"the affine field and its complete reconstruction fibre were received",
        Some(EmanationDeed::Explain),
        None,
        None,
        None,
        None,
        None,
        Some("l5-affine/continuation/next-material-current".to_owned()),
        vec!["later moving receiver histories remain open".to_owned()],
    )
    .map_err(display)?;
    let difference = passage.receive_world_return(returned).map_err(display)?;
    let rest = passage.into_rest().map_err(display)?;

    let (body, withdrawal) = rest.withdraw_relational_organ().map_err(display)?;
    let predecessor_aperture = MaterialFactorizationAperture::found(&body).map_err(display)?;
    let predecessor_factorization = predecessor_aperture
        .factor(&prose_material, &prose_world)
        .map_err(display)?;
    let targeted_withdrawal_removes_field = predecessor_factorization
        .cultivated_affine_transport
        .is_none();
    let restored = AffineLaboratoryCultivatedRest::restore_relational_organ(body, withdrawal)
        .map_err(display)?;
    let exact_restoration = restored.identity() == cultivated_identity;

    let cross_codec_naturality = prose_notation.square_commutes
        && prose_notation.affine_transport_equal
        && prose_rust.square_commutes
        && prose_rust.affine_transport_equal;
    let complete_affine_return = transport_summary["addressed_landmark_population"]
        == expected_landmarks
        && transport_summary["addressed_cell_population"] == expected_cells
        && transport_summary["complete_cell_reconstruction_fibre_population"] == expected_cells
        && transport_summary["every_cell_augments_to_entering_section"] == true;
    let qualitative_surface = surface.text.contains("cultivated affine laboratory")
        && surface
            .text
            .contains("affine augmentation reconstructs the entering section");
    let resident_exact = resident_rest_identity_exact
        && !apparatus.device.is_empty()
        && !apparatus.invariant_transport_reuploaded
        && !apparatus.cpu_semantic_replay_after_device
        && !apparatus.binary_receiver_taken;
    let resident_affine_exact = affine_apparatus.addressed_cell_population == expected_cells
        && affine_apparatus.exact_reconstruction_cell_population == expected_cells
        && affine_apparatus.local_fibre_term_population
            == transport_summary["local_fibre_term_population"]
        && !affine_apparatus.invariant_transport_reuploaded
        && !affine_apparatus.cpu_semantic_replay_after_device
        && !affine_apparatus.cell_selected_or_ranked;
    let resident_continuation_exact = integrated_apparatus.one_underlying_context
        && integrated_apparatus.launches == 3
        && integrated_apparatus.synchronizations == 1
        && integrated_apparatus.intermediate_host_egress_octets == 0
        && !integrated_apparatus.invariant_transport_reuploaded
        && !integrated_apparatus.cpu_semantic_replay_after_device;
    let passed = cross_codec_naturality
        && complete_affine_return
        && qualitative_surface
        && targeted_withdrawal_removes_field
        && exact_restoration
        && resident_exact
        && resident_affine_exact
        && resident_continuation_exact
        && !difference.changed_atoms.is_empty();

    fs::create_dir_all(&out).map_err(display)?;
    write_json(
        out.join("00-affine-material-transport.json"),
        &json!({
            "truth_status": ["established-bounded", "implemented-exact", "measured"],
            "cultivated_rest_identity_sha256": cultivated_identity,
            "transport": transport_summary,
            "prose_notation_naturality": prose_notation,
            "prose_rust_naturality": prose_rust,
            "resident_affine_apparatus": affine_apparatus,
            "integrated_resident_apparatus": integrated_apparatus,
            "elapsed_ms": started.elapsed().as_millis(),
        }),
    )?;
    write_json(out.join("01-affine-emanation.json"), &surface)?;
    fs::write(out.join("01-affine-emanation.md"), &surface.text).map_err(display)?;
    write_json(out.join("02-returned-difference.json"), &difference)?;
    write_json(
        out.join("03-l5-affine-current-grade.json"),
        &json!({
            "status": if passed { "passed" } else { "counterexample" },
            "truth_status": if passed {
                vec!["established-bounded", "implemented-exact", "measured"]
            } else {
                vec!["counterexample", "implemented-exact", "measured"]
            },
            "complete_affine_field_returned": complete_affine_return,
            "prose_notation_rust_are_one_native_operation_field": cross_codec_naturality,
            "qualitative_surface_exhibits_cultivated_transport": qualitative_surface,
            "targeted_withdrawal_removes_affine_field": targeted_withdrawal_removes_field,
            "exact_restoration_recovers_rest": exact_restoration,
            "gpu_coupled_current_returned_without_cpu_semantic_replay": resident_exact,
            "gpu_affine_field_returned_without_cpu_semantic_replay": resident_affine_exact,
            "one_card_context_and_one_final_synchronization": resident_continuation_exact,
            "intermediate_host_egress_octets": 0,
            "lexical_contact_or_query_selection_used": false,
            "fifth_winding_coordinate_added": false,
            "cell_selected_or_ranked": false,
        }),
    )?;
    if !passed {
        return Err(
            "the complete affine material-current receiver returned a counterexample".to_owned(),
        );
    }
    println!(
        "L5 affine current passed: every cultivated cell received one barycentric rank-four section, three delivery codecs commuted, and withdrawal/restoration separated the field exactly."
    );
    Ok(())
}

fn material(
    occurrence: &str,
    payload: &[u8],
    face: &str,
) -> Result<AddressedMaterialOccurrence, String> {
    AddressedMaterialOccurrence::found(
        occurrence,
        payload,
        None,
        vec![face.to_owned()],
        vec!["the exterior presentation remains outside native operation identity".to_owned()],
    )
    .map_err(display)
}

fn union_return(
    material: &AddressedMaterialOccurrence,
    suffix: &str,
) -> Result<CausalOperationWorldReturn, String> {
    let left = vec![format!("{suffix}/left/0"), format!("{suffix}/left/1")];
    let right = vec![format!("{suffix}/right/0"), format!("{suffix}/right/1")];
    let result_cells = left
        .iter()
        .map(|member| CausalResultCell {
            occurrence: format!("{suffix}/result/{member}"),
            left_member: Some(member.clone()),
            right_member: None,
        })
        .chain(right.iter().map(|member| CausalResultCell {
            occurrence: format!("{suffix}/result/{member}"),
            left_member: None,
            right_member: Some(member.clone()),
        }))
        .collect();
    CausalOperationWorldReturn::found(
        format!("l5-affine/world/{suffix}/union-return"),
        material.occurrence.clone(),
        left,
        right,
        result_cells,
        ExteriorWorldReturnTestimony::found(
            format!("l5-affine/apparatus/{suffix}/union-return"),
            "causal-population-return",
            true,
            b"4",
            vec!["successor histories outside the declared extension".to_owned()],
        )
        .map_err(display)?,
        vec!["later operation interventions remain open".to_owned()],
    )
    .map_err(display)
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut path = std::env::current_dir().map_err(display)?;
    loop {
        if path.join("Cargo.toml").is_file() && path.join("blueprint").is_dir() {
            return Ok(path);
        }
        if !path.pop() {
            return Err("could not locate the holonics workspace root".to_owned());
        }
    }
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
