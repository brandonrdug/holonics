use std::{env, error::Error, fs, path::PathBuf, time::Instant};

use life::native_intelligence::{transduce_source_neutral_exterior, SourceNeutralEcologyRest};
use serde::{Deserialize, Serialize};
use serde_json::Value;

const CHILD: &str = concat!(
    ".local/artifacts/",
    "the_situated_world_return_deposits_and_remounts_the_same_athena_body_uar3/",
    "athena-uar3-child.rest"
);
const D1_RECEIPT: &str = concat!(
    ".local/artifacts/",
    "the_published_native_seam_returns_one_situated_difference_uar3/",
    "uar3-d1-situated-difference.json"
);
const HELD_LATER_MATERIAL: &str = "docs/canon/TABLET_THE_UNIVERSALITY_MACHINE.md";
const OUTPUT: &str = concat!(
    ".local/artifacts/",
    "the_receiver_radical_departs_without_changing_later_conduct_and_restores_uar3"
);
const CHILD_STAGE: &str = "uar3-d3-radical-child-stage.json";

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Uar3D3RadicalChildStage {
    schema: String,
    child_rest_identity_sha256: String,
    held_later_current_identity_sha256: String,
    child_native_section_identity_sha256: String,
    child_ingress_current_identity_sha256: String,
    child_native_consequence: Value,
    child_complete_section: Value,
    selected_reconstruction_fibre_address: String,
    admitted_radical_population: usize,
    moved_radical_basis_position: usize,
    ablated_body_identity_sha256: String,
    conduct_constitution_before_sha256: String,
    conduct_constitution_after_sha256: String,
    same_native_radiation_constitution: bool,
    withdrawn_direction_in_receiver_radical: bool,
    returned_covector_preserved: bool,
    child_receiver_consequence_identity_sha256: String,
    preserved_receiver_consequence_identity_sha256: String,
    exact_restoration_identity_sha256: String,
    exact_restoration_recovers_child: bool,
    source_codec_consulted: bool,
    exterior_reconstruction_fibre_reachable: bool,
}

#[derive(Serialize)]
struct Uar3D3RadicalAudit {
    truth_status: &'static str,
    child_rest_identity_sha256: String,
    held_later_current_identity_sha256: String,
    child_native_section_identity_sha256: String,
    selected_reconstruction_fibre_address: String,
    admitted_radical_population: usize,
    moved_radical_basis_position: usize,
    ablated_body_identity_sha256: String,
    conduct_constitution_before_sha256: String,
    conduct_constitution_after_sha256: String,
    same_native_radiation_constitution: bool,
    withdrawn_direction_in_receiver_radical: bool,
    returned_covector_preserved: bool,
    child_receiver_consequence_identity_sha256: String,
    preserved_receiver_consequence_identity_sha256: String,
    exact_restoration_identity_sha256: String,
    exact_restoration_recovers_child: bool,
    restored_native_section_identity_sha256: String,
    restored_conduct_exactly_equals_child_conduct: bool,
    complete_apparatus_testimony_equal: bool,
    source_codec_consulted: bool,
    exterior_reconstruction_fibre_reachable: bool,
}

fn main() -> Result<(), Box<dyn Error>> {
    let started = Instant::now();
    let root = repository_root()?;
    let output = env::var_os("HOLONICS_OUTPUT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join(OUTPUT));
    fs::create_dir_all(&output)?;
    if env::var_os("HOLONICS_UAR3_D3_VERIFY_EXISTING").is_some() {
        return verify_existing_restoration(&root, &output);
    }

    let child = SourceNeutralEcologyRest::read(&fs::read(root.join(CHILD))?)?;
    let child_rest_identity_sha256 = child.identity().to_owned();
    let d1: serde_json::Value = serde_json::from_slice(&fs::read(root.join(D1_RECEIPT))?)?;
    let selected_reconstruction_fibre_address = d1
        .get("selected_reconstruction_fibre_address")
        .and_then(serde_json::Value::as_str)
        .ok_or("the D1 receipt lost its selected reconstruction fibre")?
        .to_owned();
    let admitted_radical_population = child
        .body()
        .ecology()
        .exact_reconstruction_fibres()
        .iter()
        .find(|fibre| fibre.address == selected_reconstruction_fibre_address)
        .map(|fibre| fibre.radical.len())
        .ok_or("the D1 reconstruction fibre is absent from the D2 child")?;
    if admitted_radical_population == 0 {
        return Err("the D1 reconstruction fibre has no support-disjoint basis direction".into());
    }
    // The basis order is part of the exact reconstruction fibre.  This intervention removes its
    // first retained basis occurrence; it does not choose a native capacity or cultivation axis.
    let moved_radical_basis_position = 0;
    eprintln!("uar3-d3-radical child {}ms", started.elapsed().as_millis());

    let held_material = fs::read(root.join(HELD_LATER_MATERIAL))?;
    let held_section = first_file_chart_line(&held_material)?;
    let (held_current, held_witness) = transduce_source_neutral_exterior(
        &child,
        "uar3/held-later/docs/canon/TABLET_THE_UNIVERSALITY_MACHINE.md:0..first-line",
        held_section,
    )?;
    drop(held_material);
    drop(held_witness);
    let held_later_current_identity_sha256 = held_current.identity_sha256.clone();
    let mut resident = child.mount_resident()?;
    let child_section = resident.condition_native(&held_current)?;
    let child = resident.into_rest();
    eprintln!(
        "uar3-d3-radical child-conduct {}ms",
        started.elapsed().as_millis()
    );

    let ablation = child.withdraw_radical_direction(
        &selected_reconstruction_fibre_address,
        moved_radical_basis_position,
    )?;
    let preservation = ablation.preserve_native_radiation(&held_current, &child_section)?;
    let restored = ablation.restore()?;
    let exact_restoration_identity_sha256 = restored.identity().to_owned();
    let exact_restoration_recovers_child =
        exact_restoration_identity_sha256 == child_rest_identity_sha256;
    eprintln!(
        "uar3-d3-radical restored {}ms",
        started.elapsed().as_millis()
    );

    drop(restored);
    let stage = Uar3D3RadicalChildStage {
        schema: "soma-life.uar3-d3-radical-child-stage.v1".to_owned(),
        child_rest_identity_sha256,
        held_later_current_identity_sha256,
        child_native_section_identity_sha256: child_section.native_section_identity_sha256.clone(),
        child_ingress_current_identity_sha256: child_section
            .ingress_current_identity_sha256
            .clone(),
        child_native_consequence: native_consequence_value(&child_section),
        child_complete_section: serde_json::to_value(&child_section)?,
        selected_reconstruction_fibre_address,
        admitted_radical_population,
        moved_radical_basis_position,
        ablated_body_identity_sha256: preservation.ablated_body_identity_sha256.clone(),
        conduct_constitution_before_sha256: preservation.conduct_constitution_before_sha256.clone(),
        conduct_constitution_after_sha256: preservation.conduct_constitution_after_sha256.clone(),
        same_native_radiation_constitution: preservation.same_native_radiation_constitution,
        withdrawn_direction_in_receiver_radical: preservation
            .withdrawn_direction_in_receiver_radical,
        returned_covector_preserved: preservation.returned_covector_preserved,
        child_receiver_consequence_identity_sha256: preservation
            .child_receiver_consequence_identity_sha256
            .clone(),
        preserved_receiver_consequence_identity_sha256: preservation
            .preserved_receiver_consequence_identity_sha256
            .clone(),
        exact_restoration_identity_sha256,
        exact_restoration_recovers_child,
        source_codec_consulted: child_section.source_codec_consulted
            || preservation.source_codec_consulted,
        exterior_reconstruction_fibre_reachable: child_section
            .exterior_reconstruction_fibre_reachable
            || preservation.exterior_reconstruction_fibre_reachable,
    };
    fs::write(
        output.join("uar3-d3-radical-preservation-receipt.json"),
        serde_json::to_vec_pretty(&preservation)?,
    )?;
    fs::write(output.join(CHILD_STAGE), serde_json::to_vec_pretty(&stage)?)?;
    if stage.schema != "soma-life.uar3-d3-radical-child-stage.v1"
        || !stage.same_native_radiation_constitution
        || !stage.withdrawn_direction_in_receiver_radical
        || !stage.returned_covector_preserved
        || stage.child_receiver_consequence_identity_sha256
            != stage.preserved_receiver_consequence_identity_sha256
        || !stage.exact_restoration_recovers_child
        || stage.source_codec_consulted
        || stage.exterior_reconstruction_fibre_reachable
    {
        return Err("the UAR3-D3 support-disjoint child stage failed".into());
    }
    println!("{}", stage.child_rest_identity_sha256);
    Ok(())
}

fn verify_existing_restoration(root: &PathBuf, output: &PathBuf) -> Result<(), Box<dyn Error>> {
    let started = Instant::now();
    let stage: Uar3D3RadicalChildStage =
        serde_json::from_slice(&fs::read(output.join(CHILD_STAGE))?)?;
    if stage.schema != "soma-life.uar3-d3-radical-child-stage.v1"
        || !stage.same_native_radiation_constitution
        || !stage.withdrawn_direction_in_receiver_radical
        || !stage.returned_covector_preserved
        || stage.child_receiver_consequence_identity_sha256
            != stage.preserved_receiver_consequence_identity_sha256
        || !stage.exact_restoration_recovers_child
        || stage.source_codec_consulted
        || stage.exterior_reconstruction_fibre_reachable
    {
        return Err("the detached UAR3-D3 verifier received an invalid radical stage".into());
    }
    let restored = SourceNeutralEcologyRest::read(&fs::read(root.join(CHILD))?)?;
    if restored.identity() != stage.exact_restoration_identity_sha256
        || restored.identity() != stage.child_rest_identity_sha256
    {
        return Err("the detached radical verifier received a different restored child".into());
    }
    eprintln!(
        "uar3-d3-radical-verify restored {}ms",
        started.elapsed().as_millis()
    );

    let held_material = fs::read(root.join(HELD_LATER_MATERIAL))?;
    let held_section = first_file_chart_line(&held_material)?;
    let (held_current, held_witness) = transduce_source_neutral_exterior(
        &restored,
        "uar3/held-later/docs/canon/TABLET_THE_UNIVERSALITY_MACHINE.md:0..first-line",
        held_section,
    )?;
    drop(held_material);
    drop(held_witness);
    if held_current.identity_sha256 != stage.held_later_current_identity_sha256 {
        return Err("the held-later current changed across the radical process boundary".into());
    }
    let mut restored_resident = restored.mount_resident()?;
    let restored_section = restored_resident.condition_native(&held_current)?;
    eprintln!(
        "uar3-d3-radical-verify rerun {}ms",
        started.elapsed().as_millis()
    );
    let restored_complete_section = serde_json::to_value(&restored_section)?;
    let restored_conduct_exactly_equals_child_conduct =
        stable_native_consequence_value(&restored_complete_section)
            == stable_native_consequence_value(&stage.child_complete_section);
    let complete_apparatus_testimony_equal =
        restored_complete_section == stage.child_complete_section;
    let audit = Uar3D3RadicalAudit {
        truth_status: "implemented-exact; measured",
        child_rest_identity_sha256: stage.child_rest_identity_sha256,
        held_later_current_identity_sha256: stage.held_later_current_identity_sha256,
        child_native_section_identity_sha256: stage.child_native_section_identity_sha256,
        selected_reconstruction_fibre_address: stage.selected_reconstruction_fibre_address,
        admitted_radical_population: stage.admitted_radical_population,
        moved_radical_basis_position: stage.moved_radical_basis_position,
        ablated_body_identity_sha256: stage.ablated_body_identity_sha256,
        conduct_constitution_before_sha256: stage.conduct_constitution_before_sha256,
        conduct_constitution_after_sha256: stage.conduct_constitution_after_sha256,
        same_native_radiation_constitution: stage.same_native_radiation_constitution,
        withdrawn_direction_in_receiver_radical: stage.withdrawn_direction_in_receiver_radical,
        returned_covector_preserved: stage.returned_covector_preserved,
        child_receiver_consequence_identity_sha256: stage
            .child_receiver_consequence_identity_sha256,
        preserved_receiver_consequence_identity_sha256: stage
            .preserved_receiver_consequence_identity_sha256,
        exact_restoration_identity_sha256: stage.exact_restoration_identity_sha256,
        exact_restoration_recovers_child: stage.exact_restoration_recovers_child,
        restored_native_section_identity_sha256: restored_section
            .native_section_identity_sha256
            .clone(),
        restored_conduct_exactly_equals_child_conduct,
        complete_apparatus_testimony_equal,
        source_codec_consulted: stage.source_codec_consulted
            || restored_section.source_codec_consulted,
        exterior_reconstruction_fibre_reachable: stage.exterior_reconstruction_fibre_reachable
            || restored_section.exterior_reconstruction_fibre_reachable,
    };
    if !audit.same_native_radiation_constitution
        || !audit.withdrawn_direction_in_receiver_radical
        || !audit.returned_covector_preserved
        || audit.child_receiver_consequence_identity_sha256
            != audit.preserved_receiver_consequence_identity_sha256
        || !audit.exact_restoration_recovers_child
        || !audit.restored_conduct_exactly_equals_child_conduct
        || audit.source_codec_consulted
        || audit.exterior_reconstruction_fibre_reachable
    {
        return Err("the UAR3-D3 support-disjoint/restoration gate failed".into());
    }
    fs::write(
        output.join("uar3-d3-radical-audit.json"),
        serde_json::to_vec_pretty(&audit)?,
    )?;
    println!("{}", audit.child_rest_identity_sha256);
    Ok(())
}

fn native_consequence_value(
    section: &life::native_intelligence::SourceNeutralResidentRadiationSection,
) -> Value {
    serde_json::json!({
        "ingress_current_identity_sha256": section.ingress_current_identity_sha256,
        "entered_octet_population": section.entered_octet_population,
        "crossed_structural_ports": section.crossed_structural_ports,
        "boundary_front": section.boundary_front,
        "branches": section.branches,
        "phase_front_higher_faces": section.phase_front_higher_faces,
        "phase_front_ports": section.phase_front_ports,
        "situated_receiver_higher_faces": section.situated_receiver_higher_faces,
        "situated_receiver_ports": section.situated_receiver_ports,
        "complete_successor_addressed_faces": section.complete_successor_addressed_faces,
        "complete_successor_zero_face_population": section.complete_successor_zero_face_population,
        "radiation": section.radiation,
        "reconstruction_dag": section.reconstruction_dag,
        "source_codec_consulted": section.source_codec_consulted,
        "exterior_reconstruction_fibre_reachable": section.exterior_reconstruction_fibre_reachable,
        "invariant_transport_reuploaded": section.invariant_transport_reuploaded,
        "cpu_semantic_replay_after_device": section.cpu_semantic_replay_after_device,
    })
}

/// Reproduce `SourceNeutralResidentRadiationSection::same_native_receiver_consequence` over a
/// sealed JSON face.  This excludes CUDA context handles, launch/synchronization counts, transfer
/// quantities, and other remount apparatus while retaining every causal coordinate named by the
/// native-section identity.
fn stable_native_consequence_value(section: &Value) -> Value {
    let at = |pointer: &str| section.pointer(pointer).cloned().unwrap_or(Value::Null);
    serde_json::json!({
        "schema": at("/schema"),
        "rest_identity_sha256": at("/rest_identity_sha256"),
        "ingress_current_identity_sha256": at("/ingress_current_identity_sha256"),
        "entered_octet_population": at("/entered_octet_population"),
        "crossed_structural_ports": at("/crossed_structural_ports"),
        "boundary_front": at("/boundary_front"),
        "branches": at("/branches"),
        "phase_front_higher_faces": at("/phase_front_higher_faces"),
        "phase_front_ports": at("/phase_front_ports"),
        "situated_receiver_higher_faces": at("/situated_receiver_higher_faces"),
        "situated_receiver_ports": at("/situated_receiver_ports"),
        "complete_successor_addressed_faces": at("/complete_successor_addressed_faces"),
        "complete_successor_zero_face_population": at("/complete_successor_zero_face_population"),
        "conditioned_current_passage": at("/radiation/conditioned_current/passage"),
        "receiver_coordinate_denominator": at("/radiation/receiver_coordinate_denominator"),
        "ports": at("/radiation/ports"),
        "port_returns": at("/radiation/port_returns"),
        "entering_current": at("/radiation/entering_current"),
        "total_returned_current": at("/radiation/total_returned_current"),
        "stored_difference": at("/radiation/stored_difference"),
        "local_balance_closes": at("/radiation/local_balance_closes"),
        "phase_locked_port_population": at("/radiation/phase_locked_port_population"),
        "phase_front_is_unique": at("/radiation/phase_front_is_unique"),
        "situated_receiver_pairing": at("/radiation/situated_receiver_pairing"),
        "complete_successor_faces": at("/radiation/complete_successor_faces"),
        "complete_successor_face_population": at("/radiation/complete_successor_face_population"),
        "active_factor_population": at("/radiation/active_factor_population"),
        "native_factor_population": at("/radiation/native_factor_population"),
        "moment_field_materialized": at("/radiation/moment_field_materialized"),
        "moment_factorization_retained": at("/radiation/moment_factorization_retained"),
        "context_population": at("/radiation/context_population"),
        "restriction_population": at("/radiation/restriction_population"),
        "generator_population": at("/radiation/generator_population"),
        "reconstruction_dag": at("/reconstruction_dag"),
        "native_section_identity_sha256": at("/native_section_identity_sha256"),
        "source_codec_consulted": at("/source_codec_consulted"),
        "exterior_reconstruction_fibre_reachable": at("/exterior_reconstruction_fibre_reachable"),
        "invariant_transport_reuploaded": at("/invariant_transport_reuploaded"),
        "cpu_semantic_replay_after_device": at("/cpu_semantic_replay_after_device"),
    })
}

fn first_file_chart_line(bytes: &[u8]) -> Result<&[u8], Box<dyn Error>> {
    let byte_end = bytes
        .iter()
        .position(|octet| *octet == b'\n')
        .map(|at| at + 1)
        .unwrap_or(bytes.len());
    if byte_end == 0 {
        return Err("the held-later file chart has no first section".into());
    }
    Ok(&bytes[..byte_end])
}

fn repository_root() -> Result<PathBuf, Box<dyn Error>> {
    let mut root = std::env::current_dir()?;
    while !root.join("Cargo.toml").is_file() || !root.join("docs/plans/THE_ROADMAP.md").is_file() {
        if !root.pop() {
            return Err("repository root was not found".into());
        }
    }
    Ok(root)
}
