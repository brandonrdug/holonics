use std::{collections::BTreeSet, env, error::Error, fs, path::PathBuf, time::Instant};

use life::native_intelligence::{transduce_source_neutral_exterior, SourceNeutralEcologyRest};
use serde::{Deserialize, Serialize};
use serde_json::Value;

const PARENT_AUDIT: &str = concat!(
    ".local/artifacts/",
    "the_source_bearing_rail_departs_and_the_complete_native_state_incidence_remounts_uar0/",
    "source-absence-and-detached-remount-audit.json"
);
const CHILD: &str = concat!(
    ".local/artifacts/",
    "the_situated_world_return_deposits_and_remounts_the_same_athena_body_uar3/",
    "athena-uar3-child.rest"
);
const HELD_LATER_MATERIAL: &str = "docs/canon/TABLET_THE_UNIVERSALITY_MACHINE.md";
const OUTPUT: &str = concat!(
    ".local/artifacts/",
    "the_returned_difference_separates_later_conduct_and_withdraws_exactly_uar3"
);
const PARENT_STAGE: &str = "uar3-d3-targeted-parent-stage.json";

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Uar3D3TargetedParentStage {
    schema: String,
    parent_rest_identity_sha256: String,
    child_rest_identity_sha256: String,
    held_later_current_identity_sha256: String,
    parent_native_section_identity_sha256: String,
    parent_ingress_current_identity_sha256: String,
    parent_native_consequence: Value,
    targeted_withdrawal_predecessor_identity_sha256: String,
    targeted_withdrawal_recovers_exact_parent: bool,
    targeted_restoration_successor_identity_sha256: String,
    targeted_restoration_recovers_exact_child: bool,
    source_codec_consulted: bool,
    exterior_reconstruction_fibre_reachable: bool,
}

#[derive(Serialize)]
struct Uar3D3TargetedAudit {
    truth_status: &'static str,
    parent_rest_identity_sha256: String,
    child_rest_identity_sha256: String,
    held_later_current_identity_sha256: String,
    parent_native_section_identity_sha256: String,
    child_native_section_identity_sha256: String,
    same_held_later_current: bool,
    non_lineage_separator_path: String,
    parent_separator_face: Value,
    child_separator_face: Value,
    targeted_withdrawal_predecessor_identity_sha256: String,
    targeted_withdrawal_recovers_exact_parent: bool,
    targeted_restoration_successor_identity_sha256: String,
    targeted_restoration_recovers_exact_child: bool,
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
        return verify_existing_child(&root, &output);
    }

    let parent_audit: Value = serde_json::from_slice(&fs::read(root.join(PARENT_AUDIT))?)?;
    let admitted_parent_identity_sha256 = parent_audit
        .get("successor_identity_sha256")
        .and_then(Value::as_str)
        .ok_or("the UAR0 audit lost its successor identity")?
        .to_owned();
    let child = SourceNeutralEcologyRest::read(&fs::read(root.join(CHILD))?)?;
    let child_rest_identity_sha256 = child.identity().to_owned();
    let (parent, targeted_withdrawal) = child.withdraw_latest_returned_difference()?;
    let parent_rest_identity_sha256 = parent.identity().to_owned();
    let targeted_withdrawal_predecessor_identity_sha256 = parent_rest_identity_sha256.clone();
    let targeted_withdrawal_recovers_exact_parent =
        targeted_withdrawal_predecessor_identity_sha256 == admitted_parent_identity_sha256;
    eprintln!("uar3-d3-targeted rests {}ms", started.elapsed().as_millis());

    let held_material = fs::read(root.join(HELD_LATER_MATERIAL))?;
    let held_section = first_file_chart_line(&held_material)?;
    let (held_current, held_witness) = transduce_source_neutral_exterior(
        &parent,
        "uar3/held-later/docs/canon/TABLET_THE_UNIVERSALITY_MACHINE.md:0..first-line",
        held_section,
    )?;
    drop(held_material);
    drop(held_witness);
    let held_later_current_identity_sha256 = held_current.identity_sha256.clone();

    let mut parent_resident = parent.mount_resident()?;
    let parent_section = parent_resident.condition_native(&held_current)?;
    let parent = parent_resident.into_rest();
    eprintln!(
        "uar3-d3-targeted parent-conduct {}ms",
        started.elapsed().as_millis()
    );

    let child = SourceNeutralEcologyRest::restore_returned_difference(parent, targeted_withdrawal)?;
    let targeted_restoration_successor_identity_sha256 = child.identity().to_owned();
    let targeted_restoration_recovers_exact_child =
        targeted_restoration_successor_identity_sha256 == child_rest_identity_sha256;
    let stage = Uar3D3TargetedParentStage {
        schema: "soma-life.uar3-d3-targeted-parent-stage.v1".to_owned(),
        parent_rest_identity_sha256,
        child_rest_identity_sha256,
        held_later_current_identity_sha256,
        parent_native_section_identity_sha256: parent_section
            .native_section_identity_sha256
            .clone(),
        parent_ingress_current_identity_sha256: parent_section
            .ingress_current_identity_sha256
            .clone(),
        parent_native_consequence: native_consequence_value(&parent_section)?,
        targeted_withdrawal_predecessor_identity_sha256,
        targeted_withdrawal_recovers_exact_parent,
        targeted_restoration_successor_identity_sha256,
        targeted_restoration_recovers_exact_child,
        source_codec_consulted: parent_section.source_codec_consulted,
        exterior_reconstruction_fibre_reachable: parent_section
            .exterior_reconstruction_fibre_reachable,
    };
    if stage.schema != "soma-life.uar3-d3-targeted-parent-stage.v1"
        || !stage.targeted_withdrawal_recovers_exact_parent
        || !stage.targeted_restoration_recovers_exact_child
        || stage.source_codec_consulted
        || stage.exterior_reconstruction_fibre_reachable
    {
        return Err("the UAR3-D3 targeted parent stage failed".into());
    }
    fs::write(
        output.join(PARENT_STAGE),
        serde_json::to_vec_pretty(&stage)?,
    )?;
    println!("{}", stage.child_rest_identity_sha256);
    Ok(())
}

fn verify_existing_child(root: &PathBuf, output: &PathBuf) -> Result<(), Box<dyn Error>> {
    let started = Instant::now();
    let stage: Uar3D3TargetedParentStage =
        serde_json::from_slice(&fs::read(output.join(PARENT_STAGE))?)?;
    if stage.schema != "soma-life.uar3-d3-targeted-parent-stage.v1"
        || !stage.targeted_withdrawal_recovers_exact_parent
        || !stage.targeted_restoration_recovers_exact_child
        || stage.source_codec_consulted
        || stage.exterior_reconstruction_fibre_reachable
    {
        return Err("the detached UAR3-D3 verifier received an invalid parent stage".into());
    }
    let child = SourceNeutralEcologyRest::read(&fs::read(root.join(CHILD))?)?;
    if child.identity() != stage.child_rest_identity_sha256 {
        return Err("the detached UAR3-D3 verifier received a different child".into());
    }
    eprintln!(
        "uar3-d3-targeted-verify child {}ms",
        started.elapsed().as_millis()
    );

    let held_material = fs::read(root.join(HELD_LATER_MATERIAL))?;
    let held_section = first_file_chart_line(&held_material)?;
    let (held_current, held_witness) = transduce_source_neutral_exterior(
        &child,
        "uar3/held-later/docs/canon/TABLET_THE_UNIVERSALITY_MACHINE.md:0..first-line",
        held_section,
    )?;
    drop(held_material);
    drop(held_witness);
    if held_current.identity_sha256 != stage.held_later_current_identity_sha256 {
        return Err("the held-later current changed across the D3 process boundary".into());
    }
    let mut child_resident = child.mount_resident()?;
    let child_section = child_resident.condition_native(&held_current)?;
    eprintln!(
        "uar3-d3-targeted-verify child-conduct {}ms",
        started.elapsed().as_millis()
    );

    let child_consequence = native_consequence_value(&child_section)?;
    let (non_lineage_separator_path, parent_separator_face, child_separator_face) =
        first_leaf_difference(&stage.parent_native_consequence, &child_consequence, "")
            .ok_or("the returned difference did not separate the held later native consequence")?;
    let audit = Uar3D3TargetedAudit {
        truth_status: "implemented-exact; measured",
        parent_rest_identity_sha256: stage.parent_rest_identity_sha256,
        child_rest_identity_sha256: stage.child_rest_identity_sha256,
        held_later_current_identity_sha256: stage.held_later_current_identity_sha256,
        parent_native_section_identity_sha256: stage.parent_native_section_identity_sha256,
        child_native_section_identity_sha256: child_section.native_section_identity_sha256.clone(),
        same_held_later_current: stage.parent_ingress_current_identity_sha256
            == child_section.ingress_current_identity_sha256,
        non_lineage_separator_path,
        parent_separator_face,
        child_separator_face,
        targeted_withdrawal_predecessor_identity_sha256: stage
            .targeted_withdrawal_predecessor_identity_sha256,
        targeted_withdrawal_recovers_exact_parent: stage.targeted_withdrawal_recovers_exact_parent,
        targeted_restoration_successor_identity_sha256: stage
            .targeted_restoration_successor_identity_sha256,
        targeted_restoration_recovers_exact_child: stage.targeted_restoration_recovers_exact_child,
        source_codec_consulted: stage.source_codec_consulted
            || child_section.source_codec_consulted,
        exterior_reconstruction_fibre_reachable: stage.exterior_reconstruction_fibre_reachable
            || child_section.exterior_reconstruction_fibre_reachable,
    };
    if !audit.same_held_later_current
        || audit.non_lineage_separator_path.is_empty()
        || !audit.targeted_withdrawal_recovers_exact_parent
        || !audit.targeted_restoration_recovers_exact_child
        || audit.source_codec_consulted
        || audit.exterior_reconstruction_fibre_reachable
    {
        return Err("the UAR3-D3 targeted attribution gate failed".into());
    }
    fs::write(
        output.join("uar3-d3-targeted-audit.json"),
        serde_json::to_vec_pretty(&audit)?,
    )?;
    println!("{}", audit.child_rest_identity_sha256);
    Ok(())
}

fn native_consequence_value(
    section: &life::native_intelligence::SourceNeutralResidentRadiationSection,
) -> Result<Value, Box<dyn Error>> {
    Ok(serde_json::json!({
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
    }))
}

fn first_leaf_difference(
    left: &Value,
    right: &Value,
    path: &str,
) -> Option<(String, Value, Value)> {
    if left == right {
        return None;
    }
    match (left, right) {
        (Value::Object(left), Value::Object(right)) => {
            let keys = left.keys().chain(right.keys()).collect::<BTreeSet<_>>();
            for key in keys {
                let next = format!("{path}/{}", key.replace('~', "~0").replace('/', "~1"));
                match (left.get(key), right.get(key)) {
                    (Some(left), Some(right)) => {
                        if let Some(found) = first_leaf_difference(left, right, &next) {
                            return Some(found);
                        }
                    }
                    (left, right) => {
                        return Some((
                            next,
                            left.cloned().unwrap_or(Value::Null),
                            right.cloned().unwrap_or(Value::Null),
                        ));
                    }
                }
            }
            None
        }
        (Value::Array(left), Value::Array(right)) => {
            let population = left.len().max(right.len());
            for at in 0..population {
                let next = format!("{path}/{at}");
                match (left.get(at), right.get(at)) {
                    (Some(left), Some(right)) => {
                        if let Some(found) = first_leaf_difference(left, right, &next) {
                            return Some(found);
                        }
                    }
                    (left, right) => {
                        return Some((
                            next,
                            left.cloned().unwrap_or(Value::Null),
                            right.cloned().unwrap_or(Value::Null),
                        ));
                    }
                }
            }
            None
        }
        _ => Some((path.to_owned(), left.clone(), right.clone())),
    }
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
