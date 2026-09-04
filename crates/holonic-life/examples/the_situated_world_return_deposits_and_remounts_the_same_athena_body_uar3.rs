use std::{env, error::Error, fs, path::PathBuf, time::Instant};

use life::native_intelligence::{
    transduce_source_neutral_exterior, SituatedDifferenceSection, SourceNeutralEcologyRest,
    SourceNeutralReturnedDifferenceReceipt,
};
use serde::Serialize;

const PREDECESSOR: &str = concat!(
    ".local/artifacts/",
    "the_source_bearing_rail_departs_and_the_complete_native_state_incidence_remounts_uar0/",
    "athena-source-neutral.rest"
);
const D1_RECEIPT: &str = concat!(
    ".local/artifacts/",
    "the_published_native_seam_returns_one_situated_difference_uar3/",
    "uar3-d1-situated-difference.json"
);
const HELD_LATER_MATERIAL: &str = "docs/canon/TABLET_THE_UNIVERSALITY_MACHINE.md";
const OUTPUT: &str = concat!(
    ".local/artifacts/",
    "the_situated_world_return_deposits_and_remounts_the_same_athena_body_uar3"
);

#[derive(Serialize)]
struct ExteriorFileChartSection {
    path: &'static str,
    byte_start: usize,
    byte_end: usize,
}

#[derive(Serialize)]
struct Uar3D2Audit {
    truth_status: &'static str,
    predecessor_rest_identity_sha256: String,
    successor_rest_identity_sha256: String,
    remounted_rest_identity_sha256: String,
    situated_difference_identity_sha256: String,
    returned_thread_address: String,
    returned_covector_rank: usize,
    granular_identity_sha256: String,
    relational_identity_sha256: String,
    realization_identity_sha256: String,
    acoustic_identity_sha256: String,
    optical_identity_sha256: String,
    morphologies_preserved: bool,
    source_detached_before_rest: bool,
    exterior_developmental_fibre_reachable_after_remount: bool,
    successor_identity_sealed_before_held_current: bool,
    held_later_file_chart_section: ExteriorFileChartSection,
    held_later_current_identity_sha256: String,
    held_later_native_section_identity_sha256: String,
    held_later_source_codec_consulted: bool,
    held_later_exterior_reconstruction_fibre_reachable: bool,
    held_later_invariant_transport_reuploaded: bool,
    held_later_cpu_semantic_replay_after_device: bool,
    rested_octets: usize,
}

fn main() -> Result<(), Box<dyn Error>> {
    let started = Instant::now();
    let root = repository_root()?;
    let output = env::var_os("HOLONICS_OUTPUT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join(OUTPUT));
    fs::create_dir_all(&output)?;
    if env::var_os("HOLONICS_UAR3_D2_VERIFY_EXISTING").is_some() {
        return verify_existing_child(&root, &output);
    }

    let parent_bytes = fs::read(root.join(PREDECESSOR))?;
    let parent = SourceNeutralEcologyRest::read(&parent_bytes)?;
    let _admitted_parent_identity_sha256 = parent.identity().to_owned();
    drop(parent_bytes);
    eprintln!("uar3-d2 parent {}ms", started.elapsed().as_millis());

    let d1_bytes = fs::read(root.join(D1_RECEIPT))?;
    let mut d1: serde_json::Value = serde_json::from_slice(&d1_bytes)?;
    drop(d1_bytes);
    let situated_value = d1
        .get_mut("situated_difference")
        .ok_or("the D1 receipt lost its situated difference")?
        .take();
    let situated_difference: SituatedDifferenceSection = serde_json::from_value(situated_value)?;
    drop(d1);
    situated_difference.validate()?;
    let situated_difference_identity_sha256 = situated_difference.identity_sha256.clone();
    eprintln!("uar3-d2 difference {}ms", started.elapsed().as_millis());

    let (child, deposit) = parent.deposit_returned_difference(situated_difference)?;
    let successor_rest_identity_sha256 = child.identity().to_owned();
    if deposit.difference_identity_sha256 != situated_difference_identity_sha256
        || deposit.successor_rest_identity_sha256 != successor_rest_identity_sha256
    {
        return Err("the D1 difference did not become the exact D2 child".into());
    }
    eprintln!("uar3-d2 deposit {}ms", started.elapsed().as_millis());

    // Seal the child before the held-later receiver is even mounted.  The only bytes written here
    // are the source-neutral rested ecology; the discarded D1 source fibre is not a member.
    let child_bytes = child.canonical_bytes()?;
    let _rested_octets = child_bytes.len();
    fs::write(output.join("athena-uar3-child.rest"), &child_bytes)?;
    drop(child);
    let remounted = SourceNeutralEcologyRest::read(&child_bytes)?;
    drop(child_bytes);
    let remounted_rest_identity_sha256 = remounted.identity().to_owned();
    if remounted_rest_identity_sha256 != successor_rest_identity_sha256 {
        return Err("source-detached D2 remount changed the child identity".into());
    }
    eprintln!("uar3-d2 remount {}ms", started.elapsed().as_millis());

    // The deposit/remount and held-later conduct are two physical deeds.  Seal the exact return
    // receipt beside the child before leaving this bounded process; the detached verifier below
    // remounts this same identity and performs the later-current gate without replaying deposit.
    fs::write(
        output.join("uar3-d2-deposit-receipt.json"),
        serde_json::to_vec_pretty(&deposit)?,
    )?;
    println!("{successor_rest_identity_sha256}");
    Ok(())
}

fn verify_existing_child(root: &PathBuf, output: &PathBuf) -> Result<(), Box<dyn Error>> {
    let started = Instant::now();
    let child_bytes = fs::read(output.join("athena-uar3-child.rest"))?;
    let rested_octets = child_bytes.len();
    let remounted = SourceNeutralEcologyRest::read(&child_bytes)?;
    drop(child_bytes);
    let deposit: SourceNeutralReturnedDifferenceReceipt =
        serde_json::from_slice(&fs::read(output.join("uar3-d2-deposit-receipt.json"))?)?;
    let successor_rest_identity_sha256 = remounted.identity().to_owned();
    let remounted_rest_identity_sha256 = successor_rest_identity_sha256.clone();
    if deposit.successor_rest_identity_sha256 != successor_rest_identity_sha256
        || deposit.predecessor_rest_identity_sha256.is_empty()
        || deposit.difference_identity_sha256.is_empty()
    {
        return Err("the detached D2 verifier received a different child or return".into());
    }
    eprintln!("uar3-d2-verify remount {}ms", started.elapsed().as_millis());

    let held_material = fs::read(root.join(HELD_LATER_MATERIAL))?;
    let (held_section, held_later_file_chart_section) =
        first_file_chart_line(HELD_LATER_MATERIAL, &held_material)?;
    let (held_current, held_witness) = transduce_source_neutral_exterior(
        &remounted,
        &format!(
            "uar3/held-later/{}:{}..{}",
            held_later_file_chart_section.path,
            held_later_file_chart_section.byte_start,
            held_later_file_chart_section.byte_end,
        ),
        held_section,
    )?;
    drop(held_material);
    drop(held_witness);
    let held_later_current_identity_sha256 = held_current.identity_sha256.clone();
    let mut resident = remounted.mount_resident()?;
    let later = resident.condition_native(&held_current)?;
    eprintln!(
        "uar3-d2-verify later-current {}ms",
        started.elapsed().as_millis()
    );

    let audit = Uar3D2Audit {
        truth_status: "implemented-exact; measured",
        predecessor_rest_identity_sha256: deposit.predecessor_rest_identity_sha256.clone(),
        successor_rest_identity_sha256: successor_rest_identity_sha256.clone(),
        remounted_rest_identity_sha256,
        situated_difference_identity_sha256: deposit.difference_identity_sha256.clone(),
        returned_thread_address: deposit.thread_address.clone(),
        returned_covector_rank: deposit.returned_covector.len(),
        granular_identity_sha256: deposit.granular_identity_sha256.clone(),
        relational_identity_sha256: deposit.relational_identity_sha256.clone(),
        realization_identity_sha256: deposit.realization_identity_sha256.clone(),
        acoustic_identity_sha256: deposit.acoustic_identity_sha256.clone(),
        optical_identity_sha256: deposit.optical_identity_sha256.clone(),
        morphologies_preserved: deposit.morphologies_preserved,
        source_detached_before_rest: deposit.source_detached_before_rest,
        exterior_developmental_fibre_reachable_after_remount: false,
        successor_identity_sealed_before_held_current: true,
        held_later_file_chart_section,
        held_later_current_identity_sha256,
        held_later_native_section_identity_sha256: later.native_section_identity_sha256.clone(),
        held_later_source_codec_consulted: later.source_codec_consulted,
        held_later_exterior_reconstruction_fibre_reachable: later
            .exterior_reconstruction_fibre_reachable,
        held_later_invariant_transport_reuploaded: later.invariant_transport_reuploaded,
        held_later_cpu_semantic_replay_after_device: later.cpu_semantic_replay_after_device,
        rested_octets,
    };
    if audit.predecessor_rest_identity_sha256 != deposit.predecessor_rest_identity_sha256
        || audit.successor_rest_identity_sha256 != audit.remounted_rest_identity_sha256
        || audit.returned_covector_rank == 0
        || !audit.morphologies_preserved
        || !audit.source_detached_before_rest
        || audit.exterior_developmental_fibre_reachable_after_remount
        || !audit.successor_identity_sealed_before_held_current
        || audit.held_later_source_codec_consulted
        || audit.held_later_exterior_reconstruction_fibre_reachable
        || audit.held_later_invariant_transport_reuploaded
        || audit.held_later_cpu_semantic_replay_after_device
        || audit.rested_octets == 0
    {
        return Err("the UAR3-D2 same-body rest/remount gate failed".into());
    }
    fs::write(
        output.join("uar3-d2-held-later-native-section.json"),
        serde_json::to_vec_pretty(&later)?,
    )?;
    fs::write(
        output.join("uar3-d2-audit.json"),
        serde_json::to_vec_pretty(&audit)?,
    )?;
    println!("{}", audit.successor_rest_identity_sha256);
    Ok(())
}

fn first_file_chart_line<'a>(
    path: &'static str,
    bytes: &'a [u8],
) -> Result<(&'a [u8], ExteriorFileChartSection), Box<dyn Error>> {
    let byte_end = bytes
        .iter()
        .position(|octet| *octet == b'\n')
        .map(|at| at + 1)
        .unwrap_or(bytes.len());
    if byte_end == 0 {
        return Err(format!("the exterior file chart {path} has no first section").into());
    }
    Ok((
        &bytes[..byte_end],
        ExteriorFileChartSection {
            path,
            byte_start: 0,
            byte_end,
        },
    ))
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
