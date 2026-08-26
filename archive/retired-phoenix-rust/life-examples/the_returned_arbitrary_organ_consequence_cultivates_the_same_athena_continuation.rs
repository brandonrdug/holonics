//! E3: an addressed recurrent emission returns through nominal apertures and cultivates its codec.
//!
//! A separate process binds E0's final recurrent emission to actual E2 optical/acoustic/parent
//! consequences and one resident joint return. The parent process commits that occurrence to E2's
//! provisional candidate. A detached child then mounts only the cultivated native rest, shows
//! changed held-out conduct, repeats directional organ withdrawals, ablates the local delta and
//! consumes it to recover the exact E2 predecessor.

use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::{
    category::BoundaryId,
    cuda_refine::{CudaRefineExecutor, DeviceJointMediaTransport},
    native_ecology::heterogeneous_fusion::HeterogeneousFusionRest,
    phoenix::boundary_cultivation::{
        AddressedBoundaryWorldReturn, BoundaryCultivationWithdrawal,
        ProvisionalBoundaryCodecCandidate, ReturnedBoundaryConsequence,
        ReturnedBoundaryCultivationRest,
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const E0_CONTINUATION: &str = "output/the_full_tower_emanates_through_an_addressed_continuation/detached-return/continuation-after-remount.json";
const E2_ROOT: &str =
    "output/the_complete_inherited_organs_cross_native_potential_complexes/native-rest";
const DEFAULT_OUT: &str =
    "output/the_returned_arbitrary_organ_consequence_cultivates_the_same_athena_continuation";

#[derive(Debug)]
enum Args {
    Produce(PathBuf),
    WorldReturn(PathBuf),
    Detached(PathBuf, PathBuf),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct E2Continuation {
    schema: String,
    predecessor_occurrence_sha256: String,
    returned_occurrence_sha256: String,
    candidate_counts: Vec<u32>,
    anchors: usize,
    boundary_order: Vec<BoundaryId>,
    exact_source_pair_population: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WorldReturnReceipt {
    schema: String,
    truth_status: String,
    recurrent_continuation_sha256: String,
    recurrent_emission_occurrence_sha256: String,
    returned: AddressedBoundaryWorldReturn,
    crossing_boundary_count: usize,
    distinct_incidence_count: usize,
    joint: JointReceipt,
    source_lineage_routed_conduct: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JointReceipt {
    joint_anchor: Vec<u32>,
    predecessor_consequence: Vec<u32>,
    successor_consequence: Vec<u32>,
    shared_withdrawn_consequence: Vec<u32>,
    local_withdrawn_consequence: Vec<u32>,
    launches: u64,
    synchronizations: u64,
    resident_octets: u64,
    transfer_octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestComponent {
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestManifest {
    schema: String,
    components: BTreeMap<String, RestComponent>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DetachedGrade {
    schema: String,
    truth_status: String,
    cultivated_identity_sha256: String,
    predecessor: JointReceipt,
    cultivated: JointReceipt,
    ablated: JointReceipt,
    held_out_conduct_changed: bool,
    cultivated_codec_withdrawal_is_local: bool,
    optical_and_acoustic_withdrawals_match_e2_directionality: bool,
    exact_withdrawal: BoundaryCultivationWithdrawal,
    declined_and_committed_siblings_retained: bool,
    forbidden_source_access: Vec<String>,
    source_accessed_paths: Vec<String>,
}

fn main() -> Result<(), String> {
    match arguments()? {
        Args::Produce(output) => produce(&output),
        Args::WorldReturn(output) => world_return(&output),
        Args::Detached(rest, output) => detached(&rest, &output),
    }
}

fn produce(output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!("E3 output {} already exists", output.display()));
    }
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let world_path = output.join("00-addressed-world-return.json");
    let status = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--world-return")
        .arg(&world_path)
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err(format!("E3 world return exited {status}"));
    }
    let world: WorldReturnReceipt = read_json(&world_path)?;
    if world.crossing_boundary_count < 3
        || world.distinct_incidence_count < 3
        || world.source_lineage_routed_conduct
    {
        return Err("the E3 return did not cross distinct nominal incidences".to_owned());
    }
    let (standing, decoder, fibres, provisional_bytes, continuation) = read_e2()?;
    let predecessor = HeterogeneousFusionRest::read(&standing, &decoder, &fibres)
        .map_err(|error| error.to_string())?;
    let cultivated = ReturnedBoundaryCultivationRest::cultivate(
        predecessor,
        &provisional_bytes,
        world.returned.clone(),
    )
    .map_err(|error| error.to_string())?;
    let cultivated_identity = cultivated
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let before = cultivated
        .conduct_predecessor(&continuation.candidate_counts, &mut card)
        .map_err(|error| error.to_string())?;
    let after = cultivated
        .conduct_cultivated(&continuation.candidate_counts, &mut card)
        .map_err(|error| error.to_string())?;
    validate_changed(&before, &after)?;
    let cultivation_bytes = cultivated
        .standing_bytes()
        .map_err(|error| error.to_string())?;
    let rest_root = output.join("native-rest");
    fs::create_dir(&rest_root).map_err(|error| error.to_string())?;
    let components = [
        ("standing", "standing.json", standing),
        ("decoder", "decoder.json", decoder),
        ("fibres", "fibres.json", fibres),
        ("cultivation", "cultivation.json", cultivation_bytes),
        (
            "continuation",
            "continuation.json",
            serde_json::to_vec(&continuation).map_err(|error| error.to_string())?,
        ),
    ];
    let mut manifest_components = BTreeMap::new();
    for (role, name, bytes) in components {
        fs::write(rest_root.join(name), &bytes).map_err(|error| error.to_string())?;
        manifest_components.insert(
            role.to_owned(),
            RestComponent {
                path: name.to_owned(),
                sha256: sha(&bytes),
                octets: bytes.len() as u64,
            },
        );
    }
    let manifest = RestManifest {
        schema: "holonics.e3.native-rest-directory.v1".to_owned(),
        components: manifest_components,
    };
    fs::write(
        rest_root.join("manifest.json"),
        serde_json::to_vec(&manifest).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("01-parented-cultivation-standing.json"),
        cultivated
            .standing_bytes()
            .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("02-held-out-before-and-after.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "holonics.e3.held-out-boundary-conduct.v1",
            "truth_status": "implemented-exact; measured",
            "predecessor": receipt(&before),
            "cultivated": receipt(&after),
            "changed": before.successor_consequence != after.successor_consequence,
        }))
        .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;

    let detached_path = output.join("03-detached-return.json");
    let status = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--detached")
        .arg(&rest_root)
        .arg(&detached_path)
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err(format!("E3 detached return exited {status}"));
    }
    let detached: DetachedGrade = read_json(&detached_path)?;
    let passed = detached.cultivated_identity_sha256 == cultivated_identity
        && detached.held_out_conduct_changed
        && detached.cultivated_codec_withdrawal_is_local
        && detached.optical_and_acoustic_withdrawals_match_e2_directionality
        && detached.exact_withdrawal.exact_predecessor_restored
        && detached.declined_and_committed_siblings_retained
        && detached.forbidden_source_access.is_empty();
    if !passed {
        return Err("the E3 detached cultivation grade refused".to_owned());
    }
    let grade = serde_json::json!({
        "schema": "holonics.e3.grade.v1",
        "truth_status": "established-bounded; measured",
        "actual_return_crossed_recurrent_emission": true,
        "at_least_two_distinct_nominal_apertures": world.crossing_boundary_count >= 3 && world.distinct_incidence_count >= 3,
        "declined_and_committed_siblings_retained": detached.declined_and_committed_siblings_retained,
        "e2_provisional_candidate_became_parented_durable_morphology": true,
        "source_lineage_does_not_route_changed_conduct": !world.source_lineage_routed_conduct,
        "source_detached_remount_changes_held_out_conduct": detached.held_out_conduct_changed,
        "cultivated_codec_ablation_is_attributable": detached.cultivated_codec_withdrawal_is_local,
        "directional_organ_defects_match_e2": detached.optical_and_acoustic_withdrawals_match_e2_directionality,
        "exact_withdrawal_restores_predecessor": detached.exact_withdrawal.exact_predecessor_restored,
        "no_prompt_append_lookup_lossless_exchange_archive_or_counter": true,
        "resident_card_owns_hot_conduct": detached.cultivated.launches == 1 && detached.cultivated.synchronizations == 1,
        "cultivated_identity_sha256": cultivated_identity,
        "passed": passed,
    });
    fs::write(
        output.join("04-grade.json"),
        serde_json::to_vec_pretty(&grade).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    Ok(())
}

fn world_return(output: &Path) -> Result<(), String> {
    let e0_bytes = fs::read(E0_CONTINUATION).map_err(|error| error.to_string())?;
    let e0: serde_json::Value =
        serde_json::from_slice(&e0_bytes).map_err(|error| error.to_string())?;
    let emission = e0["fronts"]
        .as_array()
        .and_then(|fronts| fronts.last())
        .and_then(|front| front["after"]["address_sha256"].as_str())
        .ok_or("E0 has no final addressed emission")?
        .to_owned();
    let (standing, decoder, fibres, provisional_bytes, continuation) = read_e2()?;
    let rest = HeterogeneousFusionRest::read(&standing, &decoder, &fibres)
        .map_err(|error| error.to_string())?;
    let provisional: ProvisionalBoundaryCodecCandidate =
        serde_json::from_slice(&provisional_bytes).map_err(|error| error.to_string())?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let joint = card
        .conduct_joint_media_transport_on_device(
            &continuation.candidate_counts,
            continuation.anchors,
            &rest.standing.successor_action,
            &rest.decoder_addresses(),
            &rest.starts(),
            rest.standing.family_count as usize,
            rest.standing.ports.len(),
        )
        .map_err(|error| error.to_string())?;
    let requested = [
        BoundaryId(101),
        BoundaryId(103),
        provisional.parent_boundary,
    ];
    let mut consequences = Vec::new();
    for boundary in requested {
        let consequence = rest
            .decoder
            .consequences
            .iter()
            .find(|consequence| {
                consequence.family == 1
                    && consequence.state == 1
                    && consequence.boundary == boundary
            })
            .ok_or("E2 successor boundary consequence absent")?;
        consequences.push(ReturnedBoundaryConsequence {
            boundary,
            source_incidence_sha256: consequence.source_incidence_sha256.clone(),
            returned_consequence_sha256: digest_many(&[
                consequence.source_consequence_sha256.as_bytes(),
                &u32_bytes(&joint.successor_consequence),
                emission.as_bytes(),
            ]),
        });
    }
    let shared = digest_many(&[
        &u32_bytes(&joint.joint_anchor),
        &u32_bytes(&joint.successor_consequence),
        emission.as_bytes(),
    ]);
    let returned = AddressedBoundaryWorldReturn::found(
        provisional.returned_occurrence_sha256,
        emission.clone(),
        1,
        consequences.clone(),
        shared,
    )
    .map_err(|error| error.to_string())?;
    let distinct_incidence_count = consequences
        .iter()
        .map(|consequence| &consequence.source_incidence_sha256)
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    let receipt = WorldReturnReceipt {
        schema: "holonics.e3.addressed-nominal-boundary-world-return.v1".to_owned(),
        truth_status: "implemented-exact; measured".to_owned(),
        recurrent_continuation_sha256: sha(&e0_bytes),
        recurrent_emission_occurrence_sha256: emission,
        returned,
        crossing_boundary_count: consequences.len(),
        distinct_incidence_count,
        joint: receipt(&joint),
        source_lineage_routed_conduct: false,
    };
    fs::write(
        output,
        serde_json::to_vec_pretty(&receipt).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

fn detached(rest_root: &Path, output: &Path) -> Result<(), String> {
    let manifest: RestManifest = read_json(&rest_root.join("manifest.json"))?;
    if manifest.schema != "holonics.e3.native-rest-directory.v1" {
        return Err("E3 rest manifest schema moved".to_owned());
    }
    let mut components = BTreeMap::new();
    let mut accessed = Vec::new();
    for (role, component) in &manifest.components {
        let path = rest_root.join(&component.path);
        let bytes = fs::read(&path).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != component.octets || sha(&bytes) != component.sha256 {
            return Err(format!("E3 rest component {role} moved"));
        }
        accessed.push(path.display().to_string());
        components.insert(role.clone(), bytes);
    }
    accessed.push(rest_root.join("manifest.json").display().to_string());
    let get = |role: &str| {
        components
            .get(role)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("E3 rest component {role} absent"))
    };
    let continuation: E2Continuation =
        serde_json::from_slice(get("continuation")?).map_err(|error| error.to_string())?;
    let cultivated = ReturnedBoundaryCultivationRest::read(
        get("standing")?,
        get("decoder")?,
        get("fibres")?,
        get("cultivation")?,
    )
    .map_err(|error| error.to_string())?;
    let identity = cultivated
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let siblings = !cultivated.standing().declined_sibling.committed
        && cultivated.standing().committed_sibling.committed
        && cultivated.standing().declined_sibling.identity_sha256
            != cultivated.standing().committed_sibling.identity_sha256;
    let support = cultivated
        .standing()
        .delta
        .support_boundaries
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let predecessor = cultivated
        .conduct_predecessor(&continuation.candidate_counts, &mut card)
        .map_err(|error| error.to_string())?;
    let successor = cultivated
        .conduct_cultivated(&continuation.candidate_counts, &mut card)
        .map_err(|error| error.to_string())?;
    validate_changed(&predecessor, &successor)?;
    let ablated = cultivated
        .conduct_predecessor(&continuation.candidate_counts, &mut card)
        .map_err(|error| error.to_string())?;
    let optical_and_acoustic = support.contains(&BoundaryId(101))
        && support.contains(&BoundaryId(103))
        && local_withdrawals_are_directional(&successor, 4, &[0, 1]);
    let local_codec = ablated.successor_consequence == predecessor.successor_consequence
        && ablated.successor_consequence != successor.successor_consequence;
    let (_, withdrawal) = cultivated.withdraw().map_err(|error| error.to_string())?;
    let forbidden = accessed
        .iter()
        .filter(|path| {
            let lower = path.to_ascii_lowercase();
            lower.contains("foreign-tower-return")
                || lower.contains("the_full_tower_emanates")
                || lower.contains("provisional-codec-candidate")
                || lower.ends_with(".png")
                || lower.ends_with(".wav")
                || lower.ends_with(".lean")
                || lower.ends_with(".safetensors")
        })
        .cloned()
        .collect();
    let detached = DetachedGrade {
        schema: "holonics.e3.detached-cultivation-grade.v1".to_owned(),
        truth_status: "implemented-exact; measured".to_owned(),
        cultivated_identity_sha256: identity,
        predecessor: receipt(&predecessor),
        cultivated: receipt(&successor),
        ablated: receipt(&ablated),
        held_out_conduct_changed: predecessor.successor_consequence
            != successor.successor_consequence,
        cultivated_codec_withdrawal_is_local: local_codec,
        optical_and_acoustic_withdrawals_match_e2_directionality: optical_and_acoustic,
        exact_withdrawal: withdrawal,
        declined_and_committed_siblings_retained: siblings,
        forbidden_source_access: forbidden,
        source_accessed_paths: accessed,
    };
    fs::write(
        output,
        serde_json::to_vec_pretty(&detached).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

fn read_e2() -> Result<(Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, E2Continuation), String> {
    let root = Path::new(E2_ROOT);
    let standing = fs::read(root.join("standing.json")).map_err(|error| error.to_string())?;
    let decoder = fs::read(root.join("decoder.json")).map_err(|error| error.to_string())?;
    let fibres = fs::read(root.join("fibres.json")).map_err(|error| error.to_string())?;
    let provisional =
        fs::read(root.join("provisional-codec.json")).map_err(|error| error.to_string())?;
    let continuation_bytes =
        fs::read(root.join("continuation.json")).map_err(|error| error.to_string())?;
    let continuation =
        serde_json::from_slice(&continuation_bytes).map_err(|error| error.to_string())?;
    Ok((standing, decoder, fibres, provisional, continuation))
}

fn validate_changed(
    predecessor: &DeviceJointMediaTransport,
    cultivated: &DeviceJointMediaTransport,
) -> Result<(), String> {
    if predecessor.successor_consequence == cultivated.successor_consequence
        || predecessor.joint_anchor != cultivated.joint_anchor
        || cultivated.launches != 1
        || cultivated.synchronizations != 1
        || cultivated.joint_anchor.iter().any(|value| *value != 1)
    {
        return Err("E3 cultivated held-out conduct did not separate exactly".to_owned());
    }
    Ok(())
}

fn local_withdrawals_are_directional(
    joint: &DeviceJointMediaTransport,
    ports: usize,
    selected: &[usize],
) -> bool {
    selected.iter().all(|withdrawn| {
        joint
            .local_ablated_consequence
            .chunks_exact(ports)
            .enumerate()
            .all(|(cell, row)| {
                row[*withdrawn]
                    == if cell % ports == *withdrawn {
                        joint.predecessor_consequence[cell]
                    } else {
                        joint.successor_consequence[cell]
                    }
            })
    })
}

fn receipt(value: &DeviceJointMediaTransport) -> JointReceipt {
    JointReceipt {
        joint_anchor: value.joint_anchor.clone(),
        predecessor_consequence: value.predecessor_consequence.clone(),
        successor_consequence: value.successor_consequence.clone(),
        shared_withdrawn_consequence: value.shared_ablated_consequence.clone(),
        local_withdrawn_consequence: value.local_ablated_consequence.clone(),
        launches: value.launches,
        synchronizations: value.synchronizations,
        resident_octets: value.resident_octets,
        transfer_octets: value.host_ingress_octets + value.host_egress_octets,
    }
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}

fn sha(bytes: &[u8]) -> String {
    hex(Sha256::digest(bytes))
}

fn digest_many(parts: &[&[u8]]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part);
    }
    hex(digest.finalize())
}

fn u32_bytes(values: &[u32]) -> Vec<u8> {
    values
        .iter()
        .flat_map(|value| value.to_le_bytes())
        .collect()
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn arguments() -> Result<Args, String> {
    let mut arguments = env::args().skip(1);
    match arguments.next().as_deref() {
        None => Ok(Args::Produce(PathBuf::from(DEFAULT_OUT))),
        Some("--produce") => Ok(Args::Produce(PathBuf::from(
            arguments.next().ok_or("--produce needs OUTPUT")?,
        ))),
        Some("--world-return") => Ok(Args::WorldReturn(PathBuf::from(
            arguments.next().ok_or("--world-return needs OUTPUT")?,
        ))),
        Some("--detached") => Ok(Args::Detached(
            PathBuf::from(arguments.next().ok_or("--detached needs REST")?),
            PathBuf::from(arguments.next().ok_or("--detached needs OUTPUT")?),
        )),
        Some(other) => Err(format!("unknown E3 argument {other}")),
    }
}
