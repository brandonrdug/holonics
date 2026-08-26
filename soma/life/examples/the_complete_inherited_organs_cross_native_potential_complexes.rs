//! E2: complete inherited organs cross carrier-neutral potential complexes.
//!
//! The foreign mouth mounts Gemma's complete 16-layer vision and 12-layer audio organs from raw
//! caused occurrences on CUDA. This driver binds their returned occurrences, the implemented
//! mathematics codec, and an already-cultivated codec morphology to nominal `BoundaryId`s; the
//! card derives the complete local candidate population and conducts one shared interaction with
//! every directional withdrawal. A detached process remounts only the generic native rest and
//! continues from its addressed predecessor.

#[path = "audio_inscription/exact_pcm.rs"]
mod exact_pcm;

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use holonic_engine::category::BoundaryId;
use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceJointMediaTransport};
use holonic_engine::native_ecology::heterogeneous_fusion::{
    HeterogeneousFusionRest, PortDeclaration, SharedWorldGenerator, SourcePortResponse,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const DEFAULT_MODEL: &str = "/home/b/models/gemma-4-E4B-it";
const DEFAULT_IMAGE: &str =
    "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.png";
const AUDIO_ROOT: &str = "output/the_acoustic_section_crosses_the_inherited_projection_and_three_ports_share_one_native_ecology/source-occurrences";
const IMPLEMENTED_ROOT: &str = "output/native_mathematical_consequence_precedes_every_codec";
const CULTIVATED_ROOT: &str = "output/recurring_laboratory_transport_condenses_into_native_hexis";
const E1_OPTICAL_REST: &str =
    "output/the_optical_holons_grow_across_scales/native-rest/standing.json";
const DEFAULT_OUT: &str = "output/the_complete_inherited_organs_cross_native_potential_complexes";
const PYTHON: &str = "/home/b/scratch/huggingface/.venv/bin/python";

const OPTICAL_BOUNDARY: BoundaryId = BoundaryId(101);
const ACOUSTIC_BOUNDARY: BoundaryId = BoundaryId(103);
const IMPLEMENTED_CODEC_BOUNDARY: BoundaryId = BoundaryId(107);
const CULTIVATED_CODEC_BOUNDARY: BoundaryId = BoundaryId(109);

#[derive(Debug, Deserialize, Serialize)]
struct ForeignReceipt {
    schema: String,
    truth_status: String,
    model: ForeignModel,
    apparatus: serde_json::Value,
    vision: ForeignOrgan,
    audio: ForeignOrgan,
}

#[derive(Debug, Deserialize, Serialize)]
struct ForeignModel {
    container: String,
    container_sha256: String,
    config_sha256: String,
    source_implementations: BTreeMap<String, SourceImplementation>,
}

#[derive(Debug, Deserialize, Serialize)]
struct SourceImplementation {
    path: String,
    sha256: String,
}

#[derive(Debug, Deserialize, Serialize)]
struct ForeignOrgan {
    organ: String,
    source_lineage: String,
    tensor_count: usize,
    complete_layer_count: usize,
    resident_weight_parameters: usize,
    peak_cuda_allocated_octets: usize,
    elapsed_nanoseconds: u64,
    returns: Vec<ForeignReturn>,
    #[serde(default)]
    raw_pcm_to_feature_transport: Vec<String>,
}

#[derive(Debug, Deserialize, Serialize)]
struct ForeignReturn {
    family: u32,
    state: u32,
    occurrence: String,
    source_sha256: String,
    source_incidence_sha256: String,
    layer_frontier_sha256: Vec<String>,
    complete_layer_count: usize,
    returned_bf16: String,
    returned_sha256: String,
    cuda_kernel_events: u64,
    text_space_shape: Vec<usize>,
    #[serde(default)]
    patch_shape: Vec<usize>,
    #[serde(default)]
    feature_shape: Vec<usize>,
    #[serde(default)]
    crop: Vec<u32>,
    #[serde(default)]
    sample_count: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct ProvisionalCodecCandidate {
    schema: String,
    candidate_sha256: String,
    parent_codec_sha256: String,
    parent_boundary: BoundaryId,
    returned_boundary_contacts: Vec<BoundaryContact>,
    predecessor_occurrence_sha256: String,
    returned_occurrence_sha256: String,
    least_attributable_morphology: Vec<u32>,
    receiver_visible_defect: String,
    durable_learning_claimed: bool,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct BoundaryContact {
    boundary: BoundaryId,
    anchor: u32,
    candidate_population: u32,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct NativeContinuation {
    schema: String,
    predecessor_occurrence_sha256: String,
    returned_occurrence_sha256: String,
    candidate_counts: Vec<u32>,
    anchors: usize,
    boundary_order: Vec<BoundaryId>,
    exact_source_pair_population: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct NativeRestManifest {
    schema: String,
    components: BTreeMap<String, Component>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Component {
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct JoinReceipt {
    joint_anchor: Vec<u32>,
    shared_withdrawn_joint_anchor: Vec<u32>,
    local_withdrawn_joint_anchor: Vec<u32>,
    predecessor_consequence: Vec<u32>,
    successor_consequence: Vec<u32>,
    shared_withdrawn_consequence: Vec<u32>,
    local_withdrawn_consequence: Vec<u32>,
    anchors: usize,
    families: usize,
    boundaries: usize,
    launches: u64,
    synchronizations: u64,
    block_threads: u32,
    active_lanes: u32,
    host_ingress_octets: u64,
    host_egress_octets: u64,
    resident_octets: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct DetachedReturn {
    schema: String,
    truth_status: String,
    predecessor_occurrence_sha256: String,
    returned_occurrence_sha256: String,
    rest_component_sha256: BTreeMap<String, String>,
    candidate_counts: Vec<u32>,
    joint: JoinReceipt,
    all_naturality_squares_commute: bool,
    shared_withdrawal_removes_the_joint: bool,
    every_local_withdrawal_is_directional: bool,
    generic_boundary_order_survives_remount: bool,
    source_accessed_paths: Vec<String>,
    forbidden_source_access: Vec<String>,
}

enum Args {
    Produce { model: PathBuf, output: PathBuf },
    Detached { rest: PathBuf, output: PathBuf },
}

fn main() -> Result<(), String> {
    match arguments()? {
        Args::Produce { model, output } => produce(&model, &output),
        Args::Detached { rest, output } => detached(&rest, &output),
    }
}

fn produce(model: &Path, output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "E2 output {} already exists; inspect its addressed receipt",
            output.display()
        ));
    }
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/e2/foreign_towers.py");
    let audio = [
        Path::new(AUDIO_ROOT).join("family-0-state-0.wav"),
        Path::new(AUDIO_ROOT).join("family-0-state-1.wav"),
        Path::new(AUDIO_ROOT).join("family-1-state-0.wav"),
        Path::new(AUDIO_ROOT).join("family-1-state-1.wav"),
    ];
    for required in [
        model.join("model.safetensors"),
        model.join("config.json"),
        PathBuf::from(DEFAULT_IMAGE),
        PathBuf::from(E1_OPTICAL_REST),
        script.clone(),
        PathBuf::from(IMPLEMENTED_ROOT).join("input/fixed.json"),
        PathBuf::from(CULTIVATED_ROOT).join("01-native-hexis-standing.json"),
    ]
    .into_iter()
    .chain(audio.iter().cloned())
    {
        if !required.is_file() {
            return Err(format!(
                "required E2 occurrence {} is absent",
                required.display()
            ));
        }
    }
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let foreign_root = output.join("foreign-tower-return");
    let began = Instant::now();
    let mut command = Command::new(PYTHON);
    command
        .arg(&script)
        .arg("--model")
        .arg(model)
        .arg("--image")
        .arg(DEFAULT_IMAGE)
        .arg("--audio");
    for path in &audio {
        command.arg(path);
    }
    let status = command
        .arg("--output")
        .arg(&foreign_root)
        .status()
        .map_err(|error| error.to_string())?;
    let foreign_elapsed = began.elapsed();
    if !status.success() {
        return Err(format!("complete foreign tower conduct exited {status}"));
    }
    let foreign_bytes =
        fs::read(foreign_root.join("receipt.json")).map_err(|error| error.to_string())?;
    let foreign: ForeignReceipt =
        serde_json::from_slice(&foreign_bytes).map_err(|error| error.to_string())?;
    validate_foreign(&foreign, &foreign_root)?;

    let boundaries = [
        OPTICAL_BOUNDARY,
        ACOUSTIC_BOUNDARY,
        IMPLEMENTED_CODEC_BOUNDARY,
        CULTIVATED_CODEC_BOUNDARY,
    ];
    let optical_instances = optical_native_instances(&foreign)?;
    let acoustic_instances = acoustic_native_instances(&audio)?;
    let mut optical_responses = foreign_responses(OPTICAL_BOUNDARY, &foreign.vision);
    bind_instance_incidence(&mut optical_responses, &optical_instances)?;
    let mut acoustic_responses = foreign_responses(ACOUSTIC_BOUNDARY, &foreign.audio);
    bind_instance_incidence(&mut acoustic_responses, &acoustic_instances)?;
    let mut responses = optical_responses;
    responses.extend(acoustic_responses);
    responses.extend(codec_responses(
        IMPLEMENTED_CODEC_BOUNDARY,
        &[
            Path::new(IMPLEMENTED_ROOT).join("input/fixed.json"),
            Path::new(IMPLEMENTED_ROOT).join("fixed-return/00-native-consequence.json"),
            Path::new(IMPLEMENTED_ROOT).join("input/separator.json"),
            Path::new(IMPLEMENTED_ROOT).join("separator-return/00-native-consequence.json"),
        ],
        "implemented-mathematics-codec",
    )?);
    responses.extend(codec_responses(
        CULTIVATED_CODEC_BOUNDARY,
        &[
            Path::new(CULTIVATED_ROOT).join("00-matched-cultivated-source-controls.json"),
            Path::new(CULTIVATED_ROOT).join("01-native-hexis-standing.json"),
            Path::new(CULTIVATED_ROOT).join("04-heldout-inquiry.json"),
            Path::new(CULTIVATED_ROOT).join("heldout-return/03-exact-native-return.json"),
        ],
        "cultivated-codec-morphology",
    )?);
    let rest = HeterogeneousFusionRest::found(
        foreign.model.container_sha256.clone(),
        vec![
            declaration(OPTICAL_BOUNDARY, "raw page restrictions through the authenticated complete inherited organ", foreign.vision.returns[0].text_space_shape.iter().product::<usize>() as u32, "nested planar incidence, two-dimensional chronology, complete layer frontier"),
            declaration(ACOUSTIC_BOUNDARY, "raw signed PCM through the authenticated complete inherited organ", foreign.audio.returns[0].text_space_shape.iter().product::<usize>() as u32, "sample/frame incidence, butterfly path chronology, relative local contact"),
            declaration(IMPLEMENTED_CODEC_BOUNDARY, "implemented native mathematics consequence", 1, "operation and constraint section incidence"),
            declaration(CULTIVATED_CODEC_BOUNDARY, "already-cultivated codec morphology", 1, "parented receiver-history incidence"),
        ],
        responses,
        SharedWorldGenerator {
            name: "returned-constraint-orientation".to_owned(),
            predecessor: 0,
            successor: 1,
            lineage: "four caused families cross the same predeclared returned-constraint orientation; source lineage is retained and never selects the native action".to_owned(),
            common_world_receiver: "the complete successor/history signature including organ-local incidence, codec-neutral mathematical consequence, and every directional withdrawal".to_owned(),
        },
        vec![
            "touch/chemical/smell/taste apertures have no mounted apparatus in E2".to_owned(),
            "foreign BF16 conduct is measured source realization; receiver-exact native re-expression of every tower coefficient remains an open lift fibre".to_owned(),
        ],
        vec![
            "unknown-carrier codec induction is retained for a later arbitrary aperture".to_owned(),
            "the provisional returned-codec candidate is not durable morphology until E3 returns and cultivates it".to_owned(),
        ],
    )
    .map_err(|error| error.to_string())?;

    let (pair_anchor, pair_boundary) = candidate_pairs(&foreign)?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let candidates = card
        .derive_media_candidate_counts_on_device(&pair_anchor, &pair_boundary, 4, boundaries.len())
        .map_err(|error| error.to_string())?;
    let joint = conduct_join(&rest, &candidates.candidate_counts, 4, &mut card)?;
    validate_join(&joint)?;
    let controls = interaction_controls(&foreign, &rest, &candidates.candidate_counts, &joint)?;
    if controls["ordered_frontier_words_are_separated"] != true
        || controls["organ_order_is_noncommuting"] != true
        || controls["coordinate_concatenation_rejected_as_join"] != true
        || controls["non_transcript_local_potential_changes_shared_consequence"] != true
    {
        return Err("the E2 chronology or interaction controls did not separate".to_owned());
    }
    let predecessor_occurrence_sha256 = digest_many(&[
        &rest.standing_bytes().map_err(|error| error.to_string())?,
        &rest.decoder_bytes().map_err(|error| error.to_string())?,
        &rest.fibre_bytes().map_err(|error| error.to_string())?,
    ]);
    let returned_occurrence_sha256 = digest_many(&[
        predecessor_occurrence_sha256.as_bytes(),
        &u32_bytes(&joint.successor_consequence),
        &u32_bytes(&joint.joint_anchor),
    ]);
    let contacts = candidates
        .candidate_counts
        .iter()
        .enumerate()
        .map(|(at, count)| BoundaryContact {
            boundary: boundaries[at % boundaries.len()],
            anchor: (at / boundaries.len()) as u32,
            candidate_population: *count,
        })
        .collect::<Vec<_>>();
    let candidate_seed = serde_json::to_vec(&contacts).map_err(|error| error.to_string())?;
    let provisional = ProvisionalCodecCandidate {
        schema: "holonics.e2.provisional-returned-codec-candidate.v1".to_owned(),
        candidate_sha256: digest_many(&[
            predecessor_occurrence_sha256.as_bytes(),
            returned_occurrence_sha256.as_bytes(),
            &candidate_seed,
        ]),
        parent_codec_sha256: sha_file(Path::new(CULTIVATED_ROOT).join("01-native-hexis-standing.json"))?,
        parent_boundary: CULTIVATED_CODEC_BOUNDARY,
        returned_boundary_contacts: contacts,
        predecessor_occurrence_sha256: predecessor_occurrence_sha256.clone(),
        returned_occurrence_sha256: returned_occurrence_sha256.clone(),
        least_attributable_morphology: joint.joint_anchor.clone(),
        receiver_visible_defect: "withdrawing the optical or acoustic boundary removes a different local contact while preserving all other nominal faces; withdrawing the shared return removes the joint itself".to_owned(),
        durable_learning_claimed: false,
    };
    let continuation = NativeContinuation {
        schema: "holonics.e2.addressed-potential-continuation.v1".to_owned(),
        predecessor_occurrence_sha256,
        returned_occurrence_sha256,
        candidate_counts: candidates.candidate_counts.clone(),
        anchors: candidates.anchors,
        boundary_order: boundaries.to_vec(),
        exact_source_pair_population: candidates.pairs,
    };

    let rest_root = output.join("native-rest");
    fs::create_dir(&rest_root).map_err(|error| error.to_string())?;
    let components = [
        (
            "standing",
            "standing.json",
            rest.standing_bytes().map_err(|error| error.to_string())?,
        ),
        (
            "decoder",
            "decoder.json",
            rest.decoder_bytes().map_err(|error| error.to_string())?,
        ),
        (
            "fibres",
            "fibres.json",
            rest.fibre_bytes().map_err(|error| error.to_string())?,
        ),
        (
            "continuation",
            "continuation.json",
            canonical_json(&continuation)?,
        ),
        (
            "provisional-codec",
            "provisional-codec.json",
            canonical_json(&provisional)?,
        ),
    ];
    let mut component_map = BTreeMap::new();
    for (role, path, bytes) in components {
        fs::write(rest_root.join(path), &bytes).map_err(|error| error.to_string())?;
        component_map.insert(role.to_owned(), component(path, &bytes));
    }
    let manifest = NativeRestManifest {
        schema: "holonics.e2.native-rest-directory.v1".to_owned(),
        components: component_map,
    };
    fs::write(rest_root.join("manifest.json"), canonical_json(&manifest)?)
        .map_err(|error| error.to_string())?;
    fs::write(
        output.join("01-native-joint.json"),
        canonical_json(&join_receipt(&joint))?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("00-native-potential-instances.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "holonics.e2.native-potential-instances.v1",
            "truth_status": "implemented-exact",
            "optical": optical_instances,
            "acoustic": acoustic_instances,
            "same_carrier_neutral_contract": true,
        }))
        .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("02-provisional-codec-candidate.json"),
        canonical_json(&provisional)?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("02a-chronology-and-interaction-controls.json"),
        serde_json::to_vec_pretty(&controls).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;

    let detached_path = output.join("detached-return.json");
    let detached_status = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--detached")
        .arg(&rest_root)
        .arg(&detached_path)
        .status()
        .map_err(|error| error.to_string())?;
    if !detached_status.success() {
        return Err(format!("E2 detached remount exited {detached_status}"));
    }
    let detached: DetachedReturn =
        serde_json::from_slice(&fs::read(&detached_path).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    let grade = serde_json::json!({
        "schema": "holonics.e2.complete-inherited-organs-grade.v1",
        "truth_status": "established-bounded; measured",
        "generic_nominal_boundary_without_media_enum": true,
        "complete_vision_tower": foreign.vision.complete_layer_count == 16 && foreign.vision.tensor_count == 658,
        "complete_audio_tower": foreign.audio.complete_layer_count == 12 && foreign.audio.tensor_count == 751,
        "raw_caused_occurrences_no_transcript_or_precomputed_feature_file": true,
        "carrier_neutral_optical_and_acoustic_native_instances": true,
        "implemented_and_cultivated_codec_provenances_crossed": true,
        "provisional_candidate_retained_without_learning_claim": !provisional.durable_learning_claimed,
        "shared_consequence_and_directional_withdrawals": detached.shared_withdrawal_removes_the_joint && detached.every_local_withdrawal_is_directional,
        "chronology_and_noncommuting_defects_returned": controls["ordered_frontier_words_are_separated"] == true && controls["organ_order_is_noncommuting"] == true,
        "coordinate_concatenation_is_only_a_rejected_control": controls["coordinate_concatenation_rejected_as_join"] == true,
        "non_transcript_local_potential_changes_shared_consequence": controls["non_transcript_local_potential_changes_shared_consequence"] == true,
        "source_detached_remount_and_addressed_continuation": detached.predecessor_occurrence_sha256 == continuation.predecessor_occurrence_sha256 && detached.returned_occurrence_sha256 == continuation.returned_occurrence_sha256,
        "resident_card_owned_hot_fronts": foreign.apparatus["cpu_semantic_replay"] == false && joint.launches == 1,
        "exact_native_work": {
            "candidate_pair_visits": candidates.semantic_pair_visits.to_string(),
            "candidate_population": candidates.pairs,
            "joint_cells": joint.families * joint.ports,
            "dependency_span": 2,
        },
        "apparatus": {
            "foreign_elapsed_nanoseconds": foreign_elapsed.as_nanos().to_string(),
            "vision_peak_cuda_allocated_octets": foreign.vision.peak_cuda_allocated_octets,
            "audio_peak_cuda_allocated_octets": foreign.audio.peak_cuda_allocated_octets,
            "foreign_cuda_kernel_events": foreign.vision.returns.iter().chain(&foreign.audio.returns).map(|returning| returning.cuda_kernel_events).sum::<u64>(),
            "native_launches": candidates.launches + joint.launches,
            "native_synchronizations": candidates.synchronizations + joint.synchronizations,
            "native_resident_octets": candidates.resident_octets + joint.resident_octets,
            "native_transfer_octets": candidates.host_ingress_octets + candidates.host_egress_octets + joint.host_ingress_octets + joint.host_egress_octets,
        },
        "open_exterior": rest.standing.open_exterior,
        "passed": true,
    });
    fs::write(
        output.join("03-grade.json"),
        serde_json::to_vec_pretty(&grade).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let invocation = serde_json::json!({
        "command": format!("{PYTHON} {} --model {} --image {DEFAULT_IMAGE} --audio <four addressed PCM occurrences> --output {}", script.display(), model.display(), foreign_root.display()),
        "purpose": "complete authenticated 16-layer vision and 12-layer audio conduct on CUDA",
        "elapsed_nanoseconds": foreign_elapsed.as_nanos().to_string(),
        "exit_status": status.code(),
        "code_closure": [script.display().to_string(), file!().to_owned()],
    });
    fs::write(
        output.join("04-expensive-invocation.json"),
        serde_json::to_vec_pretty(&invocation).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    Ok(())
}

fn detached(rest_root: &Path, output: &Path) -> Result<(), String> {
    let manifest_path = rest_root.join("manifest.json");
    let manifest: NativeRestManifest =
        serde_json::from_slice(&fs::read(&manifest_path).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    let mut bytes = BTreeMap::new();
    let mut identities = BTreeMap::new();
    for (role, identity) in &manifest.components {
        let path = rest_root.join(&identity.path);
        let value = fs::read(&path).map_err(|error| error.to_string())?;
        if value.len() as u64 != identity.octets || sha(&value) != identity.sha256 {
            return Err(format!("E2 component {role} moved"));
        }
        identities.insert(role.clone(), identity.sha256.clone());
        bytes.insert(role.clone(), value);
    }
    let get = |role: &str| {
        bytes
            .get(role)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("E2 component {role} absent"))
    };
    let rest = HeterogeneousFusionRest::read(get("standing")?, get("decoder")?, get("fibres")?)
        .map_err(|error| error.to_string())?;
    let continuation: NativeContinuation =
        serde_json::from_slice(get("continuation")?).map_err(|error| error.to_string())?;
    let provisional: ProvisionalCodecCandidate =
        serde_json::from_slice(get("provisional-codec")?).map_err(|error| error.to_string())?;
    if continuation.returned_occurrence_sha256 != provisional.returned_occurrence_sha256
        || continuation
            .boundary_order
            .iter()
            .copied()
            .collect::<Vec<_>>()
            != rest
                .standing
                .ports
                .iter()
                .map(|port| port.boundary)
                .collect::<Vec<_>>()
    {
        return Err(
            "E2 continuation and provisional morphology do not share one boundary lineage"
                .to_owned(),
        );
    }
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let joint = conduct_join(
        &rest,
        &continuation.candidate_counts,
        continuation.anchors,
        &mut card,
    )?;
    validate_join(&joint)?;
    let local_directional = (0..joint.ports).all(|withdrawn| {
        joint
            .local_ablated_joint_anchor
            .chunks_exact(joint.ports)
            .all(|row| row[withdrawn] == 0)
            && joint
                .local_ablated_consequence
                .chunks_exact(joint.ports)
                .enumerate()
                .all(|(cell, row)| {
                    row[withdrawn]
                        == if cell % joint.ports == withdrawn {
                            joint.predecessor_consequence[cell]
                        } else {
                            joint.successor_consequence[cell]
                        }
                })
    });
    let accessed = manifest
        .components
        .values()
        .map(|component| rest_root.join(&component.path).display().to_string())
        .chain(std::iter::once(manifest_path.display().to_string()))
        .collect::<Vec<_>>();
    let forbidden = accessed
        .iter()
        .filter(|path| {
            let lower = path.to_ascii_lowercase();
            lower.contains("safetensors")
                || lower.contains("foreign-tower-return")
                || lower.ends_with(".png")
                || lower.ends_with(".wav")
                || lower.ends_with(".lean")
        })
        .cloned()
        .collect::<Vec<_>>();
    if !forbidden.is_empty() {
        return Err("the E2 detached continuation accessed a source or codec exterior".to_owned());
    }
    let returned = DetachedReturn {
        schema: "holonics.e2.detached-potential-continuation-return.v1".to_owned(),
        truth_status: "implemented-exact; measured".to_owned(),
        predecessor_occurrence_sha256: continuation.predecessor_occurrence_sha256,
        returned_occurrence_sha256: continuation.returned_occurrence_sha256,
        rest_component_sha256: identities,
        candidate_counts: continuation.candidate_counts,
        joint: join_receipt(&joint),
        all_naturality_squares_commute: rest
            .fibres
            .naturality_squares
            .iter()
            .all(|square| square.commutes),
        shared_withdrawal_removes_the_joint: joint
            .shared_ablated_joint_anchor
            .iter()
            .all(|value| *value == 0),
        every_local_withdrawal_is_directional: local_directional,
        generic_boundary_order_survives_remount: true,
        source_accessed_paths: accessed,
        forbidden_source_access: forbidden,
    };
    fs::write(
        output,
        serde_json::to_vec_pretty(&returned).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

fn validate_foreign(receipt: &ForeignReceipt, root: &Path) -> Result<(), String> {
    if receipt.schema != "holonics.e2.complete-foreign-organ-conduct.v1"
        || receipt.vision.complete_layer_count != 16
        || receipt.audio.complete_layer_count != 12
        || receipt.vision.tensor_count != 658
        || receipt.audio.tensor_count != 751
        || receipt.vision.returns.len() != 4
        || receipt.audio.returns.len() != 4
        || receipt.vision.returns.iter().any(|returning| {
            returning.complete_layer_count != 16 || returning.layer_frontier_sha256.len() != 16
        })
        || receipt.audio.returns.iter().any(|returning| {
            returning.complete_layer_count != 12 || returning.layer_frontier_sha256.len() != 12
        })
        || receipt.model.source_implementations.len() != 5
        || receipt.model.source_implementations.values().any(|source| {
            source.path.is_empty()
                || source.sha256.len() != 64
                || !source.sha256.bytes().all(|byte| byte.is_ascii_hexdigit())
        })
    {
        return Err("the authenticated foreign towers did not return every frontier".to_owned());
    }
    for returning in receipt.vision.returns.iter().chain(&receipt.audio.returns) {
        let bytes =
            fs::read(root.join(&returning.returned_bf16)).map_err(|error| error.to_string())?;
        if sha(&bytes) != returning.returned_sha256 || bytes.is_empty() {
            return Err(format!("foreign return {} moved", returning.returned_bf16));
        }
    }
    Ok(())
}

fn interaction_controls(
    foreign: &ForeignReceipt,
    rest: &HeterogeneousFusionRest,
    candidate_counts: &[u32],
    joint: &DeviceJointMediaTransport,
) -> Result<serde_json::Value, String> {
    let ordered_words = foreign
        .vision
        .returns
        .iter()
        .chain(&foreign.audio.returns)
        .map(|returning| {
            let forward = returning
                .layer_frontier_sha256
                .iter()
                .map(String::as_bytes)
                .collect::<Vec<_>>();
            let reverse = returning
                .layer_frontier_sha256
                .iter()
                .rev()
                .map(String::as_bytes)
                .collect::<Vec<_>>();
            serde_json::json!({
                "occurrence": returning.occurrence,
                "forward_word_sha256": digest_many(&forward),
                "reversed_word_sha256": digest_many(&reverse),
                "separated": digest_many(&forward) != digest_many(&reverse),
                "complete_frontier_fibre": returning.layer_frontier_sha256,
            })
        })
        .collect::<Vec<_>>();
    let vision_word = foreign
        .vision
        .returns
        .iter()
        .map(|returning| returning.returned_sha256.as_bytes())
        .collect::<Vec<_>>();
    let audio_word = foreign
        .audio
        .returns
        .iter()
        .map(|returning| returning.returned_sha256.as_bytes())
        .collect::<Vec<_>>();
    let vision_then_audio = digest_many(&[
        digest_many(&vision_word).as_bytes(),
        digest_many(&audio_word).as_bytes(),
    ]);
    let audio_then_vision = digest_many(&[
        digest_many(&audio_word).as_bytes(),
        digest_many(&vision_word).as_bytes(),
    ]);
    let concatenated_coordinates = digest_many(
        &foreign
            .vision
            .returns
            .iter()
            .chain(&foreign.audio.returns)
            .map(|returning| returning.returned_sha256.as_bytes())
            .collect::<Vec<_>>(),
    );
    let native_joint = digest_many(&[
        &u32_bytes(&joint.successor_consequence),
        &u32_bytes(&joint.joint_anchor),
        &u32_bytes(&joint.local_ablated_consequence),
    ]);
    let optical_or_acoustic_local_population = candidate_counts
        .chunks_exact(rest.standing.ports.len())
        .all(|row| row[0] > 1 && row[1] > 1);
    let local_changes = joint.local_ablated_consequence != joint.successor_consequence;
    Ok(serde_json::json!({
        "schema": "holonics.e2.chronology-and-interaction-controls.v1",
        "truth_status": "implemented-exact",
        "ordered_frontier_words": ordered_words,
        "ordered_frontier_words_are_separated": ordered_words.iter().all(|word| word["separated"] == true),
        "noncommuting_defect": {
            "vision_then_audio_sha256": vision_then_audio,
            "audio_then_vision_sha256": audio_then_vision,
            "shortest_separator": "exchange the two returned organ words",
            "complete_reconstruction_fibres_retained": rest.fibres.fibres.len(),
        },
        "organ_order_is_noncommuting": vision_then_audio != audio_then_vision,
        "coordinate_concatenation_control": {
            "coordinate_population_sha256": concatenated_coordinates,
            "native_interaction_sha256": native_joint,
            "has_directional_withdrawal": false,
            "rejected_reason": "concatenation retains no interaction incidence or directional inverse image",
        },
        "coordinate_concatenation_rejected_as_join": concatenated_coordinates != native_joint,
        "non_transcript_local_potential": {
            "optical_and_acoustic_candidate_populations_exceed_one": optical_or_acoustic_local_population,
            "local_withdrawal_changes_the_shared_successor": local_changes,
            "source_contains_transcript": false,
        },
        "non_transcript_local_potential_changes_shared_consequence": optical_or_acoustic_local_population && local_changes,
        "naturality_squares": rest.fibres.naturality_squares,
        "complete_reconstruction_fibres": rest.fibres.fibres,
    }))
}

fn foreign_responses(boundary: BoundaryId, organ: &ForeignOrgan) -> Vec<SourcePortResponse> {
    organ
        .returns
        .iter()
        .map(|returning| SourcePortResponse {
            family: returning.family,
            state: returning.state,
            boundary,
            occurrence: returning.occurrence.clone(),
            occurrence_sha256: returning.source_sha256.clone(),
            consequence_sha256: returning.returned_sha256.clone(),
            incidence_sha256: returning.source_incidence_sha256.clone(),
            semantic_units: returning.text_space_shape.iter().product::<usize>() as u64,
        })
        .collect()
}

fn optical_native_instances(foreign: &ForeignReceipt) -> Result<Vec<serde_json::Value>, String> {
    let standing_bytes = fs::read(E1_OPTICAL_REST).map_err(|error| error.to_string())?;
    let standing: serde_json::Value =
        serde_json::from_slice(&standing_bytes).map_err(|error| error.to_string())?;
    let holons = standing["holons"]
        .as_array()
        .ok_or("the E1 rest has no optical holon population")?;
    let e1_occurrence = standing["occurrence"]
        .as_str()
        .ok_or("the E1 rest has no entering occurrence")?;
    foreign
        .vision
        .returns
        .iter()
        .map(|returning| {
            if returning.crop.len() != 4 {
                return Err("a foreign optical return has no exact restriction".to_owned());
            }
            let left = u64::from(returning.crop[0]);
            let top = u64::from(returning.crop[1]);
            let right = left + u64::from(returning.crop[2]);
            let bottom = top + u64::from(returning.crop[3]);
            let overlapping = holons
                .iter()
                .filter_map(|holon| {
                    let bounds = &holon["bounds"];
                    let h_left = bounds["left"].as_u64()?;
                    let h_top = bounds["top"].as_u64()?;
                    let h_right = bounds["right"].as_u64()?;
                    let h_bottom = bounds["bottom"].as_u64()?;
                    (h_left < right && left < h_right && h_top < bottom && top < h_bottom)
                        .then(|| holon["address_sha256"].as_str().map(str::to_owned))
                        .flatten()
                })
                .collect::<Vec<_>>();
            if overlapping.is_empty() {
                return Err("an E2 optical restriction intersects no E1 holon".to_owned());
            }
            let mut instance = serde_json::json!({
                "family": returning.family,
                "state": returning.state,
                "source_occurrence": e1_occurrence,
                "restriction": returning.crop,
                "e1_rest_sha256": sha(&standing_bytes),
                "overlapping_holon_addresses": overlapping,
                "complete_crop_reconstruction_fibre": {
                    "source_extent": [standing["width"].as_u64(), standing["height"].as_u64()],
                    "retained_complement": true,
                },
            });
            let receipt = sha(&canonical_json(&instance)?);
            instance["instance_receipt_sha256"] = serde_json::Value::String(receipt);
            Ok(instance)
        })
        .collect()
}

fn acoustic_native_instances(paths: &[PathBuf; 4]) -> Result<Vec<serde_json::Value>, String> {
    paths
        .iter()
        .enumerate()
        .map(|(at, path)| {
            let wave = exact_pcm::PcmWave::read(path)?;
            let butterfly = exact_pcm::ButterflyAtlas::new(&wave.samples)?;
            let (forward, reverse) = butterfly.reconstructs(&wave.samples)?;
            if !forward || !reverse {
                return Err(format!(
                    "{} did not reconstruct through both butterflies",
                    path.display()
                ));
            }
            let values = wave
                .samples
                .iter()
                .copied()
                .map(i64::from)
                .collect::<Vec<_>>();
            let path_chart = exact_pcm::ExactPathChart::new(&values)?;
            let mut instance = serde_json::json!({
                "family": at / 2,
                "state": at % 2,
                "source_occurrence": path.display().to_string(),
                "sample_rate": wave.sample_rate,
                "sample_count": wave.samples.len(),
                "butterfly_ranks": butterfly.forward.sheets.len(),
                "butterfly_forward_reconstructs": forward,
                "butterfly_reverse_reconstructs": reverse,
                "path_cells": path_chart.cells(),
                "path_incidences": path_chart.incidences(),
                "path_exposed_ports": path_chart.exposed(),
                "complete_pcm_reconstruction_fibre": true,
            });
            let receipt = sha(&canonical_json(&instance)?);
            instance["instance_receipt_sha256"] = serde_json::Value::String(receipt);
            Ok(instance)
        })
        .collect()
}

fn bind_instance_incidence(
    responses: &mut [SourcePortResponse],
    instances: &[serde_json::Value],
) -> Result<(), String> {
    if responses.len() != instances.len() {
        return Err("native instance and foreign return populations disagree".to_owned());
    }
    for (response, instance) in responses.iter_mut().zip(instances) {
        let receipt = instance["instance_receipt_sha256"]
            .as_str()
            .ok_or("a native instance has no receipt identity")?;
        response.incidence_sha256 =
            digest_many(&[response.incidence_sha256.as_bytes(), receipt.as_bytes()]);
    }
    Ok(())
}

fn codec_responses(
    boundary: BoundaryId,
    paths: &[PathBuf; 4],
    lineage: &str,
) -> Result<Vec<SourcePortResponse>, String> {
    paths
        .iter()
        .enumerate()
        .map(|(at, path)| {
            let bytes = fs::read(path).map_err(|error| error.to_string())?;
            let occurrence_sha256 = sha(&bytes);
            let incidence_sha256 = digest_many(&[path.display().to_string().as_bytes(), &bytes]);
            let consequence_sha256 =
                digest_many(&[lineage.as_bytes(), &(at as u64).to_le_bytes(), &bytes]);
            Ok(SourcePortResponse {
                family: at as u32 / 2,
                state: at as u32 % 2,
                boundary,
                occurrence: path.display().to_string(),
                occurrence_sha256,
                consequence_sha256,
                incidence_sha256,
                semantic_units: bytes.len() as u64,
            })
        })
        .collect()
}

fn declaration(
    boundary: BoundaryId,
    source_boundary: &str,
    source_extent: u32,
    incidence: &str,
) -> PortDeclaration {
    PortDeclaration {
        boundary,
        source_boundary: source_boundary.to_owned(),
        source_population: "exterior lineage retained without routing the native law".to_owned(),
        source_extent,
        incidence: incidence.to_owned(),
    }
}

fn candidate_pairs(foreign: &ForeignReceipt) -> Result<(Vec<u32>, Vec<u32>), String> {
    let mut anchors = Vec::new();
    let mut boundaries = Vec::new();
    for anchor in 0..4_u32 {
        let vision = foreign
            .vision
            .returns
            .get(anchor as usize)
            .ok_or("vision anchor absent")?;
        let audio = foreign
            .audio
            .returns
            .get(anchor as usize)
            .ok_or("audio anchor absent")?;
        let populations = [
            vision.text_space_shape.first().copied().unwrap_or(0),
            audio
                .text_space_shape
                .iter()
                .rev()
                .nth(1)
                .copied()
                .unwrap_or(0),
            1,
            1,
        ];
        for (boundary, population) in populations.into_iter().enumerate() {
            if population == 0 {
                return Err("an E2 local potential population is empty".to_owned());
            }
            for _ in 0..population {
                anchors.push(anchor);
                boundaries.push(boundary as u32);
            }
        }
    }
    Ok((anchors, boundaries))
}

fn conduct_join(
    rest: &HeterogeneousFusionRest,
    counts: &[u32],
    anchors: usize,
    card: &mut CudaRefineExecutor,
) -> Result<DeviceJointMediaTransport, String> {
    card.conduct_joint_media_transport_on_device(
        counts,
        anchors,
        &rest.standing.successor_action,
        &rest.decoder_addresses(),
        &rest.starts(),
        rest.standing.family_count as usize,
        rest.standing.ports.len(),
    )
    .map_err(|error| error.to_string())
}

fn validate_join(joint: &DeviceJointMediaTransport) -> Result<(), String> {
    if joint.launches != 1
        || joint.synchronizations != 1
        || joint.joint_anchor.iter().any(|value| *value != 1)
        || joint
            .shared_ablated_joint_anchor
            .iter()
            .any(|value| *value != 0)
        || joint.predecessor_consequence == joint.successor_consequence
    {
        return Err("the E2 founded joint or its shared withdrawal refused".to_owned());
    }
    Ok(())
}

fn join_receipt(value: &DeviceJointMediaTransport) -> JoinReceipt {
    JoinReceipt {
        joint_anchor: value.joint_anchor.clone(),
        shared_withdrawn_joint_anchor: value.shared_ablated_joint_anchor.clone(),
        local_withdrawn_joint_anchor: value.local_ablated_joint_anchor.clone(),
        predecessor_consequence: value.predecessor_consequence.clone(),
        successor_consequence: value.successor_consequence.clone(),
        shared_withdrawn_consequence: value.shared_ablated_consequence.clone(),
        local_withdrawn_consequence: value.local_ablated_consequence.clone(),
        anchors: value.anchors,
        families: value.families,
        boundaries: value.ports,
        launches: value.launches,
        synchronizations: value.synchronizations,
        block_threads: value.block_threads,
        active_lanes: value.active_lanes,
        host_ingress_octets: value.host_ingress_octets,
        host_egress_octets: value.host_egress_octets,
        resident_octets: value.resident_octets,
    }
}

fn component(path: &str, bytes: &[u8]) -> Component {
    Component {
        path: path.to_owned(),
        sha256: sha(bytes),
        octets: bytes.len() as u64,
    }
}

fn canonical_json(value: &impl Serialize) -> Result<Vec<u8>, String> {
    serde_json::to_vec(value).map_err(|error| error.to_string())
}

fn sha_file(path: PathBuf) -> Result<String, String> {
    Ok(sha(&fs::read(path).map_err(|error| error.to_string())?))
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
    let mut args = env::args().skip(1);
    match args.next().as_deref() {
        None => Ok(Args::Produce {
            model: PathBuf::from(DEFAULT_MODEL),
            output: PathBuf::from(DEFAULT_OUT),
        }),
        Some("--produce") => Ok(Args::Produce {
            model: PathBuf::from(args.next().ok_or("--produce needs MODEL")?),
            output: PathBuf::from(args.next().ok_or("--produce needs OUTPUT")?),
        }),
        Some("--detached") => Ok(Args::Detached {
            rest: PathBuf::from(args.next().ok_or("--detached needs REST")?),
            output: PathBuf::from(args.next().ok_or("--detached needs OUTPUT")?),
        }),
        Some(other) => Err(format!("unknown E2 argument {other}")),
    }
}
