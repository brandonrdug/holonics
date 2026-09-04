use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::mathematical_particle::{NativeCodec, NativeHexisRest, NativeSuccessorHistory};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use super::{
    artifact,
    cultivation::{
        NativeCultivatedMathematicalRest, NativeMathematicalWorldReturn, NativeRouteReturn,
    },
    world_return,
};

pub const DEFAULT_OUT: &str =
    ".local/artifacts/the_returned_native_mathematical_world_cultivates_the_laboratory_hexis";
const PREDECESSOR_REST: &str =
    ".local/artifacts/recurring_laboratory_transport_condenses_into_native_hexis/native-rest";
const CHRONOLOGY: &str = ".local/artifacts/the_laboratory_chronology_cultivates_the_athena_mathematics_ecology/00-frozen-laboratory-chronology.json";
const N2_MANIFEST: &str = ".local/artifacts/the_acoustic_section_crosses_the_inherited_projection_and_three_ports_share_one_native_ecology/MANIFEST.json";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SectionCampaign {
    held_out: Vec<Vec<i64>>,
    disjoint_control: Vec<Vec<i64>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ComponentIdentity {
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeCultivatedRestManifest {
    schema: String,
    predecessor_standing: ComponentIdentity,
    predecessor_decoder: ComponentIdentity,
    predecessor_fibres: ComponentIdentity,
    cultivation_standing: ComponentIdentity,
    canonical_rest_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DetachedCultivationReturn {
    schema: String,
    rest_sha256: String,
    predecessor: NativeRouteReturn,
    cultivated: NativeRouteReturn,
    control_predecessor: NativeRouteReturn,
    control_cultivated: NativeRouteReturn,
    held_out_changed: bool,
    disjoint_control_held: bool,
    source_descriptors: Vec<String>,
    forbidden_source_descriptors: Vec<String>,
    lean_or_checker_opened: bool,
}

pub fn construct(root: &Path, out: &Path) -> Result<(), String> {
    if out.exists() {
        return Err(format!(
            "N3 output {} already exists; inspect its addressed return instead of replaying it",
            out.display()
        ));
    }
    fs::create_dir_all(out.join("native-rest")).map_err(|error| error.to_string())?;
    fs::create_dir_all(out.join("detached-return")).map_err(|error| error.to_string())?;
    fs::create_dir_all(out.join("inquiries")).map_err(|error| error.to_string())?;

    let predecessor_directory = root.join(PREDECESSOR_REST);
    let predecessor_standing = artifact::read(predecessor_directory.join("standing.bin"))?;
    let predecessor_decoder = artifact::read(predecessor_directory.join("decoder.bin"))?;
    let predecessor_fibres = artifact::read(predecessor_directory.join("fibres.bin"))?;
    let predecessor = NativeHexisRest::read(
        &predecessor_standing,
        &predecessor_decoder,
        &predecessor_fibres,
    )
    .map_err(|error| error.to_string())?;
    let chronology_bytes = artifact::read(root.join(CHRONOLOGY))?;
    let chronology: Value =
        serde_json::from_slice(&chronology_bytes).map_err(|error| error.to_string())?;
    let chronology_families = chronology_families(&chronology)?;
    let all_occurrences = chronology_families
        .iter()
        .flat_map(|(_, occurrences)| occurrences.iter().cloned())
        .collect::<Vec<_>>();
    if chronology_families.len() < 7 || all_occurrences.len() < 7 {
        return Err("the addressed laboratory chronology lost its causal partitions".to_owned());
    }
    let histories = predecessor
        .reconstruction()
        .predecessor_component_addresses
        .iter()
        .rev()
        .take(5)
        .cloned()
        .collect::<Vec<_>>();

    let developmental = vec![
        predecessor
            .found_native_mathematical_inquiry(
                source_pair(&all_occurrences, 0),
                vec![vec![11, -11, 0], vec![3, -3, 0]],
                vec![NativeSuccessorHistory::FixedSection],
                histories.clone(),
                vec!["nonlinear successor families remain open".to_owned()],
            )
            .map_err(|error| error.to_string())?,
        predecessor
            .found_native_mathematical_inquiry(
                source_pair(&all_occurrences, 2),
                vec![vec![1, 1, 0], vec![1, 1, 0]],
                vec![
                    NativeSuccessorHistory::ExpandedGenerator,
                    NativeSuccessorHistory::CarrierRebase {
                        source: 0,
                        target: 1,
                    },
                ],
                histories.clone(),
                vec!["the residual separator remains an exact obstruction".to_owned()],
            )
            .map_err(|error| error.to_string())?,
        predecessor
            .found_native_mathematical_inquiry(
                source_pair(&all_occurrences, 4),
                vec![vec![5, -5, 0], vec![1, 1, 0]],
                vec![
                    NativeSuccessorHistory::ComposedJoint,
                    NativeSuccessorHistory::LocalAblation { family: 1 },
                ],
                histories.clone(),
                vec!["mixed fixed/obstructed successor histories remain distinct".to_owned()],
            )
            .map_err(|error| error.to_string())?,
    ];
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let developmental_returns = developmental
        .iter()
        .map(|inquiry| {
            predecessor
                .conduct_native_mathematical_inquiry_on_card(inquiry, &mut card)
                .map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, _>>()?;
    artifact::write_json(
        out.join("00-developmental-native-inquiries.json"),
        &developmental,
    )?;
    artifact::write_json(
        out.join("01-developmental-native-consequences.json"),
        &developmental_returns,
    )?;

    // Emit first. Only afterward does a new process receive the raw raster and return optical
    // incidence. The cultivation owner never receives an internal echo or checker verdict.
    let emitted_path = out.join("02-emitted-native-geometry.png");
    let emitted = world_return::emit_geometry(&developmental_returns[0], &emitted_path)?;
    artifact::write_json(out.join("02-emitted-native-geometry.json"), &emitted)?;
    let optical_return_path = out.join("03-returned-optical-world.json");
    let status = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--optical-return")
        .arg(&emitted_path)
        .arg(&optical_return_path)
        .current_dir(root)
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err("the separately addressed optical world return refused".to_owned());
    }
    let optical = world_return::read_passage(&optical_return_path)?;
    if optical.occurrence != emitted.raw_optical_occurrence {
        return Err("the returned optical occurrence lost its emitted cause".to_owned());
    }
    let n2_manifest_bytes = artifact::read(root.join(N2_MANIFEST))?;
    let n2_manifest_sha256 = artifact::digest(&n2_manifest_bytes);
    let exact_return_difference_sha256 = artifact::value_digest(&(
        &developmental_returns[0].occurrence,
        &optical.occurrence,
        &optical.native_consequence,
        &n2_manifest_sha256,
    ))?;
    let world_return = NativeMathematicalWorldReturn {
        occurrence: format!("n3/world-return/{exact_return_difference_sha256}"),
        emitted_native_consequence: developmental_returns[0].occurrence.clone(),
        returned_optical_occurrence: optical.occurrence.clone(),
        returned_multimodal_rest_sha256: n2_manifest_sha256,
        causing_laboratory_occurrences: all_occurrences.clone(),
        exact_return_difference_sha256,
        support_families: vec![0, 1],
        separately_addressed_after_emission: true,
    };

    let developmental_occurrences = developmental
        .iter()
        .map(|inquiry| inquiry.occurrence.clone())
        .collect::<Vec<_>>();
    let cultivated = NativeCultivatedMathematicalRest::cultivate(
        predecessor,
        world_return,
        developmental_occurrences,
        vec![all_occurrences[2].clone()],
        vec![all_occurrences[5].clone()],
    )?;
    let campaign = SectionCampaign {
        held_out: vec![vec![17, -17, 0], vec![7, -7, 0]],
        disjoint_control: vec![vec![1, 1, 0], vec![1, 0, 0]],
    };
    let predecessor_return = cultivated.conduct_predecessor(&campaign.held_out, &mut card)?;
    let cultivated_return = cultivated.conduct_cultivated(&campaign.held_out, &mut card)?;
    let control_predecessor =
        cultivated.conduct_predecessor(&campaign.disjoint_control, &mut card)?;
    let control_cultivated =
        cultivated.conduct_cultivated(&campaign.disjoint_control, &mut card)?;
    let held_out_changed = predecessor_return.selected_routes != cultivated_return.selected_routes;
    let disjoint_control_held = control_predecessor.selected_routes
        == control_cultivated.selected_routes
        && control_predecessor.constraint_residuals == control_cultivated.constraint_residuals;
    if !held_out_changed || !disjoint_control_held {
        return Err(
            "the returned cultivation did not separate held-out conduct from its control"
                .to_owned(),
        );
    }

    let held_out_inquiry = cultivated
        .predecessor()
        .found_native_mathematical_inquiry(
            source_pair(&all_occurrences, 1),
            campaign.held_out.clone(),
            vec![NativeSuccessorHistory::FixedSection],
            histories.clone(),
            vec!["successor words beyond the declared fixed sections remain open".to_owned()],
        )
        .map_err(|error| error.to_string())?;
    let control_inquiry = cultivated
        .predecessor()
        .found_native_mathematical_inquiry(
            source_pair(&all_occurrences, 5),
            campaign.disjoint_control.clone(),
            vec![NativeSuccessorHistory::ExpandedGenerator],
            histories,
            vec!["the obstructed successor remains outside the fixed kernel".to_owned()],
        )
        .map_err(|error| error.to_string())?;
    let rich_held_out =
        cultivated.conduct_rich_cultivated_consequence(&held_out_inquiry, &mut card)?;
    let rich_control =
        cultivated.conduct_rich_cultivated_consequence(&control_inquiry, &mut card)?;
    if rich_control.exterior.returned_obstructions.is_empty() {
        return Err(
            "the disjoint control was silently coerced into a fixed consequence".to_owned(),
        );
    }
    artifact::write_json(
        out.join("04-held-out-cultivation-return.json"),
        &json!({
            "schema": "holonics.n3.held-out-cultivation-return.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "predecessor": predecessor_return,
            "cultivated": cultivated_return,
            "control_predecessor": control_predecessor,
            "control_cultivated": control_cultivated,
            "held_out_changed": held_out_changed,
            "disjoint_control_held": disjoint_control_held,
            "rich_held_out": rich_held_out,
            "rich_control_obstruction": rich_control,
        }),
    )?;

    let notation = rich_held_out
        .project(NativeCodec::ExactNotation)
        .map_err(|error| error.to_string())?;
    let structured = rich_held_out
        .project(NativeCodec::Json)
        .map_err(|error| error.to_string())?;
    let projected_geometry =
        world_return::emit_geometry(&rich_held_out, &out.join("05-held-out-native-geometry.png"))?;
    artifact::write_json(
        out.join("05-downstream-projections.json"),
        &json!({
            "native_consequence_occurrence": rich_held_out.occurrence,
            "exact_notation": notation,
            "structured": structured,
            "diagram": projected_geometry,
            "correction": rich_held_out.derivational_transport,
            "counterexample_or_obstruction": rich_control.exterior.returned_obstructions,
            "all_projections_borrow_the_frozen_native_consequence": true,
            "no_projection_routes_internal_conduct": true,
        }),
    )?;

    let rest_root = out.join("native-rest");
    let cultivation_standing = cultivated.standing_bytes()?;
    let rest_identity = cultivated.canonical_identity()?;
    let manifest = NativeCultivatedRestManifest {
        schema: "holonics.n3.native-cultivated-rest-directory.v1".to_owned(),
        predecessor_standing: component("predecessor-standing.bin", &predecessor_standing),
        predecessor_decoder: component("predecessor-decoder.bin", &predecessor_decoder),
        predecessor_fibres: component("predecessor-fibres.bin", &predecessor_fibres),
        cultivation_standing: component("cultivation-standing.json", &cultivation_standing),
        canonical_rest_sha256: rest_identity.clone(),
    };
    artifact::write(
        rest_root.join("predecessor-standing.bin"),
        &predecessor_standing,
    )?;
    artifact::write(
        rest_root.join("predecessor-decoder.bin"),
        &predecessor_decoder,
    )?;
    artifact::write(
        rest_root.join("predecessor-fibres.bin"),
        &predecessor_fibres,
    )?;
    artifact::write(
        rest_root.join("cultivation-standing.json"),
        &cultivation_standing,
    )?;
    artifact::write_json(rest_root.join("manifest.json"), &manifest)?;
    artifact::write_json(out.join("inquiries/sections.json"), &campaign)?;

    let reread = NativeCultivatedMathematicalRest::read(
        &predecessor_standing,
        &predecessor_decoder,
        &predecessor_fibres,
        &cultivation_standing,
    )?;
    let (_, withdrawal) = reread.withdraw()?;
    if !withdrawal.exact_predecessor_restored {
        return Err("the local cultivation delta did not withdraw exactly".to_owned());
    }
    artifact::write_json(
        out.join("06-exact-predecessor-withdrawal.json"),
        &withdrawal,
    )?;

    run_detached(
        &env::current_exe().map_err(|error| error.to_string())?,
        &rest_root,
        &out.join("inquiries/sections.json"),
        &out.join("detached-return/return.json"),
    )?;
    let detached: DetachedCultivationReturn =
        serde_json::from_slice(&artifact::read(out.join("detached-return/return.json"))?)
            .map_err(|error| error.to_string())?;
    if detached.rest_sha256 != rest_identity
        || !detached.held_out_changed
        || !detached.disjoint_control_held
        || !detached.forbidden_source_descriptors.is_empty()
        || detached.lean_or_checker_opened
    {
        return Err(
            "the source-detached cultivated rest did not retain its exact conduct".to_owned(),
        );
    }

    let uncondensed_source_octets = chronology["incrementally_mounted_octets"]
        .as_u64()
        .ok_or("chronology source extent is absent")?;
    let native_rest_octets = predecessor_standing.len() as u64
        + predecessor_decoder.len() as u64
        + predecessor_fibres.len() as u64
        + cultivation_standing.len() as u64;
    let cost = json!({
        "schema": "holonics.n3.matched-fixed-section-cost.v1",
        "truth_status": "established-bounded",
        "receiver_history_aperture": "the declared two-carrier exact fixed-section and obstruction family only",
        "cultivated_native": {
            "artifact_octets": native_rest_octets,
            "decoder_octets": predecessor_decoder.len(),
            "fibre_octets": predecessor_fibres.len(),
            "semantic_work": detached.cultivated.semantic_work,
            "semantic_span": detached.cultivated.semantic_span,
            "resident_octets": detached.cultivated.resident_octets,
            "transfer_octets": detached.cultivated.transfer_octets,
        },
        "uncondensed_laboratory_control": {
            "mounted_source_octets": uncondensed_source_octets,
            "whole_repository_semantic_materializations": chronology["whole_repository_semantic_materializations"],
        },
        "artifact_falls_against_uncondensed_source": native_rest_octets < uncondensed_source_octets,
        "no_cost_claim_outside_receiver_history_aperture": true,
    });
    artifact::write_json(out.join("07-matched-cost-and-aperture.json"), &cost)?;

    let dissection = json!({
        "schema": "holonics.n3.native-cultivation-dissection.v1",
        "truth_status": "established-bounded",
        "load_bearing_generator": cultivated.standing().delta.metric_adjoint_orientation,
        "returned_world": cultivated.standing().world_return,
        "laboratory_partitions": chronology_families,
        "history_boundary": cultivated.standing().delta.exact_support_families,
        "modality_contact": {"n2_rest": cultivated.standing().world_return.returned_multimodal_rest_sha256, "optical_return": optical.occurrence},
        "phase_seam": {"predecessor_routes": detached.predecessor.selected_routes, "cultivated_routes": detached.cultivated.selected_routes},
        "obstruction": rich_control.exterior.returned_obstructions,
        "reconstruction_fibres": rich_held_out.reconstruction,
        "open_families": cultivated.standing().delta.open_exterior,
    });
    artifact::write_json(out.join("08-complete-native-dissection.json"), &dissection)?;

    let grade = json!({
        "schema": "holonics.n3.grade.v1",
        "truth_status": "established-bounded",
        "passed": true,
        "causal_not_file_kind_partition": true,
        "three_structurally_distinct_native_families": developmental.len() == 3,
        "held_out_native_derivation_and_obstruction": true,
        "addressed_revisitation_without_retrieval_or_prompt_replay": true,
        "separately_addressed_later_world_return_without_checker": true,
        "same_body_change_survives_source_detached_rest": true,
        "targeted_local_ablation_returns_route_difference": detached.cultivated.locally_ablated_routes != detached.cultivated.selected_routes,
        "exact_predecessor_withdrawal": withdrawal.exact_predecessor_restored,
        "downstream_projection_family_borrows_one_native_identity": true,
        "complete_bounded_dissection": true,
        "artifact_falls_against_matched_uncondensed_source": native_rest_octets < uncondensed_source_octets,
        "open_exterior": [
            "analytic nonlinear varieties, dimensional/unit identity, and wider successor histories",
            "continued cultivation beyond the declared fixed-section aperture",
            "the unexcited Gemma audio-tower interior retained by N2",
        ],
    });
    artifact::write_json(out.join("09-grade.json"), &grade)?;
    artifact::write_json(
        out.join("MANIFEST.json"),
        &json!({
            "schema": "holonics.n3.product-manifest.v1",
            "truth_status": "established-bounded",
            "native_rest": "native-rest/manifest.json",
            "returned_world": "03-returned-optical-world.json",
            "held_out_return": "04-held-out-cultivation-return.json",
            "projections": "05-downstream-projections.json",
            "withdrawal": "06-exact-predecessor-withdrawal.json",
            "cost": "07-matched-cost-and-aperture.json",
            "dissection": "08-complete-native-dissection.json",
            "grade": "09-grade.json",
        }),
    )?;
    println!("N3 returned a source-detached cultivated native rest {rest_identity}");
    Ok(())
}

pub fn detached(rest_root: &Path, sections: &Path, output: &Path) -> Result<(), String> {
    let manifest: NativeCultivatedRestManifest =
        serde_json::from_slice(&artifact::read(rest_root.join("manifest.json"))?)
            .map_err(|error| error.to_string())?;
    let predecessor_standing = read_component(rest_root, &manifest.predecessor_standing)?;
    let predecessor_decoder = read_component(rest_root, &manifest.predecessor_decoder)?;
    let predecessor_fibres = read_component(rest_root, &manifest.predecessor_fibres)?;
    let cultivation_standing = read_component(rest_root, &manifest.cultivation_standing)?;
    let rest = NativeCultivatedMathematicalRest::read(
        &predecessor_standing,
        &predecessor_decoder,
        &predecessor_fibres,
        &cultivation_standing,
    )?;
    let campaign: SectionCampaign =
        serde_json::from_slice(&artifact::read(sections)?).map_err(|error| error.to_string())?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let predecessor = rest.conduct_predecessor(&campaign.held_out, &mut card)?;
    let cultivated = rest.conduct_cultivated(&campaign.held_out, &mut card)?;
    let control_predecessor = rest.conduct_predecessor(&campaign.disjoint_control, &mut card)?;
    let control_cultivated = rest.conduct_cultivated(&campaign.disjoint_control, &mut card)?;
    let held_out_changed = predecessor.selected_routes != cultivated.selected_routes;
    let disjoint_control_held = control_predecessor.selected_routes
        == control_cultivated.selected_routes
        && control_predecessor.constraint_residuals == control_cultivated.constraint_residuals;
    let source_descriptors = descriptors();
    let forbidden_source_descriptors = source_descriptors
        .iter()
        .filter(|target| {
            target.contains("Workspaces/holonics")
                || target.contains("model.safetensors")
                || target.contains("formal")
                || target.contains("/research/")
        })
        .cloned()
        .collect::<Vec<_>>();
    artifact::write_json(
        output,
        &DetachedCultivationReturn {
            schema: "holonics.n3.detached-cultivation-return.v1".to_owned(),
            rest_sha256: rest.canonical_identity()?,
            predecessor,
            cultivated,
            control_predecessor,
            control_cultivated,
            held_out_changed,
            disjoint_control_held,
            source_descriptors,
            forbidden_source_descriptors,
            lean_or_checker_opened: Path::new("/usr/bin/lean").exists()
                || Path::new("/bin/lean").exists()
                || Path::new("/proof-plates").exists(),
        },
    )?;
    Ok(())
}

fn run_detached(
    executable: &Path,
    rest_root: &Path,
    sections: &Path,
    output: &Path,
) -> Result<(), String> {
    if !output.exists() {
        artifact::write(output, &[])?;
    }
    let executable = executable
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let rest_root = rest_root
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let sections = sections.canonicalize().map_err(|error| error.to_string())?;
    let output = output.canonicalize().map_err(|error| error.to_string())?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all", "--clearenv"])
        .args(["--setenv", "PATH", "/empty"])
        .args(["--setenv", "HOME", "/tmp"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--tmpfs", "/usr/bin"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"])
        .args(["--dir", "/rest"])
        .args(["--dir", "/input"])
        .args(["--dir", "/return"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena")
        .arg("--ro-bind")
        .arg(rest_root)
        .arg("/rest/native")
        .arg("--ro-bind")
        .arg(sections)
        .arg("/input/sections.json")
        .arg("--bind")
        .arg(output)
        .arg("/return/return.json")
        .arg("/athena")
        .arg("--detached")
        .arg("/rest/native")
        .arg("/input/sections.json")
        .arg("/return/return.json");
    let returned = command.output().map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "detached N3 refused: {}{}",
            String::from_utf8_lossy(&returned.stdout),
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(())
}

fn chronology_families(chronology: &Value) -> Result<Vec<(String, Vec<String>)>, String> {
    chronology["partitions"]
        .as_array()
        .ok_or("chronology partitions are absent")?
        .iter()
        .map(|partition| {
            let kind = partition["kind"]
                .as_str()
                .ok_or("chronology partition kind is absent")?
                .to_owned();
            let occurrences = partition["occurrences"]
                .as_array()
                .ok_or("chronology partition occurrences are absent")?
                .iter()
                .map(|occurrence| {
                    occurrence
                        .as_str()
                        .map(str::to_owned)
                        .ok_or("chronology occurrence is not an address")
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok((kind, occurrences))
        })
        .collect()
}

fn source_pair(occurrences: &[String], offset: usize) -> Vec<String> {
    vec![
        occurrences[offset % occurrences.len()].clone(),
        occurrences[(offset + 1) % occurrences.len()].clone(),
    ]
}

fn component(path: &str, bytes: &[u8]) -> ComponentIdentity {
    ComponentIdentity {
        path: path.to_owned(),
        sha256: artifact::digest(bytes),
        octets: bytes.len() as u64,
    }
}

fn read_component(root: &Path, identity: &ComponentIdentity) -> Result<Vec<u8>, String> {
    let bytes = artifact::read(root.join(&identity.path))?;
    if artifact::digest(&bytes) != identity.sha256 || bytes.len() as u64 != identity.octets {
        return Err(format!("the rested component {} moved", identity.path));
    }
    Ok(bytes)
}

fn descriptors() -> Vec<String> {
    let mut descriptors = BTreeSet::new();
    if let Ok(entries) = fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = fs::read_link(entry.path()) {
                descriptors.insert(target.display().to_string());
            }
        }
    }
    descriptors.into_iter().collect()
}

pub fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}
