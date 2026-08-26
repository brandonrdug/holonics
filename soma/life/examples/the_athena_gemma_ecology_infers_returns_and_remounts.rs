//! I5: the admitted Phoenix rests freeze as one Athena-Gemma inference ecology.
//!
//! The executable mounts I3 recurrence, I4 heterogeneous transport, and one thin addressed
//! junction. A source-detached process conducts the declined sibling on the resident card. Its
//! complete passage crosses an actual exterior receiver; the returned occurrence commits only the
//! junction. A second source-detached process remounts the committed rest and returns changed
//! recurrent, text, and vision conduct together with all targeted withdrawals.

#[path = "i5/product.rs"]
mod product;

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use holonic_engine::{
    category::BoundaryId,
    cuda_refine::CudaRefineExecutor,
    native_ecology::{
        heterogeneous_fusion::HeterogeneousFusionRest,
        inference_ecology::InferenceEcologyRest,
        recurrent_condensation::{CondensedRecurrentRest, CondensedRoute},
        recurrent_return::ExteriorToolReturn,
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const DEFAULT_I3_REST: &str =
    "output/the_recurrent_realizations_condense_into_a_phoenix_ecology/native-rest";
const DEFAULT_I4_REST: &str =
    "output/the_heterogeneous_ports_found_one_shared_phoenix_ecology/native-rest";
const DEFAULT_OUT: &str = "output/the_athena_gemma_ecology_infers_returns_and_remounts";
const REST_SCHEMA: &str = "holonics.i5.inference-rest-directory.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ComponentIdentity {
    pub role: String,
    pub path: String,
    pub sha256: String,
    pub octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestDirectory {
    schema: String,
    components: Vec<ComponentIdentity>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct InferenceSemanticWork {
    pub recurrent_transition_reads: u64,
    pub recurrent_withdrawal_reads: u64,
    pub visited_incidence_tests: u64,
    pub trace_entries_written: u64,
    pub world_action_reads: u64,
    pub world_decoder_reads: u64,
    pub consequence_writes: u64,
    pub dependency_span: u64,
}

impl InferenceSemanticWork {
    pub(crate) fn total(&self) -> u64 {
        self.recurrent_transition_reads
            + self.recurrent_withdrawal_reads
            + self.visited_incidence_tests
            + self.trace_entries_written
            + self.world_action_reads
            + self.world_decoder_reads
            + self.consequence_writes
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct DetachedApparatus {
    pub device: String,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub launches: u64,
    pub synchronizations: u64,
    pub visited_words_per_route: usize,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
    pub physical_wall_microseconds: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct PortConsequence {
    pub family: u32,
    pub boundary: BoundaryId,
    pub predecessor_address: u32,
    pub successor_address: u32,
    pub selected_address: u32,
    pub predecessor_source_sha256: String,
    pub successor_source_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct DetachedReturn {
    pub schema: String,
    pub committed: bool,
    pub component_sha256: BTreeMap<String, String>,
    pub predecessor_traces: Vec<Vec<u32>>,
    pub successor_traces: Vec<Vec<u32>>,
    pub withdrawn_traces: Vec<Vec<u32>>,
    pub selected_traces: Vec<Vec<u32>>,
    pub predecessor_passages: Vec<String>,
    pub successor_passages: Vec<String>,
    pub withdrawn_passages: Vec<String>,
    pub selected_passages: Vec<String>,
    pub port_consequences: Vec<PortConsequence>,
    pub selected_route_matches_decision: bool,
    pub shared_route_withdrawal_restores_every_predecessor_face: bool,
    pub local_port_withdrawal_preserves_every_other_port: bool,
    pub native_route_withdrawal_reopens_every_passage_family: bool,
    pub source_model_absent_while_native_conduct_continues: bool,
    pub cpu_semantic_callbacks_between_fronts: u64,
    pub source_access_descriptors: Vec<String>,
    pub forbidden_source_access: Vec<String>,
    pub semantic_work: InferenceSemanticWork,
    pub apparatus: DetachedApparatus,
}

enum Args {
    Produce {
        i3_rest: PathBuf,
        i4_rest: PathBuf,
        output: PathBuf,
    },
    DetachedInfer {
        rest: PathBuf,
        output: PathBuf,
    },
}

fn main() -> Result<(), String> {
    match args()? {
        Args::Produce {
            i3_rest,
            i4_rest,
            output,
        } => produce(&i3_rest, &i4_rest, &output),
        Args::DetachedInfer { rest, output } => detached_infer(&rest, &output),
    }
}

fn produce(i3_directory: &Path, i4_directory: &Path, output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "I5 output {} already exists; inspect its addressed receipt instead of replaying it",
            output.display()
        ));
    }
    let recurrent = read_i3(i3_directory)?;
    let heterogeneous = read_i4(i4_directory)?;
    let declined = InferenceEcologyRest::bind_declined(
        recurrent,
        heterogeneous,
        "i5/junction/declined-predecessor".to_owned(),
    )
    .map_err(|error| error.to_string())?;

    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let decline_rest = output.join("matched-decline-rest");
    let declined_manifest = write_rest(&declined, &decline_rest)?;
    let declined_return_directory = output.join("declined-return");
    fs::create_dir(&declined_return_directory).map_err(|error| error.to_string())?;
    run_detached(
        &env::current_exe().map_err(|error| error.to_string())?,
        &decline_rest,
        &declined_return_directory,
    )?;
    let declined_return: DetachedReturn =
        read_json(&declined_return_directory.join("return.json"))?;
    if declined_return.committed
        || declined_return.selected_passages.is_empty()
        || !declined_return.selected_route_matches_decision
    {
        return Err(
            "the matched declined sibling did not return its predecessor passage".to_owned(),
        );
    }

    let emitted = declined_return.selected_passages[0].as_bytes();
    if emitted.is_empty() {
        return Err("the declined inference emitted no complete passage".to_owned());
    }
    let world = output.join("world-consequence");
    fs::create_dir(&world).map_err(|error| error.to_string())?;
    let returned = run_exterior_tee(&world, emitted)?;
    let consequence = fs::read(world.join("consequence.txt")).map_err(|error| error.to_string())?;
    if returned != emitted || consequence != emitted {
        return Err(
            "the exterior receiver did not return the emitted occurrence exactly".to_owned(),
        );
    }
    let exterior = ExteriorToolReturn {
        schema: "holonics.i2.exterior-tool-return.v1".to_owned(),
        receiver: "/usr/bin/tee".to_owned(),
        emitted_occurrence: "i5/emission/declined-main-passage".to_owned(),
        consequence_occurrence: "i5/world/consequence.txt".to_owned(),
        return_occurrence: "i5/return/exterior-echo".to_owned(),
        emitted_sha256: sha256(emitted),
        consequence_sha256: sha256(&consequence),
        echoed_sha256: sha256(&returned),
        before_octets: 0,
        after_octets: consequence.len() as u64,
        exact_difference_octets: consequence.len() as u64,
        process_status: 0,
    };
    exterior.validate().map_err(|error| error.to_string())?;
    write_json(output.join("00-exterior-return.json"), &exterior)?;

    let committed = declined
        .commit_return(exterior, "i5/junction/committed-return".to_owned())
        .map_err(|error| error.to_string())?;
    let canonical_rest = output.join("native-rest");
    let committed_manifest = write_rest(&committed, &canonical_rest)?;
    let committed_return_directory = output.join("committed-return");
    fs::create_dir(&committed_return_directory).map_err(|error| error.to_string())?;
    run_detached(
        &env::current_exe().map_err(|error| error.to_string())?,
        &canonical_rest,
        &committed_return_directory,
    )?;
    let committed_return: DetachedReturn =
        read_json(&committed_return_directory.join("return.json"))?;
    if !committed_return.committed
        || committed_return.selected_passages == declined_return.selected_passages
        || !committed_return.selected_route_matches_decision
    {
        return Err("the committed fresh remount did not ride the changed continuation".to_owned());
    }

    product::finish(
        output,
        i3_directory,
        i4_directory,
        &committed,
        &declined_manifest,
        &committed_manifest,
        &declined_return,
        &committed_return,
    )?;
    println!("I5 returned: {}", output.display());
    println!("declined passage: {:?}", declined_return.selected_passages);
    println!(
        "committed passage: {:?}",
        committed_return.selected_passages
    );
    Ok(())
}

fn detached_infer(rest_directory: &Path, output: &Path) -> Result<(), String> {
    let (rest, manifest) = read_i5(rest_directory)?;
    let recurrent_starts = [
        rest.recurrent.standing.main_start,
        rest.recurrent.standing.held_out_start,
    ];
    let world_starts = rest.heterogeneous.starts();
    let decoder = rest.heterogeneous.decoder_addresses();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let begun = Instant::now();
    let returned = card
        .conduct_inference_ecology_on_device(
            &rest.recurrent.standing.successor_action,
            &recurrent_starts,
            rest.recurrent.standing.predecessor_from,
            rest.recurrent.standing.predecessor_to,
            &rest.heterogeneous.standing.successor_action,
            &decoder,
            &world_starts,
            rest.heterogeneous.standing.family_count as usize,
            rest.heterogeneous.standing.ports.len(),
            rest.committed(),
        )
        .map_err(|error| error.to_string())?;
    let physical_wall_microseconds = begun.elapsed().as_micros();
    let predecessor_traces = traces(
        &returned.predecessor_trace,
        &returned.predecessor_lengths,
        returned.trace_stride,
    )?;
    let successor_traces = traces(
        &returned.successor_trace,
        &returned.successor_lengths,
        returned.trace_stride,
    )?;
    let withdrawn_traces = traces(
        &returned.withdrawn_trace,
        &returned.withdrawn_lengths,
        returned.trace_stride,
    )?;
    let selected_traces = traces(
        &returned.selected_trace,
        &returned.selected_lengths,
        returned.trace_stride,
    )?;
    for (at, start) in recurrent_starts.iter().copied().enumerate() {
        if predecessor_traces[at]
            != rest
                .recurrent
                .trace(CondensedRoute::Predecessor, start)
                .map_err(|error| error.to_string())?
            || successor_traces[at]
                != rest
                    .recurrent
                    .trace(CondensedRoute::Successor, start)
                    .map_err(|error| error.to_string())?
            || withdrawn_traces[at]
                != rest
                    .recurrent
                    .trace(CondensedRoute::Withdrawn, start)
                    .map_err(|error| error.to_string())?
        {
            return Err("the resident inference route disagrees with its exact owner".to_owned());
        }
    }
    let decode = |rows: &[Vec<u32>]| {
        rows.iter()
            .map(|trace| {
                rest.recurrent
                    .decode_trace(trace)
                    .map_err(|error| error.to_string())
            })
            .collect::<Result<Vec<_>, _>>()
    };
    let predecessor_passages = decode(&predecessor_traces)?;
    let successor_passages = decode(&successor_traces)?;
    let withdrawn_passages = decode(&withdrawn_traces)?;
    let selected_passages = decode(&selected_traces)?;
    let selected_route_matches_decision = if rest.committed() {
        selected_traces == successor_traces
            && returned.selected_consequence == returned.successor_consequence
    } else {
        selected_traces == predecessor_traces
            && returned.selected_consequence == returned.predecessor_consequence
    };

    let ports = rest.heterogeneous.standing.ports.len();
    let states = rest.heterogeneous.standing.state_count as usize;
    let mut port_consequences = Vec::with_capacity(returned.predecessor_consequence.len());
    for (cell, selected_address) in returned.selected_consequence.iter().copied().enumerate() {
        let family = (cell / ports) as u32;
        let boundary = rest.heterogeneous.standing.ports[cell % ports].boundary;
        let before_at = cell * states;
        let after_at = before_at + 1;
        port_consequences.push(PortConsequence {
            family,
            boundary,
            predecessor_address: returned.predecessor_consequence[cell],
            successor_address: returned.successor_consequence[cell],
            selected_address,
            predecessor_source_sha256: rest.heterogeneous.decoder.consequences[before_at]
                .source_consequence_sha256
                .clone(),
            successor_source_sha256: rest.heterogeneous.decoder.consequences[after_at]
                .source_consequence_sha256
                .clone(),
        });
    }
    let shared_route_withdrawal_restores_every_predecessor_face = returned
        .shared_ablated_consequence
        .iter()
        .zip(&returned.predecessor_consequence)
        .all(|(ablated, predecessor)| ablated == predecessor)
        && returned
            .successor_consequence
            .iter()
            .zip(&returned.predecessor_consequence)
            .all(|(successor, predecessor)| successor != predecessor);
    let local_port_withdrawal_preserves_every_other_port =
        (0..returned.predecessor_consequence.len()).all(|cell| {
            let local_port = cell % ports;
            (0..ports).all(|withdrawn_port| {
                let actual = returned.local_ablated_consequence[cell * ports + withdrawn_port];
                let expected = if local_port == withdrawn_port {
                    returned.predecessor_consequence[cell]
                } else {
                    returned.successor_consequence[cell]
                };
                actual == expected
            })
        });
    let native_route_withdrawal_reopens_every_passage_family = predecessor_passages
        .iter()
        .zip(&withdrawn_passages)
        .all(|(passage, withdrawn)| passage != withdrawn)
        && successor_passages
            .iter()
            .zip(&withdrawn_passages)
            .all(|(passage, withdrawn)| passage != withdrawn);
    let descriptors = descriptor_targets()?;
    let forbidden = descriptors
        .iter()
        .filter(|target| {
            let lower = target.to_ascii_lowercase();
            lower.contains("gemma")
                || lower.contains("safetensors")
                || lower.contains("tokenizer")
                || lower.contains("source-conduct")
                || lower.contains("/downloads/")
        })
        .cloned()
        .collect::<Vec<_>>();
    let source_model_absent_while_native_conduct_continues =
        forbidden.is_empty() && !selected_passages.is_empty() && !port_consequences.is_empty();
    let steps = |lengths: &[u32]| {
        lengths
            .iter()
            .map(|length| u64::from(length - 1))
            .sum::<u64>()
    };
    let recurrent_transition_reads = steps(&returned.predecessor_lengths)
        + steps(&returned.successor_lengths)
        + steps(&returned.selected_lengths);
    let recurrent_withdrawal_reads = steps(&returned.withdrawn_lengths);
    let visited_incidence_tests = recurrent_transition_reads + recurrent_withdrawal_reads;
    let trace_entries_written =
        (returned.trace_stride * returned.predecessor_lengths.len() * 4) as u64;
    let world_cells = returned.predecessor_consequence.len() as u64;
    let consequence_writes = world_cells * 4 + returned.local_ablated_consequence.len() as u64;
    let semantic_work = InferenceSemanticWork {
        recurrent_transition_reads,
        recurrent_withdrawal_reads,
        visited_incidence_tests,
        trace_entries_written,
        world_action_reads: world_cells,
        world_decoder_reads: world_cells * 2,
        consequence_writes,
        dependency_span: returned
            .selected_lengths
            .iter()
            .copied()
            .max()
            .map_or(0, |length| u64::from(length - 1) + 1),
    };
    let report = DetachedReturn {
        schema: "holonics.i5.detached-inference-return.v1".to_owned(),
        committed: rest.committed(),
        component_sha256: manifest
            .components
            .iter()
            .map(|component| (component.role.clone(), component.sha256.clone()))
            .collect(),
        predecessor_traces,
        successor_traces,
        withdrawn_traces,
        selected_traces,
        predecessor_passages,
        successor_passages,
        withdrawn_passages,
        selected_passages,
        port_consequences,
        selected_route_matches_decision,
        shared_route_withdrawal_restores_every_predecessor_face,
        local_port_withdrawal_preserves_every_other_port,
        native_route_withdrawal_reopens_every_passage_family,
        source_model_absent_while_native_conduct_continues,
        cpu_semantic_callbacks_between_fronts: 0,
        source_access_descriptors: descriptors,
        forbidden_source_access: forbidden,
        semantic_work,
        apparatus: DetachedApparatus {
            device: card.device_name().to_owned(),
            block_threads: returned.block_threads,
            active_lanes: returned.active_lanes,
            launches: returned.launches,
            synchronizations: returned.synchronizations,
            visited_words_per_route: returned.visited_words,
            host_ingress_octets: returned.host_ingress_octets,
            host_egress_octets: returned.host_egress_octets,
            resident_octets: returned.resident_octets,
            physical_wall_microseconds,
        },
    };
    if !report.selected_route_matches_decision
        || !report.shared_route_withdrawal_restores_every_predecessor_face
        || !report.local_port_withdrawal_preserves_every_other_port
        || !report.native_route_withdrawal_reopens_every_passage_family
        || !report.source_model_absent_while_native_conduct_continues
        || report.apparatus.launches != 1
        || report.apparatus.synchronizations != 1
    {
        return Err("the source-detached inference circulation refused its local grade".to_owned());
    }
    write_json(output, &report)
}

fn read_i3(directory: &Path) -> Result<CondensedRecurrentRest, String> {
    let standing = fs::read(directory.join("standing.json")).map_err(|error| error.to_string())?;
    let decoder = fs::read(directory.join("decoder.json")).map_err(|error| error.to_string())?;
    let fibres = fs::read(directory.join("fibres.json")).map_err(|error| error.to_string())?;
    CondensedRecurrentRest::read(&standing, &decoder, &fibres).map_err(|error| error.to_string())
}

fn read_i4(directory: &Path) -> Result<HeterogeneousFusionRest, String> {
    let standing = fs::read(directory.join("standing.json")).map_err(|error| error.to_string())?;
    let decoder = fs::read(directory.join("decoder.json")).map_err(|error| error.to_string())?;
    let fibres = fs::read(directory.join("fibres.json")).map_err(|error| error.to_string())?;
    HeterogeneousFusionRest::read(&standing, &decoder, &fibres).map_err(|error| error.to_string())
}

fn write_rest(rest: &InferenceEcologyRest, directory: &Path) -> Result<RestDirectory, String> {
    fs::create_dir(directory).map_err(|error| error.to_string())?;
    let components = [
        (
            "recurrent-standing",
            "recurrent-standing.json",
            rest.recurrent
                .standing_bytes()
                .map_err(|error| error.to_string())?,
        ),
        (
            "recurrent-decoder",
            "recurrent-decoder.json",
            rest.recurrent
                .decoder_bytes()
                .map_err(|error| error.to_string())?,
        ),
        (
            "recurrent-fibres",
            "recurrent-fibres.json",
            rest.recurrent
                .fibre_bytes()
                .map_err(|error| error.to_string())?,
        ),
        (
            "heterogeneous-standing",
            "heterogeneous-standing.json",
            rest.heterogeneous
                .standing_bytes()
                .map_err(|error| error.to_string())?,
        ),
        (
            "heterogeneous-decoder",
            "heterogeneous-decoder.json",
            rest.heterogeneous
                .decoder_bytes()
                .map_err(|error| error.to_string())?,
        ),
        (
            "heterogeneous-fibres",
            "heterogeneous-fibres.json",
            rest.heterogeneous
                .fibre_bytes()
                .map_err(|error| error.to_string())?,
        ),
        (
            "inference-junction",
            "inference-junction.json",
            rest.junction_bytes().map_err(|error| error.to_string())?,
        ),
    ];
    let mut identities = Vec::with_capacity(components.len());
    for (role, path, bytes) in components {
        fs::write(directory.join(path), &bytes).map_err(|error| error.to_string())?;
        identities.push(ComponentIdentity {
            role: role.to_owned(),
            path: path.to_owned(),
            sha256: sha256(&bytes),
            octets: bytes.len() as u64,
        });
    }
    let manifest = RestDirectory {
        schema: REST_SCHEMA.to_owned(),
        components: identities,
    };
    write_json(directory.join("manifest.json"), &manifest)?;
    Ok(manifest)
}

fn read_i5(directory: &Path) -> Result<(InferenceEcologyRest, RestDirectory), String> {
    let manifest: RestDirectory = read_json(&directory.join("manifest.json"))?;
    if manifest.schema != REST_SCHEMA || manifest.components.len() != 7 {
        return Err("the I5 rest directory schema or component population moved".to_owned());
    }
    let mut components = BTreeMap::new();
    for identity in &manifest.components {
        let bytes = fs::read(directory.join(&identity.path)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != identity.octets || sha256(&bytes) != identity.sha256 {
            return Err(format!("I5 component {} failed identity", identity.role));
        }
        if components.insert(identity.role.as_str(), bytes).is_some() {
            return Err("the I5 rest repeats a component role".to_owned());
        }
    }
    let component = |role: &str| {
        components
            .get(role)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("I5 component {role} is absent"))
    };
    let rest = InferenceEcologyRest::read(
        component("recurrent-standing")?,
        component("recurrent-decoder")?,
        component("recurrent-fibres")?,
        component("heterogeneous-standing")?,
        component("heterogeneous-decoder")?,
        component("heterogeneous-fibres")?,
        component("inference-junction")?,
    )
    .map_err(|error| error.to_string())?;
    Ok((rest, manifest))
}

fn traces(flat: &[u32], lengths: &[u32], stride: usize) -> Result<Vec<Vec<u32>>, String> {
    if flat.len() != lengths.len() * stride {
        return Err("the resident trace wire has the wrong extent".to_owned());
    }
    lengths
        .iter()
        .enumerate()
        .map(|(at, length)| {
            let length = *length as usize;
            if length < 2 || length > stride {
                return Err("the resident trace did not close".to_owned());
            }
            Ok(flat[at * stride..at * stride + length].to_vec())
        })
        .collect()
}

fn run_exterior_tee(world: &Path, emitted: &[u8]) -> Result<Vec<u8>, String> {
    let world = world.canonicalize().map_err(|error| error.to_string())?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    bind_system_libraries(&mut command);
    command
        .arg("--bind")
        .arg(world)
        .arg("/world")
        .args(["--chdir", "/tmp", "/usr/bin/tee", "/world/consequence.txt"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn().map_err(|error| error.to_string())?;
    child
        .stdin
        .take()
        .ok_or("the exterior receiver has no input port")?
        .write_all(emitted)
        .map_err(|error| error.to_string())?;
    let returned = child
        .wait_with_output()
        .map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "exterior receiver refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(returned.stdout)
}

fn run_detached(executable: &Path, rest: &Path, output: &Path) -> Result<(), String> {
    let executable = executable
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let rest = rest.canonicalize().map_err(|error| error.to_string())?;
    let output = output.canonicalize().map_err(|error| error.to_string())?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    bind_system_libraries(&mut command);
    command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/i5")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/i5",
            "--detached-infer",
            "/rest",
            "/return/return.json",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let returned = command.output().map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "detached I5 inference refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(())
}

fn bind_system_libraries(command: &mut Command) {
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
}

fn descriptor_targets() -> Result<Vec<String>, String> {
    let mut targets = fs::read_dir("/proc/self/fd")
        .map_err(|error| error.to_string())?
        .filter_map(Result::ok)
        .filter_map(|entry| fs::read_link(entry.path()).ok())
        .map(|target| target.display().to_string())
        .collect::<Vec<_>>();
    targets.sort();
    targets.dedup();
    Ok(targets)
}

pub(crate) fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(
        path,
        serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}

pub(crate) fn sha256(bytes: &[u8]) -> String {
    hex(Sha256::digest(bytes))
}

pub(crate) fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn args() -> Result<Args, String> {
    let mut values = env::args().skip(1);
    match values.next().as_deref() {
        None => Ok(Args::Produce {
            i3_rest: PathBuf::from(DEFAULT_I3_REST),
            i4_rest: PathBuf::from(DEFAULT_I4_REST),
            output: PathBuf::from(DEFAULT_OUT),
        }),
        Some("--produce") => {
            let i3_rest = values
                .next()
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(DEFAULT_I3_REST));
            let i4_rest = values
                .next()
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(DEFAULT_I4_REST));
            let output = values
                .next()
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(DEFAULT_OUT));
            if values.next().is_some() {
                return Err("too many I5 --produce arguments".to_owned());
            }
            Ok(Args::Produce {
                i3_rest,
                i4_rest,
                output,
            })
        }
        Some("--detached-infer") => {
            let rest = values
                .next()
                .map(PathBuf::from)
                .ok_or("--detached-infer requires REST")?;
            let output = values
                .next()
                .map(PathBuf::from)
                .ok_or("--detached-infer requires OUTPUT")?;
            if values.next().is_some() {
                return Err("too many I5 --detached-infer arguments".to_owned());
            }
            Ok(Args::DetachedInfer { rest, output })
        }
        _ => Err(
            "usage: [--produce [I3_REST I4_REST OUTPUT]] | --detached-infer REST OUTPUT".to_owned(),
        ),
    }
}
