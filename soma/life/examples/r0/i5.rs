use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::time::Instant;

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    phoenix::{heterogeneous_fusion::ModalityPort, inference_ecology::InferenceEcologyRest},
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const I5_REST: &str = "output/the_athena_gemma_ecology_infers_returns_and_remounts/native-rest";
const REST_SCHEMA: &str = "holonics.i5.inference-rest-directory.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ComponentIdentity {
    pub role: String,
    pub path: String,
    pub sha256: String,
    pub octets: u64,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestDirectory {
    schema: String,
    components: Vec<ComponentIdentity>,
}

#[derive(Debug, Serialize)]
pub struct PortConsequence {
    pub family: u32,
    pub port: ModalityPort,
    pub selected_address: u32,
    pub shared_withdrawn_address: u32,
}

#[derive(Debug, Serialize)]
pub struct ExactWork {
    pub recurrent_transition_reads: u64,
    pub recurrent_withdrawal_reads: u64,
    pub visited_incidence_tests: u64,
    pub trace_entries_written: u64,
    pub world_action_reads: u64,
    pub world_decoder_reads: u64,
    pub consequence_writes: u64,
    pub dependency_span: u64,
    pub total: u64,
}

#[derive(Debug, Serialize)]
pub struct ApparatusReceipt {
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub visited_words_per_route: usize,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
    pub physical_wall_microseconds: u128,
    pub cpu_semantic_callbacks_between_fronts: u64,
}

#[derive(Debug, Serialize)]
pub struct I5BaselineReturn {
    pub rest_schema: String,
    pub components: Vec<ComponentIdentity>,
    pub component_sha256: BTreeMap<String, String>,
    pub committed: bool,
    pub entry_boundary: String,
    pub inquiry_occurrence_was_an_entry_argument: bool,
    pub operation_passage_was_an_entry_argument: bool,
    pub selected_traces: Vec<Vec<u32>>,
    pub alternative_predecessor_traces: Vec<Vec<u32>>,
    pub alternative_successor_traces: Vec<Vec<u32>>,
    pub withdrawn_traces: Vec<Vec<u32>>,
    pub selected_passages: Vec<String>,
    pub predecessor_passages: Vec<String>,
    pub successor_passages: Vec<String>,
    pub withdrawn_passages: Vec<String>,
    pub port_consequences: Vec<PortConsequence>,
    pub exact_work: ExactWork,
    pub apparatus: ApparatusReceipt,
    pub source_accessed_paths: Vec<String>,
    pub forbidden_formal_or_inquiry_source_access: bool,
}

pub fn conduct(root: &Path) -> Result<I5BaselineReturn, String> {
    let directory = root.join(I5_REST);
    let manifest_path = directory.join("manifest.json");
    let manifest_bytes = fs::read(&manifest_path).map_err(|error| error.to_string())?;
    let manifest: RestDirectory =
        serde_json::from_slice(&manifest_bytes).map_err(|error| error.to_string())?;
    if manifest.schema != REST_SCHEMA || manifest.components.len() != 7 {
        return Err("the canonical I5 rest schema or component population moved".to_owned());
    }
    let mut components = BTreeMap::<String, Vec<u8>>::new();
    let mut accessed = vec![format!("{I5_REST}/manifest.json")];
    for identity in &manifest.components {
        let relative = format!("{I5_REST}/{}", identity.path);
        let bytes = fs::read(root.join(&relative)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != identity.octets || digest(&bytes) != identity.sha256 {
            return Err(format!("I5 component {} failed identity", identity.role));
        }
        accessed.push(relative);
        if components.insert(identity.role.clone(), bytes).is_some() {
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

    let recurrent_starts = [
        rest.recurrent.standing.main_start,
        rest.recurrent.standing.held_out_start,
    ];
    let world_starts = rest.heterogeneous.starts();
    let decoder = rest.heterogeneous.decoder_addresses();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let began = Instant::now();
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
    let physical_wall_microseconds = began.elapsed().as_micros();

    let predecessor = traces(
        &returned.predecessor_trace,
        &returned.predecessor_lengths,
        returned.trace_stride,
    )?;
    let successor = traces(
        &returned.successor_trace,
        &returned.successor_lengths,
        returned.trace_stride,
    )?;
    let withdrawn = traces(
        &returned.withdrawn_trace,
        &returned.withdrawn_lengths,
        returned.trace_stride,
    )?;
    let selected = traces(
        &returned.selected_trace,
        &returned.selected_lengths,
        returned.trace_stride,
    )?;
    let decode = |population: &[Vec<u32>]| {
        population
            .iter()
            .map(|trace| {
                rest.recurrent
                    .decode_trace(trace)
                    .map_err(|error| error.to_string())
            })
            .collect::<Result<Vec<_>, _>>()
    };
    let predecessor_passages = decode(&predecessor)?;
    let successor_passages = decode(&successor)?;
    let withdrawn_passages = decode(&withdrawn)?;
    let selected_passages = decode(&selected)?;

    let ports = rest.heterogeneous.standing.ports.len();
    let port_consequences = returned
        .selected_consequence
        .iter()
        .copied()
        .zip(returned.shared_ablated_consequence.iter().copied())
        .enumerate()
        .map(
            |(cell, (selected_address, shared_withdrawn_address))| PortConsequence {
                family: (cell / ports) as u32,
                port: rest.heterogeneous.standing.ports[cell % ports].port,
                selected_address,
                shared_withdrawn_address,
            },
        )
        .collect::<Vec<_>>();
    let recurrent_transition_reads = (returned.predecessor_lengths.iter().sum::<u32>()
        + returned.successor_lengths.iter().sum::<u32>()
        + returned.selected_lengths.iter().sum::<u32>()
        - 3 * returned.predecessor_lengths.len() as u32)
        as u64;
    let recurrent_withdrawal_reads = (returned.withdrawn_lengths.iter().sum::<u32>()
        - returned.withdrawn_lengths.len() as u32) as u64;
    let visited_incidence_tests = recurrent_transition_reads + recurrent_withdrawal_reads;
    // The card writes each fixed-stride route buffer in full.  Semantic work prices that exact
    // resident write population, including padding retained by the wire, rather than only the
    // decoded prefix lengths.
    let trace_entries_written =
        (returned.trace_stride * returned.predecessor_lengths.len() * 4) as u64;
    let world_action_reads = returned.selected_consequence.len() as u64;
    let world_decoder_reads = (returned.selected_consequence.len() * 2) as u64;
    let consequence_writes = (returned.selected_consequence.len() * (4 + ports)) as u64;
    let dependency_span = returned.selected_lengths.iter().copied().max().unwrap_or(0) as u64;
    let total = recurrent_transition_reads
        + recurrent_withdrawal_reads
        + visited_incidence_tests
        + trace_entries_written
        + world_action_reads
        + world_decoder_reads
        + consequence_writes;
    let device_name = card.device_name().to_owned();
    let forbidden_formal_or_inquiry_source_access = accessed
        .iter()
        .any(|path| path.contains("FamilySupport.lean") || path.contains("r0_rich_inquiry"));
    if forbidden_formal_or_inquiry_source_access {
        return Err("the I5 conduct crossed a forbidden inquiry/formal source path".to_owned());
    }
    Ok(I5BaselineReturn {
        rest_schema: manifest.schema,
        components: manifest.components.clone(),
        component_sha256: manifest
            .components
            .iter()
            .map(|identity| (identity.role.clone(), identity.sha256.clone()))
            .collect(),
        committed: rest.committed(),
        entry_boundary: "frozen recurrent action + two recurrent starts + frozen heterogeneous action/decoder/world starts + family/port extents + committed decision".to_owned(),
        inquiry_occurrence_was_an_entry_argument: false,
        operation_passage_was_an_entry_argument: false,
        selected_traces: selected,
        alternative_predecessor_traces: predecessor,
        alternative_successor_traces: successor,
        withdrawn_traces: withdrawn,
        selected_passages,
        predecessor_passages,
        successor_passages,
        withdrawn_passages,
        port_consequences,
        exact_work: ExactWork {
            recurrent_transition_reads,
            recurrent_withdrawal_reads,
            visited_incidence_tests,
            trace_entries_written,
            world_action_reads,
            world_decoder_reads,
            consequence_writes,
            dependency_span,
            total,
        },
        apparatus: ApparatusReceipt {
            device: device_name,
            launches: returned.launches,
            synchronizations: returned.synchronizations,
            block_threads: returned.block_threads,
            active_lanes: returned.active_lanes,
            visited_words_per_route: returned.visited_words,
            host_ingress_octets: returned.host_ingress_octets,
            host_egress_octets: returned.host_egress_octets,
            resident_octets: returned.resident_octets,
            physical_wall_microseconds,
            cpu_semantic_callbacks_between_fronts: 0,
        },
        source_accessed_paths: accessed,
        forbidden_formal_or_inquiry_source_access,
    })
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

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
