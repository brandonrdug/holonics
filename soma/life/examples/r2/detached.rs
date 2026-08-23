use std::fs;
use std::path::Path;
use std::time::Instant;

use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::mathematical_particle::DerivationRecurrenceRest;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DetachedDerivationReturn {
    pub schema: String,
    pub rest_sha256: String,
    pub native_trace: Vec<u32>,
    pub trace_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub device: String,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
    pub physical_wall_microseconds: u128,
    pub open_descriptors: Vec<String>,
    pub forbidden_source_access: Vec<String>,
    pub cpu_semantic_callbacks_between_fronts: u64,
}

pub fn conduct(rest_path: &Path, receipt_path: &Path) -> Result<(), String> {
    let rest_bytes = fs::read(rest_path).map_err(|error| error.to_string())?;
    let rest = DerivationRecurrenceRest::read(&rest_bytes).map_err(|error| error.to_string())?;
    let states = rest.native_action.len();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let began = Instant::now();
    let returned = card
        .conduct_returned_recurrences_on_device(
            states,
            1,
            &rest.native_action,
            0,
            &rest.native_starts,
            0,
            0,
            0,
            0,
        )
        .map_err(|error| error.to_string())?;
    let physical_wall_microseconds = began.elapsed().as_micros();
    if returned.committed
        || returned.predecessor_trace != returned.successor_trace
        || returned.predecessor_trace != returned.ablated_trace
        || returned.predecessor_lengths != returned.successor_lengths
        || returned.predecessor_lengths != returned.ablated_lengths
    {
        return Err(
            "a source-free R2 rest invented a returned constraint or a second body".to_owned(),
        );
    }
    let open_descriptors = descriptors();
    let forbidden_needles = [
        "/research/fixtures/",
        "/soma/formal/",
        "inquiry.jsonl",
        "inquiry.lean",
        "support-route-a.svg",
        "support-route-b.svg",
        "familySupport.lean",
    ];
    let forbidden_source_access = open_descriptors
        .iter()
        .filter(|path| {
            let lower = path.to_ascii_lowercase();
            forbidden_needles
                .iter()
                .any(|needle| lower.contains(&needle.to_ascii_lowercase()))
        })
        .cloned()
        .collect::<Vec<_>>();
    let receipt = DetachedDerivationReturn {
        schema: "holonics.r2.detached-derivation-return.v1".to_owned(),
        rest_sha256: digest(&rest_bytes),
        native_trace: returned.predecessor_trace,
        trace_lengths: returned.predecessor_lengths,
        trace_stride: returned.trace_stride,
        device: card.device_name().to_owned(),
        block_threads: returned.block_threads,
        active_lanes: returned.active_lanes,
        launches: returned.launches,
        synchronizations: returned.synchronizations,
        host_ingress_octets: returned.host_ingress_octets,
        host_egress_octets: returned.host_egress_octets,
        resident_octets: returned.resident_octets,
        physical_wall_microseconds,
        open_descriptors,
        forbidden_source_access,
        cpu_semantic_callbacks_between_fronts: 0,
    };
    if !receipt.forbidden_source_access.is_empty() {
        return Err(format!(
            "the detached R2 recurrence retained forbidden sources: {:?}",
            receipt.forbidden_source_access
        ));
    }
    let bytes = serde_json::to_vec_pretty(&receipt).map_err(|error| error.to_string())?;
    fs::write(receipt_path, bytes).map_err(|error| error.to_string())
}

pub fn read(path: &Path) -> Result<DetachedDerivationReturn, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}

fn descriptors() -> Vec<String> {
    let mut paths = Vec::new();
    if let Ok(entries) = fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = fs::read_link(entry.path()) {
                paths.push(target.to_string_lossy().into_owned());
            }
        }
    }
    paths.sort();
    paths.dedup();
    paths
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
