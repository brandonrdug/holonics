use std::fs;
use std::path::Path;
use std::time::Instant;

use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::mathematical_particle::DynamicMorphologyRest;
use serde::{Deserialize, Serialize};

use super::artifact;

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HeldOutInquiry {
    pub schema: String,
    pub occurrence: String,
    pub material_sha256: String,
    pub predecessor_rest_sha256: String,
    pub entering_native_state: u32,
    pub structurally_related_action: Vec<u32>,
    pub outside_development_return_closure: bool,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DetachedMorphologyReturn {
    pub schema: String,
    pub rest_sha256: String,
    pub held_out_occurrence: String,
    pub returned_adjoint: Vec<i64>,
    pub predecessor_trace: Vec<u32>,
    pub successor_trace: Vec<u32>,
    pub withdrawn_trace: Vec<u32>,
    pub predecessor_lengths: Vec<u32>,
    pub successor_lengths: Vec<u32>,
    pub withdrawn_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub held_out_changed: bool,
    pub withdrawal_restored: bool,
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

pub fn conduct(rest_path: &Path, held_out_path: &Path, receipt_path: &Path) -> Result<(), String> {
    let rest_bytes = fs::read(rest_path).map_err(|error| error.to_string())?;
    let rest = DynamicMorphologyRest::read(&rest_bytes).map_err(|error| error.to_string())?;
    let held_out: HeldOutInquiry =
        serde_json::from_slice(&fs::read(held_out_path).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    if held_out.schema != "holonics.r3.held-out-inquiry.v1"
        || held_out.occurrence != rest.held_out_occurrence
        || held_out.entering_native_state != rest.held_out_start
        || held_out.structurally_related_action != rest.predecessor.native_action
        || held_out.predecessor_rest_sha256 != rest.delta.exact_withdrawal.predecessor_sha256
        || !held_out.outside_development_return_closure
    {
        return Err(
            "the held-out inquiry is not the addressed post-development occurrence".to_owned(),
        );
    }
    let incidence = rest.support_incidence_wire();
    let covector = rest.returned_covector_wire();
    let starts = rest.recurrence_starts();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let began = Instant::now();
    let returned = card
        .conduct_dynamic_morphology_on_device(
            &rest.predecessor.native_action,
            &incidence,
            &covector,
            &starts,
        )
        .map_err(|error| error.to_string())?;
    let physical_wall_microseconds = began.elapsed().as_micros();
    let predecessor = artifact::traces(
        &returned.predecessor_trace,
        &returned.predecessor_lengths,
        returned.trace_stride,
    )?;
    let successor = artifact::traces(
        &returned.successor_trace,
        &returned.successor_lengths,
        returned.trace_stride,
    )?;
    let held_out_changed = predecessor[1] != successor[1];
    let withdrawal_restored = returned.predecessor_trace == returned.withdrawn_trace
        && returned.predecessor_lengths == returned.withdrawn_lengths
        && returned.predecessor_action == returned.withdrawn_action;
    if !returned.committed || !held_out_changed || !withdrawal_restored {
        return Err(
            "the detached successor lost its held-out change or exact withdrawal".to_owned(),
        );
    }
    let open_descriptors = artifact::descriptors();
    let forbidden_needles = [
        "/research/fixtures/",
        "/soma/formal/",
        "06-returned-constraint.lean",
        "08-derivation-complex.svg",
        "09-derivation-complex.png",
        "inquiry.jsonl",
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
    if !forbidden_source_access.is_empty() {
        return Err(format!(
            "detached R3 retained forbidden sources: {forbidden_source_access:?}"
        ));
    }
    let receipt = DetachedMorphologyReturn {
        schema: "holonics.r3.detached-morphology-return.v1".to_owned(),
        rest_sha256: artifact::digest(&rest_bytes),
        held_out_occurrence: held_out.occurrence,
        returned_adjoint: returned.returned_adjoint,
        predecessor_trace: returned.predecessor_trace,
        successor_trace: returned.successor_trace,
        withdrawn_trace: returned.withdrawn_trace,
        predecessor_lengths: returned.predecessor_lengths,
        successor_lengths: returned.successor_lengths,
        withdrawn_lengths: returned.withdrawn_lengths,
        trace_stride: returned.trace_stride,
        held_out_changed,
        withdrawal_restored,
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
    artifact::write_json(receipt_path, &receipt)
}

pub fn read(path: &Path) -> Result<DetachedMorphologyReturn, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}
