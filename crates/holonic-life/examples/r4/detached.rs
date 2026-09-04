use std::fs;
use std::path::Path;
use std::time::Instant;

use holonic_engine::cuda_refine::CudaRefineExecutor;
use holonic_engine::receiver_history_compression::NativeStateId;
use life::mathematical_particle::LongHorizonRetainedBoundary;
use serde::{Deserialize, Serialize};

use super::artifact;

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DetachedInquiry {
    pub schema: String,
    pub boundary_identity: String,
    pub occurrence: String,
    pub words: Vec<u32>,
    pub word_offsets: Vec<u32>,
    pub native_starts: Vec<u32>,
    pub expected_trace: Vec<u32>,
    pub expected_trace_offsets: Vec<u32>,
    pub reconstructed_occurrence: String,
    pub expected_reconstruction_sha256: String,
    pub cultivated_front: usize,
    pub predecessor_control_front: usize,
    pub outside_development_return_closure: bool,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DetachedBoundaryReturn {
    pub schema: String,
    pub boundary_identity: String,
    pub inquiry_occurrence: String,
    pub native_trace: Vec<u32>,
    pub trace_offsets: Vec<u32>,
    pub reconstructed_history_sha256: String,
    pub reconstructed_history_octets: usize,
    pub remote_interior_reopened_without_source: bool,
    pub cultivated_revisit_changed_the_boundary: bool,
    pub ordered_holonomy_preserved: bool,
    pub device: String,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
    pub physical_wall_microseconds: u128,
    pub cpu_semantic_callbacks_between_fronts: u64,
    pub open_descriptors: Vec<String>,
    pub forbidden_source_access: Vec<String>,
}

pub fn conduct(
    standing_path: &Path,
    decoder_path: &Path,
    fibre_path: &Path,
    inquiry_path: &Path,
    receipt_path: &Path,
) -> Result<(), String> {
    let standing = fs::read(standing_path).map_err(|error| error.to_string())?;
    let decoder = fs::read(decoder_path).map_err(|error| error.to_string())?;
    let fibres = fs::read(fibre_path).map_err(|error| error.to_string())?;
    let boundary = LongHorizonRetainedBoundary::read(&standing, &decoder, &fibres)
        .map_err(|error| error.to_string())?;
    let inquiry: DetachedInquiry =
        serde_json::from_slice(&fs::read(inquiry_path).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    if inquiry.schema != "holonics.r4.detached-inquiry.v1"
        || inquiry.boundary_identity != boundary.standing.boundary_identity
        || inquiry.occurrence.is_empty()
        || inquiry.native_starts.is_empty()
        || inquiry.word_offsets.len() != inquiry.native_starts.len() + 1
        || inquiry.cultivated_front >= inquiry.native_starts.len()
        || inquiry.predecessor_control_front >= inquiry.native_starts.len()
        || !inquiry.outside_development_return_closure
    {
        return Err("the detached inquiry is not the admitted later revisit".to_owned());
    }
    let expected = inquiry
        .word_offsets
        .windows(2)
        .zip(&inquiry.native_starts)
        .flat_map(|(interval, start)| {
            boundary
                .native_trace(
                    NativeStateId(u64::from(*start)),
                    &inquiry.words[interval[0] as usize..interval[1] as usize],
                )
                .expect("the inquiry was validated against this rest")
                .into_iter()
                .map(|state| state.0 as u32)
        })
        .collect::<Vec<_>>();
    if expected != inquiry.expected_trace {
        return Err("the inquiry trace is not derived from the remounted boundary".to_owned());
    }

    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let began = Instant::now();
    let returned = card
        .conduct_native_ragged_traces_on_device(
            boundary.standing.native_states.len(),
            boundary.standing.generator_table.len() / boundary.standing.native_states.len(),
            &boundary.standing.generator_table,
            &inquiry.words,
            &inquiry.word_offsets,
            &inquiry.native_starts,
        )
        .map_err(|error| error.to_string())?;
    let physical_wall_microseconds = began.elapsed().as_micros();
    if returned.native_trace != inquiry.expected_trace
        || returned.trace_offsets != inquiry.expected_trace_offsets
    {
        return Err(
            "the resident later revisit disagrees with the exact retained boundary".to_owned(),
        );
    }
    let endpoint = |front: usize| -> Result<u32, String> {
        let end = returned
            .trace_offsets
            .get(front + 1)
            .copied()
            .ok_or("front trace boundary absent")? as usize;
        returned
            .native_trace
            .get(end.saturating_sub(1))
            .copied()
            .ok_or("front endpoint absent".to_owned())
    };
    let cultivated_revisit_changed_the_boundary =
        endpoint(inquiry.cultivated_front)? != endpoint(inquiry.predecessor_control_front)?;
    let holonomy = &boundary.standing.ordered_holonomy;
    let ordered_holonomy_preserved = holonomy.left_endpoint != holonomy.right_endpoint
        && holonomy.commutator_rank == boundary.standing.cultivation.commutator_rank;
    if !cultivated_revisit_changed_the_boundary || !ordered_holonomy_preserved {
        return Err("the detached revisit lost cultivation or ordered holonomy".to_owned());
    }
    let reconstructed = boundary
        .reconstruct_history(&inquiry.reconstructed_occurrence)
        .map_err(|error| error.to_string())?;
    let reconstructed_history_sha256 = artifact::digest(&reconstructed);
    let remote_interior_reopened_without_source =
        reconstructed_history_sha256 == inquiry.expected_reconstruction_sha256;
    if !remote_interior_reopened_without_source {
        return Err("the detached fibre did not reopen the exact remote interior".to_owned());
    }

    let open_descriptors = artifact::descriptors();
    let forbidden_needles = [
        "/research/fixtures/r0_rich_inquiry/",
        "/output/the_material_derivation_recurs_",
        "/output/the_returned_constraints_found_",
        "/formal/",
        "/.codex/",
        "/.claude/",
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
            "the detached boundary retained forbidden source access: {forbidden_source_access:?}"
        ));
    }
    artifact::write_json(
        receipt_path,
        &DetachedBoundaryReturn {
            schema: "holonics.r4.detached-boundary-return.v1".to_owned(),
            boundary_identity: boundary.standing.boundary_identity,
            inquiry_occurrence: inquiry.occurrence,
            native_trace: returned.native_trace,
            trace_offsets: returned.trace_offsets,
            reconstructed_history_sha256,
            reconstructed_history_octets: reconstructed.len(),
            remote_interior_reopened_without_source,
            cultivated_revisit_changed_the_boundary,
            ordered_holonomy_preserved,
            device: card.device_name().to_owned(),
            block_threads: returned.block_threads,
            active_lanes: returned.active_lanes,
            launches: returned.launches,
            synchronizations: returned.synchronizations,
            host_ingress_octets: returned.host_ingress_octets,
            host_egress_octets: returned.host_egress_octets,
            resident_octets: returned.resident_octets,
            physical_wall_microseconds,
            cpu_semantic_callbacks_between_fronts: 0,
            open_descriptors,
            forbidden_source_access,
        },
    )?;
    Ok(())
}

pub fn read(path: &Path) -> Result<DetachedBoundaryReturn, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}
