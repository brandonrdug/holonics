use std::fs;
use std::path::Path;
use std::time::Instant;

use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::mathematical_particle::{MathematicalMediaPort, MultimodalTransportRest};
use serde::{Deserialize, Serialize};

use super::artifact;

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DetachedMediaInquiry {
    pub schema: String,
    pub occurrence: String,
    pub expected_candidate_counts: Vec<u32>,
    pub expected_successor_consequence: Vec<u32>,
    pub expected_interior_sha256: Vec<String>,
    pub heldout_family: u32,
    pub outside_development_occurrence_closure: bool,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DetachedMediaReturn {
    pub schema: String,
    pub inquiry_occurrence: String,
    pub joint_anchor_population: usize,
    pub every_anchor_required_all_ports: bool,
    pub exact_interiors_reopened: bool,
    pub successor_consequence: Vec<u32>,
    pub shared_ablated_consequence: Vec<u32>,
    pub local_ablated_consequence: Vec<u32>,
    pub shared_withdrawal_moved_every_port: bool,
    pub local_withdrawal_moved_only_declared_port: bool,
    pub device: String,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
    pub physical_wall_microseconds: u128,
    pub cpu_semantic_callbacks: u64,
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
    let rest = MultimodalTransportRest::read(
        &fs::read(standing_path).map_err(|error| error.to_string())?,
        &fs::read(decoder_path).map_err(|error| error.to_string())?,
        &fs::read(fibre_path).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let inquiry: DetachedMediaInquiry =
        serde_json::from_slice(&fs::read(inquiry_path).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    if inquiry.schema != "holonics.r5.detached-media-inquiry.v1"
        || inquiry.occurrence.is_empty()
        || inquiry.heldout_family != rest.standing.heldout_family
        || inquiry.expected_candidate_counts != rest.device_candidate_counts()
        || inquiry.expected_interior_sha256.len() != rest.standing.ports.len()
        || !inquiry.outside_development_occurrence_closure
    {
        return Err("the detached media inquiry is not admitted by this rest".to_owned());
    }
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let began = Instant::now();
    let returned = card
        .conduct_joint_media_transport_on_device(
            &rest.device_candidate_counts(),
            rest.standing.heldout_anchor_sections.len(),
            &rest.standing.shared.successor_action,
            &rest.device_decoder_addresses(),
            &rest.device_starts(),
            rest.standing.family_occurrences.len(),
            rest.standing.ports.len(),
        )
        .map_err(|error| error.to_string())?;
    let physical_wall_microseconds = began.elapsed().as_micros();
    if returned.successor_consequence != inquiry.expected_successor_consequence
        || returned.joint_anchor.iter().any(|joint| *joint != 1)
        || returned
            .shared_ablated_joint_anchor
            .iter()
            .any(|joint| *joint != 0)
        || returned
            .local_ablated_joint_anchor
            .iter()
            .any(|joint| *joint != 0)
    {
        return Err("the detached card return changed the joint-media passage".to_owned());
    }
    let exact_interiors_reopened = [
        MathematicalMediaPort::Notation,
        MathematicalMediaPort::Vector,
        MathematicalMediaPort::RasterVision,
    ]
    .into_iter()
    .zip(&inquiry.expected_interior_sha256)
    .all(|(port, expected)| {
        rest.reconstruct_interior(inquiry.heldout_family, port)
            .is_ok_and(|bytes| artifact::digest(bytes) == *expected)
    });
    if !exact_interiors_reopened {
        return Err("the detached decoder did not reopen each exact media interior".to_owned());
    }
    let (shared_moved, local_only) = ablation_grade(&returned);
    if !shared_moved || !local_only {
        return Err("the detached shared/local withdrawal law changed".to_owned());
    }
    let open_descriptors = artifact::descriptors();
    let forbidden_needles = [
        "/output/m0_mathematical_source_circulation/",
        "/tmp/pdfs/2608.13553-heat-kernel-geometry.pdf",
        "/output/the_heterogeneous_ports_found_one_shared_phoenix_ecology/",
        "/output/the_retained_causal_boundary_carries_the_long_horizon_inquiry/",
        "/formal/",
        "/.codex/",
        "/.claude/",
    ];
    let forbidden_source_access = open_descriptors
        .iter()
        .filter(|path| forbidden_needles.iter().any(|needle| path.contains(needle)))
        .cloned()
        .collect::<Vec<_>>();
    if !forbidden_source_access.is_empty() {
        return Err(format!(
            "the detached deed retained forbidden source descriptors: {forbidden_source_access:?}"
        ));
    }
    artifact::write_json(
        receipt_path,
        &DetachedMediaReturn {
            schema: "holonics.r5.detached-media-return.v1".to_owned(),
            inquiry_occurrence: inquiry.occurrence,
            joint_anchor_population: returned.joint_anchor.len(),
            every_anchor_required_all_ports: true,
            exact_interiors_reopened,
            successor_consequence: returned.successor_consequence,
            shared_ablated_consequence: returned.shared_ablated_consequence,
            local_ablated_consequence: returned.local_ablated_consequence,
            shared_withdrawal_moved_every_port: shared_moved,
            local_withdrawal_moved_only_declared_port: local_only,
            device: card.device_name().to_owned(),
            block_threads: returned.block_threads,
            active_lanes: returned.active_lanes,
            launches: returned.launches,
            synchronizations: returned.synchronizations,
            host_ingress_octets: returned.host_ingress_octets,
            host_egress_octets: returned.host_egress_octets,
            resident_octets: returned.resident_octets,
            physical_wall_microseconds,
            cpu_semantic_callbacks: 0,
            open_descriptors,
            forbidden_source_access,
        },
    )?;
    Ok(())
}

fn ablation_grade(
    returned: &holonic_engine::cuda_refine::DeviceJointMediaTransport,
) -> (bool, bool) {
    let shared_moved = returned
        .predecessor_consequence
        .iter()
        .zip(&returned.successor_consequence)
        .zip(&returned.shared_ablated_consequence)
        .all(|((before, after), withdrawn)| before != after && before == withdrawn);
    let local_only = returned
        .successor_consequence
        .iter()
        .enumerate()
        .all(|(cell, after)| {
            (0..returned.ports).all(|withdrawn| {
                let actual = returned.local_ablated_consequence[cell * returned.ports + withdrawn];
                if cell % returned.ports == withdrawn {
                    actual == returned.predecessor_consequence[cell]
                } else {
                    actual == *after
                }
            })
        });
    (shared_moved, local_only)
}

pub fn read(path: &Path) -> Result<DetachedMediaReturn, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}
