use std::path::Path;

use holonic_engine::cuda_refine::{DeviceJointMediaTransport, DeviceMediaCandidateCounts};
use life::mathematical_particle::MultimodalTransportRest;
use serde_json::{json, Value};

use super::{artifact, source::MountedMediaSource};

pub fn verify_joint_return(
    rest: &MultimodalTransportRest,
    returned: &DeviceJointMediaTransport,
) -> Result<Value, String> {
    let ports = rest.standing.ports.len();
    let families = rest.standing.family_occurrences.len();
    if returned.anchors != rest.standing.heldout_anchor_sections.len()
        || returned.ports != ports
        || returned.families != families
        || returned.joint_anchor.iter().any(|value| *value != 1)
        || returned
            .shared_ablated_joint_anchor
            .iter()
            .any(|value| *value != 0)
        || returned
            .local_ablated_joint_anchor
            .iter()
            .any(|value| *value != 0)
    {
        return Err("the card did not return the exact joint anchor population".to_owned());
    }
    let every_shared_route_moved = returned
        .predecessor_consequence
        .iter()
        .zip(&returned.successor_consequence)
        .zip(&returned.shared_ablated_consequence)
        .all(|((before, after), withdrawn)| before != after && before == withdrawn);
    let every_local_route_is_port_exact =
        returned
            .successor_consequence
            .iter()
            .enumerate()
            .all(|(cell, after)| {
                (0..ports).all(|withdrawn| {
                    let actual = returned.local_ablated_consequence[cell * ports + withdrawn];
                    if cell % ports == withdrawn {
                        actual == returned.predecessor_consequence[cell]
                    } else {
                        actual == *after
                    }
                })
            });
    if !every_shared_route_moved || !every_local_route_is_port_exact {
        return Err("shared or local media withdrawal lost its declared support".to_owned());
    }
    Ok(json!({
        "schema": "holonics.r5.shared-and-local-ablation.v1",
        "truth_status": "implemented-exact",
        "joint_anchor_population": returned.joint_anchor.len(),
        "joint_anchor": returned.joint_anchor,
        "shared_withdrawal": {
            "joint_anchor": returned.shared_ablated_joint_anchor,
            "consequence": returned.shared_ablated_consequence,
            "moved_every_attributable_port": every_shared_route_moved,
        },
        "local_withdrawal": {
            "anchor_by_withdrawn_port": returned.local_ablated_joint_anchor,
            "consequence_by_cell_and_withdrawn_port": returned.local_ablated_consequence,
            "moved_only_its_declared_port": every_local_route_is_port_exact,
        },
    }))
}

pub fn device_receipts(
    device: &str,
    source: &DeviceMediaCandidateCounts,
    native: &DeviceJointMediaTransport,
    source_wall_microseconds: u128,
    native_wall_microseconds: u128,
) -> Value {
    json!({
        "schema": "holonics.r5.resident-card-passages.v1",
        "truth_status": "measured",
        "device": device,
        "source_correspondence_passage": {
            "anchors": source.anchors,
            "ports": source.ports,
            "pairs": source.pairs,
            "candidate_counts": source.candidate_counts,
            "semantic_pair_visits": source.semantic_pair_visits.to_string(),
            "launches": source.launches,
            "synchronizations": source.synchronizations,
            "block_threads": source.block_threads,
            "active_lanes": source.active_lanes,
            "host_ingress_octets": source.host_ingress_octets,
            "host_egress_octets": source.host_egress_octets,
            "resident_octets": source.resident_octets,
            "physical_wall_microseconds": source_wall_microseconds,
        },
        "native_joint_passage": {
            "anchors": native.anchors,
            "families": native.families,
            "ports": native.ports,
            "launches": native.launches,
            "synchronizations": native.synchronizations,
            "block_threads": native.block_threads,
            "active_lanes": native.active_lanes,
            "host_ingress_octets": native.host_ingress_octets,
            "host_egress_octets": native.host_egress_octets,
            "resident_octets": native.resident_octets,
            "physical_wall_microseconds": native_wall_microseconds,
        },
        "cpu_semantic_callbacks_between_device_fronts": 0,
        "gpu_owned_normalization_chronology_contact_gating_and_join": true,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn complete_cost(
    mounted: &MountedMediaSource,
    rest: &MultimodalTransportRest,
    standing_path: &Path,
    decoder_path: &Path,
    fibre_path: &Path,
    source_count: &DeviceMediaCandidateCounts,
    native: &DeviceJointMediaTransport,
) -> Result<Value, String> {
    let source_fibre_octets =
        ["natural_page_5", "natural_page_10"]
            .into_iter()
            .try_fold(0_u64, |total, family| {
                let bytes = serde_json::to_vec(&mounted.m0["co_testimony"][family])
                    .map_err(|error| error.to_string())?;
                total
                    .checked_add(bytes.len() as u64)
                    .ok_or_else(|| "source fibre extent overflow".to_owned())
            })?;
    let native_artifact = std::fs::metadata(standing_path)
        .map_err(|error| error.to_string())?
        .len();
    let native_decoder = std::fs::metadata(decoder_path)
        .map_err(|error| error.to_string())?
        .len();
    let native_fibre = std::fs::metadata(fibre_path)
        .map_err(|error| error.to_string())?
        .len();
    let source_semantic_work = u64::try_from(source_count.semantic_pair_visits)
        .map_err(|_| "source semantic work exceeds u64".to_owned())?;
    let anchors = rest.standing.heldout_anchor_sections.len() as u64;
    let ports = rest.standing.ports.len() as u64;
    let cells = (rest.standing.family_occurrences.len() * rest.standing.ports.len()) as u64;
    let native_semantic_work = anchors
        .checked_mul(ports * 2 + 2)
        .and_then(|work| work.checked_add(cells * (ports + 4)))
        .ok_or("native semantic work overflow")?;
    let source = [
        mounted.source_artifact_octets,
        mounted.m0_bytes.len() as u64,
        source_fibre_octets,
        source_semantic_work,
        source_count.pairs as u64,
        source_count.resident_octets,
        source_count.host_ingress_octets + source_count.host_egress_octets,
    ];
    let compact = [
        native_artifact,
        native_decoder,
        native_fibre,
        native_semantic_work,
        ports,
        native.resident_octets,
        native.host_ingress_octets + native.host_egress_octets,
    ];
    let labels = [
        "artifact_octets",
        "decoder_octets",
        "fibre_octets",
        "semantic_work",
        "semantic_span",
        "resident_octets",
        "transfer_octets",
    ];
    let coordinates = labels
        .into_iter()
        .enumerate()
        .map(|(at, label)| {
            json!({
                "coordinate": label,
                "source": source[at],
                "native": compact[at],
                "strictly_falls": compact[at] < source[at],
            })
        })
        .collect::<Vec<_>>();
    if coordinates
        .iter()
        .any(|coordinate| coordinate["strictly_falls"] != true)
    {
        return Err(format!(
            "the complete joint-media product did not strictly descend: {coordinates:?}"
        ));
    }
    Ok(json!({
        "schema": "holonics.r5.complete-product-descent.v1",
        "truth_status": "implemented-exact-with-measured-apparatus-coordinates",
        "source_definition": "M0 natural PDF plus admitted notation/vector/raster artifacts, complete M0 decoder testimony, complete candidate correspondence fibres, and complete source card scan",
        "native_definition": "one standing, complete length-framed decoder, complete fibres, and one compact joint-media card front",
        "coordinates": coordinates,
        "every_coordinate_strictly_falls": true,
        "source_face_population": mounted.source_face_paths.len(),
        "source_replay_sha256": artifact::digest(&mounted.m0_bytes),
    }))
}
