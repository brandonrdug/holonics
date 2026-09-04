use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceProductionAperture};
use life::mathematical_particle::{
    MathematicalMediaPort, ProductionEcologyRest, ProductionInquiry,
};
use serde_json::{json, Value};

use super::{artifact, render};

pub fn conduct(
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
    inquiry: &Path,
    output: &Path,
) -> Result<(), String> {
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let rest = ProductionEcologyRest::read(&read(standing)?, &read(decoder)?, &read(fibres)?)
        .map_err(|error| error.to_string())?;
    let inquiry: ProductionInquiry = serde_json::from_slice(&read(inquiry)?)
        .map_err(|error| format!("read production inquiry: {error}"))?;
    rest.admit_inquiry(&inquiry)
        .map_err(|error| error.to_string())?;

    let before = nvidia_sample();
    let began = Instant::now();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let returned = card
        .conduct_production_aperture_on_device(
            &rest.retained_boundary.standing.generator_table,
            rest.retained_boundary.standing.native_states.len(),
            &inquiry.context_word,
            &rest.context_starts().map_err(|error| error.to_string())?,
            rest.morphology.predecessor_action(),
            rest.morphology.successor_action(),
            &rest.morphology.recurrence_starts(),
            &rest.media_candidate_species(),
            rest.media.standing.heldout_anchor_sections.len(),
            &[0, 1, 2, 2],
            3,
            inquiry.requested_face.left_species as usize,
            inquiry.requested_face.right_species as usize,
            rest.committed(),
        )
        .map_err(|error| error.to_string())?;
    let wall_microseconds = began.elapsed().as_micros();
    let after = nvidia_sample();
    verify_terminal(&rest, &returned)?;

    let language = if rest.committed() {
        format!(
            "The held-out four-connected correspondence population is {} and the eight-connected population is {}. Their exact oriented difference is {} dimensionless correspondences. The returned Lean occurrence has been committed, so this later passage is certified within the bounded R0–R5 receiver/history family.",
            returned.media_species_totals[2],
            returned.media_species_totals[3],
            returned.oriented_difference
        )
    } else {
        format!(
            "The held-out four-connected correspondence population is {} and the eight-connected population is {}. Their exact oriented difference is {} dimensionless correspondences. This is an emitted candidate until its exterior Lean return is committed.",
            returned.media_species_totals[2],
            returned.media_species_totals[3],
            returned.oriented_difference
        )
    };
    fs::write(output.join("01-answer.md"), format!("{language}\n"))
        .map_err(|error| error.to_string())?;
    let proof = format!(
        "import Mathlib\n\n/-- Generated from the R6 card return; the exterior kernel supplies only a later world occurrence. -/\ntheorem r6_heldout_raster_correspondence_difference : ({} : ℤ) - {} = {} := by\n  norm_num\n",
        returned.media_species_totals[2],
        returned.media_species_totals[3],
        returned.oriented_difference
    );
    fs::write(output.join("02-returned-proof.lean"), proof.as_bytes())
        .map_err(|error| error.to_string())?;
    artifact::write_json(
        output.join("03-exact-value-and-enclosure.json"),
        &json!({
            "schema": "holonics.r6.exact-value-return.v1",
            "truth_status": "implemented-exact",
            "carrier": "integer-incidence",
            "left": returned.media_species_totals[2],
            "right": returned.media_species_totals[3],
            "oriented_difference": returned.oriented_difference,
            "hand": returned.difference_hand,
            "magnitude": returned.difference_magnitude,
            "exact_enclosure": [returned.oriented_difference, returned.oriented_difference],
        }),
    )?;
    let raster = rest
        .media
        .decoder
        .interiors
        .iter()
        .find(|interior| {
            interior.family == rest.media.standing.heldout_family
                && interior.port == MathematicalMediaPort::RasterVision
        })
        .ok_or("the held-out raster spatial declaration is absent")?;
    artifact::write_json(
        output.join("04-unit-dimension-and-chart.json"),
        &json!({
            "schema": "holonics.r6.unit-dimension-return.v1",
            "truth_status": "implemented-exact",
            "result_unit": inquiry.requested_face.unit,
            "result_dimension": inquiry.requested_face.dimension,
            "source_spatial_dimension": raster.spatial.dimension,
            "source_axes": raster.spatial.axes,
            "uncertainty_fibre_sha256": raster.spatial.uncertainty_fibre_sha256,
            "source_lineage_sha256": raster.spatial.source_lineage_sha256,
        }),
    )?;
    let rendering =
        render::exact_difference_field(&rest.media.standing.heldout_anchor_sections, output)?;
    artifact::write_json(output.join("10-rendering-receipt.json"), &rendering)?;
    artifact::write_json(
        output.join("05-complete-dissection.json"),
        &dissection(&rest, &returned)?,
    )?;

    let open_descriptors = artifact::descriptors();
    let forbidden_needles = [
        "/Workspaces/holonics/output/",
        "/Workspaces/holonics/formal/",
        "/Workspaces/holonics/research/",
        "/Workspaces/holonics/.git/",
        "/.codex/",
        "/.claude/",
        "/Downloads/dataset",
        "/Downloads/problems",
        "/Downloads/research_results",
    ];
    let forbidden_source_access = open_descriptors
        .iter()
        .filter(|target| {
            forbidden_needles
                .iter()
                .any(|needle| target.contains(needle))
        })
        .cloned()
        .collect::<Vec<_>>();
    if !forbidden_source_access.is_empty() {
        return Err(format!(
            "fresh-process production inference retained forbidden source access: {forbidden_source_access:?}"
        ));
    }
    let return_receipt = json!({
        "schema": "holonics.r6.fresh-process-production-return.v1",
        "truth_status": "implemented-exact-with-measured-apparatus-testimony",
        "inquiry_occurrence": inquiry.occurrence,
        "rest_sha256": rest.canonical_identity().map_err(|error| error.to_string())?,
        "cultivation_committed": rest.committed(),
        "language": language,
        "proof_sha256": artifact::digest(proof.as_bytes()),
        "exact_value": returned.oriented_difference,
        "unit": inquiry.requested_face.unit,
        "dimension": inquiry.requested_face.dimension,
        "device": card.device_name(),
        "resident_passage": device_json(&returned),
        "physical_telemetry": {
            "aperture": "two endpoint nvidia-smi samples; no integration or interpolation",
            "units": "timestamp, name, power.draw W, temperature.gpu C, memory.used MiB, memory.total MiB, utilization.gpu percent, utilization.memory percent",
            "before": before,
            "after": after,
            "wall_microseconds": wall_microseconds,
            "throughput": {"inquiries": 1, "microseconds": wall_microseconds},
            "energy": "unknown: endpoint power samples do not found an energy integral",
        },
        "cpu_semantic_callbacks_between_device_fronts": 0,
        "source_corpus_exchange_and_development_proof_mounted": false,
        "open_descriptors": open_descriptors,
        "forbidden_source_access": forbidden_source_access,
    });
    artifact::write_json(output.join("00-return.json"), &return_receipt)?;
    Ok(())
}

fn verify_terminal(
    rest: &ProductionEcologyRest,
    returned: &DeviceProductionAperture,
) -> Result<(), String> {
    let expected = rest.media.standing.heldout_anchor_sections.iter().fold(
        [0_u64; 4],
        |mut total, section| {
            total[0] += 1;
            total[1] += u64::from(section.vector_candidates);
            total[2] += u64::from(section.raster_four_candidates);
            total[3] += u64::from(section.raster_eight_candidates);
            total
        },
    );
    let difference = i64::try_from(expected[2]).map_err(|error| error.to_string())?
        - i64::try_from(expected[3]).map_err(|error| error.to_string())?;
    if returned.media_species_totals != expected
        || returned.total_joint_incidence != expected.iter().sum::<u64>()
        || returned.oriented_difference != difference
        || returned.media_joint_anchors != rest.media.standing.heldout_anchor_sections.len() as u64
        || returned.selected_cultivation_state != u32::from(rest.committed())
        || returned.launches != 2
        || returned.synchronizations != 1
        || returned.typed_reductions != 1
    {
        return Err(
            "the terminal production return disagrees with its exact retained sections".to_owned(),
        );
    }
    Ok(())
}

fn dissection(
    rest: &ProductionEcologyRest,
    returned: &DeviceProductionAperture,
) -> Result<Value, String> {
    Ok(json!({
        "schema": "holonics.r6.complete-source-native-dissection.v1",
        "truth_status": "implemented-exact",
        "source_passages": rest.junction.component_identities,
        "native_passages": {
            "retained_context": {
                "trace_stride": returned.context_trace_stride,
                "trace": returned.context_trace,
                "boundary_withdrawn_trace": returned.context_boundary_withdrawn_trace,
            },
            "derivation": {
                "trace_stride": returned.derivation_trace_stride,
                "predecessor": returned.derivation_predecessor_trace,
                "successor": returned.derivation_successor_trace,
                "selected": returned.derivation_selected_trace,
                "generator_withdrawn": returned.derivation_generator_withdrawn_trace,
                "predecessor_lengths": returned.derivation_predecessor_lengths,
                "successor_lengths": returned.derivation_successor_lengths,
                "selected_lengths": returned.derivation_selected_lengths,
                "generator_withdrawn_lengths": returned.derivation_generator_withdrawn_lengths,
            },
            "media_species_totals": returned.media_species_totals,
            "shared_withdrawal": returned.media_shared_withdrawn_totals,
            "local_withdrawal_by_species_and_port": returned.media_local_withdrawn_totals,
            "typed_reduction": {
                "joint_incidence": returned.total_joint_incidence,
                "oriented_difference": returned.oriented_difference,
                "hand": returned.difference_hand,
            },
        },
        "fibres": rest.reconstruction.component_fibres,
        "defects": {
            "morphology_open": rest.morphology.delta.open_exterior,
            "context_open": rest.retained_boundary.standing.open_exterior,
            "media_open": rest.media.standing.open_exterior,
        },
        "separators": rest.reconstruction.shortest_separating_receivers,
        "basins": rest.junction.receiver_basis,
        "caustics": [
            {"locus": "R3 returned-constraint support", "commutator_rank": rest.morphology.delta.cultivation_holonomy.commutator_rank},
            {"locus": "R4 ordered-word seam", "left_endpoint": rest.retained_boundary.standing.ordered_holonomy.left_endpoint, "right_endpoint": rest.retained_boundary.standing.ordered_holonomy.right_endpoint},
            {"locus": "R5 raster-connectivity seam", "oriented_difference": returned.oriented_difference},
        ],
        "holonomy": {
            "cultivation_commutator_rank": rest.morphology.delta.cultivation_holonomy.commutator_rank,
            "ordered_boundary": rest.retained_boundary.standing.ordered_holonomy,
        },
        "phase_seams": ["declined-to-committed-world-return", "context-boundary-withdrawal", "shared-and-local-media-withdrawal"],
        "higher_cells": {
            "retained_recurrences": rest.retained_boundary.standing.recurrences.len(),
            "media_naturality_squares": rest.media.fibres.naturality_squares.len(),
            "shared_media_cells": rest.media.standing.shared.higher_cells.len(),
        },
        "open_alternatives": rest.reconstruction.open_alternatives,
        "open_exterior": rest.junction.open_exterior,
    }))
}

fn device_json(returned: &DeviceProductionAperture) -> Value {
    json!({
        "context_fronts": returned.context_fronts,
        "derivation_fronts": returned.derivation_fronts,
        "media_anchors": returned.media_anchors,
        "media_species": returned.media_species,
        "media_ports": returned.media_ports,
        "committed": returned.committed,
        "launches": returned.launches,
        "synchronizations": returned.synchronizations,
        "typed_reductions": returned.typed_reductions,
        "block_threads": returned.block_threads,
        "active_lanes": returned.active_lanes,
        "semantic_work": returned.semantic_work.to_string(),
        "semantic_span": returned.semantic_span,
        "host_ingress_octets": returned.host_ingress_octets,
        "host_egress_octets": returned.host_egress_octets,
        "resident_octets": returned.resident_octets,
        "front_interchange": {
            "context_footprint": "context trace intervals",
            "derivation_footprint": "derivation trace intervals",
            "media_footprint": "exact additive species populations",
            "disjoint_before_typed_reduction": true,
            "default_stream_predecessor_order": true,
        },
    })
}

fn nvidia_sample() -> Value {
    let returned = Command::new("/usr/bin/nvidia-smi")
        .args([
            "--query-gpu=timestamp,name,power.draw,temperature.gpu,memory.used,memory.total,utilization.gpu,utilization.memory",
            "--format=csv,noheader,nounits",
        ])
        .output();
    match returned {
        Ok(output) if output.status.success() => json!({
            "available": true,
            "raw": String::from_utf8_lossy(&output.stdout).trim(),
        }),
        Ok(output) => json!({
            "available": false,
            "status": output.status.code(),
            "stderr": String::from_utf8_lossy(&output.stderr).trim(),
        }),
        Err(error) => json!({"available": false, "error": error.to_string()}),
    }
}

fn read(path: &Path) -> Result<Vec<u8>, String> {
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}
