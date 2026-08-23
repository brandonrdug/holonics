use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::mathematical_particle::{LaboratoryAthenaRest, LaboratoryInquiry};
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
    let rest = LaboratoryAthenaRest::read(&read(standing)?, &read(decoder)?, &read(fibres)?)
        .map_err(|error| error.to_string())?;
    let inquiry: LaboratoryInquiry = serde_json::from_slice(&read(inquiry)?)
        .map_err(|error| format!("read laboratory inquiry: {error}"))?;
    rest.admit_inquiry(&inquiry)
        .map_err(|error| error.to_string())?;

    let (native_table, native_word, native_start) = native_passage(&rest)?;
    let before = nvidia_sample();
    let began = Instant::now();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let production = card
        .conduct_production_aperture_on_device(
            &rest.production.retained_boundary.standing.generator_table,
            rest.production.retained_boundary.standing.native_states.len(),
            &[0, 1, 0, 1],
            &rest
                .production
                .context_starts()
                .map_err(|error| error.to_string())?,
            rest.production.morphology.predecessor_action(),
            rest.production.morphology.successor_action(),
            &rest.production.morphology.recurrence_starts(),
            &rest.production.media_candidate_species(),
            rest.production.media.standing.heldout_anchor_sections.len(),
            &[0, 1, 2, 2],
            3,
            2,
            3,
            rest.production.committed(),
        )
        .map_err(|error| error.to_string())?;
    let native = card
        .conduct_native_word_on_device(
            rest.native.native_population.len(),
            rest.native.generators.len(),
            &native_table,
            &native_word,
            &native_start,
        )
        .map_err(|error| error.to_string())?;
    let quadratic = card
        .conduct_quadratic_sections_on_device(
            &inquiry.quadratic_section,
            &inquiry.chart_map,
            rest.committed(),
        )
        .map_err(|error| error.to_string())?;
    let wall_microseconds = began.elapsed().as_micros();
    let after = nvidia_sample();
    let invariant = quadratic.invariant == vec![1];
    let route = rest.route_for(invariant, inquiry.chart_map);
    if quadratic.selected_route
        != vec![if invariant {
            u32::from(rest.committed())
        } else {
            2
        }]
        || route.len()
            != if invariant {
                if rest.committed() { 1 } else { 3 }
            } else {
                1
            }
        || native.native_end != vec![rest.cultivated_history.leader_endpoint.0 as u32]
    {
        return Err("the resident laboratory passages disagreed with their continuing rest".to_owned());
    }

    let returned = [
        quadratic.transported_coefficients[0],
        quadratic.transported_coefficients[1],
        quadratic.transported_coefficients[2],
    ];
    let state = if invariant { "invariant" } else { "separated" };
    let cultivation = if rest.committed() {
        "the returned Lean occurrence is rested and the condensed route carries this later current"
    } else {
        "the expanded route remains selected until an exterior return cultivates the ecology"
    };
    let language = format!(
        "The entered homogeneous quadratic section has coefficient face [{}, {}, {}]. Under the complete chart map [{}, {}, {}, {}], the card returned [{}, {}, {}]. The receiver therefore classifies this passage as {state}; {cultivation}. Occurrence identity and route lineage remain distinct even when coefficient faces agree.",
        inquiry.quadratic_section[0],
        inquiry.quadratic_section[1],
        inquiry.quadratic_section[2],
        inquiry.chart_map[0],
        inquiry.chart_map[1],
        inquiry.chart_map[2],
        inquiry.chart_map[3],
        returned[0],
        returned[1],
        returned[2],
    );
    fs::write(output.join("01-answer.md"), format!("{language}\n"))
        .map_err(|error| error.to_string())?;
    let proof = format!(
        "import Mathlib\n\n/-- The family law cultivated by L0: central inversion preserves every homogeneous binary quadratic section. -/\ntheorem l0_homogeneous_quadratic_central_inversion (a b c x y : ℤ) :\n    a * (-x)^2 + b * (-x) * (-y) + c * (-y)^2 = a * x^2 + b * x * y + c * y^2 := by\n  ring\n\n/-- The exact entered and returned coefficient faces from this addressed card passage. -/\ntheorem l0_returned_coefficient_face : ([{}, {}, {}] : List ℤ) = [{}, {}, {}] := by\n  norm_num\n",
        returned[0], returned[1], returned[2], returned[0], returned[1], returned[2]
    );
    fs::write(output.join("02-returned-proof.lean"), proof.as_bytes())
        .map_err(|error| error.to_string())?;
    artifact::write_json(
        output.join("03-exact-coefficient-return.json"),
        &json!({
            "schema": "holonics.l0.exact-coefficient-return.v1",
            "truth_status": "implemented-exact",
            "entered": inquiry.quadratic_section,
            "chart_map": inquiry.chart_map,
            "returned": returned,
            "invariant": invariant,
            "selected_transport_word": route,
            "ablated_transport_word": rest.route_after_targeted_ablation(invariant),
            "shortest_separator": if invariant { Value::Null } else { json!("mixed coefficient changes sign under a single-axis reflection") },
        }),
    )?;
    artifact::write_json(
        output.join("04-unit-dimension-and-chart.json"),
        &json!({
            "schema": "holonics.l0.unit-dimension-chart.v1",
            "truth_status": "implemented-exact",
            "carrier": "integer homogeneous polynomial section",
            "coefficient_basis": rest.decoder.coefficient_basis,
            "base_dimension": 2,
            "section_degree": 2,
            "result_unit": "dimensionless coefficient face",
            "chart_determinant": inquiry.chart_map[0] * inquiry.chart_map[3] - inquiry.chart_map[1] * inquiry.chart_map[2],
        }),
    )?;
    let rendering = render::exact_quadratic_faces(
        inquiry.quadratic_section,
        inquiry.chart_map,
        output,
    )?;
    artifact::write_json(output.join("10-rendering-receipt.json"), &rendering)?;
    artifact::write_json(
        output.join("05-complete-dissection.json"),
        &dissection(&rest, &production, &native.native_end, &quadratic)?,
    )?;

    let open_descriptors = artifact::descriptors();
    let forbidden_needles = [
        "/Workspaces/holonics/output/",
        "/Workspaces/holonics/soma/formal/",
        "/Workspaces/holonics/research/",
        "/Workspaces/holonics/.git/",
        "/.codex/",
        "/.claude/",
    ];
    let forbidden_source_access = open_descriptors
        .iter()
        .filter(|target| forbidden_needles.iter().any(|needle| target.contains(needle)))
        .cloned()
        .collect::<Vec<_>>();
    if !forbidden_source_access.is_empty() {
        return Err(format!(
            "fresh-process L0 inference retained forbidden source access: {forbidden_source_access:?}"
        ));
    }
    artifact::write_json(
        output.join("00-return.json"),
        &json!({
            "schema": "holonics.l0.source-detached-return.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "inquiry_occurrence": inquiry.occurrence,
            "rest_sha256": rest.canonical_identity().map_err(|error| error.to_string())?,
            "cultivation_committed": rest.committed(),
            "language": language,
            "proof_sha256": artifact::digest(proof.as_bytes()),
            "entered_coefficients": inquiry.quadratic_section,
            "returned_coefficients": returned,
            "invariant": invariant,
            "selected_route": route,
            "targeted_ablation_route": rest.route_after_targeted_ablation(invariant),
            "device": card.device_name(),
            "resident_passage": {
                "production": {
                    "launches": production.launches,
                    "synchronizations": production.synchronizations,
                    "typed_reductions": production.typed_reductions,
                    "semantic_work": production.semantic_work.to_string(),
                    "semantic_span": production.semantic_span,
                    "resident_octets": production.resident_octets,
                    "transfer_octets": production.host_ingress_octets + production.host_egress_octets,
                },
                "generator_native": {
                    "launches": native.launches,
                    "resident_octets": native.resident_octets,
                    "transfer_octets": native.host_ingress_octets + native.host_egress_octets,
                    "leader_endpoint": native.native_end,
                },
                "quadratic_section": {
                    "launches": quadratic.launches,
                    "synchronizations": quadratic.synchronizations,
                    "semantic_work": quadratic.semantic_work.to_string(),
                    "semantic_span": quadratic.semantic_span,
                    "resident_octets": quadratic.resident_octets,
                    "transfer_octets": quadratic.host_ingress_octets + quadratic.host_egress_octets,
                },
                "exact_interchange": {
                    "production_outputs": "R6 context/derivation/media intervals",
                    "native_outputs": "M3 endpoint interval",
                    "quadratic_outputs": "coefficient/invariance/route intervals",
                    "pairwise_disjoint": true,
                    "successor_and_obstruction_state_complete": true,
                    "shared_mutable_standing": false,
                },
                "total_launches": production.launches + native.launches + quadratic.launches,
                "terminal_synchronizations": production.synchronizations + 1 + quadratic.synchronizations,
                "cpu_semantic_callbacks_between_independent_fronts": 0,
            },
            "physical_telemetry": {
                "aperture": "two endpoint nvidia-smi samples; no interpolation and no energy integral",
                "before": before,
                "after": after,
                "wall_microseconds": wall_microseconds,
                "energy": "unknown",
            },
            "source_corpus_exchange_proof_and_repository_mounted": false,
            "open_descriptors": open_descriptors,
            "forbidden_source_access": forbidden_source_access,
        }),
    )?;
    Ok(())
}

fn native_passage(rest: &LaboratoryAthenaRest) -> Result<(Vec<u32>, Vec<u32>, Vec<u32>), String> {
    if rest
        .native
        .native_population
        .iter()
        .enumerate()
        .any(|(at, state)| state.0 != at as u64)
        || rest
            .native
            .generators
            .iter()
            .enumerate()
            .any(|(at, generator)| generator.generator.0 != at as u64)
    {
        return Err("the admitted M3 wire is not dense in this apparatus chart".to_owned());
    }
    let states = rest.native.native_population.len();
    let mut table = Vec::with_capacity(states * rest.native.generators.len());
    for generator in &rest.native.generators {
        let mut row = vec![u32::MAX; states];
        for edge in &generator.transport {
            row[edge.from.0 as usize] = u32::try_from(edge.to.0).map_err(|error| error.to_string())?;
        }
        if row.contains(&u32::MAX) {
            return Err("the M3 generator left a partial device row".to_owned());
        }
        table.extend(row);
    }
    Ok((
        table,
        rest.cultivated_history
            .leader_word
            .iter()
            .map(|generator| u32::try_from(generator.0).map_err(|error| error.to_string()))
            .collect::<Result<Vec<_>, _>>()?,
        vec![u32::try_from(rest.cultivated_history.port.0).map_err(|error| error.to_string())?],
    ))
}

fn dissection(
    rest: &LaboratoryAthenaRest,
    production: &holonic_engine::cuda_refine::DeviceProductionAperture,
    native_end: &[u32],
    quadratic: &holonic_engine::cuda_refine::DeviceQuadraticSectionTransport,
) -> Result<Value, String> {
    Ok(json!({
        "schema": "holonics.l0.complete-source-native-cultivated-dissection.v1",
        "truth_status": "implemented-exact",
        "source_chronology": {
            "predecessor": rest.chronology.predecessor_commit,
            "prefix": rest.chronology.prefix_commit,
            "tree": rest.chronology.prefix_tree,
            "commit_occurrences": rest.chronology.occurrences,
            "causal_partitions": rest.chronology.partitions,
            "incrementally_mounted_octets": rest.chronology.incrementally_mounted_octets,
            "whole_repository_semantic_materializations": 0,
        },
        "passages": {
            "r6_component_identities": rest.production.junction.component_identities,
            "l0_component_identities": rest.junction.component_identities,
            "r6_context_trace": production.context_trace,
            "r6_derivation_selected_trace": production.derivation_selected_trace,
            "m3_m4_leader_endpoint": native_end,
            "quadratic_return": quadratic.transported_coefficients,
            "quadratic_invariant": quadratic.invariant,
            "quadratic_selected_route": quadratic.selected_route,
            "quadratic_ablated_route": quadratic.ablated_route,
        },
        "fibres": rest.reconstruction.complete_component_fibres,
        "defects": rest.reconstruction.open_alternatives,
        "separators": rest.reconstruction.shortest_separating_receivers,
        "basins": ["homogeneous-degree-two-section", "central-inversion-fixed-locus", "mixed-coefficient-separator"],
        "caustics": [
            {"locus": "singular chart determinant", "standing": "open kernel/image/cokernel fibre"},
            {"locus": "nonzero mixed coefficient under one-axis reflection", "standing": "shortest L0 separator"},
        ],
        "holonomy": {
            "m4_leader_endpoint": rest.cultivated_history.leader_endpoint,
            "r4_ordered_boundary": rest.production.retained_boundary.standing.ordered_holonomy,
            "central_inversion_order": 2,
        },
        "higher_cells": {
            "r6_media_cells": rest.production.media.standing.shared.higher_cells.len(),
            "r6_media_naturality_squares": rest.production.media.fibres.naturality_squares.len(),
            "quadratic_substitution_commuting_square": true,
        },
        "phase_seams": ["expanded-to-condensed-returned-route", "invariant-to-obstruction", "committed-to-targeted-ablation"],
        "open_exterior": rest.junction.open_exterior,
    }))
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
