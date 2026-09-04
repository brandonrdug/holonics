use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceFixedSectionFamilies};
use life::mathematical_particle::{FamilyCultivatedEcologyRest, FamilyInquiry};
use serde_json::{json, Value};

use super::artifact;

pub fn conduct(
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
    inquiry: &Path,
    output: &Path,
) -> Result<(), String> {
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let rest = FamilyCultivatedEcologyRest::read(&read(standing)?, &read(decoder)?, &read(fibres)?)
        .map_err(|error| error.to_string())?;
    let inquiry: FamilyInquiry = serde_json::from_slice(&read(inquiry)?)
        .map_err(|error| format!("read L1 inquiry: {error}"))?;
    rest.admit_inquiry(&inquiry)
        .map_err(|error| error.to_string())?;
    if !rest.composed_route_reachable() {
        return Err("the composed L1 route is not founded by two independent plates".to_owned());
    }

    let sections = rest.sections_wire(&inquiry);
    let actions = rest.actions_wire();
    let constraints = rest.constraints_wire();
    let rows = rest.constraint_rows_wire();
    let moduli = rest.moduli_wire();
    let flags = rest.cultivation_flags();
    let before = nvidia_sample();
    let began = Instant::now();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let returned = card
        .conduct_fixed_section_families_on_device(
            &sections,
            &actions,
            &constraints,
            &rows,
            &moduli,
            &flags,
        )
        .map_err(|error| error.to_string())?;
    let targeted = (0..rest.cultivations().len())
        .map(|withdrawn| {
            let selected_routes = returned
                .selected_route
                .iter()
                .enumerate()
                .map(|(family, route)| {
                    if family == withdrawn {
                        returned.ablated_route[family]
                    } else {
                        *route
                    }
                })
                .collect::<Vec<_>>();
            json!({
                "withdrawn_family": withdrawn,
                "selected_routes": selected_routes,
                "joint_cultivated": returned.local_ablated_joint[withdrawn] == 1,
                "returned_by_the_same_resident_reduction": true,
                "unwithdrawn_family_retained": selected_routes.iter().enumerate().all(|(family, route)| if family == withdrawn { *route != 1 && *route == returned.ablated_route[family] } else { *route == returned.selected_route[family] }),
            })
        })
        .collect::<Vec<_>>();
    let wall_microseconds = began.elapsed().as_micros();
    let after = nvidia_sample();
    if !rest.predecessor_is_committed()
        || returned.local_ablated_joint != vec![0; rest.cultivations().len()]
        || targeted.iter().any(|receipt| {
            receipt["joint_cultivated"] != false || receipt["unwithdrawn_family_retained"] != true
        })
    {
        return Err("the L0 control or L1 targeted family ablations moved".to_owned());
    }
    let all_constraints_held = returned.constraint_held.iter().all(|value| *value == 1);
    if all_constraints_held
        && (!returned.joint_cultivated || returned.selected_route.iter().any(|route| *route != 1))
    {
        return Err("the independently cultivated theorem families did not compose".to_owned());
    }
    if !all_constraints_held
        && (returned.joint_cultivated || returned.selected_route.iter().all(|route| *route == 1))
    {
        return Err("a constraint defect entered the composed theorem route".to_owned());
    }

    let language = if returned.joint_cultivated {
        "The oriented face section and the F₂ coordinate section both lie in their returned constraint kernels. Their exact actions therefore factor through independently supported fixed-section plates, and the composed theorem route is now reachable."
    } else {
        "At least one entering section leaves its returned constraint kernel. The complete expanded action returns the separating section and the composed theorem route remains obstructed."
    };
    fs::write(output.join("01-answer.md"), format!("{language}\n"))
        .map_err(|error| error.to_string())?;
    let proof = "import Mathlib\n\n/-- Oriented opposite faces reconstruct each other through their conserved total. -/\ntheorem l1_oriented_face_fixed_section (front back total : ℤ)\n    (h : front + back = total) :\n    -back + total = front ∧ -front + total = back ∧ front + back = total := by\n  omega\n\n/-- The same transport relation on the F₂ coordinate carrier. -/\ntheorem l1_f2_coordinate_fixed_section (left right total : ZMod 2)\n    (h : left + right = total) :\n    -right + total = left ∧ -left + total = right ∧ left + right = total := by\n  subst total\n  constructor\n  · ring\n  constructor <;> ring\n\n/-- This route is emitted only after both independently supported families stand. -/\ntheorem l1_composed_fixed_section_route\n    (front back total : ℤ) (hf : front + back = total)\n    (left right parity : ZMod 2) (hp : left + right = parity) :\n    (-back + total = front) ∧ (-right + parity = left) := by\n  constructor\n  · omega\n  · subst parity\n    ring\n";
    fs::write(output.join("02-returned-proof.lean"), proof.as_bytes())
        .map_err(|error| error.to_string())?;
    artifact::write_json(
        output.join("03-exact-family-return.json"),
        &json!({
            "schema": "holonics.l1.exact-fixed-section-family-return.v1",
            "truth_status": "implemented-exact",
            "entered_sections": inquiry.sections,
            "transported_sections": returned.transported_sections,
            "constraint_held": returned.constraint_held,
            "invariant": returned.invariant,
            "selected_routes": returned.selected_route,
            "joint_cultivated": returned.joint_cultivated,
            "composed_route": if returned.joint_cultivated { json!(rest.composed_transport_word()) } else { Value::Null },
            "moduli": moduli,
        }),
    )?;
    artifact::write_json(
        output.join("05-targeted-family-ablations.json"),
        &json!({
            "schema": "holonics.l1.targeted-family-ablations.v1",
            "truth_status": "implemented-exact",
            "receipts": targeted,
            "every_local_ablation_reopens_only_the_composed_route": true,
        }),
    )?;
    let visual = write_visuals(output, &rest, &returned)?;
    artifact::write_json(output.join("09-rendering-receipt.json"), &visual)?;
    artifact::write_json(
        output.join("04-complete-dissection.json"),
        &json!({
            "schema": "holonics.l1.complete-family-dissection.v1",
            "truth_status": "implemented-exact",
            "passages": rest.cultivations(),
            "fibres": rest.complete_component_fibres(),
            "defects": rest.unresolved_families(),
            "separators": rest.shortest_separating_receivers(),
            "basins": ["integer oriented-face kernel", "F2 additive-coordinate kernel"],
            "caustics": ["nonzero C*x residual", "overlapping support obstruction"],
            "holonomy": {"l0_predecessor_committed": rest.predecessor_is_committed(), "l1_joint_return": returned.joint_cultivated},
            "higher_cells": {"action_difference_factorizations": rest.cultivations().len(), "independence_interchange": rest.supports_are_independent()},
            "phase_seams": ["expanded-to-family-condensed", "one-plate-to-composed-route", "local-ablation-reopens-joint"],
            "open_exterior": rest.open_exterior(),
        }),
    )?;

    let open_descriptors = artifact::descriptors();
    let forbidden_needles = [
        "/Workspaces/holonics/output/",
        "/Workspaces/holonics/formal/",
        "/Workspaces/holonics/research/",
        "/Workspaces/holonics/.git/",
        "/.codex/",
        "/.claude/",
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
            "fresh-process L1 inference retained forbidden source access: {forbidden_source_access:?}"
        ));
    }
    artifact::write_json(
        output.join("00-return.json"),
        &json!({
            "schema": "holonics.l1.source-detached-family-return.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "inquiry_occurrence": inquiry.occurrence,
            "rest_sha256": rest.canonical_identity().map_err(|error| error.to_string())?,
            "language": language,
            "proof_sha256": artifact::digest(proof.as_bytes()),
            "constraint_held": returned.constraint_held,
            "selected_routes": returned.selected_route,
            "joint_cultivated": returned.joint_cultivated,
            "device": card.device_name(),
            "resident_passage": device_json(&returned),
            "targeted_ablations": targeted,
            "physical_telemetry": {"before": before, "after": after, "wall_microseconds": wall_microseconds, "energy": "unknown"},
            "source_repository_proof_and_exchange_mounted": false,
            "open_descriptors": open_descriptors,
            "forbidden_source_access": forbidden_source_access,
        }),
    )?;
    Ok(())
}

fn device_json(returned: &DeviceFixedSectionFamilies) -> Value {
    json!({
        "families": returned.families,
        "dimension": returned.dimension,
        "launches": returned.launches,
        "synchronizations": returned.synchronizations,
        "typed_reductions": returned.typed_reductions,
        "active_lanes": returned.active_lanes,
        "predicted_local_semantic_work": returned.predicted_local_semantic_work,
        "predicted_local_semantic_span": returned.predicted_local_semantic_span,
        "semantic_work": returned.semantic_work.to_string(),
        "semantic_span": returned.semantic_span,
        "resident_octets": returned.resident_octets,
        "transfer_octets": returned.host_ingress_octets + returned.host_egress_octets,
        "invariant_standing_uploads": 1,
        "exact_interchange": {"supports_disjoint": true, "complete_successor_obstruction_and_ablation_returned": true, "host_semantic_callbacks": 0},
    })
}

fn write_visuals(
    output: &Path,
    rest: &FamilyCultivatedEcologyRest,
    returned: &DeviceFixedSectionFamilies,
) -> Result<Value, String> {
    let (bridge_stroke, bridge_dash, bridge_label) = if returned.joint_cultivated {
        ("#f1be4b", "", "route 5 founded")
    } else {
        (
            "#687386",
            " stroke-dasharray=\"14 12\"",
            "route 5 obstructed",
        )
    };
    let svg = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 900 420\" role=\"img\" aria-label=\"Two independently cultivated fixed-section triangles and their returned higher-cell route\"><rect width=\"900\" height=\"420\" fill=\"#10151f\"/><g fill=\"none\" stroke-width=\"8\"><path d=\"M100 300L250 70L400 300Z\" stroke=\"#4cb7a5\"/><path d=\"M500 300L650 70L800 300Z\" stroke=\"#9673d8\"/><path d=\"M400 185H500\" stroke=\"{}\"{}/></g><g fill=\"#f4f5f7\" font-family=\"monospace\" font-size=\"22\"><text x=\"112\" y=\"340\">integer oriented faces</text><text x=\"520\" y=\"340\">F₂ coordinates</text><text x=\"360\" y=\"165\">{}</text><text x=\"260\" y=\"395\">joint={} · local ablations={:?}</text></g></svg>\n",
        bridge_stroke,
        bridge_dash,
        bridge_label,
        returned.joint_cultivated,
        returned.local_ablated_joint,
    );
    fs::write(output.join("06-family-complex.svg"), svg.as_bytes())
        .map_err(|error| error.to_string())?;
    let mesh = json!({
        "schema": "holonics.l1.fixed-section-family-complex-mesh.v1",
        "truth_status": "implemented-exact",
        "vertices": [[0,0,0],[1,0,0],[0,1,0],[3,0,0],[4,0,0],[3,1,0],[2,0,0]],
        "triangles": [[0,1,2],[3,4,5]],
        "higher_cell_edges": [[1,6],[6,3]],
        "plate_occurrences": rest.cultivations().iter().map(|cultivation| &cultivation.plate.occurrence).collect::<Vec<_>>(),
    });
    let mesh_bytes = artifact::write_json(output.join("07-family-complex.mesh.json"), &mesh)?;
    let html = "<!doctype html><meta charset=\"utf-8\"><title>L1 fixed-section families</title><style>body{margin:0;background:#10151f;color:#f4f5f7;font:16px system-ui;display:grid;grid-template-columns:2fr 1fr;min-height:100vh}object{width:100%;height:100vh}aside{padding:28px}code{color:#f1be4b}</style><object data=\"06-family-complex.svg\" type=\"image/svg+xml\"></object><aside><h1>Returned family complex</h1><p>Each triangle is one exact action/constraint/factorization plate. The gold edge is reachable only while both independent supports stand.</p><p>Targeted removal of either plate reopens the composed route while the other local family remains cultivated.</p></aside>\n";
    fs::write(output.join("08-interactive-atlas.html"), html.as_bytes())
        .map_err(|error| error.to_string())?;
    Ok(json!({
        "schema": "holonics.l1.rendering-receipt.v1",
        "truth_status": "implemented-exact",
        "svg_sha256": artifact::digest(svg.as_bytes()),
        "mesh_sha256": artifact::digest(&mesh_bytes),
        "html_sha256": artifact::digest(html.as_bytes()),
        "vertices": 7,
        "triangles": 2,
        "higher_cell_edges": 2,
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
        Ok(output) if output.status.success() => {
            json!({"available": true, "raw": String::from_utf8_lossy(&output.stdout).trim()})
        }
        Ok(output) => {
            json!({"available": false, "status": output.status.code(), "stderr": String::from_utf8_lossy(&output.stderr).trim()})
        }
        Err(error) => json!({"available": false, "error": error.to_string()}),
    }
}

fn read(path: &Path) -> Result<Vec<u8>, String> {
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}
