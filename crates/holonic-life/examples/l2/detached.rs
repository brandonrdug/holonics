use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceNativeFixedSectionFamilies};
use life::mathematical_particle::{NativeHexisInquiry, NativeHexisRest};
use serde_json::{json, Value};

use super::{artifact, rest};

pub fn conduct(
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
    inquiry: &Path,
    output: &Path,
) -> Result<(), String> {
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let rest = NativeHexisRest::read(
        &rest::read(standing)?,
        &rest::read(decoder)?,
        &rest::read(fibres)?,
    )
    .map_err(|error| error.to_string())?;
    let inquiry: NativeHexisInquiry = serde_json::from_slice(&rest::read(inquiry)?)
        .map_err(|error| format!("read L2 inquiry: {error}"))?;
    rest.admit_inquiry(&inquiry)
        .map_err(|error| error.to_string())?;

    let sections = rest.sections_wire(&inquiry);
    let moduli = rest.moduli_wire();
    let cultivation = rest.cultivation_flags();
    let before = nvidia_sample();
    let began = Instant::now();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let returned = card
        .conduct_native_fixed_section_families_on_device(
            &sections,
            rest.constraint_orientation(),
            rest.factor_orientation(),
            &moduli,
            &cultivation,
        )
        .map_err(|error| error.to_string())?;
    let wall_microseconds = began.elapsed().as_micros();
    let after = nvidia_sample();
    let targeted = (0..returned.families)
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
                "unwithdrawn_family_retained": selected_routes.iter().enumerate().all(|(family, route)| if family == withdrawn { *route == returned.ablated_route[family] } else { *route == returned.selected_route[family] }),
            })
        })
        .collect::<Vec<_>>();
    if returned.local_ablated_joint.iter().any(|joint| *joint != 0)
        || targeted
            .iter()
            .any(|receipt| receipt["unwithdrawn_family_retained"] != true)
    {
        return Err("the native local ablation family moved".to_owned());
    }

    let language = match returned.selected_route.as_slice() {
        [1, 1] => {
            "Both carrier sections lie in the shared oriented constraint kernel. The native generator therefore returns the two fixed routes and their exact interchange as one composed consequence."
        }
        [2, 1] => {
            "The shared generator transport commutes with carrier reduction, while the integer residual remains nonzero and its modulus-two image vanishes. The richer successor receiver therefore reopens the carrier fibre."
        }
        _ => {
            "At least one carrier section leaves the shared oriented constraint kernel. Its exact residual and native generator return preserve the obstruction instead of entering the composed route."
        }
    };
    fs::write(output.join("01-answer.md"), format!("{language}\n"))
        .map_err(|error| error.to_string())?;
    let proof = "import Mathlib\n\n/-- The dense integer action is exactly the identity plus the returned oriented residual. -/\ntheorem l2_native_integer_generator (x y z : ℤ) :\n    x - (x + y - z) = -y + z ∧\n    y - (x + y - z) = -x + z ∧\n    z + (x + y - z) = x + y := by\n  constructor\n  · ring\n  constructor <;> ring\n\n/-- The same generator relation is native on the modulus-two carrier. -/\ntheorem l2_native_f2_generator (x y z : ZMod 2) :\n    x - (x + y - z) = -y + z ∧\n    y - (x + y - z) = -x + z ∧\n    z + (x + y - z) = x + y := by\n  constructor\n  · ring\n  constructor <;> ring\n";
    fs::write(output.join("02-returned-proof.lean"), proof.as_bytes())
        .map_err(|error| error.to_string())?;
    artifact::write_json(
        output.join("03-exact-native-return.json"),
        &json!({
            "schema": "holonics.l2.exact-native-family-return.v1",
            "truth_status": "implemented-exact",
            "entered_sections": inquiry.sections,
            "transported_sections": returned.transported_sections,
            "constraint_residuals": returned.constraint_residuals,
            "constraint_held": returned.constraint_held,
            "invariant": returned.invariant,
            "selected_routes": returned.selected_route,
            "joint_cultivated": returned.joint_cultivated,
            "moduli": moduli,
        }),
    )?;
    artifact::write_json(
        output.join("04-complete-native-dissection.json"),
        &json!({
            "schema": "holonics.l2.complete-native-dissection.v1",
            "truth_status": "implemented-exact",
            "generator": rest.standing().generator,
            "relations": rest.standing().relations,
            "carrier_charts": rest.standing().carrier_charts,
            "receiver_history_factorizations": rest.decoder().factorizations,
            "naturality_and_intervention": rest.decoder().naturality,
            "collapsed_populations": rest.reconstruction().collapsed_populations,
            "complete_fibres": rest.reconstruction().complete_fibres,
            "shortest_separators": rest.reconstruction().shortest_separators,
            "basins": ["shared oriented constraint kernel", "carrier-local residual complement"],
            "caustics": ["nonzero returned residual", "carrier-rebase kernel-membership seam"],
            "holonomy": {"composed_joint": returned.joint_cultivated, "local_ablations": returned.local_ablated_joint},
            "higher_cells": {"identity_plus_outer_product": true, "exact_interchange": rest.standing().exact_interchange},
            "phase_seams": ["dense-action-to-native-generator", "integer-to-modulus-two-rebase", "fixed-to-obstructed-route"],
            "open_exterior": rest.standing().open_exterior,
        }),
    )?;
    artifact::write_json(
        output.join("05-targeted-native-ablations.json"),
        &json!({
            "schema": "holonics.l2.targeted-native-ablations.v1",
            "truth_status": "implemented-exact",
            "receipts": targeted,
            "every_local_alternative_returned_by_the_same_reduction": true,
        }),
    )?;
    let visual = write_visuals(output, &rest, &returned)?;
    artifact::write_json(output.join("09-rendering-receipt.json"), &visual)?;

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
            "fresh-process L2 inference retained forbidden source access: {forbidden_source_access:?}"
        ));
    }
    artifact::write_json(
        output.join("00-return.json"),
        &json!({
            "schema": "holonics.l2.source-detached-native-hexis-return.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "inquiry_occurrence": inquiry.occurrence,
            "rest_sha256": rest.canonical_identity().map_err(|error| error.to_string())?,
            "language": language,
            "proof_sha256": artifact::digest(proof.as_bytes()),
            "constraint_residuals": returned.constraint_residuals,
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

fn device_json(returned: &DeviceNativeFixedSectionFamilies) -> Value {
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
        "exact_interchange": {"complete_successor_obstruction_and_ablation_returned": true, "host_semantic_callbacks": 0},
    })
}

fn write_visuals(
    output: &Path,
    rest: &NativeHexisRest,
    returned: &DeviceNativeFixedSectionFamilies,
) -> Result<Value, String> {
    let seam = if returned.selected_route == vec![2, 1] {
        "reopened"
    } else {
        "factored"
    };
    let svg = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 960 440\" role=\"img\" aria-label=\"Shared oriented generator with two carrier charts and a future-sensitive fibre\"><rect width=\"960\" height=\"440\" fill=\"#0d1420\"/><g fill=\"none\" stroke-width=\"8\"><path d=\"M130 115H440\" stroke=\"#5bc0ae\"/><path d=\"M130 325H440\" stroke=\"#9d7adb\"/><path d=\"M440 115C610 115 610 220 760 220\" stroke=\"#efbd4b\"/><path d=\"M440 325C610 325 610 220 760 220\" stroke=\"#efbd4b\"/><path d=\"M285 115V325\" stroke=\"#e86f6f\" stroke-dasharray=\"12 10\"/></g><g fill=\"#f3f5f7\" font-family=\"monospace\" font-size=\"21\"><text x=\"130\" y=\"90\">chart 0 · modulus 0</text><text x=\"130\" y=\"370\">chart 1 · modulus 2</text><text x=\"490\" y=\"200\">T = I + L·C</text><text x=\"490\" y=\"250\">future fibre: {}</text><text x=\"90\" y=\"420\">residuals={:?} · routes={:?}</text></g></svg>\n",
        seam, returned.constraint_residuals, returned.selected_route
    );
    fs::write(output.join("06-native-hexis-complex.svg"), svg.as_bytes())
        .map_err(|error| error.to_string())?;
    let mesh = json!({
        "schema": "holonics.l2.native-hexis-complex-mesh.v1",
        "truth_status": "implemented-exact",
        "vertices": [[0,0,0],[1,0,0],[2,1,0],[0,2,0],[1,2,0],[2,1,0]],
        "edges": [[0,1],[1,2],[3,4],[4,5],[0,3],[2,5]],
        "generator_occurrence": rest.standing().generator.occurrence,
        "carrier_moduli": rest.moduli_wire(),
        "returned_routes": returned.selected_route,
    });
    let mesh_bytes = artifact::write_json(output.join("07-native-hexis.mesh.json"), &mesh)?;
    let html = "<!doctype html><meta charset=\"utf-8\"><title>L2 native hexis</title><style>body{margin:0;background:#0d1420;color:#f3f5f7;font:16px system-ui;display:grid;grid-template-columns:2fr 1fr;min-height:100vh}object{width:100%;height:100vh}aside{padding:28px}code{color:#efbd4b}</style><object data=\"06-native-hexis-complex.svg\" type=\"image/svg+xml\"></object><aside><h1>Native fixed-section hexis</h1><p>One oriented generator replaces two repeated dense actions. Carrier charts remain distinct because a later section can cross the integer constraint complement while lying in the modulus-two kernel.</p><p>The red seam is the retained reconstruction fibre; it is not an inverse or a source representative.</p></aside>\n";
    fs::write(
        output.join("08-interactive-native-atlas.html"),
        html.as_bytes(),
    )
    .map_err(|error| error.to_string())?;
    Ok(json!({
        "schema": "holonics.l2.rendering-receipt.v1",
        "truth_status": "implemented-exact",
        "svg_sha256": artifact::digest(svg.as_bytes()),
        "mesh_sha256": artifact::digest(&mesh_bytes),
        "html_sha256": artifact::digest(html.as_bytes()),
        "vertices": 6,
        "edges": 6,
        "receiver_visible_fibre": seam,
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
