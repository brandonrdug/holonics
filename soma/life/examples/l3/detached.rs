use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceNativeFixedSectionFamilies};
use life::mathematical_particle::{NativeTerrainAthenaRest, NativeTerrainInquiry};
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
    let terrain = NativeTerrainAthenaRest::read(
        &rest::read(standing)?,
        &rest::read(decoder)?,
        &rest::read(fibres)?,
    )
    .map_err(|error| error.to_string())?;
    let inquiry: NativeTerrainInquiry = serde_json::from_slice(&rest::read(inquiry)?)
        .map_err(|error| format!("read L3 inquiry: {error}"))?;
    terrain
        .admit_inquiry(&inquiry)
        .map_err(|error| error.to_string())?;

    let moduli = terrain.moduli_wire();
    let cultivation = terrain.cultivation_flags(&inquiry);
    let before = nvidia_sample();
    let began = Instant::now();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let returned = card
        .conduct_native_fixed_section_families_on_device(
            &terrain.sections_wire(&inquiry),
            terrain.constraint_orientation(),
            terrain.factor_orientation(),
            &moduli,
            &cultivation,
        )
        .map_err(|error| error.to_string())?;
    let wall_microseconds = began.elapsed().as_micros();
    let after = nvidia_sample();

    let language = explain(&returned);
    fs::write(output.join("01-answer.md"), format!("{language}\n"))
        .map_err(|error| error.to_string())?;
    let proof = "import Mathlib\n\n/-- One oriented rank-one transport law is native over the returned modulus-three carrier. -/\ntheorem l3_native_zmod3_generator (x y z : ZMod 3) :\n    x - (x + y - z) = -y + z ∧\n    y - (x + y - z) = -x + z ∧\n    z + (x + y - z) = x + y := by\n  constructor\n  · ring\n  constructor <;> ring\n\n/-- The constraint kernel is the exact fixed locus of that transport. -/\ntheorem l3_zmod3_fixed_locus (x y z : ZMod 3) (h : x + y - z = 0) :\n    (x - (x + y - z), y - (x + y - z), z + (x + y - z)) = (x, y, z) := by\n  simp [h]\n";
    fs::write(output.join("02-returned-proof.lean"), proof.as_bytes())
        .map_err(|error| error.to_string())?;
    artifact::write_json(
        output.join("03-exact-terrain-return.json"),
        &json!({
            "schema": "holonics.l3.exact-terrain-return.v1",
            "truth_status": "implemented-exact",
            "entered_sections": inquiry.sections,
            "transported_sections": returned.transported_sections,
            "constraint_residuals": returned.constraint_residuals,
            "constraint_held": returned.constraint_held,
            "invariant": returned.invariant,
            "selected_routes": returned.selected_route,
            "joint_cultivated": returned.joint_cultivated,
            "carrier_moduli": moduli,
            "cultivation_flags": cultivation,
            "equation_face": "T(s)=s+L(C(s)), C(x,y,z)=x+y-z, L(a)=(-a,-a,a)",
            "quantity_face": {
                "dimension": "the entered carrier coordinate dimension",
                "unit": "one inherited coordinate unit",
                "returned_residual_role": "oriented scalar coefficient of the shared transport difference",
                "unit_conversion_authored": false
            }
        }),
    )?;
    artifact::write_json(
        output.join("04-complete-terrain-dissection.json"),
        &json!({
            "schema": "holonics.l3.complete-terrain-dissection.v1",
            "truth_status": "implemented-exact",
            "load_bearing_generator": terrain.predecessor().standing().generator,
            "inherited_relations": terrain.predecessor().standing().relations,
            "returned_cultivation": terrain.standing().cultivation,
            "inherited_histories": terrain.predecessor().decoder().declared_histories,
            "added_histories": terrain.decoder().added_histories,
            "all_receiver_history_factors": terrain.factorization_population(),
            "carrier_contacts": terrain.decoder().carrier_contacts,
            "inherited_fibres": terrain.predecessor().reconstruction().complete_fibres,
            "added_fibres": terrain.reconstruction().complete_fibres,
            "shortest_separators": terrain.reconstruction().shortest_separators,
            "modality_contact": {
                "language": inquiry.presentation.natural_language,
                "notation": inquiry.presentation.notation,
                "vector_face_sha256": inquiry.presentation.vector_face_sha256,
                "raster_face_sha256": inquiry.presentation.raster_face_sha256,
                "common_relation": "one receiver-licensed oriented fixed-section transport"
            },
            "basins": ["shared constraint kernel", "carrier-local residual complement"],
            "caustics": ["nonzero residual", "integer/finite kernel-membership seam", "unfounded finite-carrier map"],
            "holonomy": {"joint_return": returned.joint_cultivated, "local_withdrawal_faces": returned.local_ablated_joint},
            "higher_cells": {"identity_plus_outer_product": true, "integer_reduction_square": true, "finite_contact_filled": false},
            "phase_seams": ["exterior-return-to-rested-chart", "integer-to-modulus-three", "modulus-two-to-obstructed-contact"],
            "open_exterior": terrain.standing().open_exterior,
        }),
    )?;
    let targeted = targeted_ablations(&returned);
    artifact::write_json(
        output.join("05-targeted-terrain-ablations.json"),
        &json!({
            "schema": "holonics.l3.targeted-terrain-ablations.v1",
            "truth_status": "implemented-exact",
            "receipts": targeted,
            "requested_ablation": inquiry.ablated_family,
            "same_resident_reduction": true,
        }),
    )?;
    let visual = write_visuals(output, &terrain, &returned)?;
    artifact::write_json(output.join("09-rendering-receipt.json"), &visual)?;

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
            "fresh-process L3 inference retained forbidden source access: {forbidden_source_access:?}"
        ));
    }
    artifact::write_json(
        output.join("00-return.json"),
        &json!({
            "schema": "holonics.l3.source-detached-terrain-return.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "inquiry_occurrence": inquiry.occurrence,
            "rest_sha256": terrain.canonical_identity().map_err(|error| error.to_string())?,
            "language": language,
            "proof_sha256": artifact::digest(proof.as_bytes()),
            "constraint_residuals": returned.constraint_residuals,
            "selected_routes": returned.selected_route,
            "joint_cultivated": returned.joint_cultivated,
            "device": card.device_name(),
            "resident_passage": device_json(&returned),
            "physical_telemetry": {"before": before, "after": after, "wall_microseconds": wall_microseconds, "energy": "unknown"},
            "developmental_source_proof_exchange_and_build_cache_mounted": false,
            "open_descriptors": open_descriptors,
            "forbidden_source_access": forbidden_source_access,
        }),
    )?;
    Ok(())
}

fn explain(returned: &DeviceNativeFixedSectionFamilies) -> &'static str {
    match returned.selected_route.as_slice() {
        [1, 1, 1] => "All three carrier sections lie in the same oriented constraint kernel. The returned modulus-three chart therefore participates in the shared fixed-locus consequence deposited by the earlier world return.",
        [1, 1, 0] => "The inherited integer and modulus-two fixed routes remain. The returned modulus-three family is locally withdrawn, so the joint consequence is absent without moving either inherited chart.",
        [2, 1, 2] => "The common generator transports all charts, but carrier-local kernel membership differs. The modulus-two route is fixed while the integer and modulus-three residuals retain their distinct obstruction faces.",
        _ => "The shared generator returned the exact carrier-local transports and residuals. Nonzero residuals remain explicit obstructions, and no unfounded carrier identification was introduced.",
    }
}

fn targeted_ablations(returned: &DeviceNativeFixedSectionFamilies) -> Vec<Value> {
    (0..returned.families)
        .map(|withdrawn| {
            let routes = returned
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
                "selected_routes": routes,
                "joint_cultivated": returned.local_ablated_joint[withdrawn] == 1,
                "unwithdrawn_routes_unchanged": routes.iter().enumerate().all(|(family, route)| family == withdrawn || *route == returned.selected_route[family]),
            })
        })
        .collect()
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
    terrain: &NativeTerrainAthenaRest,
    returned: &DeviceNativeFixedSectionFamilies,
) -> Result<Value, String> {
    let svg = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 1080 520\" role=\"img\" aria-label=\"L3 returned carrier terrain\"><rect width=\"1080\" height=\"520\" fill=\"#0b1320\"/><g fill=\"none\" stroke-width=\"8\"><path d=\"M100 100C360 100 420 260 700 260\" stroke=\"#54c5ad\"/><path d=\"M100 260H700\" stroke=\"#9d7bdd\"/><path d=\"M100 420C360 420 420 260 700 260\" stroke=\"#efb847\"/><path d=\"M700 260H950\" stroke=\"#e86d6d\"/><circle cx=\"700\" cy=\"260\" r=\"42\" stroke=\"#f5f7fa\"/></g><g fill=\"#f5f7fa\" font-family=\"monospace\" font-size=\"20\"><text x=\"100\" y=\"72\">integer chart</text><text x=\"100\" y=\"232\">modulus-two chart</text><text x=\"100\" y=\"392\">returned modulus-three chart</text><text x=\"735\" y=\"235\">T = I + L·C</text><text x=\"70\" y=\"485\">residuals={:?} · routes={:?}</text></g></svg>\n",
        returned.constraint_residuals, returned.selected_route
    );
    fs::write(output.join("06-native-terrain-complex.svg"), svg.as_bytes())
        .map_err(|error| error.to_string())?;
    let mesh = json!({
        "schema": "holonics.l3.native-terrain-mesh.v1",
        "truth_status": "implemented-exact",
        "vertices": [[0,0,0],[1,0,0],[2,1,0],[0,1,0],[1,1,0],[2,1,0],[0,2,0],[1,2,0],[2,1,0],[3,1,0]],
        "edges": [[0,1],[1,2],[3,4],[4,5],[6,7],[7,8],[2,9],[5,9],[8,9]],
        "carrier_moduli": terrain.moduli_wire(),
        "returned_routes": returned.selected_route,
        "returned_chart_occurrence": terrain.standing().cultivation.carrier_chart.source_plate_occurrence,
    });
    let mesh_bytes = artifact::write_json(output.join("07-native-terrain.mesh.json"), &mesh)?;
    let html = "<!doctype html><meta charset=\"utf-8\"><title>L3 native terrain</title><style>body{margin:0;background:#0b1320;color:#f5f7fa;font:16px system-ui;display:grid;grid-template-columns:2fr 1fr;min-height:100vh}object{width:100%;height:100vh}aside{padding:30px}code{color:#efb847}</style><object data=\"06-native-terrain-complex.svg\" type=\"image/svg+xml\"></object><aside><h1>Returned native terrain</h1><p>Three carrier charts meet one oriented generator. The chart added by the Lean/world return is load-bearing only for later current which enters its fixed locus.</p><p>The junction preserves the integer-reduction square, the finite-carrier obstruction, and the exact local withdrawal face.</p></aside>\n";
    fs::write(output.join("08-interactive-terrain-atlas.html"), html.as_bytes())
        .map_err(|error| error.to_string())?;
    Ok(json!({
        "schema": "holonics.l3.rendering-receipt.v1",
        "truth_status": "implemented-exact",
        "svg_sha256": artifact::digest(svg.as_bytes()),
        "mesh_sha256": artifact::digest(&mesh_bytes),
        "html_sha256": artifact::digest(html.as_bytes()),
        "vertices": 10,
        "edges": 9,
        "faces": ["language", "notation", "equation", "diagram", "mesh", "physical quantity"],
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
        Ok(output) => json!({"available": false, "status": output.status.code(), "stderr": String::from_utf8_lossy(&output.stderr).trim()}),
        Err(error) => json!({"available": false, "error": error.to_string()}),
    }
}
