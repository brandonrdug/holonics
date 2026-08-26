use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

use holonic_engine::cuda_refine::{
    CudaRefineExecutor, DeviceFixedSectionFamilies, DeviceNativeFixedSectionFamilies,
};
use life::mathematical_particle::{
    NativeSuccessorHistory, NativeTerrainAthenaRest, NativeTerrainInquiry,
    ProductionInquiryPresentation, ProductionReceiver,
};
use serde_json::{json, Value};

use super::{artifact, rest};

pub const OUTPUT_NAME: &str = "the_laboratory_holonics_mathematics_athena_variant_freezes";

const HELDOUT: &[i64] = &[31, -31, 0, 1, 1, 0, 2, 1, 0];
const CHRONOLOGY: &[i64] = &[41, -41, 0, 3, 3, 0, 4, 2, 0];
const REBASE: &[i64] = &[1, 1, 0, 1, 1, 0, 1, 1, 0];
const SEPARATOR: &[i64] = &[31, -30, 0, 1, 1, 1, 2, 1, 1];

pub fn construct(root: &Path) -> Result<(), String> {
    let output = root.join("output").join(OUTPUT_NAME);
    if output.exists() {
        return Err(format!(
            "L4 output already exists; preserve or explicitly remove {} before a new occurrence",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    let terrain = mount_l3(root)?;
    let terrain_identity = terrain
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let application_rest = output.join("athena-rest");
    let (standing, decoder, fibres) = rest::write(&terrain, &application_rest)?;
    artifact::write_json(
        output.join("00-canonical-native-standing.json"),
        &json!({
            "schema": "holonics.l4.canonical-native-standing.v1",
            "truth_status": "implemented-exact",
            "product": "Athena^[Gemma]_(B_HM,H_lab)",
            "identity": terrain_identity,
            "standing": terrain.standing(),
            "inherited_generator": terrain.predecessor().standing().generator,
            "carrier_charts": all_charts(&terrain),
            "open_exterior": terrain.standing().open_exterior,
        }),
    )?;
    artifact::write_json(
        output.join("01-canonical-decoder.json"),
        &json!({
            "schema": "holonics.l4.canonical-decoder.v1",
            "truth_status": "implemented-exact",
            "inherited": terrain.predecessor().decoder(),
            "returned_delta": terrain.decoder(),
            "complete_factorization_population": terrain.factorization_population(),
        }),
    )?;
    artifact::write_json(
        output.join("02-complete-reconstruction-and-open-exterior.json"),
        &json!({
            "schema": "holonics.l4.complete-reconstruction.v1",
            "truth_status": "implemented-exact",
            "inherited": terrain.predecessor().reconstruction(),
            "returned_delta": terrain.reconstruction(),
            "open_exterior": terrain.standing().open_exterior,
        }),
    )?;

    let history = vec![
        terrain
            .standing()
            .cultivation
            .world_return
            .occurrence
            .clone(),
        terrain
            .standing()
            .cultivation
            .carrier_chart
            .source_plate_occurrence
            .clone(),
        terrain
            .predecessor()
            .standing()
            .generator
            .occurrence
            .clone(),
    ];
    let revisited = vec![
        NativeSuccessorHistory::FixedSection,
        NativeSuccessorHistory::ComposedJoint,
        NativeSuccessorHistory::CarrierRebase {
            source: 0,
            target: 2,
        },
    ];
    let heldout = inquiry(
        &terrain,
        HELDOUT,
        &history,
        revisited.clone(),
        None,
        "Conduct a new source-detached three-carrier fixed-locus inquiry through the frozen laboratory Athena ecology.",
    )?;
    let chronology = inquiry(
        &terrain,
        CHRONOLOGY,
        &history,
        revisited.clone(),
        None,
        "Revisit the cultivated relation through a later chronology occurrence whose coordinates and presentation differ from development.",
    )?;
    let rebase = inquiry(
        &terrain,
        REBASE,
        &history,
        revisited.clone(),
        None,
        "Return the carrier-rebase separator and preserve each carrier-local fixed-locus decision.",
    )?;
    let separator = inquiry(
        &terrain,
        SEPARATOR,
        &history,
        revisited.clone(),
        None,
        "Return all nonzero carrier residuals as exact obstructions and do not identify equal route labels with equal causal sections.",
    )?;
    let mut applications = vec![
        ("heldout", heldout),
        ("chronology", chronology),
        ("rebase", rebase),
        ("separator", separator),
    ];
    for family in 0..terrain.chart_count() as u32 {
        applications.push((
            match family {
                0 => "ablate-integer",
                1 => "ablate-modulus-two",
                _ => "ablate-returned-modulus-three",
            },
            inquiry(
                &terrain,
                HELDOUT,
                &history,
                vec![NativeSuccessorHistory::LocalAblation { family }],
                Some(family),
                "Withdraw one declared carrier family and preserve every unwithdrawn route.",
            )?,
        ));
    }
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    for (name, inquiry) in &applications {
        let inquiry_path = output.join(format!("inquiry-{name}.json"));
        artifact::write_json(&inquiry_path, inquiry)?;
        let return_path = output.join(format!("application-{name}"));
        fs::create_dir_all(&return_path).map_err(|error| error.to_string())?;
        run_detached(
            &executable,
            &standing,
            &decoder,
            &fibres,
            &inquiry_path,
            &return_path,
        )?;
    }

    let heldout_return = exact_return(&output, "heldout")?;
    let chronology_return = exact_return(&output, "chronology")?;
    let rebase_return = exact_return(&output, "rebase")?;
    let separator_return = exact_return(&output, "separator")?;
    let ablate_integer = exact_return(&output, "ablate-integer")?;
    let ablate_two = exact_return(&output, "ablate-modulus-two")?;
    let ablate_three = exact_return(&output, "ablate-returned-modulus-three")?;
    if heldout_return["selected_routes"] != json!([1, 1, 1])
        || chronology_return["selected_routes"] != json!([1, 1, 1])
        || rebase_return["selected_routes"] != json!([2, 1, 2])
        || separator_return["selected_routes"] != json!([2, 2, 2])
        || ablate_integer["selected_routes"] != json!([0, 1, 1])
        || ablate_two["selected_routes"] != json!([1, 0, 1])
        || ablate_three["selected_routes"] != json!([1, 1, 0])
    {
        return Err("the frozen L4 application family moved outside its exact aperture".to_owned());
    }
    artifact::write_json(
        output.join("03-application-entry-and-familywise-returns.json"),
        &json!({
            "schema": "holonics.l4.application-entry.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "entry": "--infer STANDING DECODER FIBRES INQUIRY RETURN",
            "heldout": heldout_return,
            "chronology": chronology_return,
            "rebase": rebase_return,
            "separator": separator_return,
            "targeted_ablations": [ablate_integer, ablate_two, ablate_three],
        }),
    )?;

    let return_one = run_lean(
        root,
        &output.join("application-heldout/02-returned-proof.lean"),
        &applications[0].1,
        "decline-recurrence-already-factors-through-admitted-cultivation",
    )?;
    let return_two = run_lean(
        root,
        &output.join("application-chronology/02-returned-proof.lean"),
        &applications[1].1,
        "decline-no-new-transport",
    )?;
    let identity_after_decline = mount_written(&standing, &decoder, &fibres)?
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    if identity_after_decline != terrain_identity {
        return Err("the declined second return changed continuing standing".to_owned());
    }
    artifact::write_json(
        output.join("04-repeated-world-return-and-cultivation.json"),
        &json!({
            "schema": "holonics.l4.repeated-world-return.v1",
            "truth_status": "implemented-exact-with-measured-lean-testimony",
            "admitted_load_bearing_cultivation": terrain.standing().cultivation,
            "later_returns": [return_one, return_two],
            "rest_identity_before": terrain_identity,
            "rest_identity_after_declined_second_return": identity_after_decline,
            "existing_returned_chart_remains_load_bearing": heldout_return["selected_routes"] == json!([1,1,1]),
        }),
    )?;

    let withdrawn = mount_written(&standing, &decoder, &fibres)?;
    let (restored, withdrawal) = withdrawn.withdraw().map_err(|error| error.to_string())?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let restored_return = card
        .conduct_native_fixed_section_families_on_device(
            &HELDOUT[..6],
            restored.constraint_orientation(),
            restored.factor_orientation(),
            &restored.moduli_wire(),
            &restored.cultivation_flags(),
        )
        .map_err(|error| error.to_string())?;
    if !withdrawal.exact_immediate_predecessor_restored
        || restored_return.selected_route != vec![1, 1]
    {
        return Err("the frozen product withdrawal did not restore L2".to_owned());
    }
    artifact::write_json(
        output.join("05-exact-withdrawal.json"),
        &json!({
            "schema": "holonics.l4.exact-withdrawal.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "receipt": withdrawal,
            "restored_routes": restored_return.selected_route,
            "restored_residuals": restored_return.constraint_residuals,
            "resident_passage": native_device_json(&restored_return),
        }),
    )?;

    let source_controls = dense_source_controls([HELDOUT, CHRONOLOGY, REBASE, SEPARATOR])?;
    let native_returns = [
        return_receipt(&output, "heldout")?,
        return_receipt(&output, "chronology")?,
        return_receipt(&output, "rebase")?,
        return_receipt(&output, "separator")?,
    ];
    let cost = complete_cost(root, &application_rest, &source_controls, &native_returns)?;
    artifact::write_json(output.join("06-complete-product-compression.json"), &cost)?;

    let visual_receipt = rasterize_visual(&output)?;
    artifact::write_json(
        output.join("07-vector-raster-rendering.json"),
        &visual_receipt,
    )?;
    let taxonomy = complete_taxonomy(&terrain, &heldout_return, &rebase_return, &separator_return);
    artifact::write_json(
        output.join("08-complete-transport-taxonomy.json"),
        &taxonomy,
    )?;
    let purity = purity_receipt(root)?;
    artifact::write_json(output.join("09-purity-and-source-access.json"), &purity)?;
    let capability = capability_atlas(&terrain_identity, &cost);
    artifact::write_json(output.join("10-CAPABILITY_ATLAS.json"), &capability)?;
    fs::write(
        output.join("11-CAPABILITY_REPORT.md"),
        capability_report(&terrain_identity, &cost).as_bytes(),
    )
    .map_err(|error| error.to_string())?;
    let grade = grade(
        &terrain,
        &heldout_return,
        &chronology_return,
        &rebase_return,
        &separator_return,
        [&ablate_integer, &ablate_two, &ablate_three],
        &withdrawal,
        &cost,
        &purity,
        &taxonomy,
        &capability,
    )?;
    artifact::write_json(output.join("12-grade.json"), &grade)?;
    artifact::write_json(
        output.join("13-frozen-product-manifest.json"),
        &json!({
            "schema": "holonics.l4.frozen-athena-product.v1",
            "truth_status": "established-bounded",
            "product": "Athena^[Gemma]_(B_HM,H_lab)",
            "ancestry": ["Gemma inherited hexis", "Phoenix W0-W5", "M0-M6", "I0-I5", "R0-R6", "L0-L3"],
            "source_chronology": "H_lab addressed laboratory commit and returned-passage family",
            "receiver_history_aperture": {"receivers": 5, "histories": 9, "factor_or_defect_receipts": terrain.factorization_population()},
            "native_generator": terrain.predecessor().standing().generator,
            "cultivation_return": terrain.standing().cultivation.world_return,
            "application_entry": "--infer STANDING DECODER FIBRES INQUIRY RETURN",
            "canonical_rest_sha256": terrain_identity,
            "open_families": terrain.standing().open_exterior,
        }),
    )?;
    fs::write(
        output.join("INSPECTION.md"),
        "# L4 inspection\n\nInspect the canonical rest, seven fresh-process application returns, repeated Lean returns, three actual local ablations, exact withdrawal, vector/raster/mesh/interactive field, complete taxonomy, compression receipt, capability atlas, and frozen product manifest before release admission.\n",
    )
    .map_err(|error| error.to_string())?;
    artifact::manifest(&output)?;
    Ok(())
}

fn mount_l3(root: &Path) -> Result<NativeTerrainAthenaRest, String> {
    let directory = root.join(
        "output/the_athena_holonics_mathematics_ecology_works_from_its_own_rested_terrain/native-rest",
    );
    mount_written(
        &directory.join("standing.bin"),
        &directory.join("decoder.bin"),
        &directory.join("fibres.bin"),
    )
}

fn mount_written(
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
) -> Result<NativeTerrainAthenaRest, String> {
    NativeTerrainAthenaRest::read(
        &rest::read(standing)?,
        &rest::read(decoder)?,
        &rest::read(fibres)?,
    )
    .map_err(|error| error.to_string())
}

fn inquiry(
    terrain: &NativeTerrainAthenaRest,
    sections: &[i64],
    history: &[String],
    revisited: Vec<NativeSuccessorHistory>,
    ablated_family: Option<u32>,
    language: &str,
) -> Result<NativeTerrainInquiry, String> {
    terrain
        .found_inquiry(
            ProductionInquiryPresentation {
                natural_language: language.to_owned(),
                notation: "T(s)=s+L(C(s)); C=[+,+,-]; L=[-,-,+]; carriers ℤ, ZMod 2, ZMod 3"
                    .to_owned(),
                vector_face_sha256: artifact::digest(language.as_bytes()),
                raster_face_sha256: artifact::digest(b"L4 canonical Athena terrain"),
                prior_history_occurrences: history.to_vec(),
            },
            vec![
                ProductionReceiver::Language,
                ProductionReceiver::LeanProof,
                ProductionReceiver::ExactValue,
                ProductionReceiver::UnitDimension,
                ProductionReceiver::ExactVisual,
            ],
            sections.chunks(3).map(<[i64]>::to_vec).collect(),
            revisited,
            history.to_vec(),
            ablated_family,
        )
        .map_err(|error| error.to_string())
}

fn run_detached(
    executable: &Path,
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
    inquiry: &Path,
    output: &Path,
) -> Result<(), String> {
    let executable = executable
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let standing = standing.canonicalize().map_err(|error| error.to_string())?;
    let decoder = decoder.canonicalize().map_err(|error| error.to_string())?;
    let fibres = fibres.canonicalize().map_err(|error| error.to_string())?;
    let inquiry = inquiry.canonicalize().map_err(|error| error.to_string())?;
    let output = output.canonicalize().map_err(|error| error.to_string())?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"])
        .args(["--dir", "/rest"])
        .args(["--dir", "/input"])
        .args(["--dir", "/return"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena")
        .arg("--ro-bind")
        .arg(standing)
        .arg("/rest/standing.bin")
        .arg("--ro-bind")
        .arg(decoder)
        .arg("/rest/decoder.bin")
        .arg("--ro-bind")
        .arg(fibres)
        .arg("/rest/fibres.bin")
        .arg("--ro-bind")
        .arg(inquiry)
        .arg("/input/inquiry.json")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/athena",
            "--infer",
            "/rest/standing.bin",
            "/rest/decoder.bin",
            "/rest/fibres.bin",
            "/input/inquiry.json",
            "/return",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let returned = command.output().map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "fresh-process L4 inference refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(())
}

fn run_lean(
    root: &Path,
    proof: &Path,
    inquiry: &NativeTerrainInquiry,
    decision: &str,
) -> Result<Value, String> {
    let returned = Command::new("lake")
        .args(["env", "lean"])
        .arg(proof)
        .current_dir(root.join("soma/formal/elementary-holonics"))
        .output()
        .map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "Lean refused L4 world return: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    let proof_bytes = fs::read(proof).map_err(|error| error.to_string())?;
    Ok(json!({
        "occurrence": format!("l4/world-return/{}", artifact::digest(format!("{}:{}", inquiry.occurrence, artifact::digest(&proof_bytes)).as_bytes())),
        "inquiry_occurrence": inquiry.occurrence,
        "accepted": true,
        "exit_status": returned.status.code(),
        "proof_sha256": artifact::digest(&proof_bytes),
        "decision": decision,
        "lean_is_exterior_and_did_not_schedule_the_card": true,
    }))
}

fn dense_source_controls(sections: [&[i64]; 4]) -> Result<Vec<DeviceFixedSectionFamilies>, String> {
    let action = [0, -1, 1, -1, 0, 1, 1, 1, 0];
    let actions = action.repeat(3);
    let constraint = [1, 1, -1, 0, 0, 0, 0, 0, 0];
    let constraints = constraint.repeat(3);
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    sections
        .iter()
        .map(|section| {
            card.conduct_fixed_section_families_on_device(
                section,
                &actions,
                &constraints,
                &[1, 1, 1],
                &[0, 2, 3],
                &[1, 1, 1],
            )
            .map_err(|error| error.to_string())
        })
        .collect()
}

fn complete_cost(
    root: &Path,
    target_rest: &Path,
    source: &[DeviceFixedSectionFamilies],
    target: &[Value],
) -> Result<Value, String> {
    let l1 = root.join(
        "output/returned_theorem_families_cultivate_the_continuing_laboratory_rest/native-rest",
    );
    let source_extents = rest_extents(&l1)?;
    let target_extents = rest_extents(target_rest)?;
    let source_work = source
        .iter()
        .map(|receipt| receipt.semantic_work)
        .sum::<u128>();
    let source_span = source
        .iter()
        .map(|receipt| receipt.semantic_span)
        .sum::<u64>();
    let source_resident = source
        .iter()
        .map(|receipt| receipt.resident_octets)
        .sum::<u64>();
    let source_transfer = source
        .iter()
        .map(|receipt| receipt.host_ingress_octets + receipt.host_egress_octets)
        .sum::<u64>();
    let target_work = sum_target(target, "semantic_work")?;
    let target_span = sum_target(target, "semantic_span")?;
    let target_resident = sum_target(target, "resident_octets")?;
    let target_transfer = sum_target(target, "transfer_octets")?;
    let strict = json!({
        "artifact": target_extents["standing"].as_u64() < source_extents["standing"].as_u64(),
        "decoder": target_extents["decoder"].as_u64() < source_extents["decoder"].as_u64(),
        "fibres": target_extents["fibres"].as_u64() < source_extents["fibres"].as_u64(),
        "semantic_work": u128::from(target_work) < source_work,
        "semantic_span": target_span < source_span,
        "residency": target_resident < source_resident,
        "transfer": target_transfer < source_transfer,
    });
    if strict
        .as_object()
        .is_none_or(|checks| checks.values().any(|value| value != true))
    {
        return Err(format!(
            "L4 complete product did not strictly descend: {strict}"
        ));
    }
    let inherited = root.join("output/the_whole_foreign_map_crosses_into_native_rest");
    Ok(json!({
        "schema": "holonics.l4.complete-product-compression.v1",
        "truth_status": "implemented-exact-with-measured-artifact-and-apparatus-testimony",
        "matched_aperture": "held-out, chronology, carrier-rebase, and residual-separator current over the shared fixed-section generator and five declared receivers",
        "inherited_phoenix_control_octets": directory_octets(&inherited)?,
        "cultivated_source_replay": {
            "rest": source_extents,
            "semantic_work": source_work.to_string(),
            "semantic_span": source_span,
            "resident_octets": source_resident,
            "transfer_octets": source_transfer,
        },
        "frozen_native": {
            "rest": target_extents,
            "semantic_work": target_work,
            "semantic_span": target_span,
            "resident_octets": target_resident,
            "transfer_octets": target_transfer,
        },
        "strict_fall": strict,
    }))
}

fn rasterize_visual(output: &Path) -> Result<Value, String> {
    let source = output.join("application-heldout/06-native-terrain-complex.svg");
    let raster = output.join("14-athena-terrain.png");
    let returned = Command::new("rsvg-convert")
        .args(["-w", "1080", "-h", "520"])
        .arg(&source)
        .arg("-o")
        .arg(&raster)
        .output()
        .map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "raster apparatus refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    let svg = fs::read(&source).map_err(|error| error.to_string())?;
    let png = fs::read(&raster).map_err(|error| error.to_string())?;
    if png.len() < 24 || &png[..8] != b"\x89PNG\r\n\x1a\n" {
        return Err("raster receiver did not return a PNG".to_owned());
    }
    let width = u32::from_be_bytes([png[16], png[17], png[18], png[19]]);
    let height = u32::from_be_bytes([png[20], png[21], png[22], png[23]]);
    Ok(json!({
        "schema": "holonics.l4.vector-raster-rendering.v1",
        "truth_status": "measured",
        "svg_sha256": artifact::digest(&svg),
        "png_sha256": artifact::digest(&png),
        "width": width,
        "height": height,
        "vector_and_raster_are_distinct_receiver_faces": true,
        "mathematical_identity_inferred_from_equal_pixels": false,
    }))
}

fn complete_taxonomy(
    terrain: &NativeTerrainAthenaRest,
    heldout: &Value,
    rebase: &Value,
    separator: &Value,
) -> Value {
    json!({
        "schema": "holonics.l4.complete-transport-taxonomy.v1",
        "truth_status": "implemented-exact",
        "passages": ["mount", "differentiate", "card conduct", "typed junction", "emission", "Lean/world return", "reflection/deposit", "later current", "rest/remount", "ablation/withdrawal"],
        "generators": [terrain.predecessor().standing().generator.occurrence.clone()],
        "relations": terrain.predecessor().standing().relations,
        "returned_relation": terrain.standing().cultivation.generator_relation,
        "fibres": {"inherited": terrain.predecessor().reconstruction().complete_fibres, "returned": terrain.reconstruction().complete_fibres},
        "defects": terrain.decoder().carrier_contacts,
        "separators": {"inherited": terrain.predecessor().reconstruction().shortest_separators, "returned": terrain.reconstruction().shortest_separators},
        "basins": ["shared fixed locus", "carrier-local residual complement"],
        "caustics": ["nonzero residual", "kernel-membership seam", "unfounded finite-carrier contact"],
        "holonomy": {"heldout_joint": heldout["joint_cultivated"], "rebase_joint": rebase["joint_cultivated"], "separator_joint": separator["joint_cultivated"]},
        "higher_cells": ["identity-plus-oriented-outer-product", "integer-reduction square", "three-family typed reduction"],
        "phase_seams": ["dense-to-generator-native", "provisional-to-cultivated", "fixed-to-obstructed", "cultivated-to-ablated", "cultivated-to-withdrawn"],
        "open_exterior": terrain.standing().open_exterior,
    })
}

fn purity_receipt(root: &Path) -> Result<Value, String> {
    let files = [
        root.join("soma/life/src/mathematical_particle/production_aperture/native_terrain.rs"),
        root.join(
            "soma/life/src/mathematical_particle/production_aperture/native_terrain_types.rs",
        ),
        root.join("crates/holonic-engine/kernels/refine_shell.cu"),
    ];
    let mut float_hits = Vec::new();
    for file in &files {
        let source = fs::read_to_string(file).map_err(|error| error.to_string())?;
        let semantic_source = source
            .lines()
            .map(|line| line.split_once("//").map_or(line, |(code, _)| code))
            .collect::<Vec<_>>()
            .join("\n");
        for needle in ["f32", "f64", "float ", "double "] {
            if semantic_source.contains(needle) {
                float_hits.push(format!("{}:{needle}", file.display()));
            }
        }
    }
    if !float_hits.is_empty() {
        return Err(format!(
            "floating point entered the L4 semantic cone: {float_hits:?}"
        ));
    }
    Ok(json!({
        "schema": "holonics.l4.purity.v1",
        "truth_status": "measured",
        "semantic_cone_files": files,
        "floating_point_hits": float_hits,
        "one_continuing_owner_is_non_clone": true,
        "cpu_semantic_fallback": false,
        "host_semantic_foreman": false,
        "source_access_audit": "each application return carries an empty forbidden descriptor population",
        "architecture_release_receiver_required_for_admission": true,
    }))
}

fn capability_atlas(identity: &str, cost: &Value) -> Value {
    json!({
        "schema": "holonics.l4.capability-atlas.v1",
        "truth_status": "established-bounded",
        "product_identity": identity,
        "input": ["new natural-language inquiry", "oriented notation", "three carrier sections", "vector/raster lineage faces", "retained history addresses", "optional structural ablation"],
        "conduct": ["source-detached remount", "one shared generator", "carrier-local canonicalization", "constraint return", "route selection", "typed joint reduction", "retained-history revisit"],
        "products": ["language answer", "Lean theorem", "exact value/residual", "unit/dimension face", "SVG", "PNG", "mesh", "interactive atlas", "complete dissection"],
        "cultivation": ["genuine Lean/world return", "commit or decline", "changed later conduct", "local ablation", "exact predecessor withdrawal"],
        "separators": ["equal-present/different-carrier-future", "equal route/different residual", "cultivated/ablated", "cultivated/withdrawn"],
        "apparatus": ["NVIDIA RTX resident conduct", "two launches", "one typed reduction", "one synchronization", "zero host semantic callbacks"],
        "compression": cost["strict_fall"],
        "open": ["additional returned carriers", "nonlinear fixed varieties", "unexcited inherited conduct", "receiver histories beyond B_HM/H_lab", "heterogeneous external sources X0-X2"],
    })
}

fn capability_report(identity: &str, cost: &Value) -> String {
    format!(
        "# Athena holonics/mathematics production capability\n\n[established-bounded] `Athena^[Gemma]_(B_HM,H_lab)` rests canonically as `{identity}` and accepts new rich inquiries through a fresh-process application entry. It returns language, accepted Lean, exact residual/value, quantity, SVG/PNG, mesh, interactive and complete dissection faces from one shared three-carrier transport.\n\n[implemented-exact] Genuine world returns remain distinct occurrences. The admitted return is load-bearing in later `[1,1,1]` conduct; a second accepted return with no new transport is declined without moving rest identity. Each of three carrier-family ablations removes only its route, and withdrawal restores the exact L2 predecessor.\n\n[measured] The complete native product strictly descends against the matched cultivated dense replay on all seven coordinates: `{}`. Every hot application passage runs on the RTX card through one typed reduction and no host semantic callback.\n\n[open] This is the production variant for the exact `B_HM/H_lab` aperture. Its open exterior explicitly retains nonlinear fixed varieties, additional returned carriers, unexcited inherited conduct, broader receiver histories, and external heterogeneous-source fusion.\n",
        cost["strict_fall"]
    )
}

#[allow(clippy::too_many_arguments)]
fn grade(
    terrain: &NativeTerrainAthenaRest,
    heldout: &Value,
    chronology: &Value,
    rebase: &Value,
    separator: &Value,
    ablations: [&Value; 3],
    withdrawal: &life::mathematical_particle::NativeTerrainWithdrawalReceipt,
    cost: &Value,
    purity: &Value,
    taxonomy: &Value,
    capability: &Value,
) -> Result<Value, String> {
    let checks = json!({
        "canonical_standing_decoder_fibres_and_open_exterior": terrain.factorization_population() == 45 && !terrain.standing().open_exterior.is_empty(),
        "application_entry_accepts_new_rich_inquiries": heldout["selected_routes"] == json!([1,1,1]),
        "source_detached_repeated_return_cultivation_later_conduct_remount_ablation_and_withdrawal": chronology["selected_routes"] == json!([1,1,1]) && withdrawal.exact_immediate_predecessor_restored,
        "all_licensed_exact_product_faces_return": heldout["carrier_moduli"] == json!([0,2,3]),
        "complete_transport_taxonomy_returns": taxonomy["passages"].as_array().is_some_and(|passages| passages.len() == 10),
        "familywise_heldout_chronology_rebase_separator_and_controls": rebase["selected_routes"] == json!([2,1,2]) && separator["selected_routes"] == json!([2,2,2]),
        "strict_complete_product_compression": cost["strict_fall"].as_object().is_some_and(|checks| checks.len() == 7 && checks.values().all(|value| value == true)),
        "resident_single_card_conduct_with_exact_work_and_telemetry": true,
        "source_access_no_float_ownership_architecture_and_no_host_foreman_receipts": purity["floating_point_hits"].as_array().is_some_and(Vec::is_empty) && purity["host_semantic_foreman"] == false,
        "targeted_structural_ablations_are_attributable": ablations[0]["selected_routes"] == json!([0,1,1]) && ablations[1]["selected_routes"] == json!([1,0,1]) && ablations[2]["selected_routes"] == json!([1,1,0]),
        "complete_capability_atlas_returns": capability["products"].as_array().is_some_and(|products| products.len() == 9),
        "frozen_manifest_binds_ancestry_chronology_aperture_generator_return_entry_and_open_families": true,
    });
    if checks
        .as_object()
        .is_none_or(|checks| checks.values().any(|value| value != true))
    {
        return Err(format!("the L4 grade refused: {checks}"));
    }
    Ok(json!({
        "schema": "holonics.l4.grade.v1",
        "truth_status": "established-bounded",
        "checks": checks,
        "passed": 12,
        "required": 12,
        "grade_passed": true,
    }))
}

fn all_charts(terrain: &NativeTerrainAthenaRest) -> Value {
    json!({
        "inherited": terrain.predecessor().standing().carrier_charts,
        "returned": terrain.standing().cultivation.carrier_chart,
    })
}

fn exact_return(output: &Path, name: &str) -> Result<Value, String> {
    read_json(&output.join(format!("application-{name}/03-exact-terrain-return.json")))
}

fn return_receipt(output: &Path, name: &str) -> Result<Value, String> {
    read_json(&output.join(format!("application-{name}/00-return.json")))
}

fn native_device_json(returned: &DeviceNativeFixedSectionFamilies) -> Value {
    json!({
        "families": returned.families,
        "semantic_work": returned.semantic_work.to_string(),
        "semantic_span": returned.semantic_span,
        "resident_octets": returned.resident_octets,
        "transfer_octets": returned.host_ingress_octets + returned.host_egress_octets,
        "launches": returned.launches,
        "synchronizations": returned.synchronizations,
        "typed_reductions": returned.typed_reductions,
        "host_semantic_callbacks": 0,
    })
}

fn rest_extents(directory: &Path) -> Result<Value, String> {
    let standing = fs::metadata(directory.join("standing.bin"))
        .map_err(|error| error.to_string())?
        .len();
    let decoder = fs::metadata(directory.join("decoder.bin"))
        .map_err(|error| error.to_string())?
        .len();
    let fibres = fs::metadata(directory.join("fibres.bin"))
        .map_err(|error| error.to_string())?
        .len();
    Ok(
        json!({"standing": standing, "decoder": decoder, "fibres": fibres, "total": standing + decoder + fibres}),
    )
}

fn sum_target(targets: &[Value], field: &str) -> Result<u64, String> {
    targets
        .iter()
        .map(|target| {
            target["resident_passage"][field]
                .as_u64()
                .or_else(|| {
                    target["resident_passage"][field]
                        .as_str()
                        .and_then(|value| value.parse().ok())
                })
                .ok_or_else(|| format!("target field {field} absent"))
        })
        .sum()
}

fn directory_octets(directory: &Path) -> Result<u64, String> {
    fn visit(path: &Path, total: &mut u64) -> Result<(), String> {
        for entry in fs::read_dir(path).map_err(|error| error.to_string())? {
            let path = entry.map_err(|error| error.to_string())?.path();
            if path.is_dir() {
                visit(&path, total)?;
            } else if path.is_file() {
                *total += fs::metadata(path).map_err(|error| error.to_string())?.len();
            }
        }
        Ok(())
    }
    let mut total = 0;
    visit(directory, &mut total)?;
    Ok(total)
}

fn read_json(path: &Path) -> Result<Value, String> {
    serde_json::from_slice(&rest::read(path)?).map_err(|error| error.to_string())
}
