use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceFixedSectionFamilies};
use life::mathematical_particle::{
    FamilyCultivatedEcologyRest, NativeHexisInquiry, NativeHexisRest,
    ProductionInquiryPresentation, ProductionReceiver,
};
use serde_json::{json, Value};

use super::{artifact, rest};

const HELDOUT: &[i64] = &[11, -11, 0, 1, 1, 0];
const RESIDUAL_SEPARATOR: &[i64] = &[11, -10, 0, 1, 1, 1];
const CARRIER_SEPARATOR: &[i64] = &[1, 1, 0, 1, 1, 0];

pub fn construct(root: &Path) -> Result<(), String> {
    let output = root.join("output").join(rest::OUTPUT_NAME);
    if output.exists() {
        return Err(format!(
            "L2 output already exists; preserve or explicitly remove {} before a new occurrence",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;

    let cultivated = rest::mount_l1(root)?;
    let cultivated_identity = cultivated
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let l1_rest_directory = root.join(
        "output/returned_theorem_families_cultivate_the_continuing_laboratory_rest/native-rest",
    );
    let source_extents = rest_extents(&l1_rest_directory)?;
    let mut source_card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let source_heldout = source_passage(&cultivated, HELDOUT, &mut source_card)?;
    let source_residual = source_passage(&cultivated, RESIDUAL_SEPARATOR, &mut source_card)?;
    let source_carrier = source_passage(&cultivated, CARRIER_SEPARATOR, &mut source_card)?;
    if source_heldout.selected_route != vec![1, 1]
        || source_residual.selected_route != vec![2, 2]
        || source_carrier.selected_route != vec![2, 1]
    {
        return Err("the matched cultivated L1 family moved before condensation".to_owned());
    }
    let source_controls = vec![
        source_receipt("heldout", &source_heldout),
        source_receipt("residual-separator", &source_residual),
        source_receipt("carrier-future-separator", &source_carrier),
    ];
    artifact::write_json(
        output.join("00-matched-cultivated-source-controls.json"),
        &json!({
            "schema": "holonics.l2.matched-cultivated-source-controls.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "cultivated_predecessor_sha256": cultivated_identity,
            "controls": source_controls,
            "device": source_card.device_name(),
            "cpu_semantic_replay": false,
        }),
    )?;

    let native = NativeHexisRest::condense(cultivated).map_err(|error| error.to_string())?;
    let native_identity = native
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let native_rest = output.join("native-rest");
    let (standing, decoder, fibres) = rest::write(&native, &native_rest)?;
    let target_extents = rest_extents(&native_rest)?;
    artifact::write_json(
        output.join("01-native-hexis-standing.json"),
        native.standing(),
    )?;
    artifact::write_json(
        output.join("02-receiver-history-factorization.json"),
        native.decoder(),
    )?;
    artifact::write_json(
        output.join("03-complete-reconstruction-fibres.json"),
        native.reconstruction(),
    )?;

    let history = native
        .reconstruction()
        .predecessor_component_addresses
        .iter()
        .rev()
        .take(4)
        .cloned()
        .collect::<Vec<_>>();
    let heldout = inquiry(
        &native,
        HELDOUT,
        &history,
        "Conduct the recurring integer and modulus-two fixed-section theorem families through their shared native generator and return the exact composed route.",
    )?;
    let residual = inquiry(
        &native,
        RESIDUAL_SEPARATOR,
        &history,
        "Return both exact residual obstructions and their expanded native transports without collapsing the composed route.",
    )?;
    let carrier = inquiry(
        &native,
        CARRIER_SEPARATOR,
        &history,
        "Apply the shortest successor intervention which separates the equal-present integer and modulus-two carrier sections.",
    )?;
    let inquiries = [
        ("04-heldout-inquiry.json", "heldout-return", &heldout),
        (
            "05-residual-separator-inquiry.json",
            "residual-separator-return",
            &residual,
        ),
        (
            "06-carrier-future-separator-inquiry.json",
            "carrier-future-separator-return",
            &carrier,
        ),
    ];
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    for (inquiry_name, return_name, inquiry) in inquiries {
        let inquiry_path = output.join(inquiry_name);
        artifact::write_json(&inquiry_path, inquiry)?;
        let returned = output.join(return_name);
        fs::create_dir_all(&returned).map_err(|error| error.to_string())?;
        run_detached(
            &executable,
            &standing,
            &decoder,
            &fibres,
            &inquiry_path,
            &returned,
        )?;
    }

    let native_heldout = read_json(&output.join("heldout-return/03-exact-native-return.json"))?;
    let native_residual =
        read_json(&output.join("residual-separator-return/03-exact-native-return.json"))?;
    let native_carrier =
        read_json(&output.join("carrier-future-separator-return/03-exact-native-return.json"))?;
    let heldout_agrees = agrees(&source_heldout, &native_heldout);
    let residual_agrees = agrees(&source_residual, &native_residual);
    let carrier_agrees = agrees(&source_carrier, &native_carrier);
    if !heldout_agrees || !residual_agrees || !carrier_agrees {
        return Err("the source-detached native relation disagreed with cultivated L1".to_owned());
    }
    artifact::write_json(
        output.join("07-source-detached-factorization-agreement.json"),
        &json!({
            "schema": "holonics.l2.source-detached-factorization-agreement.v1",
            "truth_status": "implemented-exact",
            "heldout_complete_agreement": heldout_agrees,
            "residual_separator_complete_agreement": residual_agrees,
            "carrier_future_separator_complete_agreement": carrier_agrees,
            "source_access_after_condensation": false,
        }),
    )?;
    let naturality = &native.decoder().naturality[0];
    if native_carrier["constraint_residuals"] != json!([2, 0])
        || native_carrier["selected_routes"] != json!([2, 1])
        || !naturality.generator_square_commutes
        || naturality.cultivation_square_commutes
    {
        return Err("the richer carrier receiver did not reopen the unlawful quotient".to_owned());
    }
    artifact::write_json(
        output.join("08-richer-receiver-reopening.json"),
        &json!({
            "schema": "holonics.l2.richer-receiver-reopening.v1",
            "truth_status": "implemented-exact",
            "equal_present_sections": [[0,0,0],[0,0,0]],
            "shortest_successor_sections": [[1,1,0],[1,1,0]],
            "returned_residuals": native_carrier["constraint_residuals"],
            "returned_routes": native_carrier["selected_routes"],
            "raw_generator_naturality": naturality.generator_square_commutes,
            "cultivation_membership_naturality": naturality.cultivation_square_commutes,
            "exact_defect": naturality.exact_defect,
            "unlawful_quotient_reopened": true,
        }),
    )?;

    let lean_return = run_lean(root, &output.join("heldout-return/02-returned-proof.lean"))?;
    artifact::write_json(
        output.join("09-native-generator-world-return.json"),
        &lean_return,
    )?;
    let target_returns = [
        read_json(&output.join("heldout-return/00-return.json"))?,
        read_json(&output.join("residual-separator-return/00-return.json"))?,
        read_json(&output.join("carrier-future-separator-return/00-return.json"))?,
    ];
    let cost = complete_cost(
        &source_extents,
        &target_extents,
        [&source_heldout, &source_residual, &source_carrier],
        &target_returns,
    )?;
    artifact::write_json(output.join("10-complete-product-cost.json"), &cost)?;
    fs::write(
        output.join("11-CAPABILITY_REPORT.md"),
        capability_report(&native_identity, &cost).as_bytes(),
    )
    .map_err(|error| error.to_string())?;
    let grade = grade(
        &native,
        &native_heldout,
        &native_residual,
        &native_carrier,
        &lean_return,
        &cost,
    )?;
    artifact::write_json(output.join("12-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        "# L2 inspection\n\nThe shared oriented generator, two carrier charts, retained future-sensitive fibre, exact intervention seam, mesh, SVG and interactive atlas returned. Visual inspection remains required before release admission.\n",
    )
    .map_err(|error| error.to_string())?;
    artifact::manifest(&output)?;
    Ok(())
}

fn source_passage(
    rest: &FamilyCultivatedEcologyRest,
    sections: &[i64],
    card: &mut CudaRefineExecutor,
) -> Result<DeviceFixedSectionFamilies, String> {
    card.conduct_fixed_section_families_on_device(
        sections,
        &rest.actions_wire(),
        &rest.constraints_wire(),
        &rest.constraint_rows_wire(),
        &rest.moduli_wire(),
        &rest.cultivation_flags(),
    )
    .map_err(|error| error.to_string())
}

fn source_receipt(control: &str, returned: &DeviceFixedSectionFamilies) -> Value {
    json!({
        "control": control,
        "transported_sections": returned.transported_sections,
        "constraint_held": returned.constraint_held,
        "selected_routes": returned.selected_route,
        "joint_cultivated": returned.joint_cultivated,
        "semantic_work": returned.semantic_work.to_string(),
        "semantic_span": returned.semantic_span,
        "resident_octets": returned.resident_octets,
        "transfer_octets": returned.host_ingress_octets + returned.host_egress_octets,
        "launches": returned.launches,
        "synchronizations": returned.synchronizations,
        "typed_reductions": returned.typed_reductions,
    })
}

fn inquiry(
    rest: &NativeHexisRest,
    sections: &[i64],
    history: &[String],
    language: &str,
) -> Result<NativeHexisInquiry, String> {
    let sections = sections.chunks(3).map(<[i64]>::to_vec).collect::<Vec<_>>();
    rest.found_inquiry(
        ProductionInquiryPresentation {
            natural_language: language.to_owned(),
            notation: "T(s)=s+L(C(s)); C=[+,+,-], L=[-,-,+], with carrier-local canonicalization"
                .to_owned(),
            vector_face_sha256: artifact::digest(language.as_bytes()),
            raster_face_sha256: artifact::digest(b"L2 native oriented generator complex"),
            prior_history_occurrences: history.to_vec(),
        },
        vec![
            ProductionReceiver::Language,
            ProductionReceiver::LeanProof,
            ProductionReceiver::ExactValue,
            ProductionReceiver::UnitDimension,
            ProductionReceiver::ExactVisual,
        ],
        sections,
        history.to_vec(),
    )
    .map_err(|error| error.to_string())
}

fn agrees(source: &DeviceFixedSectionFamilies, native: &Value) -> bool {
    native["transported_sections"] == json!(source.transported_sections)
        && native["constraint_held"] == json!(source.constraint_held)
        && native["selected_routes"] == json!(source.selected_route)
        && native["joint_cultivated"] == json!(source.joint_cultivated)
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
            "fresh-process L2 inference refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(())
}

fn run_lean(root: &Path, proof: &Path) -> Result<Value, String> {
    let returned = Command::new("lake")
        .args(["env", "lean"])
        .arg(proof)
        .current_dir(root.join("soma/formal/elementary-holonics"))
        .output()
        .map_err(|error| error.to_string())?;
    let receipt = json!({
        "schema": "holonics.l2.native-generator-lean-return.v1",
        "truth_status": "measured",
        "accepted": returned.status.success(),
        "exit_status": returned.status.code(),
        "stdout": String::from_utf8_lossy(&returned.stdout),
        "stderr": String::from_utf8_lossy(&returned.stderr),
        "proof_sha256": artifact::digest(&fs::read(proof).map_err(|error| error.to_string())?),
        "lean_is_exterior_and_did_not_schedule_the_card": true,
    });
    if receipt["accepted"] != true {
        return Err(format!("Lean refused the L2 generator relation: {receipt}"));
    }
    Ok(receipt)
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
    Ok(json!({
        "artifact_octets": standing,
        "decoder_octets": decoder,
        "fibre_octets": fibres,
        "total_octets": standing + decoder + fibres,
    }))
}

fn target_measure(returned: &Value, field: &str) -> Result<u64, String> {
    let value = &returned["resident_passage"][field];
    value
        .as_u64()
        .or_else(|| value.as_str().and_then(|value| value.parse().ok()))
        .ok_or_else(|| format!("target {field} absent"))
}

fn complete_cost(
    source_extents: &Value,
    target_extents: &Value,
    source: [&DeviceFixedSectionFamilies; 3],
    target: &[Value; 3],
) -> Result<Value, String> {
    let source_work = source
        .iter()
        .map(|passage| passage.semantic_work)
        .sum::<u128>();
    let source_span = source
        .iter()
        .map(|passage| passage.semantic_span)
        .sum::<u64>();
    let source_resident = source
        .iter()
        .map(|passage| passage.resident_octets)
        .sum::<u64>();
    let source_transfer = source
        .iter()
        .map(|passage| passage.host_ingress_octets + passage.host_egress_octets)
        .sum::<u64>();
    let target_work = target
        .iter()
        .map(|passage| target_measure(passage, "semantic_work"))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .sum::<u64>();
    let target_span = target
        .iter()
        .map(|passage| target_measure(passage, "semantic_span"))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .sum::<u64>();
    let target_resident = target
        .iter()
        .map(|passage| target_measure(passage, "resident_octets"))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .sum::<u64>();
    let target_transfer = target
        .iter()
        .map(|passage| target_measure(passage, "transfer_octets"))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .sum::<u64>();
    let strict = json!({
        "artifact": target_extents["artifact_octets"].as_u64() < source_extents["artifact_octets"].as_u64(),
        "decoder": target_extents["decoder_octets"].as_u64() < source_extents["decoder_octets"].as_u64(),
        "fibres": target_extents["fibre_octets"].as_u64() < source_extents["fibre_octets"].as_u64(),
        "semantic_work": u128::from(target_work) < source_work,
        "semantic_span": target_span < source_span,
        "residency": target_resident < source_resident,
        "transfer": target_transfer < source_transfer,
    });
    if strict
        .as_object()
        .is_none_or(|fields| fields.values().any(|value| value != true))
    {
        return Err(format!(
            "the L2 complete product did not strictly descend: {strict}"
        ));
    }
    Ok(json!({
        "schema": "holonics.l2.complete-product-cost.v1",
        "truth_status": "implemented-exact-with-measured-artifact-extents",
        "aperture": "held-out fixed sections, two residual obstructions, and the equal-present/different-future carrier separator across all five declared receivers and six successor histories",
        "source_cultivated": {
            "rest": source_extents,
            "semantic_work": source_work.to_string(),
            "semantic_span": source_span,
            "resident_octets": source_resident,
            "transfer_octets": source_transfer,
        },
        "generator_native": {
            "rest": target_extents,
            "semantic_work": target_work,
            "semantic_span": target_span,
            "resident_octets": target_resident,
            "transfer_octets": target_transfer,
        },
        "strict_fall": strict,
    }))
}

fn capability_report(identity: &str, cost: &Value) -> String {
    format!(
        "# L2 capability report\n\n[established-bounded] Native rest `{identity}` replaces the two repeated dense L1 action/constraint/factor plates with one shared oriented generator `T=I+L·C`. The integer and modulus-two carriers remain distinct charts with independent support and cultivation lineage.\n\n[implemented-exact] Every one of the five declared product receivers factors over fixed, expanded, composed, locally ablated, and carrier-rebased successor histories, or returns the exact carrier-kernel defect. The raw generator square commutes across reduction; cultivation membership correctly does not. Three complete collapsed populations, six reconstruction fibres, and the one-step shortest future separator remain in the decoder boundary.\n\n[measured] Source-detached RTX conduct agrees with cultivated L1 on the held-out, residual, and carrier-future family. The complete product falls on artifact, decoder, fibres, semantic work, span, residency, and transfer: `{}`.\n\n[open] Only receiver histories outside the frozen L1 aperture, nonlinear fixed varieties, and overlapping supports remain exterior to this L2 rest.\n",
        cost["strict_fall"]
    )
}

fn grade(
    native: &NativeHexisRest,
    heldout: &Value,
    residual: &Value,
    carrier: &Value,
    lean: &Value,
    cost: &Value,
) -> Result<Value, String> {
    let checks = json!({
        "native_generators_and_relations_derived": native.standing().relations.len() == 2 && native.standing().relations.iter().all(|relation| relation.identity_plus_oriented_outer_product && relation.fixed_kernel_factors),
        "every_declared_receiver_history_factors_or_returns_defect": native.decoder().factorizations.len() == native.decoder().receivers.len() * native.decoder().declared_histories.len(),
        "shared_transport_has_naturality_and_intervention_receipts": native.decoder().naturality.len() == 1 && native.decoder().naturality[0].generator_square_commutes && !native.decoder().naturality[0].cultivation_square_commutes,
        "collapsed_populations_retain_complete_fibres_and_shortest_separator": native.reconstruction().collapsed_populations.iter().all(|population| population.complete) && native.reconstruction().shortest_separators.len() == 1,
        "source_detached_native_conduct_matches_cultivated_ecology": heldout["selected_routes"] == json!([1,1]) && residual["selected_routes"] == json!([2,2]) && lean["accepted"] == true,
        "richer_receiver_reopens_unlawful_quotient": carrier["constraint_residuals"] == json!([2,0]) && carrier["selected_routes"] == json!([2,1]),
        "complete_product_strictly_falls_on_all_seven_coordinates": cost["strict_fall"].as_object().is_some_and(|fields| fields.len() == 7 && fields.values().all(|value| value == true)),
    });
    let passed = checks
        .as_object()
        .is_some_and(|checks| checks.values().all(|value| value == true));
    if !passed {
        return Err(format!("the L2 grade refused: {checks}"));
    }
    Ok(json!({
        "schema": "holonics.l2.grade.v1",
        "truth_status": "established-bounded",
        "checks": checks,
        "passed": 7,
        "required": 7,
        "grade_passed": true,
    }))
}

fn read_json(path: &Path) -> Result<Value, String> {
    serde_json::from_slice(&rest::read(path)?).map_err(|error| error.to_string())
}
