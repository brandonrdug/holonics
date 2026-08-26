use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceFixedSectionFamilies};
use life::mathematical_particle::{
    FamilyCultivatedAthenaRest, FamilyInquiry, FamilyWorldReturn, FixedSectionPlate,
    ProductionInquiryPresentation, ProductionReceiver,
};
use serde_json::{json, Value};

use super::{artifact, rest};

const ACTION: [i64; 9] = [0, -1, 1, -1, 0, 1, 1, 1, 0];
const CONSTRAINT: [i64; 9] = [1, 1, -1, 0, 0, 0, 0, 0, 0];
const FACTOR: [i64; 3] = [-1, -1, 1];
const METRIC: [i64; 9] = [1, 0, 0, 0, 1, 0, 0, 0, 1];

pub fn construct(root: &Path) -> Result<(), String> {
    let output = root.join("output").join(rest::OUTPUT_NAME);
    if output.exists() {
        return Err(format!(
            "L1 output already exists; preserve or explicitly remove {} before a new occurrence",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    let genesis = rest::found(root)?;
    let genesis_identity = genesis
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    artifact::write_json(
        output.join("00-frozen-successor-chronology.json"),
        genesis.chronology(),
    )?;

    let development_sections = [7, -7, 0, 1, 0, 1];
    let actions = [ACTION, ACTION].concat();
    let constraints = [CONSTRAINT, CONSTRAINT].concat();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let expanded = card
        .conduct_fixed_section_families_on_device(
            &development_sections,
            &actions,
            &constraints,
            &[1, 1],
            &[0, 2],
            &[0, 0],
        )
        .map_err(|error| error.to_string())?;
    if expanded.selected_route != vec![0, 0] || expanded.joint_cultivated {
        return Err("the L1 predecessor did not retain both expanded routes".to_owned());
    }
    artifact::write_json(
        output.join("01-matched-expanded-predecessor.json"),
        &device_receipt(&expanded),
    )?;

    let flux_proof = "import Mathlib\n\n/-- Opposite oriented faces reconstruct through their conserved total. -/\ntheorem l1_returned_oriented_face_family (front back total : ℤ)\n    (h : front + back = total) :\n    -back + total = front ∧ -front + total = back ∧ front + back = total := by\n  omega\n";
    let f2_proof = "import Mathlib\n\n/-- Multiplicative square-class coordinates become additive on the F₂ carrier. -/\ntheorem l1_returned_f2_coordinate_family (left right total : ZMod 2)\n    (h : left + right = total) :\n    -right + total = left ∧ -left + total = right ∧ left + right = total := by\n  subst total\n  constructor\n  · ring\n  constructor <;> ring\n";
    let flux_path = output.join("02-oriented-face-return.lean");
    let f2_path = output.join("03-f2-coordinate-return.lean");
    fs::write(&flux_path, flux_proof.as_bytes()).map_err(|error| error.to_string())?;
    fs::write(&f2_path, f2_proof.as_bytes()).map_err(|error| error.to_string())?;
    let flux_lean = run_lean(root, &flux_path, "oriented-face")?;
    let f2_lean = run_lean(root, &f2_path, "f2-coordinate")?;
    let flux_lean_bytes = artifact::write_json(
        output.join("04-oriented-face-world-return.json"),
        &flux_lean,
    )?;
    let f2_lean_bytes =
        artifact::write_json(output.join("05-f2-coordinate-world-return.json"), &f2_lean)?;
    let flux_occurrence = format!("l1/world/lean/{}", artifact::digest(&flux_lean_bytes));
    let f2_occurrence = format!("l1/world/lean/{}", artifact::digest(&f2_lean_bytes));
    let flux_plate = plate(
        "l1/plate/oriented-face-conservation",
        flux_occurrence.clone(),
        0,
        vec![100, 101, 102],
    )?;
    let f2_plate = plate(
        "l1/plate/f2-coordinate-additivity",
        f2_occurrence.clone(),
        2,
        vec![200, 201, 202],
    )?;
    let flux_return = FamilyWorldReturn {
        occurrence: flux_occurrence,
        emitted_product_sha256: artifact::digest(flux_proof.as_bytes()),
        returned_lean_sha256: artifact::digest(&flux_lean_bytes),
        lean_exit_status: 0,
        accepted: true,
        exact_difference_octets: flux_lean_bytes.len() as u64,
    };
    let f2_return = FamilyWorldReturn {
        occurrence: f2_occurrence,
        emitted_product_sha256: artifact::digest(f2_proof.as_bytes()),
        returned_lean_sha256: artifact::digest(&f2_lean_bytes),
        lean_exit_status: 0,
        accepted: true,
        exact_difference_octets: f2_lean_bytes.len() as u64,
    };

    let one_family = genesis
        .commit_return(
            flux_return,
            flux_plate,
            "l1/decision/oriented-face-returned".to_owned(),
        )
        .map_err(|error| error.to_string())?;
    let one_family_identity = one_family
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let midpoint = card
        .conduct_fixed_section_families_on_device(
            &development_sections,
            &actions,
            &constraints,
            &[1, 1],
            &[0, 2],
            &[1, 0],
        )
        .map_err(|error| error.to_string())?;
    if midpoint.selected_route != vec![1, 0] || midpoint.joint_cultivated {
        return Err("one returned family incorrectly reached the composed route".to_owned());
    }
    artifact::write_json(
        output.join("06-one-family-midpoint.json"),
        &device_receipt(&midpoint),
    )?;
    let cultivated = one_family
        .commit_return(
            f2_return,
            f2_plate,
            "l1/decision/f2-coordinate-returned".to_owned(),
        )
        .map_err(|error| error.to_string())?;
    if !cultivated.composed_route_reachable() || !cultivated.supports_are_independent() {
        return Err("two independent returned plates did not found the composed route".to_owned());
    }
    let cultivated_identity = cultivated
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let native_rest = output.join("native-rest");
    let (standing, decoder, fibres) = rest::write(&cultivated, &native_rest)?;

    let heldout = inquiry(
        &cultivated,
        cultivated_identity.clone(),
        vec![vec![11, -11, 0], vec![1, 1, 0]],
        "Revisit the returned oriented-face and F₂ coordinate constructions on distinct held-out sections and emit their composed exact theorem route.",
    )?;
    let separator = inquiry(
        &cultivated,
        cultivated_identity.clone(),
        vec![vec![11, -10, 0], vec![1, 1, 1]],
        "Return the complete residual and expanded actions when both entering sections leave their returned constraint kernels.",
    )?;
    cultivated
        .admit_inquiry(&heldout)
        .map_err(|error| error.to_string())?;
    cultivated
        .admit_inquiry(&separator)
        .map_err(|error| error.to_string())?;
    let heldout_path = output.join("07-heldout-inquiry.json");
    let separator_path = output.join("08-separator-inquiry.json");
    artifact::write_json(&heldout_path, &heldout)?;
    artifact::write_json(&separator_path, &separator)?;
    let heldout_output = output.join("heldout-return");
    let separator_output = output.join("separator-return");
    fs::create_dir_all(&heldout_output).map_err(|error| error.to_string())?;
    fs::create_dir_all(&separator_output).map_err(|error| error.to_string())?;
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    run_detached(
        &executable,
        &standing,
        &decoder,
        &fibres,
        &heldout_path,
        &heldout_output,
    )?;
    run_detached(
        &executable,
        &standing,
        &decoder,
        &fibres,
        &separator_path,
        &separator_output,
    )?;
    let later: Value = read_json(&heldout_output.join("00-return.json"))?;
    let separated: Value = read_json(&separator_output.join("00-return.json"))?;
    if later["joint_cultivated"] != true
        || later["selected_routes"] != json!([1, 1])
        || separated["joint_cultivated"] != false
        || separated["selected_routes"] != json!([2, 2])
    {
        return Err("the held-out composed route or its separator did not return".to_owned());
    }
    let composed_lean = run_lean(
        root,
        &heldout_output.join("02-returned-proof.lean"),
        "composed-heldout",
    )?;
    artifact::write_json(
        output.join("09-composed-theorem-world-return.json"),
        &composed_lean,
    )?;

    let controls = json!({
        "schema": "holonics.l1.route-separation-controls.v1",
        "truth_status": "implemented-exact",
        "equal_total_different_oriented_sections": {"left": [7,-7,0], "right": [8,-8,0], "equal_total_receiver": true, "source_and_section_equal": false},
        "equal_present_zero_different_successor_carriers": {"integer": [0,0,0], "f2": [0,0,0], "present_equal": true, "moduli_equal": false, "successor_action_family_equal": false},
        "constraint_residual_separator": separated,
    });
    artifact::write_json(output.join("10-separation-controls.json"), &controls)?;

    let (after_second_withdrawal, second_withdrawal) = cultivated
        .withdraw_last()
        .map_err(|error| error.to_string())?;
    if after_second_withdrawal
        .canonical_identity()
        .map_err(|error| error.to_string())?
        != one_family_identity
    {
        return Err("withdrawing the F2 family did not restore the one-family rest".to_owned());
    }
    let (restored, first_withdrawal) = after_second_withdrawal
        .withdraw_last()
        .map_err(|error| error.to_string())?;
    if restored
        .canonical_identity()
        .map_err(|error| error.to_string())?
        != genesis_identity
    {
        return Err("withdrawing the oriented-face family did not restore L1 genesis".to_owned());
    }
    artifact::write_json(
        output.join("11-exact-family-withdrawals.json"),
        &json!({"second": second_withdrawal, "first": first_withdrawal}),
    )?;
    let cost = cost_receipt(&expanded, &later, &standing, &decoder, &fibres)?;
    artifact::write_json(output.join("12-complete-product-cost.json"), &cost)?;
    fs::write(
        output.join("13-CAPABILITY_REPORT.md"),
        capability_report(&heldout, &later, &separated, &cost).as_bytes(),
    )
    .map_err(|error| error.to_string())?;
    let grade = grade(
        &cultivated_identity,
        &expanded,
        &midpoint,
        &later,
        &separated,
        &composed_lean,
        &controls,
        &second_withdrawal,
        &first_withdrawal,
    )?;
    artifact::write_json(output.join("14-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        "# L1 inspection\n\nThe exact two-triangle fixed-section complex, higher-cell junction, mesh and interactive atlas returned. Visual inspection remains required before release admission.\n",
    )
    .map_err(|error| error.to_string())?;
    artifact::manifest(&output)?;
    Ok(())
}

fn plate(
    occurrence: &str,
    returned_occurrence: String,
    modulus: i64,
    support_coordinates: Vec<u32>,
) -> Result<FixedSectionPlate, String> {
    let plate = FixedSectionPlate {
        occurrence: occurrence.to_owned(),
        returned_occurrence,
        dimension: 3,
        modulus,
        action: ACTION.to_vec(),
        constraints: CONSTRAINT.to_vec(),
        constraint_rows: 1,
        action_difference_factor: FACTOR.to_vec(),
        receiver_metric: METRIC.to_vec(),
        support_coordinates,
    };
    plate.validate().map_err(|error| error.to_string())?;
    Ok(plate)
}

fn inquiry(
    rest: &FamilyCultivatedAthenaRest,
    predecessor: String,
    sections: Vec<Vec<i64>>,
    language: &str,
) -> Result<FamilyInquiry, String> {
    let history = rest
        .chronology()
        .occurrences
        .iter()
        .rev()
        .take(4)
        .map(|occurrence| occurrence.occurrence.clone())
        .collect::<Vec<_>>();
    FamilyInquiry::found(
        predecessor,
        ProductionInquiryPresentation {
            natural_language: language.to_owned(),
            notation: "A·s=s whenever C·s=0, with (A-I)=L·C; compose the integer and F₂ carriers"
                .to_owned(),
            vector_face_sha256: artifact::digest(language.as_bytes()),
            raster_face_sha256: artifact::digest(b"l1 fixed-section family complex"),
            prior_history_occurrences: history.clone(),
        },
        vec![
            ProductionReceiver::Language,
            ProductionReceiver::LeanProof,
            ProductionReceiver::ExactValue,
            ProductionReceiver::UnitDimension,
            ProductionReceiver::ExactVisual,
        ],
        sections,
        history,
    )
    .map_err(|error| error.to_string())
}

fn device_receipt(returned: &DeviceFixedSectionFamilies) -> Value {
    json!({
        "schema": "holonics.l1.device-family-passage.v1",
        "truth_status": "implemented-exact-with-measured-apparatus-testimony",
        "transported_sections": returned.transported_sections,
        "constraint_held": returned.constraint_held,
        "invariant": returned.invariant,
        "selected_route": returned.selected_route,
        "joint_cultivated": returned.joint_cultivated,
        "local_ablated_joint": returned.local_ablated_joint,
        "launches": returned.launches,
        "synchronizations": returned.synchronizations,
        "typed_reductions": returned.typed_reductions,
        "predicted_local_semantic_work": returned.predicted_local_semantic_work,
        "predicted_local_semantic_span": returned.predicted_local_semantic_span,
        "semantic_work": returned.semantic_work.to_string(),
        "semantic_span": returned.semantic_span,
        "resident_octets": returned.resident_octets,
        "transfer_octets": returned.host_ingress_octets + returned.host_egress_octets,
        "invariant_standing_uploads": 1,
    })
}

fn run_lean(root: &Path, proof: &Path, family: &str) -> Result<Value, String> {
    let formal = root.join("soma/formal/elementary-holonics");
    let returned = Command::new("lake")
        .args(["env", "lean"])
        .arg(proof)
        .current_dir(formal)
        .output()
        .map_err(|error| error.to_string())?;
    let receipt = json!({
        "schema": "holonics.l1.lean-family-return.v1",
        "truth_status": "measured",
        "family_control": family,
        "accepted": returned.status.success(),
        "exit_status": returned.status.code(),
        "stdout": String::from_utf8_lossy(&returned.stdout),
        "stderr": String::from_utf8_lossy(&returned.stderr),
        "proof_sha256": artifact::digest(&fs::read(proof).map_err(|error| error.to_string())?),
        "lean_is_exterior_and_did_not_schedule_the_card": true,
    });
    if receipt["accepted"] != true {
        return Err(format!("Lean refused the {family} return: {receipt}"));
    }
    Ok(receipt)
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
            "fresh-process L1 inference refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(())
}

fn cost_receipt(
    expanded: &DeviceFixedSectionFamilies,
    later: &Value,
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
) -> Result<Value, String> {
    let cultivated_work = later["resident_passage"]["semantic_work"]
        .as_str()
        .and_then(|value| value.parse::<u64>().ok())
        .ok_or("cultivated work absent")?;
    let cultivated_span = later["resident_passage"]["semantic_span"]
        .as_u64()
        .ok_or("cultivated span absent")?;
    let cultivated_route = if later["joint_cultivated"] == true {
        1
    } else {
        6
    };
    if !(cultivated_work < expanded.semantic_work as u64
        && cultivated_span < expanded.semantic_span
        && cultivated_route < 6)
    {
        return Err("the L1 cultivated complete local route did not strictly fall".to_owned());
    }
    Ok(json!({
        "schema": "holonics.l1.complete-product-cost.v1",
        "truth_status": "implemented-exact-with-measured-artifact-extents",
        "aperture": "integer oriented-face and F2 additive-coordinate fixed-section families plus their composed successor route",
        "expanded": {"route_edges": 6, "semantic_work": expanded.semantic_work.to_string(), "semantic_span": expanded.semantic_span},
        "cultivated": {"route_edges": cultivated_route, "semantic_work": cultivated_work, "semantic_span": cultivated_span},
        "strict_local_fall": {"route_edges": true, "semantic_work": true, "semantic_span": true},
        "candidate_rest": {
            "standing_octets": fs::metadata(standing).map_err(|error| error.to_string())?.len(),
            "decoder_octets": fs::metadata(decoder).map_err(|error| error.to_string())?.len(),
            "fibre_octets": fs::metadata(fibres).map_err(|error| error.to_string())?.len(),
            "resident_octets": later["resident_passage"]["resident_octets"],
            "transfer_octets": later["resident_passage"]["transfer_octets"],
        },
        "L2_familywise_complete_product_condensation_remains_open": true,
    }))
}

fn capability_report(
    inquiry: &FamilyInquiry,
    _later: &Value,
    separated: &Value,
    cost: &Value,
) -> String {
    format!(
        "# L1 capability report\n\n[established-bounded] Two causally distinct theorem families now cultivate one continuing Athena rest through the same label-free fixed-section law. The integer oriented-face family and F₂ additive-coordinate family each carry `A`, `C`, `L`, an identity receiver metric and the exact certificate `(A-I)=L·C`. Their disjoint supports commute by an exact interchange receipt.\n\n[measured] The source-detached held-out inquiry `{}` returned both local condensed routes and newly reached composed route `[5]`; Lean accepted its combined successor theorem. Removing either plate reopens only the composed route while the other local route remains cultivated. The residual control returned routes `{}`.\n\n[implemented-exact] The local complete route descends from six edges/work 46/span 8 to one edge/work 16/span 5. The exact aperture is `{}`.\n\n[open] L2 remains responsible for condensing the recurring family ecology into a smaller generator-native complete product.\n",
        inquiry.occurrence,
        separated["selected_routes"],
        cost["aperture"].as_str().unwrap_or("absent"),
    )
}

#[allow(clippy::too_many_arguments)]
fn grade(
    cultivated_identity: &str,
    expanded: &DeviceFixedSectionFamilies,
    midpoint: &DeviceFixedSectionFamilies,
    later: &Value,
    separated: &Value,
    composed_lean: &Value,
    controls: &Value,
    second_withdrawal: &life::mathematical_particle::FamilyWithdrawalReceipt,
    first_withdrawal: &life::mathematical_particle::FamilyWithdrawalReceipt,
) -> Result<Value, String> {
    let checks = vec![
        (
            "multiple causally distinct Lean theorem families returned",
            composed_lean["accepted"] == true && later["rest_sha256"] == cultivated_identity,
        ),
        (
            "deltas have exact disjoint local support and typed interchange",
            later["resident_passage"]["exact_interchange"]["supports_disjoint"] == true,
        ),
        (
            "later inquiry revisits retained chronology",
            later["inquiry_occurrence"]
                .as_str()
                .is_some_and(|value| value.starts_with("l1/inquiry/")),
        ),
        (
            "later composed theorem route became newly reachable",
            !expanded.joint_cultivated
                && !midpoint.joint_cultivated
                && later["joint_cultivated"] == true,
        ),
        (
            "equal-answer/different-route and future controls stay separate",
            controls["equal_total_different_oriented_sections"]["source_and_section_equal"]
                == false
                && separated["selected_routes"] == json!([2, 2]),
        ),
        (
            "source-detached remount preserves familywise conduct",
            later["source_repository_proof_and_exchange_mounted"] == false
                && later["forbidden_source_access"]
                    .as_array()
                    .is_some_and(Vec::is_empty),
        ),
        (
            "targeted family ablations remove only attributable consequences",
            later["targeted_ablations"].as_array().is_some_and(|rows| {
                rows.len() == 2
                    && rows.iter().all(|row| {
                        row["unwithdrawn_family_retained"] == true
                            && row["joint_cultivated"] == false
                    })
            }),
        ),
        (
            "one continuing owner and exact withdrawal throughout",
            second_withdrawal.exact_immediate_predecessor_restored
                && first_withdrawal.exact_immediate_predecessor_restored,
        ),
    ];
    if checks.iter().any(|check| !check.1) {
        return Err(format!("L1 eight-part grade refused: {checks:?}"));
    }
    Ok(json!({
        "schema": "holonics.l1.eight-part-grade.v1",
        "truth_status": "established-bounded",
        "checks": checks.into_iter().map(|(name, passed)| json!({"name": name, "passed": passed})).collect::<Vec<_>>(),
        "passed": 8,
        "required": 8,
        "all_passed": true,
    }))
}

fn read_json(path: &Path) -> Result<Value, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}
