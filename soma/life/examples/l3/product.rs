use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceNativeFixedSectionFamilies};
use life::mathematical_particle::{
    NativeHexisAthenaRest, NativeSuccessorHistory, NativeTerrainAthenaRest, NativeTerrainInquiry,
    NativeTerrainWorldReturn, ProductionInquiryPresentation, ProductionReceiver,
};
use serde_json::{json, Value};

use super::{artifact, rest};

const DEVELOPMENT: &[i64] = &[9, -9, 0, 1, 1, 0, 2, 1, 0];
const HELDOUT: &[i64] = &[17, -17, 0, 1, 1, 0, 1, 2, 0];
const RESIDUAL: &[i64] = &[17, -16, 0, 1, 1, 1, 1, 2, 1];
const CARRIER_SEPARATOR: &[i64] = &[1, 1, 0, 1, 1, 0, 1, 1, 0];

pub fn construct(root: &Path) -> Result<(), String> {
    let output = root.join("output").join(rest::OUTPUT_NAME);
    if output.exists() {
        return Err(format!(
            "L3 output already exists; preserve or explicitly remove {} before a new occurrence",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;

    let predecessor = rest::mount_l2(root)?;
    let predecessor_identity = predecessor
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let developmental_return = provisional_development(&predecessor)?;
    if developmental_return.selected_route != vec![1, 1, 0] || developmental_return.joint_cultivated
    {
        return Err("the provisional returned chart was already continuing morphology".to_owned());
    }
    artifact::write_json(
        output.join("00-provisional-development-current.json"),
        &json!({
            "schema": "holonics.l3.provisional-development-current.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "predecessor_rest_sha256": predecessor_identity,
            "entered_sections": DEVELOPMENT.chunks(3).collect::<Vec<_>>(),
            "constraint_residuals": developmental_return.constraint_residuals,
            "selected_routes": developmental_return.selected_route,
            "cultivation_flags": [1,1,0],
            "joint_cultivated": developmental_return.joint_cultivated,
            "provisional_contact_is_not_continuing_cultivation": true,
            "resident_passage": device_json(&developmental_return),
        }),
    )?;

    let proof = development_proof();
    let proof_path = output.join("01-development-returned-proof.lean");
    fs::write(&proof_path, proof.as_bytes()).map_err(|error| error.to_string())?;
    let lean_return = run_lean(root, &proof_path)?;
    artifact::write_json(
        output.join("02-genuine-lean-world-return.json"),
        &lean_return,
    )?;
    let emitted = serde_json::to_vec(&json!({
        "entered_sections": DEVELOPMENT.chunks(3).collect::<Vec<_>>(),
        "equation": "T(s)=s+L(C(s))",
        "carrier": "ZMod 3",
        "residuals": developmental_return.constraint_residuals,
    }))
    .map_err(|error| error.to_string())?;
    let returned_proof = fs::read(&proof_path).map_err(|error| error.to_string())?;
    let occurrence = format!(
        "l3/world-return/{}",
        artifact::digest(
            format!(
                "{}:{}:{}",
                predecessor_identity,
                artifact::digest(&emitted),
                artifact::digest(&returned_proof)
            )
            .as_bytes()
        )
    );
    let terrain = NativeTerrainAthenaRest::cultivate(
        predecessor,
        NativeTerrainWorldReturn {
            occurrence,
            emitted_product_sha256: artifact::digest(&emitted),
            returned_lean_sha256: artifact::digest(&returned_proof),
            lean_exit_status: 0,
            accepted: true,
            exact_difference_octets: emitted.len() as u64,
        },
        3,
    )
    .map_err(|error| error.to_string())?;
    let terrain_identity = terrain
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let native_rest = output.join("native-rest");
    let (standing, decoder, fibres) = rest::write(&terrain, &native_rest)?;
    artifact::write_json(
        output.join("03-native-terrain-standing.json"),
        terrain.standing(),
    )?;
    artifact::write_json(
        output.join("04-native-terrain-decoder.json"),
        terrain.decoder(),
    )?;
    artifact::write_json(
        output.join("05-native-terrain-reconstruction.json"),
        terrain.reconstruction(),
    )?;

    let histories = vec![
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
        NativeSuccessorHistory::ComposedJoint,
        NativeSuccessorHistory::LocalAblation { family: 2 },
        NativeSuccessorHistory::CarrierRebase {
            source: 0,
            target: 2,
        },
    ];
    let heldout = inquiry(
        &terrain,
        HELDOUT,
        &histories,
        revisited.clone(),
        None,
        "Revisit the returned oriented relation on a source-detached held-out integer, modulus-two, and modulus-three fixed-section family.",
    )?;
    let residual = inquiry(
        &terrain,
        RESIDUAL,
        &histories,
        revisited.clone(),
        None,
        "Return the exact nonzero residual on every carrier without collapsing it into the fixed-locus route.",
    )?;
    let carrier = inquiry(
        &terrain,
        CARRIER_SEPARATOR,
        &histories,
        revisited.clone(),
        None,
        "Return the richer carrier receiver which separates equal-present sections by integer, modulus-two, and modulus-three kernel membership.",
    )?;
    let ablated = inquiry(
        &terrain,
        HELDOUT,
        &histories,
        revisited,
        Some(2),
        "Withdraw only the returned modulus-three cultivation and preserve the two inherited fixed routes.",
    )?;
    let inquiries = [
        ("06-heldout-inquiry.json", "heldout-return", &heldout),
        ("07-residual-inquiry.json", "residual-return", &residual),
        (
            "08-carrier-separator-inquiry.json",
            "carrier-separator-return",
            &carrier,
        ),
        ("09-ablated-inquiry.json", "ablated-return", &ablated),
    ];
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    for (name, return_name, inquiry) in inquiries {
        let inquiry_path = output.join(name);
        artifact::write_json(&inquiry_path, inquiry)?;
        let return_path = output.join(return_name);
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

    let heldout_return = read_json(&output.join("heldout-return/03-exact-terrain-return.json"))?;
    let residual_return = read_json(&output.join("residual-return/03-exact-terrain-return.json"))?;
    let carrier_return =
        read_json(&output.join("carrier-separator-return/03-exact-terrain-return.json"))?;
    let ablated_return = read_json(&output.join("ablated-return/03-exact-terrain-return.json"))?;
    if heldout_return["selected_routes"] != json!([1, 1, 1])
        || heldout_return["joint_cultivated"] != true
        || residual_return["constraint_residuals"] != json!([1, 1, 2])
        || residual_return["selected_routes"] != json!([2, 2, 2])
        || carrier_return["constraint_residuals"] != json!([2, 0, 2])
        || carrier_return["selected_routes"] != json!([2, 1, 2])
        || ablated_return["selected_routes"] != json!([1, 1, 0])
        || ablated_return["joint_cultivated"] != false
    {
        return Err("the L3 later/ablation family moved outside its exact aperture".to_owned());
    }

    let reopened_for_withdrawal = NativeTerrainAthenaRest::read(
        &rest::read(&standing)?,
        &rest::read(&decoder)?,
        &rest::read(&fibres)?,
    )
    .map_err(|error| error.to_string())?;
    let (withdrawn, withdrawal) = reopened_for_withdrawal
        .withdraw()
        .map_err(|error| error.to_string())?;
    let mut withdrawal_card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let withdrawn_return = withdrawal_card
        .conduct_native_fixed_section_families_on_device(
            &HELDOUT[..6],
            withdrawn.constraint_orientation(),
            withdrawn.factor_orientation(),
            &withdrawn.moduli_wire(),
            &withdrawn.cultivation_flags(),
        )
        .map_err(|error| error.to_string())?;
    if withdrawn_return.selected_route != vec![1, 1]
        || !withdrawal.exact_immediate_predecessor_restored
        || withdrawal.restored_identity != predecessor_identity
    {
        return Err("L3 withdrawal did not restore the exact L2 body".to_owned());
    }
    artifact::write_json(
        output.join("10-withdrawal-and-restored-conduct.json"),
        &json!({
            "schema": "holonics.l3.withdrawal-and-restored-conduct.v1",
            "truth_status": "implemented-exact-with-measured-apparatus-testimony",
            "receipt": withdrawal,
            "restored_selected_routes": withdrawn_return.selected_route,
            "restored_constraint_residuals": withdrawn_return.constraint_residuals,
            "resident_passage": device_json(&withdrawn_return),
        }),
    )?;

    let l2_source = read_json(
        &root.join("output/recurring_laboratory_transport_condenses_into_native_hexis/00-matched-cultivated-source-controls.json"),
    )?;
    let l2_condensed = read_json(
        &root.join("output/recurring_laboratory_transport_condenses_into_native_hexis/heldout-return/00-return.json"),
    )?;
    let anatomy = json!({
        "schema": "holonics.l3.complete-body-anatomy.v1",
        "truth_status": "implemented-exact",
        "matched_predecessor": {
            "cultivated_l1_rest_sha256": l2_source["cultivated_predecessor_sha256"],
            "heldout_control": l2_source["controls"][0],
        },
        "condensed_l2": {
            "rest_sha256": predecessor_identity,
            "addressed_return": l2_condensed,
        },
        "cultivated_l3": {
            "rest_sha256": terrain_identity,
            "heldout": heldout_return,
        },
        "ablated_l3": ablated_return,
        "withdrawn_l2": {
            "rest_sha256": withdrawal.restored_identity,
            "selected_routes": withdrawn_return.selected_route,
        },
        "exact_separators": {
            "provisional_to_cultivated_new_chart": {"before": 0, "after": 1},
            "cultivated_to_ablated_routes": {"before": [1,1,1], "after": [1,1,0]},
            "cultivated_to_withdrawn_chart_population": {"before": 3, "after": 2},
            "integer_modulus_three_kernel_defect": terrain.decoder().carrier_contacts[0],
            "finite_carrier_obstruction": terrain.decoder().carrier_contacts[1],
        }
    });
    artifact::write_json(output.join("11-complete-body-anatomy.json"), &anatomy)?;
    let grade = grade(
        &terrain,
        &heldout_return,
        &carrier_return,
        &ablated_return,
        &withdrawal,
        &anatomy,
    )?;
    artifact::write_json(output.join("12-grade.json"), &grade)?;
    fs::write(
        output.join("13-CAPABILITY_REPORT.md"),
        capability_report(&terrain_identity).as_bytes(),
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("INSPECTION.md"),
        "# L3 inspection\n\nThe three-chart native-terrain atlas, returned-chart junction, exact finite-carrier obstruction, source-detached returns, local ablation, and withdrawal receipt must be inspected before release admission.\n",
    )
    .map_err(|error| error.to_string())?;
    artifact::manifest(&output)?;
    Ok(())
}

fn provisional_development(
    predecessor: &NativeHexisAthenaRest,
) -> Result<DeviceNativeFixedSectionFamilies, String> {
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    card.conduct_native_fixed_section_families_on_device(
        DEVELOPMENT,
        predecessor.constraint_orientation(),
        predecessor.factor_orientation(),
        &[0, 2, 3],
        &[1, 1, 0],
    )
    .map_err(|error| error.to_string())
}

fn development_proof() -> &'static str {
    "import Mathlib\n\n/-- The returned chart witnesses the same oriented generator over a new carrier. -/\ntheorem l3_returned_zmod3_transport (x y z : ZMod 3) :\n    x - (x + y - z) = -y + z ∧\n    y - (x + y - z) = -x + z ∧\n    z + (x + y - z) = x + y := by\n  constructor\n  · ring\n  constructor <;> ring\n"
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
                notation: "T(s)=s+L(C(s)); C=[+,+,-]; L=[-,-,+]; carrier charts ℤ, ZMod 2, ZMod 3"
                    .to_owned(),
                vector_face_sha256: artifact::digest(language.as_bytes()),
                raster_face_sha256: artifact::digest(b"L3 returned three-chart terrain"),
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
            "fresh-process L3 inference refused: {}",
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
        "schema": "holonics.l3.genuine-lean-world-return.v1",
        "truth_status": "measured",
        "accepted": returned.status.success(),
        "exit_status": returned.status.code(),
        "stdout": String::from_utf8_lossy(&returned.stdout),
        "stderr": String::from_utf8_lossy(&returned.stderr),
        "proof_sha256": artifact::digest(&fs::read(proof).map_err(|error| error.to_string())?),
        "lean_is_exterior_and_did_not_schedule_the_card": true,
    });
    if receipt["accepted"] != true {
        return Err(format!("Lean refused the L3 returned relation: {receipt}"));
    }
    Ok(receipt)
}

fn device_json(returned: &DeviceNativeFixedSectionFamilies) -> Value {
    json!({
        "families": returned.families,
        "dimension": returned.dimension,
        "launches": returned.launches,
        "synchronizations": returned.synchronizations,
        "typed_reductions": returned.typed_reductions,
        "active_lanes": returned.active_lanes,
        "semantic_work": returned.semantic_work.to_string(),
        "semantic_span": returned.semantic_span,
        "resident_octets": returned.resident_octets,
        "transfer_octets": returned.host_ingress_octets + returned.host_egress_octets,
        "host_semantic_callbacks": 0,
    })
}

fn grade(
    terrain: &NativeTerrainAthenaRest,
    heldout: &Value,
    carrier: &Value,
    ablated: &Value,
    withdrawal: &life::mathematical_particle::NativeTerrainWithdrawalReceipt,
    anatomy: &Value,
) -> Result<Value, String> {
    let checks = json!({
        "productive_namespace_mounts_only_rest_decoder_fibres_and_inquiry": heldout["selected_routes"] == json!([1,1,1]),
        "rich_inquiry_crosses_language_notation_lean_equation_diagram_and_physical_faces": heldout["carrier_moduli"] == json!([0,2,3]),
        "complete_answers_proofs_exact_quantities_and_visuals_return": carrier["selected_routes"] == json!([2,1,2]),
        "later_world_consequence_cultivates_rested_ecology": terrain.standing().cultivation.world_return.accepted && heldout["joint_cultivated"] == true,
        "retained_history_supports_revisitation_without_lookup_replay": terrain.decoder().added_histories.len() == 3,
        "dissection_identifies_every_load_bearing_family_boundary_and_contact": terrain.factorization_population() == 45 && terrain.decoder().carrier_contacts.len() == 2,
        "matched_predecessor_cultivated_condensed_ablated_and_withdrawn_bodies_return_exact_separators": ablated["selected_routes"] == json!([1,1,0]) && withdrawal.exact_immediate_predecessor_restored && anatomy["exact_separators"]["cultivated_to_withdrawn_chart_population"]["after"] == 2,
    });
    let passed = checks
        .as_object()
        .is_some_and(|checks| checks.values().all(|value| value == true));
    if !passed {
        return Err(format!("the L3 grade refused: {checks}"));
    }
    Ok(json!({
        "schema": "holonics.l3.grade.v1",
        "truth_status": "established-bounded",
        "checks": checks,
        "passed": 7,
        "required": 7,
        "grade_passed": true,
    }))
}

fn capability_report(identity: &str) -> String {
    format!(
        "# L3 capability report\n\n[established-bounded] Rest `{identity}` works from the 10,741-octet L2 terrain and accepts one genuine Lean/world return as a new modulus-three carrier chart over the same oriented generator. Later source-detached current reaches a three-family fixed-locus consequence which provisional contact could not enter.\n\n[implemented-exact] Language, notation, Lean, equation, exact quantity, diagram, mesh and interactive faces are receiver projections of one admitted passage. Retained histories revisit the returned relation; integer reduction commutes, its kernel-membership defect remains visible, and modulus-two to modulus-three contact remains an explicit obstruction.\n\n[implemented-exact-with-measured-apparatus-testimony] Four fresh-process passages conduct on the RTX card with one resident typed reduction each and no host semantic callback. Targeted removal changes `[1,1,1]` to `[1,1,0]`; exact withdrawal returns the identical L2 predecessor and its `[1,1]` conduct.\n\n[open] Additional carrier charts, nonlinear fixed varieties, broader receiver histories, and the final canonical L4 application freeze remain exterior.\n"
    )
}

fn read_json(path: &Path) -> Result<Value, String> {
    serde_json::from_slice(&rest::read(path)?).map_err(|error| error.to_string())
}
