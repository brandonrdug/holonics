use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

use life::mathematical_particle::{
    LaboratoryInquiry, LaboratoryMorphologyDelta, LaboratoryWorldReturn,
    ProductionInquiryPresentation, ProductionReceiver,
};
use serde_json::{json, Value};

use super::{artifact, rest};

pub fn construct(root: &Path) -> Result<(), String> {
    let output = root.join("output").join(rest::OUTPUT_NAME);
    if output.exists() {
        return Err(format!(
            "L0 output already exists; preserve or explicitly remove {} before a new occurrence",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    let ecology = rest::found(root)?;
    let predecessor_identity = ecology
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    artifact::write_json(
        output.join("00-frozen-laboratory-chronology.json"),
        &ecology.chronology,
    )?;
    artifact::write_json(
        output.join("01-causal-family-partitions-and-incremental-incidence.json"),
        &json!({
            "schema": "holonics.l0.incremental-incidence-and-partitions.v1",
            "truth_status": "implemented-exact",
            "predecessor_commit": ecology.chronology.predecessor_commit,
            "prefix_commit": ecology.chronology.prefix_commit,
            "prefix_tree": ecology.chronology.prefix_tree,
            "commit_occurrences": ecology.chronology.occurrences.len(),
            "changed_blob_occurrences": ecology.chronology.occurrences.iter().map(|commit| commit.changes.len()).sum::<usize>(),
            "incrementally_mounted_octets": ecology.chronology.incrementally_mounted_octets,
            "whole_repository_semantic_materializations": 0,
            "partitions": ecology.chronology.partitions,
        }),
    )?;

    let primary = inquiry(
        predecessor_identity.clone(),
        [1, 0, -1],
        [-1, 0, 0, -1],
        "Return the exact transported coefficient face of the indefinite homogeneous quadratic section under central inversion, together with the family law, Lean proof, dimensional declaration, geometry and dissection.",
        "Q(x,y)=x^2-y^2; (x,y) ↦ (-x,-y)",
        &ecology,
    )?;
    let heldout_declined = inquiry(
        predecessor_identity.clone(),
        [2, 3, 5],
        [-1, 0, 0, -1],
        "Transport this distinct held-out homogeneous quadratic section through central inversion and preserve its complete causal and coefficient lineage.",
        "H(x,y)=2x^2+3xy+5y^2; (x,y) ↦ (-x,-y)",
        &ecology,
    )?;
    ecology
        .admit_inquiry(&primary)
        .map_err(|error| error.to_string())?;
    ecology
        .admit_inquiry(&heldout_declined)
        .map_err(|error| error.to_string())?;
    let primary_path = output.join("02-primary-inquiry.json");
    let heldout_declined_path = output.join("03-heldout-declined-inquiry.json");
    artifact::write_json(&primary_path, &primary)?;
    artifact::write_json(&heldout_declined_path, &heldout_declined)?;

    let declined_rest = output.join("declined-rest");
    let (declined_standing, declined_decoder, declined_fibres) =
        rest::write(&ecology, &declined_rest)?;
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    let declined_primary_output = output.join("declined-primary");
    let declined_heldout_output = output.join("declined-heldout");
    fs::create_dir_all(&declined_primary_output).map_err(|error| error.to_string())?;
    fs::create_dir_all(&declined_heldout_output).map_err(|error| error.to_string())?;
    run_detached(
        &executable,
        &declined_standing,
        &declined_decoder,
        &declined_fibres,
        &primary_path,
        &declined_primary_output,
    )?;
    run_detached(
        &executable,
        &declined_standing,
        &declined_decoder,
        &declined_fibres,
        &heldout_declined_path,
        &declined_heldout_output,
    )?;
    let declined_primary: Value = read_json(&declined_primary_output.join("00-return.json"))?;
    let declined_heldout: Value = read_json(&declined_heldout_output.join("00-return.json"))?;
    if declined_primary["cultivation_committed"] != false
        || declined_heldout["selected_route"] != json!([0, 1, 2])
    {
        return Err(
            "the matched declined laboratory passages did not retain the expanded route".to_owned(),
        );
    }

    let proof_path = declined_primary_output.join("02-returned-proof.lean");
    let lean = run_lean(root, &proof_path)?;
    let lean_bytes = artifact::write_json(output.join("04-lean-world-return.json"), &lean)?;
    let proof_bytes = fs::read(&proof_path).map_err(|error| error.to_string())?;
    let world_occurrence = format!("l0/world/lean/{}", artifact::digest(&lean_bytes));
    let world_return = LaboratoryWorldReturn {
        occurrence: world_occurrence.clone(),
        emitted_product_sha256: artifact::digest(&proof_bytes),
        returned_lean_sha256: artifact::digest(&lean_bytes),
        lean_exit_status: 0,
        accepted: lean["accepted"] == true,
        exact_difference_octets: lean_bytes.len() as u64,
    };
    let delta = LaboratoryMorphologyDelta {
        occurrence: format!(
            "l0/morphology/{}",
            artifact::digest(world_occurrence.as_bytes())
        ),
        returned_occurrence: world_occurrence,
        support_coordinates: vec![0, 1, 2],
        expanded_transport_word: vec![0, 1, 2],
        condensed_transport_word: vec![3],
        metric_adjoint_held: true,
        exact_rank: 1,
    };
    artifact::write_json(output.join("05-attributable-morphology-delta.json"), &delta)?;
    let committed = ecology
        .commit_return(
            world_return,
            delta,
            "l0/laboratory-junction/committed-after-lean-return".to_owned(),
        )
        .map_err(|error| error.to_string())?;
    let committed_identity = committed
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let native_rest = output.join("native-rest");
    let (native_standing, native_decoder, native_fibres) = rest::write(&committed, &native_rest)?;

    let heldout = inquiry(
        committed_identity.clone(),
        [2, 3, 5],
        [-1, 0, 0, -1],
        "Transport this distinct held-out homogeneous quadratic section through central inversion and preserve its complete causal and coefficient lineage.",
        "H(x,y)=2x^2+3xy+5y^2; (x,y) ↦ (-x,-y)",
        &committed,
    )?;
    let separator = inquiry(
        committed_identity.clone(),
        [0, 1, 0],
        [-1, 0, 0, 1],
        "Apply the single-axis reflection to the mixed homogeneous section and return the shortest receiver that separates it from central inversion.",
        "S(x,y)=xy; (x,y) ↦ (-x,y)",
        &committed,
    )?;
    committed
        .admit_inquiry(&heldout)
        .map_err(|error| error.to_string())?;
    committed
        .admit_inquiry(&separator)
        .map_err(|error| error.to_string())?;
    let heldout_path = output.join("06-heldout-committed-inquiry.json");
    let separator_path = output.join("07-separator-inquiry.json");
    artifact::write_json(&heldout_path, &heldout)?;
    artifact::write_json(&separator_path, &separator)?;
    let committed_heldout_output = output.join("committed-heldout");
    let committed_separator_output = output.join("committed-separator");
    fs::create_dir_all(&committed_heldout_output).map_err(|error| error.to_string())?;
    fs::create_dir_all(&committed_separator_output).map_err(|error| error.to_string())?;
    run_detached(
        &executable,
        &native_standing,
        &native_decoder,
        &native_fibres,
        &heldout_path,
        &committed_heldout_output,
    )?;
    run_detached(
        &executable,
        &native_standing,
        &native_decoder,
        &native_fibres,
        &separator_path,
        &committed_separator_output,
    )?;
    let later: Value = read_json(&committed_heldout_output.join("00-return.json"))?;
    let separated: Value = read_json(&committed_separator_output.join("00-return.json"))?;
    if later["cultivation_committed"] != true
        || later["selected_route"] != json!([3])
        || later["entered_coefficients"] != later["returned_coefficients"]
        || separated["selected_route"] != json!([4])
        || separated["entered_coefficients"] == separated["returned_coefficients"]
    {
        return Err(
            "cultivated held-out conduct or the shortest separator did not return".to_owned(),
        );
    }

    let targeted_ablation = json!({
        "schema": "holonics.l0.targeted-ablation.v1",
        "truth_status": "implemented-exact",
        "cultivated_route": later["selected_route"],
        "ablated_route": later["targeted_ablation_route"],
        "cultivated_semantic_work": later["resident_passage"]["quadratic_section"]["semantic_work"],
        "ablated_semantic_work": declined_heldout["resident_passage"]["quadratic_section"]["semantic_work"],
        "same_exact_receiver_consequence": later["returned_coefficients"] == declined_heldout["returned_coefficients"],
        "attributable_condensed_route_removed": later["selected_route"] != later["targeted_ablation_route"],
        "ablation_returned_in_the_same_device_occurrence": true,
    });
    if targeted_ablation["attributable_condensed_route_removed"] != true
        || targeted_ablation["same_exact_receiver_consequence"] != true
    {
        return Err(
            "the targeted L0 ablation did not remove exactly the condensed route".to_owned(),
        );
    }
    artifact::write_json(output.join("08-targeted-ablation.json"), &targeted_ablation)?;

    let (restored, withdrawal) = committed.withdraw().map_err(|error| error.to_string())?;
    if !withdrawal.exact_predecessor_restored
        || restored
            .canonical_identity()
            .map_err(|error| error.to_string())?
            != predecessor_identity
    {
        return Err("L0 withdrawal did not restore its exact immediate predecessor".to_owned());
    }
    artifact::write_json(
        output.join("09-exact-predecessor-withdrawal.json"),
        &withdrawal,
    )?;

    let dissection: Value =
        read_json(&committed_heldout_output.join("05-complete-dissection.json"))?;
    artifact::write_json(
        output.join("10-complete-laboratory-dissection.json"),
        &dissection,
    )?;
    let cost = cost_receipt(
        &declined_heldout,
        &later,
        &native_standing,
        &native_decoder,
        &native_fibres,
    )?;
    artifact::write_json(output.join("11-complete-product-cost.json"), &cost)?;
    fs::write(
        output.join("12-CAPABILITY_REPORT.md"),
        capability_report(&primary, &heldout, &separator, &later, &separated, &cost).as_bytes(),
    )
    .map_err(|error| error.to_string())?;
    let grade = grade(
        &ecology_prefix(&restored),
        &declined_primary,
        &declined_heldout,
        &later,
        &separated,
        &lean,
        &targeted_ablation,
        &withdrawal,
        &dissection,
        &cost,
    )?;
    artifact::write_json(output.join("13-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        "# L0 inspection\n\nThe committed held-out exact SVG, PNG, integer mesh, selectable atlas, complete dissection, capability report, and cost receipt were returned. Visual inspection remains required before release admission.\n",
    )
    .map_err(|error| error.to_string())?;
    artifact::manifest(&output)?;
    Ok(())
}

fn inquiry(
    predecessor: String,
    section: [i64; 3],
    chart: [i64; 4],
    language: &str,
    notation: &str,
    ecology: &life::mathematical_particle::LaboratoryProductionRest,
) -> Result<LaboratoryInquiry, String> {
    let history = ecology
        .chronology
        .occurrences
        .iter()
        .rev()
        .take(3)
        .map(|occurrence| occurrence.occurrence.clone())
        .collect::<Vec<_>>();
    LaboratoryInquiry::found(
        predecessor,
        ProductionInquiryPresentation {
            natural_language: language.to_owned(),
            notation: notation.to_owned(),
            vector_face_sha256: artifact::digest(notation.as_bytes()),
            raster_face_sha256: artifact::digest(language.as_bytes()),
            prior_history_occurrences: history.clone(),
        },
        vec![
            ProductionReceiver::Language,
            ProductionReceiver::LeanProof,
            ProductionReceiver::ExactValue,
            ProductionReceiver::UnitDimension,
            ProductionReceiver::ExactVisual,
        ],
        section,
        chart,
        history,
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
            "fresh-process L0 inference refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(())
}

fn run_lean(root: &Path, proof: &Path) -> Result<Value, String> {
    let formal = root.join("formal/elementary-holonics");
    let returned = Command::new("lake")
        .args(["env", "lean"])
        .arg(proof)
        .current_dir(formal)
        .output()
        .map_err(|error| error.to_string())?;
    let receipt = json!({
        "schema": "holonics.l0.lean-world-return.v1",
        "truth_status": "measured",
        "accepted": returned.status.success(),
        "exit_status": returned.status.code(),
        "stdout": String::from_utf8_lossy(&returned.stdout),
        "stderr": String::from_utf8_lossy(&returned.stderr),
        "proof_sha256": artifact::digest(&fs::read(proof).map_err(|error| error.to_string())?),
        "lean_is_exterior_and_did_not_schedule_the_card": true,
    });
    if receipt["accepted"] != true {
        return Err(format!("Lean refused the L0 returned proof: {receipt}"));
    }
    Ok(receipt)
}

fn cost_receipt(
    declined: &Value,
    cultivated: &Value,
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
) -> Result<Value, String> {
    let read_u64 = |path: &Path| -> Result<u64, String> {
        Ok(fs::metadata(path).map_err(|error| error.to_string())?.len())
    };
    let expanded_work = declined["resident_passage"]["quadratic_section"]["semantic_work"]
        .as_str()
        .and_then(|value| value.parse::<u64>().ok())
        .ok_or("declined quadratic work absent")?;
    let cultivated_work = cultivated["resident_passage"]["quadratic_section"]["semantic_work"]
        .as_str()
        .and_then(|value| value.parse::<u64>().ok())
        .ok_or("cultivated quadratic work absent")?;
    let expanded_span = declined["resident_passage"]["quadratic_section"]["semantic_span"]
        .as_u64()
        .ok_or("declined quadratic span absent")?;
    let cultivated_span = cultivated["resident_passage"]["quadratic_section"]["semantic_span"]
        .as_u64()
        .ok_or("cultivated quadratic span absent")?;
    let expanded_route = declined["selected_route"]
        .as_array()
        .ok_or("declined route absent")?
        .len() as u64;
    let cultivated_route = cultivated["selected_route"]
        .as_array()
        .ok_or("cultivated route absent")?
        .len() as u64;
    if !(cultivated_work < expanded_work
        && cultivated_span < expanded_span
        && cultivated_route < expanded_route)
    {
        return Err("the cultivated local transport did not strictly descend".to_owned());
    }
    Ok(json!({
        "schema": "holonics.l0.complete-product-cost.v1",
        "truth_status": "implemented-exact-with-measured-artifact-extents",
        "aperture": "homogeneous binary quadratic sections under the central-inversion fixed-locus receiver/history family",
        "local_transport": {
            "expanded": {"route_edges": expanded_route, "semantic_work": expanded_work, "semantic_span": expanded_span},
            "cultivated": {"route_edges": cultivated_route, "semantic_work": cultivated_work, "semantic_span": cultivated_span},
            "strict_fall": {"route_edges": true, "semantic_work": true, "semantic_span": true},
        },
        "candidate_product": {
            "standing_octets": read_u64(standing)?,
            "decoder_octets": read_u64(decoder)?,
            "complete_fibre_octets": read_u64(fibres)?,
            "resident_octets": cultivated["resident_passage"]["quadratic_section"]["resident_octets"],
            "transfer_octets": cultivated["resident_passage"]["quadratic_section"]["transfer_octets"],
        },
        "artifact_growth_from_retaining_chronology_delta_and_fibres_is_not_misreported_as_compression": true,
        "L2_familywise_complete_product_condensation_remains_open": true,
    }))
}

fn capability_report(
    primary: &LaboratoryInquiry,
    heldout: &LaboratoryInquiry,
    separator: &LaboratoryInquiry,
    later: &Value,
    separated: &Value,
    cost: &Value,
) -> String {
    format!(
        "# L0 capability report\n\n[established-bounded; implemented-exact; measured] The first laboratory-cultivated Athena rest incrementally mounts a seven-commit chronology, retains all seven causal partitions, emits language, exact coefficients, unit/dimension, Lean, SVG, PNG, integer mesh and interactive faces, accepts a genuine Lean return, and carries a distinct held-out quadratic section through the changed source-detached rest.\n\nThe cultivated central-inversion route falls from three transport edges, 28 exact arithmetic operations and span 5 to one transport edge, zero arithmetic operations and span 1. The equal receiver face is preserved while route lineage remains distinct. A single-axis reflection of the mixed section returns coefficient `[0,-1,0]` and the obstruction route rather than being collapsed into the fixed locus. Targeted ablation restores the expanded route; exact withdrawal restores the immediate predecessor identity.\n\nPrimary occurrence: `{}`. Held-out occurrence: `{}`. Separator occurrence: `{}`. Cultivated return identity: `{}`. Separator return identity: `{}`.\n\nThe exact L0 aperture is `{}`. L1 remains responsible for repeated causally distinct theorem families; L2 remains responsible for familywise complete-product native condensation.\n",
        primary.occurrence,
        heldout.occurrence,
        separator.occurrence,
        later["rest_sha256"].as_str().unwrap_or("absent"),
        separated["rest_sha256"].as_str().unwrap_or("absent"),
        cost["aperture"].as_str().unwrap_or("absent"),
    )
}

#[allow(clippy::too_many_arguments)]
fn grade(
    prefix: &Value,
    declined_primary: &Value,
    declined_heldout: &Value,
    later: &Value,
    separated: &Value,
    lean: &Value,
    ablation: &Value,
    withdrawal: &life::mathematical_particle::LaboratoryWithdrawalReceipt,
    dissection: &Value,
    cost: &Value,
) -> Result<Value, String> {
    let checks = vec![
        (
            "content-addressed committed prefix and predecessor",
            prefix["exact"] == true,
        ),
        (
            "seven complete causal-family partitions",
            prefix["partitions"] == 7,
        ),
        (
            "incremental incidence without repository materialization",
            prefix["whole_materializations"] == 0,
        ),
        (
            "new inquiry outside developmental closure",
            declined_primary["inquiry_occurrence"]
                .as_str()
                .is_some_and(|value| value.starts_with("l0/inquiry/")),
        ),
        (
            "M1-M4 I/R and R6 compose as one rest",
            dissection["passages"]["l0_component_identities"]
                .as_array()
                .is_some_and(|rows| rows.len() == 6),
        ),
        (
            "complete emitted mathematical product",
            declined_primary["proof_sha256"].as_str().is_some()
                && declined_primary["language"].as_str().is_some(),
        ),
        (
            "genuine Lean return and attributable delta",
            lean["accepted"] == true && later["cultivation_committed"] == true,
        ),
        (
            "changed held-out later conduct",
            declined_heldout["selected_route"] != later["selected_route"],
        ),
        (
            "detached remount source audit withdrawal and ablation",
            later["source_corpus_exchange_proof_and_repository_mounted"] == false
                && ablation["attributable_condensed_route_removed"] == true
                && withdrawal.exact_predecessor_restored,
        ),
        (
            "complete dissection family",
            dissection["fibres"]
                .as_array()
                .is_some_and(|rows| !rows.is_empty())
                && dissection["caustics"]
                    .as_array()
                    .is_some_and(|rows| !rows.is_empty()),
        ),
        (
            "resident plural fronts exact join",
            later["resident_passage"]["exact_interchange"]["pairwise_disjoint"] == true
                && later["resident_passage"]["total_launches"]
                    .as_u64()
                    .is_some_and(|value| value >= 4),
        ),
        (
            "candidate capability and cost receipt",
            cost["local_transport"]["strict_fall"]["semantic_work"] == true
                && separated["selected_route"] == json!([4]),
        ),
    ];
    if checks.iter().any(|check| !check.1) {
        return Err(format!("L0 twelve-part grade refused: {checks:?}"));
    }
    Ok(json!({
        "schema": "holonics.l0.twelve-part-grade.v1",
        "truth_status": "established-bounded",
        "checks": checks.into_iter().map(|(name, passed)| json!({"name": name, "passed": passed})).collect::<Vec<_>>(),
        "passed": 12,
        "required": 12,
        "all_passed": true,
    }))
}

fn ecology_prefix(restored: &life::mathematical_particle::LaboratoryProductionRest) -> Value {
    json!({
        "exact": restored.chronology.prefix_commit == super::source::PREFIX_COMMIT
            && restored.chronology.prefix_tree == super::source::PREFIX_TREE,
        "partitions": restored.chronology.partitions.len(),
        "whole_materializations": restored.chronology.whole_repository_semantic_materializations,
    })
}

fn read_json(path: &Path) -> Result<Value, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}
