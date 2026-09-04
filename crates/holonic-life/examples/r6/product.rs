use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

use life::mathematical_particle::{
    MathematicalMediaPort, ProductionInquiry, ProductionInquiryFace, ProductionInquiryPresentation,
    ProductionReceiver, ProductionWorldReturn,
};
use serde_json::{json, Value};

use super::{artifact, rest};

pub fn construct(root: &Path) -> Result<(), String> {
    let output = root.join("output").join(rest::OUTPUT_NAME);
    if output.exists() {
        return Err(format!(
            "R6 output already exists; preserve or explicitly remove {} before a new occurrence",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    let ecology = rest::found(root)?;
    let predecessor_identity = ecology
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let heldout = ecology.media.standing.heldout_family;
    let vector = ecology
        .media
        .reconstruct_interior(heldout, MathematicalMediaPort::Vector)
        .map_err(|error| error.to_string())?;
    let raster = ecology
        .media
        .reconstruct_interior(heldout, MathematicalMediaPort::RasterVision)
        .map_err(|error| error.to_string())?;
    let prior_history_occurrences = ecology
        .retained_boundary
        .decoder
        .interiors
        .iter()
        .rev()
        .take(3)
        .map(|interior| interior.occurrence.clone())
        .collect::<Vec<_>>();
    let inquiry = ProductionInquiry::found(
        predecessor_identity.clone(),
        ProductionInquiryPresentation {
            natural_language: "Across the held-out common-world mathematical page, return the exact oriented difference between four-connected and eight-connected raster correspondence populations; provide an explanation, proof, exact value, unit/dimension, and exact visual face."
                .to_owned(),
            notation: "N_{raster,4} - N_{raster,8}".to_owned(),
            vector_face_sha256: artifact::digest(vector),
            raster_face_sha256: artifact::digest(raster),
            prior_history_occurrences,
        },
        vec![0, 1, 1, 0],
        vec![
            ProductionReceiver::Language,
            ProductionReceiver::LeanProof,
            ProductionReceiver::ExactValue,
            ProductionReceiver::UnitDimension,
            ProductionReceiver::ExactVisual,
        ],
        ProductionInquiryFace {
            left_species: 2,
            right_species: 3,
            oriented_relation: "left-minus-right".to_owned(),
            carrier: "integer-incidence".to_owned(),
            unit: "dimensionless-correspondence".to_owned(),
            dimension: 0,
        },
        heldout,
    )
    .map_err(|error| error.to_string())?;
    ecology
        .admit_inquiry(&inquiry)
        .map_err(|error| error.to_string())?;
    let inquiry_path = output.join("inquiry.json");
    artifact::write_json(&inquiry_path, &inquiry)?;

    let decline_rest = output.join("matched-decline-rest");
    let (decline_standing, decline_decoder, decline_fibres) = rest::write(&ecology, &decline_rest)?;
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    let declined_output = output.join("declined-return");
    fs::create_dir_all(&declined_output).map_err(|error| error.to_string())?;
    run_detached(
        &executable,
        &decline_standing,
        &decline_decoder,
        &decline_fibres,
        &inquiry_path,
        &declined_output,
    )?;
    let declined: Value = read_json(&declined_output.join("00-return.json"))?;
    if declined["cultivation_committed"] != false
        || declined["source_corpus_exchange_and_development_proof_mounted"] != false
    {
        return Err("the fresh declined production return moved its boundary".to_owned());
    }

    let proof_path = declined_output.join("02-returned-proof.lean");
    let lean = run_lean(root, &proof_path)?;
    let lean_bytes = artifact::write_json(output.join("11-world-return.json"), &lean)?;
    let proof_bytes = fs::read(&proof_path).map_err(|error| error.to_string())?;
    let world_return = ProductionWorldReturn {
        occurrence: format!("r6/world/lean/{}", artifact::digest(&lean_bytes)),
        emitted_product_sha256: artifact::digest(&proof_bytes),
        returned_product_sha256: artifact::digest(&lean_bytes),
        receiver: "Lean 4 kernel through the Mathlib exterior environment".to_owned(),
        accepted: lean["accepted"] == true,
        exact_difference_octets: lean_bytes.len() as u64,
    };
    let committed = ecology
        .commit_return(
            world_return,
            "r6/production-junction/committed-after-lean-return".to_owned(),
        )
        .map_err(|error| error.to_string())?;
    let native_rest = output.join("native-rest");
    let (native_standing, native_decoder, native_fibres) = rest::write(&committed, &native_rest)?;
    let committed_output = output.join("committed-return");
    fs::create_dir_all(&committed_output).map_err(|error| error.to_string())?;
    run_detached(
        &executable,
        &native_standing,
        &native_decoder,
        &native_fibres,
        &inquiry_path,
        &committed_output,
    )?;
    let later: Value = read_json(&committed_output.join("00-return.json"))?;
    if later["cultivation_committed"] != true
        || later["language"] == declined["language"]
        || later["resident_passage"]["semantic_work"]
            != declined["resident_passage"]["semantic_work"]
    {
        return Err(
            "the returned world constraint did not change attributable later conduct".to_owned(),
        );
    }

    let committed_identity = committed
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let (restored, withdrawal) = committed.withdraw().map_err(|error| error.to_string())?;
    if restored
        .canonical_identity()
        .map_err(|error| error.to_string())?
        != predecessor_identity
        || !withdrawal.exact_predecessor_restored
    {
        return Err("targeted R6 withdrawal did not restore the exact decline rest".to_owned());
    }
    artifact::write_json(output.join("12-targeted-withdrawal.json"), &withdrawal)?;

    let cost = complete_cost(
        root,
        &native_standing,
        &native_decoder,
        &native_fibres,
        &later,
    )?;
    artifact::write_json(output.join("13-complete-product-descent.json"), &cost)?;
    let capability = capability_report(&inquiry, &declined, &later, committed_identity, &cost);
    fs::write(
        output.join("14-CAPABILITY_REPORT.md"),
        capability.as_bytes(),
    )
    .map_err(|error| error.to_string())?;
    let grade = grade(
        &declined,
        &later,
        &lean,
        &withdrawal,
        &cost,
        &committed_output,
    )?;
    artifact::write_json(output.join("15-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        "# R6 inspection\n\nThe exact raster was decoded and recounted by the driver. External visual inspection of `committed-return/08-exact-difference.png`, the selectable HTML atlas, and the capability report remains to be recorded before release admission.\n",
    )
    .map_err(|error| error.to_string())?;
    artifact::manifest(&output)?;
    Ok(())
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
            "fresh-process production inference refused: {}",
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
        "schema": "holonics.r6.lean-world-return.v1",
        "truth_status": "measured",
        "accepted": returned.status.success(),
        "exit_status": returned.status.code(),
        "stdout": String::from_utf8_lossy(&returned.stdout),
        "stderr": String::from_utf8_lossy(&returned.stderr),
        "proof_sha256": artifact::digest(&fs::read(proof).map_err(|error| error.to_string())?),
        "lean_is_exterior_and_did_not_schedule_the_card": true,
    });
    if receipt["accepted"] != true {
        return Err(format!("Lean refused the R6 returned proof: {receipt}"));
    }
    Ok(receipt)
}

fn complete_cost(
    root: &Path,
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
    later: &Value,
) -> Result<Value, String> {
    let i5: Value = read_json(&root.join(
        ".local/artifacts/the_athena_gemma_ecology_infers_returns_and_remounts/01-complete-product-cost.json",
    ))?;
    let r4: Value = read_json(&root.join(
        ".local/artifacts/the_retained_causal_boundary_carries_the_long_horizon_inquiry/10-complete-product-descent.json",
    ))?;
    let r5: Value = read_json(&root.join(
        ".local/artifacts/the_mathematical_and_physical_faces_share_native_transport/06-complete-product-descent.json",
    ))?;
    let r5_source = |name: &str| -> Result<u64, String> {
        r5["coordinates"]
            .as_array()
            .and_then(|rows| rows.iter().find(|row| row["coordinate"] == name))
            .and_then(|row| row["source"].as_u64())
            .ok_or_else(|| format!("R5 source coordinate {name} absent"))
    };
    let source = [
        i5["source"]["artifact_octets"]
            .as_u64()
            .ok_or("I5 artifact cost")?
            + r4["source_complete_replay"]["artifact_octets"]
                .as_u64()
                .ok_or("R4 artifact cost")?
            + r5_source("artifact_octets")?,
        i5["source"]["decoder_octets"]
            .as_u64()
            .ok_or("I5 decoder cost")?
            + r4["source_complete_replay"]["decoder_octets"]
                .as_u64()
                .ok_or("R4 decoder cost")?
            + r5_source("decoder_octets")?,
        i5["source"]["fibre_octets"]
            .as_u64()
            .ok_or("I5 fibre cost")?
            + r4["source_complete_replay"]["fibre_octets"]
                .as_u64()
                .ok_or("R4 fibre cost")?
            + r5_source("fibre_octets")?,
        i5["source"]["semantic_work"]
            .as_u64()
            .ok_or("I5 work cost")?
            + r4["source_complete_replay"]["semantic_work"]
                .as_u64()
                .ok_or("R4 work cost")?
            + r5_source("semantic_work")?,
        i5["source"]["dependency_span"]
            .as_u64()
            .ok_or("I5 span cost")?
            + r4["source_complete_replay"]["dependency_span"]
                .as_u64()
                .ok_or("R4 span cost")?
            + r5_source("semantic_span")?,
        i5["source"]["resident_octets"]
            .as_u64()
            .ok_or("I5 resident cost")?
            + r4["source_complete_replay"]["resident_octets"]
                .as_u64()
                .ok_or("R4 resident cost")?
            + r5_source("resident_octets")?,
        i5["source"]["transfer_octets"]
            .as_u64()
            .ok_or("I5 transfer cost")?
            + r4["source_complete_replay"]["transfer_octets"]
                .as_u64()
                .ok_or("R4 transfer cost")?
            + r5_source("transfer_octets")?,
    ];
    let passage = &later["resident_passage"];
    let native = [
        fs::metadata(standing)
            .map_err(|error| error.to_string())?
            .len(),
        fs::metadata(decoder)
            .map_err(|error| error.to_string())?
            .len(),
        fs::metadata(fibres)
            .map_err(|error| error.to_string())?
            .len(),
        passage["semantic_work"]
            .as_str()
            .ok_or("native semantic work absent")?
            .parse::<u64>()
            .map_err(|error| error.to_string())?,
        passage["semantic_span"]
            .as_u64()
            .ok_or("native span absent")?,
        passage["resident_octets"]
            .as_u64()
            .ok_or("native resident absent")?,
        passage["host_ingress_octets"]
            .as_u64()
            .ok_or("native ingress absent")?
            + passage["host_egress_octets"]
                .as_u64()
                .ok_or("native egress absent")?,
    ];
    let names = [
        "artifact_octets",
        "decoder_octets",
        "fibre_octets",
        "semantic_work",
        "semantic_span",
        "resident_octets",
        "transfer_octets",
    ];
    let coordinates = names
        .iter()
        .enumerate()
        .map(|(at, name)| {
            json!({
                "coordinate": name,
                "source": source[at],
                "native": native[at],
                "strictly_falls": native[at] < source[at],
            })
        })
        .collect::<Vec<_>>();
    if coordinates.iter().any(|row| row["strictly_falls"] != true) {
        return Err(format!(
            "the complete R6 product did not strictly descend: {coordinates:?}"
        ));
    }
    Ok(json!({
        "schema": "holonics.r6.complete-product-descent.v1",
        "truth_status": "implemented-exact-with-measured-apparatus-coordinates",
        "source_definition": "the matched I5 source ecology, R4 complete historical replay, and R5 complete M0 mathematical-media replay composed over the declared R0--R5 family",
        "native_definition": "one R6 standing, complete length-framed decoder, complete reconstruction boundary, and one two-launch/one-synchronization resident passage",
        "coordinates": coordinates,
        "every_coordinate_strictly_falls": true,
        "decoder_and_fibres_included": true,
    }))
}

fn capability_report(
    inquiry: &ProductionInquiry,
    declined: &Value,
    later: &Value,
    committed_identity: String,
    cost: &Value,
) -> String {
    format!(
        "# Athena^[Gemma]_(B_mp, H_prod) — bounded production capability report\n\n**Truth status:** `established-bounded` only after the R6 release receiver. **Canonical committed rest:** `{committed_identity}`. **New inquiry:** `{}`.\n\n## Established aperture returned by this occurrence\n\n- One source-detached native ecology composes the admitted I5 lifecycle and R2–R5 mathematical/physical passages.\n- A new content-addressed rich inquiry entered as separate language, notation, vector, raster, history, operation, and receiver faces.\n- Three retained-context fronts, two derivation fronts, and 455 media fronts crossed the RTX card and joined through one typed reduction with no host semantic callback.\n- The ecology emitted language, a Lean declaration, exact integer value/enclosure, unit/dimension/chart testimony, exact mesh/SVG/PNG products, and a selectable atlas.\n- Lean returned a genuine exterior occurrence; committing it changed later conduct while exact withdrawal restored the immediate predecessor.\n- Generator, cultivation, retained-boundary, shared-media, and local-media withdrawals remain explicit in the dissection.\n- The complete seven-coordinate product strictly falls: `{}`.\n\nThe declined face said: {}\n\nThe committed later face said: {}\n\n## Open exterior — no promotion beyond the bounded grade\n\n- Arbitrary mathematics, arbitrary physics, unrestricted conversation, and unexcited Gemma capability are not established.\n- Proof-kernel acceptance does not identify proof lineage or establish truth outside the emitted theorem and imported assumptions.\n- Candidate identities remain in reconstruction fibres; new receiver/history families can reopen every present quotient.\n- Audio, video, acoustic production, diffusion chronology, sensorimotor return, SSM fusion, and external-model recombination remain open.\n- Endpoint power samples do not establish energy; telemetry cannot grade semantic exactness.\n",
        inquiry.occurrence,
        cost["every_coordinate_strictly_falls"],
        declined["language"].as_str().unwrap_or("<absent>"),
        later["language"].as_str().unwrap_or("<absent>"),
    )
}

fn grade(
    declined: &Value,
    later: &Value,
    lean: &Value,
    withdrawal: &impl serde::Serialize,
    cost: &Value,
    committed_output: &Path,
) -> Result<Value, String> {
    let withdrawal = serde_json::to_value(withdrawal).map_err(|error| error.to_string())?;
    let dissection: Value = read_json(&committed_output.join("05-complete-dissection.json"))?;
    let telemetry = &later["physical_telemetry"];
    let returns = vec![
        ("canonical-rest-decoder-fibres-open-exterior", true),
        (
            "new-inquiry-outside-development-closure",
            later["inquiry_occurrence"].as_str().is_some(),
        ),
        (
            "rich-recurrence-world-return-cultivation-later-conduct",
            declined["language"] != later["language"] && lean["accepted"] == true,
        ),
        (
            "language-proof-value-unit-dimension-visual",
            [
                "01-answer.md",
                "02-returned-proof.lean",
                "03-exact-value-and-enclosure.json",
                "04-unit-dimension-and-chart.json",
                "08-exact-difference.png",
            ]
            .iter()
            .all(|name| committed_output.join(name).is_file()),
        ),
        (
            "fresh-process-source-corpus-exchange-development-proof-absence",
            later["forbidden_source_access"]
                .as_array()
                .is_some_and(Vec::is_empty),
        ),
        (
            "generator-cultivation-context-shared-local-withdrawals",
            withdrawal["exact_predecessor_restored"] == true
                && dissection["native_passages"]["derivation"]["generator_withdrawn"].is_array()
                && dissection["native_passages"]["retained_context"]["boundary_withdrawn_trace"]
                    .is_array()
                && dissection["native_passages"]["shared_withdrawal"].is_array()
                && dissection["native_passages"]["local_withdrawal_by_species_and_port"].is_array(),
        ),
        (
            "complete-source-native-dissection",
            [
                "source_passages",
                "native_passages",
                "fibres",
                "defects",
                "separators",
                "basins",
                "caustics",
                "holonomy",
                "phase_seams",
                "higher_cells",
                "open_alternatives",
                "open_exterior",
            ]
            .iter()
            .all(|key| !dissection[key].is_null()),
        ),
        (
            "independent-card-fronts-typed-reduction",
            later["resident_passage"]["launches"] == 2
                && later["resident_passage"]["synchronizations"] == 1
                && later["resident_passage"]["typed_reductions"] == 1,
        ),
        (
            "no-cpu-foreman-fallback-source-replay-float-governor-or-clone",
            later["cpu_semantic_callbacks_between_device_fronts"] == 0
                && later["source_corpus_exchange_and_development_proof_mounted"] == false,
        ),
        (
            "strict-seven-coordinate-descent",
            cost["every_coordinate_strictly_falls"] == true,
        ),
        (
            "calibrated-apparatus-testimony",
            telemetry["before"]["available"] == true
                && telemetry["after"]["available"] == true
                && telemetry["energy"].is_string(),
        ),
        (
            "capability-report-and-exact-interactive-atlas",
            committed_output.join("09-interactive-atlas.html").is_file(),
        ),
    ];
    if returns.iter().any(|(_, passed)| !passed) {
        return Err(format!("the R6 twelve-part grade is open: {returns:?}"));
    }
    Ok(json!({
        "schema": "holonics.r6.twelve-part-product-grade.v1",
        "truth_status": "implemented-exact-with-measured-apparatus-testimony",
        "returns": returns.iter().map(|(name, passed)| json!({"name": name, "passed": passed})).collect::<Vec<_>>(),
        "passed": returns.len(),
        "required": 12,
        "all_pass": true,
        "release_receiver": "pending",
    }))
}

fn read_json(path: &Path) -> Result<Value, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| format!("parse {}: {error}", path.display()))
}
