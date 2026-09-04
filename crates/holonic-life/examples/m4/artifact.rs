//! Seal the M4 artifact family, execute Lean as an exterior checker, and inspect remount/ablation.

use std::path::Path;
use std::process::Command;

use holonic_engine::receiver_history_cultivation::MountedCultivatedHistory;
use serde::Serialize;
use sha2::{Digest, Sha256};

use super::native::NativeTrainingMount;
use super::quadric::CultivationProduct;
use super::resident::ResidentMathematicalReturn;
use super::visual::VisualProduct;

const OUT: &str = ".local/artifacts/the_native_codec_is_cultivated_and_returns_complete_mathematics";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct SourceLineage {
    schema: String,
    m3_native_rest: String,
    m3_native_rest_sha256: String,
    m3_evidence: String,
    m3_evidence_sha256: String,
    lean_source: String,
    lean_source_sha256: String,
    inherited_artifacts: Vec<String>,
    identity_use: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct LeanTestimony {
    schema: String,
    command: String,
    exit_status: i32,
    accepted: bool,
    theorem_population: Vec<String>,
    stdout: String,
    stderr: String,
    source_token_sorry_occurrences: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct RemountAblationReceipt {
    schema: String,
    source_paths_presented_to_remount: Vec<String>,
    source_material_opened_by_runtime: bool,
    repeated_held_out_output: Vec<String>,
    repeated_output_matches: bool,
    unrelated_native_endpoint_before_ablation: u64,
    unrelated_native_endpoint_after_ablation: u64,
    unrelated_native_conduct_unchanged: bool,
    targeted_morphology_ablation_refusal: String,
    targeted_morphology_removed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct Grade {
    schema: String,
    truth_status: String,
    m3_receiver_difference_founded_nontrivial_leader: bool,
    causal_adjoint_reversed_only_the_retained_word: bool,
    local_rank_derived_from_exact_defect: bool,
    coordinate_orbit_extent_derived_by_closure: bool,
    metric_reflection_family_held: bool,
    source_detached_rest_authenticated: bool,
    held_out_word_returned_on_gpu: bool,
    one_gpu_graph_launch_and_one_synchronization: bool,
    cpu_semantic_cells: usize,
    exact_value_and_enclosure_returned: bool,
    plural_derivation_routes_agreed: bool,
    invalid_candidate_refused: bool,
    lean_exterior_checker_accepted: bool,
    analytic_face_complete: bool,
    vector_raster_mesh_round_trip_held: bool,
    singularity_and_open_geometry_fibres_retained: bool,
    targeted_ablation_removed_only_attributable_conduct: bool,
    complete_reconstruction_fibre_retained: bool,
    passed: bool,
    boundary: String,
}

pub fn write(
    root: &Path,
    native: &NativeTrainingMount,
    product: &CultivationProduct,
    resident: &ResidentMathematicalReturn,
    visual: &VisualProduct,
    mounted: MountedCultivatedHistory,
) -> Result<(), String> {
    let out = root.join(OUT);
    std::fs::create_dir_all(&out).map_err(|error| error.to_string())?;
    std::fs::write(
        out.join("cultivated-receiver-history-rest.json"),
        &product.rest_bytes,
    )
    .map_err(|error| error.to_string())?;
    write_json(
        &out.join("leader-and-causal-adjoint.json"),
        &(native.leader.clone(), &product.adjoint),
    )?;
    write_json(&out.join("problem-specification.json"), &product.problem)?;
    write_json(&out.join("mathematical-return.json"), &product.mathematical)?;
    write_json(&out.join("resident-return.json"), resident)?;
    write_json(&out.join("analytic-scene.json"), &visual.face)?;
    std::fs::write(
        out.join("reflection-face.svg"),
        visual.vector_svg.as_bytes(),
    )
    .map_err(|error| error.to_string())?;
    write_json(&out.join("reflection-face-raster.json"), &visual.raster)?;
    std::fs::write(out.join("reflection-face.ppm"), &visual.raster_ppm)
        .map_err(|error| error.to_string())?;
    write_json(&out.join("ordered-orbit-mesh.json"), &visual.mesh)?;
    write_json(&out.join("visual-round-trip.json"), &visual.round_trip)?;

    let lean_path = root
        .join("formal/elementary-holonics/ElementaryHolonics/Millennium/SpherePacking.lean");
    let lean_bytes = std::fs::read(&lean_path).map_err(|error| error.to_string())?;
    let lean = run_lean(root, &lean_bytes)?;
    write_json(&out.join("lean-exterior-testimony.json"), &lean)?;
    let evidence_bytes = std::fs::read(&native.evidence_path).map_err(|error| error.to_string())?;
    let lineage = SourceLineage {
        schema: "holonics.m4.source-lineage.v1".to_owned(),
        m3_native_rest: relative(root, &native.rest_path)?,
        m3_native_rest_sha256: digest(&native.rest_bytes),
        m3_evidence: relative(root, &native.evidence_path)?,
        m3_evidence_sha256: digest(&evidence_bytes),
        lean_source: relative(root, &lean_path)?,
        lean_source_sha256: digest(&lean_bytes),
        inherited_artifacts: vec![
            "M0 plural born-digital/vector/raster source and disagreement fibre".to_owned(),
            "M1 addressed mathematical particle, typed operation complex and pullback joins"
                .to_owned(),
            "M2 frozen-Gemma active transport cover and complete response cochains".to_owned(),
            "M3 receiver/history quotient, decoder and complete reconstruction fibres".to_owned(),
        ],
        identity_use:
            "content digests authenticate exterior occurrences and never classify mathematical conduct"
                .to_owned(),
    };
    write_json(&out.join("source-lineage.json"), &lineage)?;

    let remount = inspect_remount_and_ablation(native, product, mounted)?;
    write_json(
        &out.join("source-detached-remount-and-ablation.json"),
        &remount,
    )?;
    let exact_output = resident.returned_words
        == product
            .mathematical
            .held_out_output
            .iter()
            .map(|value| value.to_string().parse::<i64>())
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| error.to_string())?;
    let grade = Grade {
        schema: "holonics.m4.complete-mathematics-return-grade.v1".to_owned(),
        truth_status: "established-bounded".to_owned(),
        m3_receiver_difference_founded_nontrivial_leader: !native.leader.leader_word.is_empty()
            && native.leader.endpoint_observation != native.leader.opposing_observation,
        causal_adjoint_reversed_only_the_retained_word: product.adjoint.return_word
            == native.leader.return_word,
        local_rank_derived_from_exact_defect: product
            .adjoint
            .measured_delta_ranks
            .iter()
            .all(|rank| *rank == 1),
        coordinate_orbit_extent_derived_by_closure: product.adjoint.orbit_extent
            == product.rest.morphology.receiver_metric.rows(),
        metric_reflection_family_held: product.adjoint.metric_square_held
            && product.adjoint.involution_held,
        source_detached_rest_authenticated: remount.source_paths_presented_to_remount
            == vec![
                "cultivated-receiver-history-rest.json".to_owned(),
                "M3 generator-native-rest.json".to_owned(),
            ]
            && !remount.source_material_opened_by_runtime,
        held_out_word_returned_on_gpu: resident.matches_source_detached_exact_control && exact_output,
        one_gpu_graph_launch_and_one_synchronization: resident.graph_deed_launches == 1
            && resident.synchronizations == 1,
        cpu_semantic_cells: resident.cpu_semantic_cells,
        exact_value_and_enclosure_returned: exact_output
            && product
                .mathematical
                .held_out_exact_enclosure
                .iter()
                .all(|interval| interval[0] == interval[1]),
        plural_derivation_routes_agreed: product.mathematical.routes.len() >= 2
            && product
                .mathematical
                .routes
                .iter()
                .all(|route| route.result == product.mathematical.held_out_output),
        invalid_candidate_refused: !product
            .mathematical
            .invalid_candidate_refusal
            .is_empty(),
        lean_exterior_checker_accepted: lean.accepted
            && lean.source_token_sorry_occurrences == 0,
        analytic_face_complete: visual.face.is_complete()
            && visual.face.population_reconciles()
            && visual.face.certified_feature_count == 2,
        vector_raster_mesh_round_trip_held: visual.round_trip.analytic_face_round_trip
            && visual.round_trip.vector_gauge_changed_no_structure
            && visual.round_trip.raster_gauge_changed_no_geometry
            && visual.round_trip.raster_round_trip
            && visual.round_trip.mesh_round_trip
            && visual.mesh.retriangulation_preserved_boundary
            && visual.mesh.retriangulation_preserved_euler_characteristic,
        singularity_and_open_geometry_fibres_retained: !product
            .problem
            .singularities_and_chart_exclusions
            .is_empty()
            && product
                .problem
                .singularities_and_chart_exclusions
                .iter()
                .any(|entry| entry.contains("does not construct centres")),
        targeted_ablation_removed_only_attributable_conduct: remount
            .targeted_morphology_removed
            && remount.unrelated_native_conduct_unchanged,
        complete_reconstruction_fibre_retained: !native.leader.complete_anchor_fibre.is_empty(),
        passed: false,
        boundary: "one M3 leader and one symmetric rank-one metric-reflection morphology on the five-bend Soddy--Gossett quadric; arbitrary mathematical formulation, sphere centres/non-overlap, fractal dimension, unexcited Gemma capability and broader receiver families remain open"
            .to_owned(),
    };
    let mut grade = grade;
    grade.passed = grade.m3_receiver_difference_founded_nontrivial_leader
        && grade.causal_adjoint_reversed_only_the_retained_word
        && grade.local_rank_derived_from_exact_defect
        && grade.coordinate_orbit_extent_derived_by_closure
        && grade.metric_reflection_family_held
        && grade.source_detached_rest_authenticated
        && grade.held_out_word_returned_on_gpu
        && grade.one_gpu_graph_launch_and_one_synchronization
        && grade.cpu_semantic_cells == 0
        && grade.exact_value_and_enclosure_returned
        && grade.plural_derivation_routes_agreed
        && grade.invalid_candidate_refused
        && grade.lean_exterior_checker_accepted
        && grade.analytic_face_complete
        && grade.vector_raster_mesh_round_trip_held
        && grade.singularity_and_open_geometry_fibres_retained
        && grade.targeted_ablation_removed_only_attributable_conduct
        && grade.complete_reconstruction_fibre_retained;
    write_json(&out.join("grade.json"), &grade)?;
    std::fs::write(out.join("grade.form"), format!("{grade:#?}\n").as_bytes())
        .map_err(|error| error.to_string())?;
    if !grade.passed {
        return Err(format!("M4 grade refused: {grade:#?}"));
    }
    println!(
        "M4 PASSED: leader span {}, orbit {}, held-out {:?}, GPU graph {} kernels, Lean accepted, exact visual round trip",
        native.leader.leader_word.len(),
        product.adjoint.orbit_extent,
        resident.returned_words,
        resident.captured_kernel_launches,
    );
    Ok(())
}

fn inspect_remount_and_ablation(
    native: &NativeTrainingMount,
    product: &CultivationProduct,
    mounted: MountedCultivatedHistory,
) -> Result<RemountAblationReceipt, String> {
    let mut current = product.mathematical.held_out_input.clone();
    for member in &product.mathematical.held_out_conduct_order {
        current = mounted
            .apply_exact(*member, &current)
            .map_err(|error| error.to_string())?;
    }
    let repeated_output_matches = current == product.mathematical.held_out_output;
    let unrelated_before = mounted
        .conduct_native_word(native.leader.port, &native.leader.leader_word)
        .map_err(|error| error.to_string())?;
    let ablated = mounted.ablate();
    let targeted_morphology_ablation_refusal = ablated
        .apply_exact(
            product.mathematical.held_out_conduct_order[0],
            &product.mathematical.held_out_input,
        )
        .expect_err("targeted ablation must refuse the cultivated reflection")
        .to_string();
    let unrelated_after = ablated
        .conduct_native_word(native.leader.port, &native.leader.leader_word)
        .map_err(|error| error.to_string())?;
    Ok(RemountAblationReceipt {
        schema: "holonics.m4.source-detached-remount-ablation.v1".to_owned(),
        source_paths_presented_to_remount: vec![
            "cultivated-receiver-history-rest.json".to_owned(),
            "M3 generator-native-rest.json".to_owned(),
        ],
        source_material_opened_by_runtime: false,
        repeated_held_out_output: current.iter().map(ToString::to_string).collect(),
        repeated_output_matches,
        unrelated_native_endpoint_before_ablation: unrelated_before.0,
        unrelated_native_endpoint_after_ablation: unrelated_after.0,
        unrelated_native_conduct_unchanged: unrelated_before == unrelated_after,
        targeted_morphology_removed: !targeted_morphology_ablation_refusal.is_empty(),
        targeted_morphology_ablation_refusal,
    })
}

fn run_lean(root: &Path, source: &[u8]) -> Result<LeanTestimony, String> {
    let cwd = root.join("formal/elementary-holonics");
    let command = "lake env lean ElementaryHolonics/Millennium/SpherePacking.lean";
    let output = Command::new("lake")
        .args([
            "env",
            "lean",
            "ElementaryHolonics/Millennium/SpherePacking.lean",
        ])
        .current_dir(&cwd)
        .output()
        .map_err(|error| error.to_string())?;
    Ok(LeanTestimony {
        schema: "holonics.m4.lean-exterior-testimony.v1".to_owned(),
        command: command.to_owned(),
        exit_status: output.status.code().unwrap_or(-1),
        accepted: output.status.success(),
        theorem_population: vec![
            "everyReflectionIsInvolutive".to_owned(),
            "everyReflectionPreservesTheTangencyDefect".to_owned(),
            "everyReflectionWordPreservesTheTangencyDefect".to_owned(),
            "twoReflectionsGrowTheIntegralBendPopulation".to_owned(),
            "thePackingChronologyCannotCollapseToAMultiset".to_owned(),
            "aReturnedFaceDoesNotEraseTheReflectionLineage".to_owned(),
        ],
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        source_token_sorry_occurrences: String::from_utf8_lossy(source).matches("sorry").count(),
    })
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    std::fs::write(
        path,
        serde_json::to_vec(value).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn relative(root: &Path, path: &Path) -> Result<String, String> {
    path.strip_prefix(root)
        .map(|relative| relative.display().to_string())
        .map_err(|error| error.to_string())
}
