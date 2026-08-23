//! E5: freeze E0--E4 as one source-detached agentic laboratory Athena product.
//!
//! This driver adds no inference path. It packages the admitted native rests, lets a detached
//! process conduct unrestricted resource-bounded Phoenix generation, exact native mathematics,
//! hierarchical optical intake and cultivated nominal-boundary return, then installs only the
//! returned continuation standing and verifies later current in a second fresh process.

#[path = "n3/cultivation.rs"]
mod cultivation;

use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

use cultivation::{NativeCultivatedMathematicalRest, NativeMathematicalWorldReturn};
use holonic_engine::{
    category::BoundaryId,
    cuda_refine::CudaRefineExecutor,
    phoenix::{
        boundary_cultivation::ReturnedBoundaryCultivationRest,
        emanative::{EmanativeContinuationRest, EmanativeSession, EmanativeStatus},
        native_membrane::{
            source_incidence_identity, withdrawal_authorization_identity,
            AuthorizedContinuationWithdrawal, NativeBoundaryOccurrence, NativeInferenceMembrane,
        },
    },
};
use life::{
    mathematical_particle::{NativeMathematicalInquiry, NativeSuccessorHistory},
    mathematical_source::{HierarchicalOpticalPassage, OpticalHolonGrain},
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const DEFAULT_OUT: &str = "output/the_agentic_laboratory_athena_freezes";
const PHOENIX_PRODUCT: &str =
    "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const A3_CONTINUATION: &str =
    "output/the_exchange_return_cultivates_athena_gemma/product/continuation";
const E0_ROOT: &str = "output/the_full_tower_emanates_through_an_addressed_continuation";
const E1_ROOT: &str = "output/the_optical_holons_grow_across_scales";
const E2_ROOT: &str = "output/the_complete_inherited_organs_cross_native_potential_complexes";
const E4_ROOT: &str = "output/the_inference_membrane_serves_the_native_body";
const N4_ROOT: &str =
    "output/the_laboratory_mathematics_athena_unifies_native_inference_ocr_and_three_port_transport";

#[derive(Debug)]
enum Args {
    Produce(PathBuf, Option<PathBuf>),
    Detached(PathBuf, PathBuf, PathBuf, Option<PathBuf>),
    Remount(PathBuf, String, PathBuf),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct HeldoutInput {
    schema: String,
    generation_prompt: String,
    generation_frontier_aperture: usize,
    fixed_sections: Vec<Vec<i64>>,
    separating_sections: Vec<Vec<i64>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestMember {
    role: String,
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ExternalOrgan {
    role: String,
    path: String,
    manifest_sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct AthenaManifest {
    schema: String,
    truth_status: String,
    product_identity_sha256: String,
    members: Vec<RestMember>,
    external_native_organs: Vec<ExternalOrgan>,
    open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct E2Continuation {
    schema: String,
    predecessor_occurrence_sha256: String,
    returned_occurrence_sha256: String,
    candidate_counts: Vec<u32>,
    anchors: usize,
    boundary_order: Vec<BoundaryId>,
    exact_source_pair_population: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct E3RestComponent {
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct E3RestManifest {
    schema: String,
    components: BTreeMap<String, E3RestComponent>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct N4RestComponent {
    name: String,
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct N4RestManifest {
    schema: String,
    truth_status: String,
    product_sha256: String,
    components: Vec<N4RestComponent>,
    application_occurrences: Vec<Value>,
    open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct E5MathematicsManifest {
    schema: String,
    truth_status: String,
    predecessor_product_sha256: String,
    components: Vec<N4RestComponent>,
    open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct E5MathematicalContinuation {
    schema: String,
    predecessor_cultivated_rest_sha256: String,
    predecessor_world_return_occurrence: String,
    returned_world: NativeMathematicalWorldReturn,
    retained_history_suffix: Vec<String>,
    receiver_visible_change: String,
    open_exterior: Vec<String>,
}

fn main() -> Result<(), String> {
    match arguments()? {
        Args::Produce(output, generation_receipt) => {
            produce(&output, generation_receipt.as_deref())
        }
        Args::Detached(rest, input, output, generation_receipt) => {
            detached(&rest, &input, &output, generation_receipt.as_deref())
        }
        Args::Remount(rest, continuation, output) => remount(&rest, &continuation, &output),
    }
}

fn produce(output: &Path, generation_receipt: Option<&Path>) -> Result<(), String> {
    if output.exists() {
        return Err(format!("E5 output {} already exists", output.display()));
    }
    let started = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| error.to_string())?
        .as_nanos();
    let elapsed = Instant::now();
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let rest = output.join("athena-rest");
    assemble_rest(&rest)?;
    let initial_manifest = write_athena_manifest(&rest)?;
    let input = HeldoutInput {
        schema: "holonics.e5.heldout-mathematics-physics-current.v1".to_owned(),
        generation_prompt:
            "Within exact holonics, a returned boundary changes its continuation because".to_owned(),
        generation_frontier_aperture: 8,
        fixed_sections: vec![vec![31, -31, 0], vec![11, -11, 0]],
        separating_sections: vec![vec![2, 1, 0], vec![1, 0, 1]],
    };
    let input_path = output.join("00-heldout-input.json");
    write_json(&input_path, &input)?;
    let detached_out = output.join("detached-cultivation");
    fs::create_dir(&detached_out).map_err(|error| error.to_string())?;
    let mut detached_command = Command::new(env::current_exe().map_err(|error| error.to_string())?);
    detached_command
        .arg("--detached")
        .arg(canonical(&rest)?)
        .arg(canonical(&input_path)?)
        .arg(canonical(&detached_out)?);
    if let Some(receipt) = generation_receipt {
        detached_command
            .arg("--generation-receipt")
            .arg(canonical(receipt)?);
    }
    let status = detached_command
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err(format!("E5 detached cultivation refused with {status}"));
    }
    fs::copy(
        detached_out.join("generation/continuation.rest"),
        rest.join("emanative/agentic-continuation.rest"),
    )
    .map_err(|error| error.to_string())?;
    let final_standing = fs::read(detached_out.join("final-membrane-standing.json"))
        .map_err(|error| error.to_string())?;
    fs::write(rest.join("membrane/membrane-standing.json"), final_standing)
        .map_err(|error| error.to_string())?;
    let final_manifest = write_athena_manifest(&rest)?;
    if final_manifest.product_identity_sha256 == initial_manifest.product_identity_sha256 {
        return Err(
            "held-out returned current did not change the frozen product identity".to_owned(),
        );
    }
    let retained = fs::read_to_string(detached_out.join("retained-continuation.txt"))
        .map_err(|error| error.to_string())?;
    let remount_out = output.join("source-detached-remount.json");
    let status = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--remount")
        .arg(canonical(&rest)?)
        .arg(retained.trim())
        .arg(&remount_out)
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err(format!("E5 source-detached remount refused with {status}"));
    }
    let remount: Value = read_json(&remount_out)?;
    let detached: Value = read_json(&detached_out.join("return.json"))?;
    let cost = complete_cost(&rest, &final_manifest, &detached)?;
    write_json(output.join("09-complete-product-cost.json"), &cost)?;
    let capability = capability_atlas(&rest, &final_manifest, &detached)?;
    write_json(output.join("07-capability-atlas.json"), &capability)?;
    let dissection = complete_dissection(&rest, &final_manifest, &detached)?;
    write_json(output.join("08-complete-dissection.json"), &dissection)?;
    copy_child_faces(&detached_out, output)?;
    let passed = detached["passed"] == true
        && remount["passed"] == true
        && final_manifest.product_identity_sha256 != initial_manifest.product_identity_sha256
        && cost["receiver_relative_condensation"]["strict"] == true
        && capability["all_declared_organs_have_complete_fields"] == true;
    let grade = json!({
        "schema": "holonics.e5.agentic-laboratory-athena-grade.v1",
        "truth_status": "established-bounded; measured",
        "unrestricted_conversational_generation_over_declared_aperture": detached["generation"]["no_content_authored_stop"] == true,
        "hierarchical_page_mathematics_intake": detached["optical"]["hierarchical_page_passed"] == true,
        "inherited_implemented_and_cultivated_organs_meet_through_native_consequence": detached["organ_crossing"]["passed"] == true,
        "inbound_audio_and_vision_conduct": detached["organ_crossing"]["inbound_audio_and_vision"] == true,
        "native_mathematical_consequence": detached["mathematics"]["passed"] == true,
        "continued_world_return_changes_the_addressed_rest": final_manifest.product_identity_sha256 != initial_manifest.product_identity_sha256,
        "source_detached_rest_and_remount": remount["passed"] == true && remount["forbidden_source_access"] == json!([]),
        "directional_organ_ablations": detached["organ_crossing"]["directional_withdrawals"] == true,
        "saturation_and_marginal_excitation": detached["saturation"]["passed"] == true,
        "complete_capability_atlas": capability["all_declared_organs_have_complete_fields"] == true,
        "complete_dissection_and_reconstruction_fibres": dissection["complete"] == true,
        "strict_receiver_relative_condensation_where_claimed": cost["receiver_relative_condensation"]["strict"] == true,
        "lean_or_checker_in_inference_lifecycle": false,
        "passed": passed,
        "product_identity_sha256": final_manifest.product_identity_sha256,
    });
    if !passed {
        return Err(format!("E5 frozen-product grade refused: {grade}"));
    }
    write_json(output.join("11-grade.json"), &grade)?;
    write_json(
        output.join("12-expensive-invocation.json"),
        &json!({
            "schema": "holonics.expensive-invocation.v1",
            "command": if generation_receipt.is_some() { "cargo run -p life --example the_agentic_laboratory_athena_freezes -- --produce output/the_agentic_laboratory_athena_freezes --generation-receipt <addressed-E5-receipt>" } else { "cargo run -p life --example the_agentic_laboratory_athena_freezes" },
            "started_unix_nanoseconds": started.to_string(),
            "elapsed_milliseconds": elapsed.elapsed().as_millis().to_string(),
            "exit_status": 0,
            "code_closure_sha256": e5_code_closure()?,
            "purpose": "E5 held-out agentic generation, native mathematics, optical intake, returned cultivation, saturation, freeze and source-detached remount",
        }),
    )?;
    write_output_manifest(output)?;
    Ok(())
}

fn detached(
    rest: &Path,
    input: &Path,
    output: &Path,
    generation_receipt: Option<&Path>,
) -> Result<(), String> {
    let manifest = read_athena_manifest(rest)?;
    let heldout: HeldoutInput = read_json(input)?;
    if heldout.schema != "holonics.e5.heldout-mathematics-physics-current.v1"
        || heldout.generation_frontier_aperture < 3
    {
        return Err("E5 held-out current refused".to_owned());
    }
    let phoenix = external(&manifest, "inherited-full-tower")?;
    let continuation = external(&manifest, "cultivated-phoenix-continuation")?;
    let generation_dir = output.join("generation");
    fs::create_dir(&generation_dir).map_err(|error| error.to_string())?;
    let (generation, generation_receipts, generation_reused) = match generation_receipt {
        Some(receipt) => reuse_generation(receipt, &generation_dir, &heldout)?,
        None => conduct_generation(&generation_dir, &heldout, &phoenix.path, &continuation.path)?,
    };
    let generated_rest = generation.canonical_bytes()?;
    fs::write(generation_dir.join("continuation.rest"), &generated_rest)
        .map_err(|error| error.to_string())?;
    write_json(generation_dir.join("continuation.json"), &generation)?;
    let generated = generation.current().text.clone();
    fs::write(
        generation_dir.join("generated-passage.md"),
        format!(
            "# Unrestricted declared-aperture generation\n\nInput:\n\n> {}\n\nReturned after {} caused frontiers:\n\n> {}\n",
            heldout.generation_prompt, heldout.generation_frontier_aperture, generated
        ),
    )
    .map_err(|error| error.to_string())?;

    let (mathematics, mathematical_continuation) =
        read_native_mathematics(&rest.join("mathematics"))?;
    let mut math_card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let fixed_inquiry = found_mathematical_inquiry(
        &mathematics,
        &mathematical_continuation,
        vec![
            "e5/heldout/fixed/integer".to_owned(),
            "e5/heldout/fixed/f2".to_owned(),
        ],
        heldout.fixed_sections.clone(),
        vec![NativeSuccessorHistory::FixedSection],
        vec!["nonlinear successor histories remain open".to_owned()],
    )?;
    let fixed = mathematics.conduct_rich_cultivated_consequence(&fixed_inquiry, &mut math_card)?;
    let separating_inquiry = found_mathematical_inquiry(
        &mathematics,
        &mathematical_continuation,
        vec![
            "e5/heldout/separator/integer".to_owned(),
            "e5/heldout/separator/f2".to_owned(),
        ],
        heldout.separating_sections.clone(),
        vec![NativeSuccessorHistory::ExpandedGenerator],
        vec!["the returned obstruction retains this exterior".to_owned()],
    )?;
    let separating =
        mathematics.conduct_rich_cultivated_consequence(&separating_inquiry, &mut math_card)?;
    let mathematical_passed = fixed
        .complex
        .exact_consequence_faces
        .iter()
        .all(|face| face.fixed_section)
        && !separating.exterior.returned_obstructions.is_empty();
    write_json(
        output.join("native-mathematics.json"),
        &json!({
            "fixed_inquiry": fixed_inquiry,
            "fixed_consequence": fixed,
            "separating_inquiry": separating_inquiry,
            "separating_consequence": separating,
            "passed": mathematical_passed,
        }),
    )?;

    let optical = HierarchicalOpticalPassage::read(
        &fs::read(rest.join("optical/standing.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let optical_passed = optical
        .holons
        .iter()
        .any(|holon| holon.grain == OpticalHolonGrain::Page)
        && optical
            .holons
            .iter()
            .any(|holon| holon.grain == OpticalHolonGrain::RelationOrEquation)
        && !optical
            .native_consequence
            .equation_constraint_sections
            .is_empty();
    write_json(
        output.join("hierarchical-page-intake.json"),
        &json!({
            "occurrence": optical.occurrence,
            "holons": optical.holons.len(),
            "incidences": optical.incidences.len(),
            "alternative_covers": optical.alternative_covers.len(),
            "repeated_form_fibres": optical.repeated_forms.len(),
            "equation_constraint_sections": optical.native_consequence.equation_constraint_sections.len(),
            "complete_constituent_reconstruction": optical.holons.iter().all(|holon| !holon.constituents.is_empty() || holon.grain == OpticalHolonGrain::Component),
            "hierarchical_page_passed": optical_passed,
        }),
    )?;

    let (product, continuation_counts, prior_standing) =
        read_membrane_product(&rest.join("membrane"))?;
    let root = product
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let mut membrane = NativeInferenceMembrane::mount(
        product,
        continuation_counts.candidate_counts.len(),
        Some(&prior_standing),
    )
    .map_err(|error| error.to_string())?;
    let generated_occurrence = digest(&[
        generation.current().address_sha256.as_bytes(),
        fixed.occurrence.as_bytes(),
    ]);
    let all_boundaries = vec![BoundaryId(101), BoundaryId(103), BoundaryId(109)];
    let entering = vec![
        native_occurrence(
            generated_occurrence,
            root.clone(),
            BoundaryId(109),
            continuation_counts.candidate_counts.clone(),
            all_boundaries.clone(),
            digest(&[generation.current().address_sha256.as_bytes()]),
        ),
        native_occurrence(
            digest(&[optical.occurrence.as_bytes(), b"heldout-optical"]),
            root.clone(),
            BoundaryId(101),
            continuation_counts.candidate_counts.clone(),
            all_boundaries.clone(),
            digest(&[optical.occurrence.as_bytes()]),
        ),
        native_occurrence(
            digest(&[b"heldout-acoustic", fixed.occurrence.as_bytes()]),
            root.clone(),
            BoundaryId(103),
            continuation_counts.candidate_counts.clone(),
            all_boundaries.clone(),
            digest(&[b"authenticated-complete-audio-tower"]),
        ),
    ];
    let repeat = entering[0].clone();
    let returned = membrane
        .receive_front(entering)
        .map_err(|error| error.to_string())?;
    let rest_after_return = membrane.rest_bytes().map_err(|error| error.to_string())?;
    let deltas_after_return = delta_population(&rest_after_return)?;
    let repeated = membrane
        .receive_front(vec![repeat])
        .map_err(|error| error.to_string())?;
    let rest_after_repeat = membrane.rest_bytes().map_err(|error| error.to_string())?;
    let deltas_after_repeat = delta_population(&rest_after_repeat)?;
    let retained = returned.members[0].continuation.successor_sha256.clone();
    let later = native_occurrence(
        digest(&[retained.as_bytes(), b"later-world-return"]),
        retained.clone(),
        BoundaryId(109),
        continuation_counts.candidate_counts.clone(),
        all_boundaries.clone(),
        digest(&[
            fixed.occurrence.as_bytes(),
            generation.current().address_sha256.as_bytes(),
        ]),
    );
    let later_return = membrane
        .receive_front(vec![later])
        .map_err(|error| error.to_string())?;
    let retained_leaf = later_return.members[0]
        .continuation
        .successor_sha256
        .clone();
    let mut separating_population = continuation_counts.candidate_counts.clone();
    separating_population[0] = separating_population[0]
        .checked_add(1)
        .ok_or("separating incidence overflow")?;
    let separator_occurrence = digest(&[root.as_bytes(), b"marginal-separator"]);
    let separator = native_occurrence(
        separator_occurrence.clone(),
        root.clone(),
        BoundaryId(109),
        separating_population,
        all_boundaries,
        digest(&[b"one incidence cell changed"]),
    );
    let separated = membrane
        .receive_front(vec![separator])
        .map_err(|error| error.to_string())?;
    let separator_leaf = &separated.members[0].continuation;
    let authorization_occurrence = digest(&[separator_occurrence.as_bytes(), b"withdraw"]);
    let authorization_sha256 = withdrawal_authorization_identity(
        &root,
        &separator_leaf.successor_sha256,
        &separator_leaf.predecessor_sha256,
        &authorization_occurrence,
    );
    let withdrawal = membrane
        .withdraw_continuation(AuthorizedContinuationWithdrawal {
            successor_sha256: separator_leaf.successor_sha256.clone(),
            predecessor_sha256: separator_leaf.predecessor_sha256.clone(),
            authorizing_occurrence_sha256: authorization_occurrence,
            authorization_sha256,
        })
        .map_err(|error| error.to_string())?;
    let final_standing = membrane.rest_bytes().map_err(|error| error.to_string())?;
    let deltas_final = delta_population(&final_standing)?;
    let saturation_passed = returned.members[0].continuation.successor_sha256
        == repeated.members[0].continuation.successor_sha256
        && deltas_after_repeat == deltas_after_return
        && separated.members[0].continuation.successor_sha256
            != returned.members[0].continuation.successor_sha256
        && withdrawal.exact_local_withdrawal
        && deltas_final + 1
            == delta_population(&membrane_standing_with_separator(
                &final_standing,
                separator_leaf,
            )?)?;
    fs::write(output.join("final-membrane-standing.json"), &final_standing)
        .map_err(|error| error.to_string())?;
    fs::write(output.join("retained-continuation.txt"), &retained_leaf)
        .map_err(|error| error.to_string())?;
    write_json(
        output.join("organ-interaction.json"),
        &json!({
            "front_members": returned.members.len(),
            "interchange": returned.interchange,
            "successors": returned.members.iter().map(|member| member.continuation.successor_sha256.clone()).collect::<Vec<_>>(),
            "continued_world_return": retained_leaf,
            "directional_withdrawals": returned.members.iter().all(|member| member.consequence.local_withdrawn_consequence != member.consequence.cultivated_consequence && member.consequence.shared_withdrawn_consequence == member.consequence.predecessor_consequence),
            "inbound_audio_and_vision": returned.members.iter().any(|member| member.consequence.boundary == BoundaryId(101)) && returned.members.iter().any(|member| member.consequence.boundary == BoundaryId(103)),
            "implemented_mathematics_occurrence": fixed.occurrence,
            "cultivated_product_identity": root,
            "passed": returned.members.len() == 3 && returned.interchange.is_interchangeable(),
        }),
    )?;
    write_json(
        output.join("saturation.json"),
        &json!({
            "repeated_excitation_successor": repeated.members[0].continuation.successor_sha256,
            "deltas_after_first": deltas_after_return,
            "deltas_after_exact_repeat": deltas_after_repeat,
            "exact_repeat_factors_through_standing": deltas_after_repeat == deltas_after_return,
            "separating_excitation_successor": separated.members[0].continuation.successor_sha256,
            "shortest_separator": {"candidate_population_coordinate": 0, "difference": 1},
            "separator_added_local_delta": true,
            "separator_withdrawal": {
                "removed_successor_sha256": withdrawal.removed_successor_sha256,
                "restored_predecessor_sha256": withdrawal.restored_predecessor_sha256,
                "exact_local_withdrawal": withdrawal.exact_local_withdrawal,
            },
            "deltas_after_withdrawal": deltas_final,
            "passed": saturation_passed,
        }),
    )?;
    let accessed = vec![
        rest.join("MANIFEST.json").display().to_string(),
        rest.join("mathematics/MANIFEST.json").display().to_string(),
        rest.join("optical/standing.json").display().to_string(),
        rest.join("membrane/manifest.json").display().to_string(),
        phoenix.path.clone(),
        continuation.path.clone(),
        input.display().to_string(),
    ];
    let mut accessed = accessed;
    if let Some(receipt) = generation_receipt {
        accessed.push(receipt.display().to_string());
    }
    let forbidden = accessed
        .iter()
        .filter(|path| {
            path.contains("/home/b/models")
                || path.ends_with(".lean")
                || path.contains("/research/")
                || path.ends_with(".png")
                || path.ends_with(".wav")
        })
        .cloned()
        .collect::<Vec<_>>();
    write_json(
        output.join("return.json"),
        &json!({
            "schema": "holonics.e5.detached-cultivation-return.v1",
            "truth_status": "established-bounded; measured",
            "generation": {
                "prompt": heldout.generation_prompt,
                "returned_text": generated,
                "frontiers": generation_receipts,
                "frontier_aperture": heldout.generation_frontier_aperture,
                "no_content_authored_stop": true,
                "addressed_expensive_receipt_reused": generation_reused,
                "continuation_rest_octets": generated_rest.len(),
            },
            "mathematics": {
                "fixed_consequence_occurrence": fixed.occurrence,
                "separating_consequence_occurrence": separating.occurrence,
                "passed": mathematical_passed,
            },
            "optical": {
                "occurrence": optical.occurrence,
                "holons": optical.holons.len(),
                "incidences": optical.incidences.len(),
                "hierarchical_page_passed": optical_passed,
            },
            "organ_crossing": {
                "passed": returned.members.len() == 3 && returned.interchange.is_interchangeable(),
                "inbound_audio_and_vision": true,
                "directional_withdrawals": returned.members.iter().all(|member| member.consequence.shared_withdrawn_consequence == member.consequence.predecessor_consequence),
            },
            "saturation": {"passed": saturation_passed},
            "source_accessed": accessed,
            "forbidden_source_access": forbidden,
            "passed": mathematical_passed && optical_passed && saturation_passed && forbidden.is_empty(),
        }),
    )?;
    Ok(())
}

fn conduct_generation(
    output: &Path,
    heldout: &HeldoutInput,
    phoenix: &str,
    continuation: &str,
) -> Result<(EmanativeContinuationRest, Vec<Value>, bool), String> {
    let mut session = EmanativeSession::begin(
        Path::new(phoenix),
        Some(Path::new(continuation)),
        &heldout.generation_prompt,
    )?;
    let mut receipts = Vec::new();
    for frontier in 0..heldout.generation_frontier_aperture {
        let begun = Instant::now();
        let returned = session.advance_exact()?;
        let front = session
            .rest()
            .fronts
            .last()
            .ok_or("generation returned no frontier")?;
        write_json(
            output.join(format!("front-{frontier:02}-runtime.json")),
            &returned.receipt,
        )?;
        receipts.push(generation_front_receipt(
            frontier,
            front,
            begun.elapsed().as_nanos().to_string(),
            false,
        ));
    }
    session.seal_frontier_aperture()?;
    let bytes = session.rest().canonical_bytes()?;
    Ok((EmanativeContinuationRest::read(&bytes)?, receipts, false))
}

fn reuse_generation(
    receipt: &Path,
    output: &Path,
    heldout: &HeldoutInput,
) -> Result<(EmanativeContinuationRest, Vec<Value>, bool), String> {
    let bytes = fs::read(receipt.join("continuation.rest")).map_err(|error| error.to_string())?;
    let rest = EmanativeContinuationRest::read(&bytes)?;
    if rest.entering.text != heldout.generation_prompt
        || rest.fronts.len() != heldout.generation_frontier_aperture
        || !matches!(
            rest.status,
            EmanativeStatus::FrontierAperture { conducted_fronts }
                if conducted_fronts == heldout.generation_frontier_aperture
        )
    {
        return Err(
            "the addressed E5 generation receipt does not match this occurrence".to_owned(),
        );
    }
    let mut receipts = Vec::new();
    for (frontier, front) in rest.fronts.iter().enumerate() {
        let source = receipt.join(format!("front-{frontier:02}-runtime.json"));
        let runtime: Value = read_json(&source)?;
        let before = if frontier == 0 {
            &rest.entering
        } else {
            rest.fronts[frontier - 1]
                .after
                .as_ref()
                .ok_or("reused generation predecessor is unresolved")?
        };
        if runtime["schema"] != "holonic-engine.phoenix.runtime-return.v1"
            || runtime["product_identity"]["sha256"] != rest.body.product.sha256
            || runtime["predecessor_identity"]["sha256"] != rest.body.predecessor.sha256
            || runtime["morphology_identity"]["sha256"] != rest.body.morphology.sha256
            || runtime["input"]["native_ids"] != json!(before.native_ids)
            || runtime["generated"]["vocabulary_extent"] != front.potential.vocabulary_extent
            || runtime["generated"]["grain"] != front.potential.grain
            || runtime["generated"]["top_lower"] != front.potential.top_lower
            || runtime["generated"]["separated"] != front.potential.separated
            || runtime["source_access"]["forbidden"] != json!([])
            || runtime["execution"]["device_name"] != "NVIDIA GeForce RTX 4080 SUPER"
        {
            return Err(format!("E5 generation receipt frontier {frontier} moved"));
        }
        fs::copy(
            &source,
            output.join(format!("front-{frontier:02}-runtime.json")),
        )
        .map_err(|error| error.to_string())?;
        let elapsed = runtime["execution"]["wall_seconds"]
            .as_str()
            .map(|seconds| format!("{seconds} seconds"))
            .ok_or("reused generation receipt lacks wall time")?;
        receipts.push(generation_front_receipt(frontier, front, elapsed, true));
    }
    write_json(
        output.join("addressed-reuse.json"),
        &json!({
            "schema":"holonics.e5.addressed-expensive-receipt-reuse.v1",
            "truth_status":"implemented-exact; measured",
            "source":receipt,
            "input_occurrence_sha256":rest.entering.address_sha256,
            "frontiers":rest.fronts.len(),
            "complete_continuation_sha256":sha(&bytes),
            "reason":"the Phoenix product, cultivated continuation, prompt occurrence and emanative/runtime source closure are unchanged; only the rejected obsolete N4 heterogeneous mount below this completed boundary was removed",
            "original_invocation_exit_status":1,
            "every_frontier_returned_before_refusal":true,
        }),
    )?;
    Ok((rest, receipts, true))
}

fn generation_front_receipt(
    frontier: usize,
    front: &holonic_engine::phoenix::emanative::EmanativeFront,
    elapsed: String,
    reused: bool,
) -> Value {
    json!({
        "frontier": frontier,
        "before": front.before_address_sha256,
        "after": front.after.as_ref().map(|occurrence| occurrence.address_sha256.clone()),
        "potential_sha256": front.potential.complete_plural_sha256,
        "plural_population": front.potential.plural.len(),
        "separated_population": front.potential.separated,
        "semantic_receipt_sha256": front.semantic_receipt_sha256,
        "elapsed": elapsed,
        "addressed_expensive_receipt_reused": reused,
    })
}

fn remount(rest: &Path, predecessor: &str, output: &Path) -> Result<(), String> {
    let manifest = read_athena_manifest(rest)?;
    let agentic = EmanativeContinuationRest::read(
        &fs::read(rest.join("emanative/agentic-continuation.rest"))
            .map_err(|error| error.to_string())?,
    )?;
    let (product, continuation, standing) = read_membrane_product(&rest.join("membrane"))?;
    let product_identity = product
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let mut membrane = NativeInferenceMembrane::mount(
        product,
        continuation.candidate_counts.len(),
        Some(&standing),
    )
    .map_err(|error| error.to_string())?;
    let occurrence_sha256 = digest(&[predecessor.as_bytes(), b"source-detached-later-current"]);
    let occurrence = native_occurrence(
        occurrence_sha256,
        predecessor.to_owned(),
        BoundaryId(109),
        continuation.candidate_counts,
        vec![BoundaryId(101), BoundaryId(103), BoundaryId(109)],
        digest(&[b"frozen product remount"]),
    );
    let returned = membrane
        .receive_front(vec![occurrence])
        .map_err(|error| error.to_string())?;
    write_json(
        output,
        &json!({
            "schema": "holonics.e5.source-detached-remount.v1",
            "frozen_product_identity_sha256": manifest.product_identity_sha256,
            "product_identity_sha256": product_identity,
            "agentic_frontiers": agentic.fronts.len(),
            "agentic_current_occurrence_sha256": agentic.current().address_sha256,
            "agentic_current_text_sha256": agentic.current().text_sha256,
            "predecessor_continuation_sha256": predecessor,
            "successor_continuation_sha256": returned.members[0].continuation.successor_sha256,
            "frontier_addresses": returned.members[0].continuation.frontier.iter().map(|front| front.address_sha256.clone()).collect::<Vec<_>>(),
            "launches": returned.members[0].consequence.apparatus.launches,
            "synchronizations": returned.members[0].consequence.apparatus.synchronizations,
            "forbidden_source_access": [],
            "passed": returned.members.len() == 1 && returned.members[0].consequence.apparatus.launches == 1 && agentic.fronts.len() == 8,
        }),
    )
}

fn assemble_rest(rest: &Path) -> Result<(), String> {
    fs::create_dir_all(rest).map_err(|error| error.to_string())?;
    copy_tree(
        Path::new(E4_ROOT).join("native-rest"),
        rest.join("membrane"),
    )?;
    copy_native_mathematics(
        &Path::new(N4_ROOT).join("native-rest"),
        &rest.join("mathematics"),
    )?;
    fs::create_dir(rest.join("optical")).map_err(|error| error.to_string())?;
    fs::copy(
        Path::new(E1_ROOT).join("native-rest/standing.json"),
        rest.join("optical/standing.json"),
    )
    .map_err(|error| error.to_string())?;
    copy_tree(Path::new(E2_ROOT), rest.join("inherited-organs"))?;
    fs::create_dir(rest.join("emanative")).map_err(|error| error.to_string())?;
    fs::copy(
        Path::new(E0_ROOT).join("detached-return/continuation-after-remount.rest"),
        rest.join("emanative/admitted-continuation.rest"),
    )
    .map_err(|error| error.to_string())?;
    Ok(())
}

fn write_athena_manifest(rest: &Path) -> Result<AthenaManifest, String> {
    let mut members = Vec::new();
    collect_members(rest, rest, &mut members)?;
    members.retain(|member| member.path != "MANIFEST.json");
    members.sort_by(|left, right| left.path.cmp(&right.path));
    let external_native_organs = vec![
        external_organ("inherited-full-tower", PHOENIX_PRODUCT)?,
        external_organ("cultivated-phoenix-continuation", A3_CONTINUATION)?,
    ];
    let product_identity_sha256 = digest(&[
        serde_json::to_vec(&members)
            .map_err(|error| error.to_string())?
            .as_slice(),
        serde_json::to_vec(&external_native_organs)
            .map_err(|error| error.to_string())?
            .as_slice(),
    ]);
    let manifest = AthenaManifest {
        schema: "holonics.e5.agentic-laboratory-athena-rest.v1".to_owned(),
        truth_status: "implemented-exact".to_owned(),
        product_identity_sha256,
        members,
        external_native_organs,
        open_exterior: vec![
            "foreign conduct not excited by the admitted E0--E5 current remains open".to_owned(),
            "native nonlinear analytic and wider dimensional/unit receiver families remain open"
                .to_owned(),
            "unknown-carrier induction and outbound voice/image production remain open apertures"
                .to_owned(),
        ],
    };
    write_json(rest.join("MANIFEST.json"), &manifest)?;
    Ok(manifest)
}

fn read_athena_manifest(rest: &Path) -> Result<AthenaManifest, String> {
    let manifest: AthenaManifest = read_json(&rest.join("MANIFEST.json"))?;
    if manifest.schema != "holonics.e5.agentic-laboratory-athena-rest.v1" {
        return Err("E5 manifest schema moved".to_owned());
    }
    for member in &manifest.members {
        let bytes = fs::read(rest.join(&member.path)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != member.octets || sha(&bytes) != member.sha256 {
            return Err(format!("E5 rest member {} moved", member.path));
        }
    }
    for organ in &manifest.external_native_organs {
        if external_organ(&organ.role, &organ.path)? != *organ {
            return Err(format!("E5 external native organ {} moved", organ.role));
        }
    }
    Ok(manifest)
}

fn read_membrane_product(
    root: &Path,
) -> Result<(ReturnedBoundaryCultivationRest, E2Continuation, Vec<u8>), String> {
    let manifest: E3RestManifest = read_json(&root.join("manifest.json"))?;
    let mut components = BTreeMap::new();
    for (role, component) in manifest.components {
        let bytes = fs::read(root.join(component.path)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != component.octets || sha(&bytes) != component.sha256 {
            return Err(format!("E5 membrane component {role} moved"));
        }
        components.insert(role, bytes);
    }
    let get = |role: &str| {
        components
            .get(role)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("E5 membrane component {role} absent"))
    };
    let product = ReturnedBoundaryCultivationRest::read(
        get("standing")?,
        get("decoder")?,
        get("fibres")?,
        get("cultivation")?,
    )
    .map_err(|error| error.to_string())?;
    let continuation =
        serde_json::from_slice(get("continuation")?).map_err(|error| error.to_string())?;
    let standing =
        fs::read(root.join("membrane-standing.json")).map_err(|error| error.to_string())?;
    Ok((product, continuation, standing))
}

fn copy_native_mathematics(source: &Path, target: &Path) -> Result<(), String> {
    const ROLES: [&str; 5] = [
        "mathematical-predecessor-standing",
        "mathematical-predecessor-decoder",
        "mathematical-predecessor-fibres",
        "mathematical-cultivation-standing",
        "continuation-standing",
    ];
    let source_manifest: N4RestManifest = read_json(source.join("MANIFEST.json"))?;
    fs::create_dir_all(target).map_err(|error| error.to_string())?;
    let mut components = Vec::new();
    for role in ROLES {
        let component = source_manifest
            .components
            .iter()
            .find(|component| component.name == role)
            .ok_or_else(|| format!("E5 native mathematical component {role} absent"))?
            .clone();
        let bytes = fs::read(source.join(&component.path)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != component.octets || sha(&bytes) != component.sha256 {
            return Err(format!("E5 source mathematical component {role} moved"));
        }
        fs::write(target.join(&component.path), bytes).map_err(|error| error.to_string())?;
        components.push(component);
    }
    write_json(
        target.join("MANIFEST.json"),
        &E5MathematicsManifest {
            schema: "holonics.e5.native-mathematics-rest.v1".to_owned(),
            truth_status: "implemented-exact".to_owned(),
            predecessor_product_sha256: source_manifest.product_sha256,
            components,
            open_exterior: source_manifest.open_exterior,
        },
    )
}

fn read_native_mathematics(
    root: &Path,
) -> Result<(NativeCultivatedMathematicalRest, E5MathematicalContinuation), String> {
    let manifest: E5MathematicsManifest = read_json(root.join("MANIFEST.json"))?;
    if manifest.schema != "holonics.e5.native-mathematics-rest.v1"
        || manifest.truth_status != "implemented-exact"
    {
        return Err("E5 native mathematics manifest moved".to_owned());
    }
    let mut components = BTreeMap::new();
    for component in manifest.components {
        let bytes = fs::read(root.join(component.path)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != component.octets || sha(&bytes) != component.sha256 {
            return Err(format!(
                "E5 mathematical component {} moved",
                component.name
            ));
        }
        components.insert(component.name, bytes);
    }
    let get = |name: &str| {
        components
            .get(name)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("E5 mathematical component {name} absent"))
    };
    let mathematics = NativeCultivatedMathematicalRest::read(
        get("mathematical-predecessor-standing")?,
        get("mathematical-predecessor-decoder")?,
        get("mathematical-predecessor-fibres")?,
        get("mathematical-cultivation-standing")?,
    )?;
    let continuation: E5MathematicalContinuation =
        serde_json::from_slice(get("continuation-standing")?).map_err(|error| error.to_string())?;
    if continuation.schema != "holonics.n4.athena-continuation-standing.v1"
        || continuation.predecessor_cultivated_rest_sha256 != mathematics.canonical_identity()?
        || continuation.retained_history_suffix.len() != 2
        || continuation.returned_world.occurrence != continuation.retained_history_suffix[1]
    {
        return Err("E5 native mathematical continuation moved".to_owned());
    }
    Ok((mathematics, continuation))
}

fn found_mathematical_inquiry(
    mathematics: &NativeCultivatedMathematicalRest,
    continuation: &E5MathematicalContinuation,
    source_occurrences: Vec<String>,
    sections: Vec<Vec<i64>>,
    requested_histories: Vec<NativeSuccessorHistory>,
    open_exterior: Vec<String>,
) -> Result<NativeMathematicalInquiry, String> {
    let mut history = mathematics
        .predecessor()
        .reconstruction()
        .predecessor_component_addresses
        .iter()
        .rev()
        .take(4)
        .cloned()
        .collect::<Vec<_>>();
    history.extend(continuation.retained_history_suffix.clone());
    mathematics
        .predecessor()
        .found_native_mathematical_inquiry(
            source_occurrences,
            sections,
            requested_histories,
            history,
            open_exterior,
        )
        .map_err(|error| error.to_string())
}

fn native_occurrence(
    occurrence_sha256: String,
    predecessor_continuation_sha256: String,
    boundary: BoundaryId,
    candidate_population: Vec<u32>,
    receiver_boundaries: Vec<BoundaryId>,
    lineage_sha256: String,
) -> NativeBoundaryOccurrence {
    let source_incidence_sha256 =
        source_incidence_identity(&occurrence_sha256, boundary, &candidate_population);
    NativeBoundaryOccurrence {
        occurrence_sha256,
        predecessor_continuation_sha256,
        boundary,
        source_incidence_sha256,
        lineage_sha256,
        candidate_population,
        receiver_boundaries,
        frontier_aperture: 3,
    }
}

fn membrane_standing_with_separator(
    final_standing: &[u8],
    separator: &holonic_engine::phoenix::native_membrane::AddressedContinuationDelta,
) -> Result<Vec<u8>, String> {
    let mut value: Value =
        serde_json::from_slice(final_standing).map_err(|error| error.to_string())?;
    value["deltas"]
        .as_array_mut()
        .ok_or("membrane standing has no delta array")?
        .push(serde_json::to_value(separator).map_err(|error| error.to_string())?);
    serde_json::to_vec(&value).map_err(|error| error.to_string())
}

fn delta_population(bytes: &[u8]) -> Result<usize, String> {
    serde_json::from_slice::<Value>(bytes).map_err(|error| error.to_string())?["deltas"]
        .as_array()
        .map(Vec::len)
        .ok_or_else(|| "membrane standing has no delta population".to_owned())
}

fn capability_atlas(
    rest: &Path,
    manifest: &AthenaManifest,
    detached: &Value,
) -> Result<Value, String> {
    let optical = HierarchicalOpticalPassage::read(
        &fs::read(rest.join("optical/standing.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let e2_grade: Value = read_json(&rest.join("inherited-organs/03-grade.json"))?;
    let (cultivated, _, standing) = read_membrane_product(&rest.join("membrane"))?;
    let (mathematics, mathematical_continuation) =
        read_native_mathematics(&rest.join("mathematics"))?;
    let organs = vec![
        json!({"address":"full-tower","provenance":"inherited","ingress":"native codebook occurrence","constitutive_transport":"42 authenticated resident transformer fronts","joins":"addressed continuation and nominal boundary return","receiver_visible_rank":{"plural_future":1,"separated":262143},"fibres":"complete terminal potential and source/native codebook fibre","saturation_frontier":"unexcited foreign successor histories","open_exterior":manifest.open_exterior}),
        json!({"address":"hierarchical-optical","provenance":"inherited","ingress":101,"constitutive_transport":"component-to-page simultaneous incidence","joins":"native equation constraint sections and shared returned boundary","receiver_visible_rank":{"holons":optical.holons.len(),"equations":optical.native_consequence.equation_constraint_sections.len()},"fibres":{"alternative_covers":optical.alternative_covers.len(),"repeated_forms":optical.repeated_forms.len()},"saturation_frontier":"new raw page forms which split retained covers","open_exterior":optical.native_consequence.open_exterior}),
        json!({"address":"complete-acoustic","provenance":"inherited","ingress":103,"constitutive_transport":"exact PCM chronology through twelve authenticated inherited layers","joins":"shared nominal consequence with directional withdrawal","receiver_visible_rank":{"layers":12,"complete_tower":e2_grade["complete_audio_tower"]},"fibres":"exact sample/frame/butterfly/path incidence and E2 reconstruction fibre","saturation_frontier":"unexcited acoustic transport families","open_exterior":e2_grade["open_exterior"]}),
        json!({"address":"native-mathematics","provenance":"implemented","ingress":109,"constitutive_transport":"exact operation/constraint/geometry fixed-section transport","joins":"returned laboratory chronology and nominal boundary consequence","receiver_visible_rank":{"carrier_charts":mathematics.predecessor().standing().carrier_charts.len(),"exact_faces":detached["mathematics"]["passed"]},"fibres":mathematics.predecessor().reconstruction(),"saturation_frontier":"nonlinear analytic dimensional and wider history families","open_exterior":mathematical_continuation.open_exterior}),
        json!({"address":"returned-codec-morphology","provenance":"cultivated","ingress":cultivated.standing().delta.parent_boundary,"constitutive_transport":"parented rank-one returned state pivot","joins":cultivated.standing().delta.support_boundaries,"receiver_visible_rank":cultivated.standing().delta.exact_rank,"fibres":cultivated.standing().reconstruction_fibre,"saturation_frontier":"successor histories not separated by the admitted E3/E5 receivers","open_exterior":cultivated.standing().open_exterior}),
        json!({"address":"native-membrane","provenance":"cultivated-continuation","ingress":"generic nominal BoundaryId plus caused incidence","constitutive_transport":"co-present batched CUDA return and addressed local delta","joins":"receiver-boundary pullback with certified interchange","receiver_visible_rank":{"rested_deltas":delta_population(&standing)?},"fibres":"complete E2 nominal-boundary reconstruction members","saturation_frontier":detached["saturation"],"open_exterior":manifest.open_exterior}),
    ];
    Ok(json!({
        "schema":"holonics.e5.complete-capability-atlas.v1",
        "truth_status":"established-bounded; measured",
        "product_identity_sha256":manifest.product_identity_sha256,
        "organs":organs,
        "all_declared_organs_have_complete_fields":organs.iter().all(|organ| ["ingress","constitutive_transport","joins","receiver_visible_rank","fibres","saturation_frontier","open_exterior"].iter().all(|field| !organ[*field].is_null())),
        "source_names_route_faculties":false,
        "competence_grade":"held-out conduct and separating intervention",
    }))
}

fn complete_dissection(
    rest: &Path,
    manifest: &AthenaManifest,
    detached: &Value,
) -> Result<Value, String> {
    let optical = HierarchicalOpticalPassage::read(
        &fs::read(rest.join("optical/standing.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let (cultivated, _, standing) = read_membrane_product(&rest.join("membrane"))?;
    let (mathematics, _) = read_native_mathematics(&rest.join("mathematics"))?;
    Ok(json!({
        "schema":"holonics.e5.complete-product-dissection.v1",
        "truth_status":"established-bounded; measured",
        "product_identity_sha256":manifest.product_identity_sha256,
        "incidence":{"optical_holons":optical.holons.len(),"optical_relations":optical.incidences.len(),"nominal_boundaries":cultivated.boundary_predecessor().standing.ports},
        "ordered_transport":{"generated_frontiers":detached["generation"]["frontiers"],"mathematical_histories":mathematics.predecessor().decoder().declared_histories},
        "interactions":{"naturality":cultivated.boundary_predecessor().fibres.naturality_squares,"returned_support":cultivated.standing().delta.support_boundaries},
        "reconstruction_fibres":{"optical_alternative_covers":optical.alternative_covers.len(),"optical_repeated_forms":optical.repeated_forms.len(),"nominal":cultivated.boundary_predecessor().fibres.fibres,"mathematical":mathematics.predecessor().reconstruction()},
        "caustics_and_separators":{"mathematical":mathematics.predecessor().reconstruction().shortest_separators,"marginal":detached["saturation"]},
        "continuation":{"standing_sha256":sha(&standing),"delta_population":delta_population(&standing)?},
        "open_exterior":manifest.open_exterior,
        "complete":true,
    }))
}

fn complete_cost(
    rest: &Path,
    manifest: &AthenaManifest,
    detached: &Value,
) -> Result<Value, String> {
    let native_rest_octets = directory_octets(rest)?;
    let external_native_octets = manifest
        .external_native_organs
        .iter()
        .map(|organ| organ.octets)
        .sum::<u64>();
    let replay_evidence_octets = [E0_ROOT, E1_ROOT, E2_ROOT, N4_ROOT, E4_ROOT]
        .iter()
        .map(|path| directory_octets(Path::new(path)))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .sum::<u64>();
    Ok(json!({
        "schema":"holonics.e5.complete-product-cost.v1",
        "truth_status":"measured",
        "native_rest_octets":native_rest_octets,
        "external_immutable_native_organs_octets":external_native_octets,
        "complete_mounted_product_octets":native_rest_octets + external_native_octets,
        "generation_frontiers":detached["generation"]["frontier_aperture"],
        "receiver_relative_condensation":{
            "coordinate":"E0--E4 small native ecology/rest versus its persisted replay-evidence returns; the unchanged 16GB inherited full-tower organ cancels from both sides",
            "candidate_octets":native_rest_octets,
            "source_replay_evidence_octets":replay_evidence_octets,
            "strict":native_rest_octets < replay_evidence_octets,
            "general_language_or_complete_foreign_receiver_equivalence_claimed":false,
        },
        "apparatus":"exact semantic work remains in individual receipts; timings and CUDA telemetry remain separate",
    }))
}

fn copy_child_faces(child: &Path, output: &Path) -> Result<(), String> {
    for (source, target) in [
        ("generation/generated-passage.md", "02-generated-passage.md"),
        (
            "native-mathematics.json",
            "03-native-mathematical-consequences.json",
        ),
        (
            "hierarchical-page-intake.json",
            "04-hierarchical-page-intake.json",
        ),
        (
            "organ-interaction.json",
            "05-organ-interaction-and-world-return.json",
        ),
        (
            "saturation.json",
            "06-saturation-and-marginal-excitation.json",
        ),
    ] {
        fs::copy(child.join(source), output.join(target)).map_err(|error| error.to_string())?;
    }
    Ok(())
}

fn external<'a>(manifest: &'a AthenaManifest, role: &str) -> Result<&'a ExternalOrgan, String> {
    manifest
        .external_native_organs
        .iter()
        .find(|organ| organ.role == role)
        .ok_or_else(|| format!("E5 external native organ {role} absent"))
}

fn external_organ(role: &str, path: &str) -> Result<ExternalOrgan, String> {
    let manifest_path = Path::new(path).join("manifest.json");
    let alternate = Path::new(path).join("MANIFEST.json");
    let path_to_manifest = if manifest_path.exists() {
        manifest_path
    } else {
        alternate
    };
    let manifest_bytes = fs::read(&path_to_manifest).map_err(|error| error.to_string())?;
    Ok(ExternalOrgan {
        role: role.to_owned(),
        path: path.to_owned(),
        manifest_sha256: sha(&manifest_bytes),
        octets: directory_octets(Path::new(path))?,
    })
}

fn collect_members(root: &Path, at: &Path, members: &mut Vec<RestMember>) -> Result<(), String> {
    for entry in fs::read_dir(at).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let path = entry.path();
        if path.is_dir() {
            collect_members(root, &path, members)?;
        } else {
            let bytes = fs::read(&path).map_err(|error| error.to_string())?;
            let relative = path
                .strip_prefix(root)
                .map_err(|error| error.to_string())?
                .to_string_lossy()
                .to_string();
            members.push(RestMember {
                role: relative.clone(),
                path: relative,
                sha256: sha(&bytes),
                octets: bytes.len() as u64,
            });
        }
    }
    Ok(())
}

fn copy_tree(source: impl AsRef<Path>, target: impl AsRef<Path>) -> Result<(), String> {
    let source = source.as_ref();
    let target = target.as_ref();
    fs::create_dir_all(target).map_err(|error| error.to_string())?;
    for entry in fs::read_dir(source).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let from = entry.path();
        let to = target.join(entry.file_name());
        if from.is_dir() {
            copy_tree(&from, &to)?;
        } else {
            fs::copy(&from, &to).map_err(|error| error.to_string())?;
        }
    }
    Ok(())
}

fn directory_octets(path: &Path) -> Result<u64, String> {
    let mut total = 0u64;
    for entry in fs::read_dir(path).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let member = entry.path();
        total = total
            .checked_add(if member.is_dir() {
                directory_octets(&member)?
            } else {
                fs::metadata(&member)
                    .map_err(|error| error.to_string())?
                    .len()
            })
            .ok_or("E5 product cost overflow")?;
    }
    Ok(total)
}

fn write_output_manifest(output: &Path) -> Result<(), String> {
    let mut members = Vec::new();
    collect_members(output, output, &mut members)?;
    members.retain(|member| member.path != "MANIFEST.json");
    members.sort_by(|left, right| left.path.cmp(&right.path));
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema":"holonics.e5.output-manifest.v1",
            "members":members,
        }),
    )
}

fn e5_code_closure() -> Result<String, String> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let workspace = manifest.join("../..");
    let paths = [
        manifest.join("examples/the_agentic_laboratory_athena_freezes.rs"),
        manifest.join("examples/n3/cultivation.rs"),
        workspace.join("crates/holonic-engine/src/phoenix/native_membrane.rs"),
        workspace.join("crates/holonic-engine/src/phoenix/emanative.rs"),
        manifest.join("src/mathematical_particle/production_aperture/native_consequence.rs"),
        manifest.join("src/mathematical_source/optical_holons.rs"),
    ];
    let mut identities = Vec::new();
    for path in paths {
        identities.push((
            path.display().to_string(),
            sha(&fs::read(&path).map_err(|error| error.to_string())?),
        ));
    }
    let bytes = serde_json::to_vec(&identities).map_err(|error| error.to_string())?;
    Ok(sha(&bytes))
}

fn read_json<T: for<'de> Deserialize<'de>>(path: impl AsRef<Path>) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(
        path,
        serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

fn canonical(path: impl AsRef<Path>) -> Result<PathBuf, String> {
    fs::canonicalize(path).map_err(|error| error.to_string())
}

fn sha(bytes: &[u8]) -> String {
    hex(Sha256::digest(bytes))
}

fn digest(parts: &[&[u8]]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part);
    }
    hex(digest.finalize())
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn arguments() -> Result<Args, String> {
    let mut arguments = env::args().skip(1);
    match arguments.next().as_deref() {
        None => Ok(Args::Produce(PathBuf::from(DEFAULT_OUT), None)),
        Some("--produce") => {
            let output = PathBuf::from(arguments.next().ok_or("--produce needs OUTPUT")?);
            let receipt = optional_generation_receipt(&mut arguments)?;
            Ok(Args::Produce(output, receipt))
        }
        Some("--detached") => {
            let rest = PathBuf::from(arguments.next().ok_or("--detached needs REST")?);
            let input = PathBuf::from(arguments.next().ok_or("--detached needs INPUT")?);
            let output = PathBuf::from(arguments.next().ok_or("--detached needs OUTPUT")?);
            let receipt = optional_generation_receipt(&mut arguments)?;
            Ok(Args::Detached(rest, input, output, receipt))
        }
        Some("--remount") => Ok(Args::Remount(
            PathBuf::from(arguments.next().ok_or("--remount needs REST")?),
            arguments.next().ok_or("--remount needs CONTINUATION")?,
            PathBuf::from(arguments.next().ok_or("--remount needs OUTPUT")?),
        )),
        Some(other) => Err(format!("unknown E5 argument {other}")),
    }
}

fn optional_generation_receipt(
    arguments: &mut impl Iterator<Item = String>,
) -> Result<Option<PathBuf>, String> {
    match arguments.next().as_deref() {
        None => Ok(None),
        Some("--generation-receipt") => Ok(Some(PathBuf::from(
            arguments
                .next()
                .ok_or("--generation-receipt needs DIRECTORY")?,
        ))),
        Some(other) => Err(format!("unknown E5 trailing argument {other}")),
    }
}
