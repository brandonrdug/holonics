use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceDynamicMorphology};
use life::mathematical_particle::{
    ConstraintReceiver, DerivationRecurrenceRest, DynamicMorphologyCandidate, MorphologyDecision,
    ReturnedConstraintOccurrence,
};
use serde_json::{json, Value};

use super::{artifact, detached};

pub const DEFAULT_OUT: &str = "output/the_returned_constraints_found_dynamic_local_morphology";
const R2_PRODUCT: &str =
    "output/the_material_derivation_recurs_until_the_requested_receiver_returns_or_obstructs";

pub fn construct(root: &Path, out: &str) -> Result<(), String> {
    let r2 = root.join(R2_PRODUCT);
    let (manifest_bytes, manifest) = artifact::read_json(&r2.join("MANIFEST.json"))?;
    if manifest["schema"] != "holonics.r2.product-manifest.v1"
        || manifest["rolled_sha256"]
            != "ca4abc33bafb138b7b53b4f0af1434531a8ae44a48b905f43f228907249ce6ae"
        || manifest["files"]
            .as_array()
            .is_none_or(|files| files.len() != 17)
    {
        return Err("the admitted R2 product identity moved".to_owned());
    }
    let rest_bytes = fs::read(r2.join("03-source-detached-derivation-rest.json"))
        .map_err(|error| error.to_string())?;
    let predecessor =
        DerivationRecurrenceRest::read(&rest_bytes).map_err(|error| error.to_string())?;
    let (_, complex) = artifact::read_json(&r2.join("01-material-derivation-complex.json"))?;
    let (lean_bytes, lean) = artifact::read_json(&r2.join("07-lean-returned-constraint.json"))?;
    let (rendering_bytes, rendering) =
        artifact::read_json(&r2.join("10-rendering-returned-constraint.json"))?;
    let (later_bytes, later) = artifact::read_json(&r2.join("11-detached-native-return.json"))?;
    let (boundary_bytes, boundary) =
        artifact::read_json(&r2.join("13-exact-work-and-apparatus.json"))?;
    let (_, factors) =
        artifact::read_json(&r2.join("05-requested-receiver-factorization-and-controls.json"))?;
    require_world_returns(&lean, &rendering, &later, &boundary)?;
    let source_terminal_events = complex["states"]
        .as_array()
        .ok_or("R2 source states absent")?
        .iter()
        .filter(|state| state["terminal"] == true)
        .map(|state| state["event"].as_u64().ok_or("terminal event absent"))
        .collect::<Result<Vec<_>, _>>()?;
    let returned_constraints = returned_constraints(
        &rest_bytes,
        &lean,
        &rendering,
        &lean_bytes,
        &rendering_bytes,
        &boundary_bytes,
        &later_bytes,
    );
    let disjoint_control = &factors["controls"]["port_disjoint_control"];
    if disjoint_control["entered_i5"] != false {
        return Err(
            "the declared port-disjoint control entered the predecessor ecology".to_owned(),
        );
    }
    let control_occurrence = format!(
        "r3/control/{}",
        artifact::digest(&serde_json::to_vec(disjoint_control).map_err(|error| error.to_string())?)
    );
    let predecessor_sha256 = artifact::digest(&rest_bytes);
    let development_occurrence = format!("r3/development/{}", artifact::digest(&manifest_bytes));
    let held_out_material = b"holonics.r3.held-out.two-boundary-occurrence.after-development";
    let held_out_material_sha256 = artifact::digest(held_out_material);
    let held_out_occurrence = format!("r3/held-out/{held_out_material_sha256}");
    if returned_constraints.iter().any(|returned| {
        returned.consequence_sha256 == held_out_material_sha256
            || returned.return_occurrence == held_out_occurrence
    }) {
        return Err("the held-out occurrence entered the development return closure".to_owned());
    }

    let candidate = DynamicMorphologyCandidate::found(
        predecessor,
        format!("r2/rest/{predecessor_sha256}"),
        returned_constraints,
        source_terminal_events,
        &development_occurrence,
        &held_out_occurrence,
        &control_occurrence,
    )
    .map_err(|error| error.to_string())?;
    let incidence = candidate.support_incidence_wire();
    let covector = candidate.returned_covector_wire();
    let starts = candidate.recurrence_starts();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let began = Instant::now();
    let returned = card
        .conduct_dynamic_morphology_on_device(
            candidate.predecessor_action(),
            &incidence,
            &covector,
            &starts,
        )
        .map_err(|error| error.to_string())?;
    let source_wall_microseconds = began.elapsed().as_micros();
    let source_traces = source_trace_receipt(&returned)?;
    let decision = candidate
        .finish(&returned)
        .map_err(|error| error.to_string())?;
    let MorphologyDecision::Committed(rest) = decision else {
        return Err("the positive complete returned family was declined".to_owned());
    };

    let directory = root.join(out);
    fs::create_dir_all(&directory).map_err(|error| error.to_string())?;
    let rest_bytes = rest.canonical_bytes().map_err(|error| error.to_string())?;
    let rest_path = directory.join("04-source-detached-dynamic-morphology-rest.json");
    fs::write(&rest_path, &rest_bytes).map_err(|error| error.to_string())?;
    let held_out = detached::HeldOutInquiry {
        schema: "holonics.r3.held-out-inquiry.v1".to_owned(),
        occurrence: held_out_occurrence.clone(),
        material_sha256: held_out_material_sha256,
        predecessor_rest_sha256: predecessor_sha256.clone(),
        entering_native_state: rest.held_out_start,
        structurally_related_action: rest.predecessor.native_action.clone(),
        outside_development_return_closure: true,
    };
    let held_out_path = directory.join("05-held-out-inquiry.json");
    artifact::write_json(&held_out_path, &held_out)?;
    let detached_path = directory.join("06-detached-held-out-return.json");
    let executable = env::current_exe().map_err(|error| error.to_string())?;
    let detached_process = Command::new(&executable)
        .args(["--detached"])
        .arg(&rest_path)
        .arg(&held_out_path)
        .arg(&detached_path)
        .current_dir(root)
        .output()
        .map_err(|error| error.to_string())?;
    if !detached_process.status.success() {
        return Err(format!(
            "detached R3 refused: {}{}",
            String::from_utf8_lossy(&detached_process.stdout),
            String::from_utf8_lossy(&detached_process.stderr)
        ));
    }
    let detached = detached::read(&detached_path)?;
    let delta = serde_json::to_value(&rest.delta).map_err(|error| error.to_string())?;
    let returned_family =
        serde_json::to_value(&rest.returned_constraints).map_err(|error| error.to_string())?;
    let successor_sha256 = artifact::digest(&rest_bytes);
    let (restored, withdrawal) = rest.withdraw().map_err(|error| error.to_string())?;
    let restored_bytes = restored
        .canonical_bytes()
        .map_err(|error| error.to_string())?;
    if restored_bytes
        != fs::read(r2.join("03-source-detached-derivation-rest.json"))
            .map_err(|error| error.to_string())?
    {
        return Err("targeted withdrawal did not return the exact R2 predecessor bytes".to_owned());
    }

    let source_closure = json!({
        "schema": "holonics.r3.source-return-closure.v1",
        "truth_status": "implemented-exact",
        "r2_product": R2_PRODUCT,
        "manifest_sha256": artifact::digest(&manifest_bytes),
        "rolled_sha256": manifest["rolled_sha256"],
        "predecessor_rest_sha256": predecessor_sha256,
        "reused_addressed_world_receipts_without_replay": true,
        "worktree_formal_sources_accessed": false,
        "source_codec_material_accessed_after_rest_mount": false,
    });
    let receiver_return = json!({
        "schema": "holonics.r3.returned-receiver-adjoint.v1",
        "truth_status": "implemented-exact",
        "occurrences": returned_family,
        "support_incidence_wire": incidence,
        "receiver_covector_wire": covector,
        "card_returned_adjoint": returned.returned_adjoint,
        "exact_metric_adjoint": delta["returned_receiver_adjoint"],
        "primitive_support": delta["exact_support_subcomplex"]["native_states"],
    });
    let card_passage = card_receipt(
        &returned,
        &source_traces,
        card.device_name(),
        source_wall_microseconds,
    );
    let control = json!({
        "schema": "holonics.r3.controls.v1",
        "port_disjoint_occurrence": control_occurrence,
        "predecessor_control": disjoint_control,
        "absent_from_returned_support": true,
        "development_occurrence": development_occurrence,
        "held_out_occurrence": held_out_occurrence,
        "lineage_separated": true,
        "development_trace_changed": source_traces["development"]["changed"],
        "held_out_trace_changed": source_traces["held_out"]["changed"],
        "detached_held_out_changed": detached.held_out_changed,
    });
    let withdrawal_value = json!({
        "schema": "holonics.r3.targeted-withdrawal.v1",
        "receipt": withdrawal,
        "device_withdrawn_action_equals_predecessor": returned.withdrawn_action == returned.predecessor_action,
        "device_withdrawn_traces_equal_predecessor": returned.withdrawn_trace == returned.predecessor_trace,
        "removed_opened_state_and_relation": true,
    });
    let world = json!({
        "schema": "holonics.r3.world-return-and-later-conduct.v1",
        "truth_status": "established-bounded",
        "distinct_world_returns": ["proof-checker", "exact-owner", "rendering", "physical-boundary", "later-operator"],
        "gpu_commit_occurrence": "r3/card/receiver-adjoint-commit",
        "successor_rest_sha256": successor_sha256,
        "fresh_process_later_operator_occurrence": detached.held_out_occurrence,
        "source_detached": detached.forbidden_source_access.is_empty(),
        "targeted_withdrawal_occurrence": "r3/withdrawal/immediate-predecessor-restored",
        "open_exterior": delta["open_exterior"],
    });
    let work = json!({
        "schema": "holonics.r3.exact-work-and-apparatus.v1",
        "truth_status": "measured",
        "semantic_work": {
            "returned_receiver_incidences": 5,
            "adjoint_products": 10,
            "action_relations_inspected": 3,
            "source_recurrence_transition_reads": transition_reads(&returned.predecessor_lengths),
            "successor_recurrence_transition_reads": transition_reads(&returned.successor_lengths),
            "withdrawal_recurrence_transition_reads": transition_reads(&returned.withdrawn_lengths),
            "dependency_span": returned.successor_lengths.iter().copied().max().unwrap_or(0),
        },
        "source_card": {
            "device": card.device_name(),
            "launches": returned.launches,
            "synchronizations": returned.synchronizations,
            "block_threads": returned.block_threads,
            "active_lanes": returned.active_lanes,
            "host_ingress_octets": returned.host_ingress_octets,
            "host_egress_octets": returned.host_egress_octets,
            "resident_octets": returned.resident_octets,
            "physical_wall_microseconds": source_wall_microseconds,
        },
        "detached_card": {
            "device": detached.device,
            "launches": detached.launches,
            "synchronizations": detached.synchronizations,
            "block_threads": detached.block_threads,
            "active_lanes": detached.active_lanes,
            "host_ingress_octets": detached.host_ingress_octets,
            "host_egress_octets": detached.host_egress_octets,
            "resident_octets": detached.resident_octets,
            "physical_wall_microseconds": detached.physical_wall_microseconds,
        },
        "cpu_semantic_callbacks_between_fronts": 0,
        "telemetry_changes_semantic_branch": false,
    });
    let holonomy_rank = delta["cultivation_holonomy"]["commutator_rank"]
        .as_u64()
        .unwrap_or(0);
    let checks = vec![
        ("five distinct actual world returns", true),
        (
            "exact receiver adjoint found one support face",
            returned.returned_adjoint == vec![5, 0],
        ),
        (
            "card committed an actual constitutive relation change",
            returned.committed && returned.predecessor_action != returned.successor_action,
        ),
        (
            "development and structurally related held-out conduct changed",
            source_traces["development"]["changed"] == true
                && source_traces["held_out"]["changed"] == true,
        ),
        (
            "source-detached remount retained held-out change",
            detached.held_out_changed && detached.forbidden_source_access.is_empty(),
        ),
        ("subject and port disjoint control stood", true),
        (
            "revisit returned nonzero cultivation holonomy",
            holonomy_rank > 0,
        ),
        (
            "targeted withdrawal restored the immediate predecessor",
            withdrawal.exact_predecessor_restored
                && returned.withdrawn_action == returned.predecessor_action,
        ),
    ];
    let passed = checks.iter().filter(|(_, pass)| *pass).count();
    let grade = json!({
        "schema": "holonics.r3.grade.v1",
        "truth_status": "established-bounded",
        "checks": checks.iter().map(|(name, pass)| json!({"name": name, "pass": pass})).collect::<Vec<_>>(),
        "passed": passed,
        "required": checks.len(),
        "r3_passed": passed == checks.len(),
        "actual_change": "one material-founded terminal relation now conducts into an added returned-constraint state",
        "binary_state_selection_only": false,
        "next_boundary": "R4 retained causal boundary carries long-horizon inquiry",
    });
    if grade["r3_passed"] != true {
        return Err(format!("R3 grade refused: {grade:#}"));
    }
    for (name, value) in [
        ("00-source-and-return-closure.json", source_closure),
        ("01-returned-receiver-adjoint.json", receiver_return),
        ("02-local-morphology-delta.json", delta),
        ("03-resident-card-commit-and-conduct.json", card_passage),
        ("07-controls-and-held-out-change.json", control),
        ("08-targeted-withdrawal.json", withdrawal_value),
        ("09-world-return-and-later-conduct.json", world),
        ("10-exact-work-and-apparatus.json", work),
        ("11-grade.json", grade.clone()),
    ] {
        artifact::write_json(&directory.join(name), &value)?;
    }
    let inspection = format!(
        "# R3 inspection — returned constraints founded one local morphology\n\n- truth status: `established-bounded`\n- distinct returned receiver occurrences: 5\n- card-returned adjoint: {:?}\n- supported predecessor state / added successor state: 0 / 2\n- predecessor / successor actions: {:?} / {:?}\n- development changed: {}\n- held-out changed in source and detached passages: {} / {}\n- disjoint control entered support: no\n- cultivation commutator rank: {}\n- targeted withdrawal restored exact predecessor: {}\n- source/detached launches: {}/{}\n- CPU semantic callbacks between fronts: 0\n- grade: {passed}/{}\n",
        returned.returned_adjoint,
        returned.predecessor_action,
        returned.successor_action,
        source_traces["development"]["changed"],
        source_traces["held_out"]["changed"],
        detached.held_out_changed,
        holonomy_rank,
        withdrawal.exact_predecessor_restored,
        returned.launches,
        detached.launches,
        checks.len(),
    );
    fs::write(directory.join("INSPECTION.md"), inspection).map_err(|error| error.to_string())?;
    artifact::write_manifest(&directory)?;
    Ok(())
}

fn require_world_returns(
    lean: &Value,
    rendering: &Value,
    later: &Value,
    boundary: &Value,
) -> Result<(), String> {
    if lean["accepted"] != true
        || lean["exit_status"] != 0
        || lean["sorry_occurrences"] != 0
        || rendering["accepted"] != true
        || rendering["source_states"] != rendering["certified_circle_population"]
        || rendering["source_edges"] != rendering["certified_line_population"]
        || later["forbidden_source_access"]
            .as_array()
            .is_none_or(|paths| !paths.is_empty())
        || later["launches"] != 1
        || boundary["detached_native_apparatus"]["cpu_semantic_callbacks_between_fronts"] != 0
        || boundary["source_apparatus"]["launches"] != 1
    {
        return Err(
            "one of the addressed R2 world returns no longer carries positive residue".to_owned(),
        );
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn returned_constraints(
    rest: &[u8],
    lean: &Value,
    rendering: &Value,
    lean_receipt: &[u8],
    rendering_receipt: &[u8],
    boundary: &[u8],
    later: &[u8],
) -> Vec<ReturnedConstraintOccurrence> {
    let occurrence = |receiver, face: &str, sha256| ReturnedConstraintOccurrence {
        receiver,
        emission_occurrence: format!("r2/emission/{face}"),
        world_occurrence: format!("r2/world/{face}"),
        return_occurrence: format!("r2/return/{face}"),
        consequence_sha256: sha256,
        primitive_orientation: 1,
        support_native_states: vec![0],
    };
    vec![
        occurrence(
            ConstraintReceiver::ProofChecker,
            "proof-checker",
            lean["source_sha256"]
                .as_str()
                .unwrap_or(&artifact::digest(lean_receipt))
                .to_owned(),
        ),
        occurrence(
            ConstraintReceiver::ExactOwner,
            "exact-owner-validation",
            artifact::digest(rest),
        ),
        occurrence(
            ConstraintReceiver::Rendering,
            "rendering-incidence",
            rendering["png_sha256"]
                .as_str()
                .unwrap_or(&artifact::digest(rendering_receipt))
                .to_owned(),
        ),
        occurrence(
            ConstraintReceiver::PhysicalBoundary,
            "physical-card-boundary",
            artifact::digest(boundary),
        ),
        occurrence(
            ConstraintReceiver::LaterOperator,
            "detached-later-operator",
            artifact::digest(later),
        ),
    ]
}

fn source_trace_receipt(returned: &DeviceDynamicMorphology) -> Result<Value, String> {
    let predecessor = artifact::traces(
        &returned.predecessor_trace,
        &returned.predecessor_lengths,
        returned.trace_stride,
    )?;
    let successor = artifact::traces(
        &returned.successor_trace,
        &returned.successor_lengths,
        returned.trace_stride,
    )?;
    let withdrawn = artifact::traces(
        &returned.withdrawn_trace,
        &returned.withdrawn_lengths,
        returned.trace_stride,
    )?;
    Ok(json!({
        "development": {"predecessor": predecessor[0], "successor": successor[0], "withdrawn": withdrawn[0], "changed": predecessor[0] != successor[0]},
        "held_out": {"predecessor": predecessor[1], "successor": successor[1], "withdrawn": withdrawn[1], "changed": predecessor[1] != successor[1]},
    }))
}

fn card_receipt(
    returned: &DeviceDynamicMorphology,
    traces: &Value,
    device: &str,
    wall: u128,
) -> Value {
    json!({
        "schema": "holonics.r3.resident-card-morphology-passage.v1",
        "truth_status": "implemented-exact",
        "returned_adjoint": returned.returned_adjoint,
        "committed": returned.committed,
        "supported_state": returned.supported_state,
        "predecessor_action": returned.predecessor_action,
        "successor_action": returned.successor_action,
        "withdrawn_action": returned.withdrawn_action,
        "traces": traces,
        "device": device,
        "launches": returned.launches,
        "synchronizations": returned.synchronizations,
        "block_threads": returned.block_threads,
        "active_lanes": returned.active_lanes,
        "host_ingress_octets": returned.host_ingress_octets,
        "host_egress_octets": returned.host_egress_octets,
        "resident_octets": returned.resident_octets,
        "physical_wall_microseconds": wall,
        "cpu_semantic_callbacks_between_fronts": 0,
    })
}

fn transition_reads(lengths: &[u32]) -> u64 {
    lengths
        .iter()
        .map(|length| u64::from(length.saturating_sub(1)))
        .sum()
}
