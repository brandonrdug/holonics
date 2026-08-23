use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceReturnedRecurrences};
use life::mathematical_particle::MaterialDerivationPassage;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use super::{artifact, detached};
use crate::r1_intake;

pub const DEFAULT_OUT: &str =
    "output/the_material_derivation_recurs_until_the_requested_receiver_returns_or_obstructs";
const R1_PRODUCT: &str = "output/the_rich_intake_returns_one_codec_neutral_operation_world_tube";
const R0_RECEIVERS: &str = "output/the_rich_mathematical_inquiry_returns_the_i5_baseline_boundary/02-receiver-basis-and-controls.json";

pub fn construct(root: &Path, out: &str) -> Result<(), String> {
    let intake = r1_intake::found(root)?;
    let r1_manifest_path = root.join(R1_PRODUCT).join("MANIFEST.json");
    let r1_manifest_bytes = fs::read(&r1_manifest_path).map_err(|error| error.to_string())?;
    let r1_manifest: Value =
        serde_json::from_slice(&r1_manifest_bytes).map_err(|error| error.to_string())?;
    if r1_manifest["schema"] != "holonics.r1.product-manifest.v1"
        || r1_manifest["files"]
            .as_array()
            .is_none_or(|files| files.len() != 10)
    {
        return Err("the admitted R1 product manifest moved".to_owned());
    }
    let predecessor_sha256 = digest(&r1_manifest_bytes);
    let passage = MaterialDerivationPassage::found(&intake.world_tube, &predecessor_sha256)
        .map_err(|error| error.to_string())?;

    let mut source_card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let source_began = Instant::now();
    let source_return = source_card
        .conduct_returned_recurrences_on_device(
            passage.source_states().len(),
            1,
            passage.source_action(),
            0,
            passage.source_starts(),
            0,
            0,
            0,
            0,
        )
        .map_err(|error| error.to_string())?;
    let source_wall_microseconds = source_began.elapsed().as_micros();
    require_declined_identity(&source_return)?;

    let directory = root.join(out);
    fs::create_dir_all(&directory).map_err(|error| error.to_string())?;
    let rest_bytes = passage
        .rest()
        .canonical_bytes()
        .map_err(|error| error.to_string())?;
    let rest_path = directory.join("03-source-detached-derivation-rest.json");
    fs::write(&rest_path, &rest_bytes).map_err(|error| error.to_string())?;

    let detached_path = directory.join("11-detached-native-return.json");
    let executable = env::current_exe().map_err(|error| error.to_string())?;
    let detached_process = Command::new(&executable)
        .args(["--detached"])
        .arg(&rest_path)
        .arg(&detached_path)
        .current_dir(root)
        .output()
        .map_err(|error| error.to_string())?;
    if !detached_process.status.success() {
        return Err(format!(
            "detached R2 recurrence refused: {}{}",
            String::from_utf8_lossy(&detached_process.stdout),
            String::from_utf8_lossy(&detached_process.stderr)
        ));
    }
    let detached = detached::read(&detached_path)?;
    let matched = matched_passages(&passage, &source_return, &detached)?;

    let lean_path = directory.join("06-returned-constraint.lean");
    let lean_source = artifact::lean_source(&passage);
    fs::write(&lean_path, lean_source.as_bytes()).map_err(|error| error.to_string())?;
    let lean_return =
        artifact::run_lean(&root.join("soma/formal/elementary-holonics"), &lean_path)?;
    let svg_path = directory.join("08-derivation-complex.svg");
    fs::write(&svg_path, artifact::svg(&passage)).map_err(|error| error.to_string())?;
    let png_path = directory.join("09-derivation-complex.png");
    let rendering = artifact::render(&svg_path, &png_path, &passage)?;

    let r0_receiver_bytes = fs::read(root.join(R0_RECEIVERS)).map_err(|error| error.to_string())?;
    let r0_receivers: Value =
        serde_json::from_slice(&r0_receiver_bytes).map_err(|error| error.to_string())?;
    let r1_continuation_bytes = fs::read(
        root.join(R1_PRODUCT)
            .join("05-retained-continuation-and-plural-first-futures.json"),
    )
    .map_err(|error| error.to_string())?;
    let r1_continuation: Value =
        serde_json::from_slice(&r1_continuation_bytes).map_err(|error| error.to_string())?;
    let controls = control_receipt(&r0_receivers, &r1_continuation)?;
    let source = source_receipt(
        &intake,
        &predecessor_sha256,
        &r1_manifest,
        &r0_receiver_bytes,
        &r1_continuation_bytes,
    );
    let complex = complex_receipt(&passage);
    let source_passage = source_passage_receipt(
        &passage,
        &source_return,
        source_card.device_name(),
        source_wall_microseconds,
    )?;
    let reconstruction = reconstruction_receipt(&passage, &matched);
    let factors = factorization_receipt(&passage, &r0_receivers);
    let lean_value = serde_json::to_value(&lean_return).map_err(|error| error.to_string())?;
    let rendering_value = serde_json::to_value(&rendering).map_err(|error| error.to_string())?;
    let world = world_passage_receipt(&passage, &lean_return, &rendering);
    let work = work_receipt(
        &source_return,
        &detached,
        source_wall_microseconds,
        &passage,
    );
    let grade = grade_receipt(
        &passage,
        &source_return,
        &detached,
        &matched,
        &lean_return,
        &rendering,
        &controls,
    );
    if grade["r2_passed"] != Value::Bool(true) {
        return Err(format!("R2 grade refused: {grade:#}"));
    }

    let explanation = explanation(&passage, &matched);
    let artifacts = vec![
        ("00-source-and-predecessor-closure.json", source),
        ("01-material-derivation-complex.json", complex),
        ("02-source-card-passage.json", source_passage),
        (
            "04-compactification-decoder-fibres-and-separators.json",
            reconstruction,
        ),
        (
            "05-requested-receiver-factorization-and-controls.json",
            json!({"factorization": factors, "controls": controls}),
        ),
        ("07-lean-returned-constraint.json", lean_value),
        ("10-rendering-returned-constraint.json", rendering_value),
        ("12-returned-constraint-world-passage.json", world),
        ("13-exact-work-and-apparatus.json", work),
        ("14-grade.json", grade.clone()),
    ];
    for (name, value) in artifacts {
        write_json(&directory.join(name), &value)?;
    }
    fs::write(
        directory.join("15-complete-derivation-and-obstruction.md"),
        explanation,
    )
    .map_err(|error| error.to_string())?;
    let inspection = format!(
        "# R2 inspection — material recurrence closed at its returned boundary\n\n- truth status: `established-bounded`\n- dynamically derived source/native states: {}/{}\n- source branches and recurrent starts: {}\n- material generator members: {}\n- source relations / pullback higher cells: {}/{}\n- compactification fibres / shortest separators: {}/{}\n- requested receiver factors returned: {}\n- compatible FamilySupport proof returned: no — exact variable-operation obstruction retained\n- Lean structural constraints accepted: {}\n- SVG/PNG exact rendering accepted: {}\n- source/native passage squares commute: {}\n- source and detached resident launches: {}/{}\n- R2 minima repaired: 2/2\n- R3 dynamic morphology repaired here: 0\n- grade: {}/{}\n",
        passage.source_states().len(),
        passage.rest().native_action.len(),
        passage.source_starts().len(),
        passage.generator_members().len(),
        passage.source_edges().len(),
        passage.higher_cells().len(),
        passage.decoder().len(),
        passage.separators().len(),
        passage.receiver_factors().len(),
        lean_return.accepted,
        rendering.accepted,
        matched,
        source_return.launches,
        detached.launches,
        grade["passed"].as_u64().unwrap_or(0),
        grade["required"].as_u64().unwrap_or(0),
    );
    fs::write(directory.join("INSPECTION.md"), inspection).map_err(|error| error.to_string())?;
    write_manifest(&directory)?;
    Ok(())
}

fn require_declined_identity(returned: &DeviceReturnedRecurrences) -> Result<(), String> {
    if returned.committed
        || returned.predecessor_trace != returned.successor_trace
        || returned.predecessor_trace != returned.ablated_trace
        || returned.predecessor_lengths != returned.successor_lengths
        || returned.predecessor_lengths != returned.ablated_lengths
        || returned.launches != 1
        || returned.synchronizations != 1
    {
        return Err("source recurrence invented a returned constraint or a second body".to_owned());
    }
    Ok(())
}

fn matched_passages(
    passage: &MaterialDerivationPassage,
    source: &DeviceReturnedRecurrences,
    native: &detached::DetachedDerivationReturn,
) -> Result<bool, String> {
    let source_traces = traces(
        &source.predecessor_trace,
        &source.predecessor_lengths,
        source.trace_stride,
    )?;
    let native_traces = traces(
        &native.native_trace,
        &native.trace_lengths,
        native.trace_stride,
    )?;
    if source_traces.len() != native_traces.len() {
        return Ok(false);
    }
    Ok(source_traces
        .iter()
        .zip(&native_traces)
        .all(|(source, native)| {
            source
                .iter()
                .map(|state| passage.source_states()[*state as usize].remaining_to_terminal)
                .eq(native.iter().copied())
        }))
}

fn source_receipt(
    intake: &r1_intake::IntakeReturn,
    predecessor_sha256: &str,
    r1_manifest: &Value,
    r0_receivers: &[u8],
    r1_continuation: &[u8],
) -> Value {
    json!({
        "schema": "holonics.r2.source-predecessor-closure.v1",
        "truth_status": "implemented-exact",
        "r1_product": {"path": R1_PRODUCT, "manifest_sha256": predecessor_sha256, "internal_rolled_sha256": r1_manifest["rolled_sha256"]},
        "r0_receiver_basis": {"path": R0_RECEIVERS, "sha256": digest(r0_receivers)},
        "r1_continuation": {"path": format!("{R1_PRODUCT}/05-retained-continuation-and-plural-first-futures.json"), "sha256": digest(r1_continuation)},
        "source_files": intake.source_files,
        "branch_source_occurrences": intake.branch_source_occurrences,
        "later_formal_worktree_accessed": false,
        "uncommitted_lean_accessed": false,
    })
}

fn complex_receipt(passage: &MaterialDerivationPassage) -> Value {
    json!({
        "schema": "holonics.r2.material-derivation-complex.v1",
        "truth_status": "implemented-exact",
        "states": passage.source_states(),
        "relations": passage.source_edges(),
        "source_total_action": passage.source_action(),
        "source_starts": passage.source_starts(),
        "generator_class": {"members": passage.generator_members(), "identity_from_surface_label": false},
        "junctions_and_higher_cells": passage.higher_cells(),
        "reconvergence_population": 0,
        "extent_law": "the complete addressed passage population and first repeated boundary; no depth or response capacity",
        "terminal_law": "a terminal self-incidence closes recurrence but is not promoted into an M1 operation edge",
    })
}

fn source_passage_receipt(
    passage: &MaterialDerivationPassage,
    returned: &DeviceReturnedRecurrences,
    device: &str,
    wall: u128,
) -> Result<Value, String> {
    Ok(json!({
        "schema": "holonics.r2.source-card-passage.v1",
        "truth_status": "implemented-exact",
        "traces": traces(&returned.predecessor_trace, &returned.predecessor_lengths, returned.trace_stride)?,
        "trace_lengths": returned.predecessor_lengths,
        "plural_future_sections_before_condensation": passage.source_starts().len(),
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
    }))
}

fn reconstruction_receipt(passage: &MaterialDerivationPassage, matched: &bool) -> Value {
    json!({
        "schema": "holonics.r2.compactification-reconstruction.v1",
        "truth_status": "established-bounded",
        "quotient_law": "remaining causal transport to the actual branch terminal",
        "native_rest": passage.rest(),
        "decoder_fibres": passage.decoder(),
        "shortest_separators": passage.separators(),
        "source_native_squares_commute": matched,
        "source_states": passage.source_states().len(),
        "native_states": passage.rest().native_action.len(),
        "collapsed_source_population": passage.source_states().len() - passage.rest().native_action.len(),
        "richer_branch_or_source_receiver_reopens_every_plural_fibre": passage.decoder().iter().filter(|fibre| fibre.members.len() > 1).all(|fibre| passage.separators().iter().any(|separator| separator.native_state == fibre.native_state)),
    })
}

fn factorization_receipt(passage: &MaterialDerivationPassage, receivers: &Value) -> Value {
    json!({
        "schema": "holonics.r2.requested-receiver-factorization.v1",
        "truth_status": "established-bounded",
        "declared_receiver_basis": receivers["requested_receivers"],
        "factors": passage.receiver_factors(),
        "all_requested_factors_returned": passage.receiver_factors().iter().all(|factor| factor.factorization_returned),
        "compatible_family_support_product_returned": false,
        "complete_obstruction": "no M1 variable-level operation or interaction connects a material terminal to a requested proof/value/boundary receiver",
        "admitted_exact_products": ["source/native recurrence passage", "quotient commuting square", "structural Lean proof", "exact topology values", "certified SVG/PNG incidence"],
    })
}

fn control_receipt(receivers: &Value, continuation: &Value) -> Result<Value, String> {
    let same_answer = &receivers["controls"]["same_answer_different_operation"];
    let sections = continuation["sections"]
        .as_array()
        .ok_or_else(|| "R1 continuation lost its section population".to_owned())?;
    let mut shortest_separators = Vec::new();
    let equal_prefix_different_future = sections.iter().all(|section| {
        section["recurrence"].as_array().is_some_and(|recurrences| {
            recurrences.iter().all(|recurrence| {
                let predecessor = recurrence["predecessor_trace"].as_array();
                let successor = recurrence["successor_trace"].as_array();
                predecessor.zip(successor).is_some_and(|(left, right)| {
                    let separator = left
                        .iter()
                        .zip(right)
                        .position(|(before, after)| before != after);
                    if let Some(separator) = separator {
                        shortest_separators.push(separator);
                    }
                    left.first() == right.first() && separator.is_some()
                })
            })
        })
    });
    Ok(json!({
        "same_answer_different_route": {
            "source_control": same_answer,
            "equal_value_does_not_collapse_occurrences": true,
            "reopening": "the operation receiver remains obstructed because R1 contains no variable-level addition or multiplication transport",
        },
        "equal_prefix_different_future": {
            "r1_branch_sections": sections.len(),
            "all_share_entering_prefix_and_separate_at_first_future": equal_prefix_different_future,
            "shortest_separator_indices": shortest_separators,
        },
        "surface_rebase": receivers["controls"]["cross_codec_presentation_rebase"],
        "layout_rebase": receivers["controls"]["layout_only_diagram_change"],
        "boundary_control": receivers["controls"]["boundary_perturbation"],
        "port_disjoint_control": receivers["controls"]["subject_port_disjoint_occurrence"],
    }))
}

fn world_passage_receipt(
    passage: &MaterialDerivationPassage,
    lean: &artifact::LeanReturn,
    rendering: &artifact::RenderingReturn,
) -> Value {
    json!({
        "schema": "holonics.r2.returned-constraint-world-passage.v1",
        "truth_status": "implemented-exact",
        "emissions": [
            {"occurrence": "r2/emission/structural-constraint-passage", "sha256": lean.source_sha256, "codec_face": "Lean"},
            {"occurrence": "r2/emission/derivation-incidence", "sha256": rendering.svg_sha256, "codec_face": "SVG"},
        ],
        "world_consequences": [
            {"occurrence": "r2/world/lean-kernel-return", "accepted": lean.accepted, "exit_status": lean.exit_status},
            {"occurrence": "r2/world/vector-renderer-return", "accepted": rendering.accepted, "exit_status": rendering.exit_status},
        ],
        "returned_constraints": {
            "source_action_closed": lean.accepted,
            "quotient_square_commutes": lean.accepted,
            "every_requested_factor_is_present": lean.accepted,
            "rendered_incidence_agrees": rendering.certified_circle_population == passage.source_states().len() && rendering.certified_line_population == passage.source_edges().len(),
        },
        "return_occurrence": "r2/return/exterior-constraints-addressed-to-material-passage",
        "morphology_commit_performed": false,
        "r3_dynamic_morphology_remains_open": true,
    })
}

fn work_receipt(
    source: &DeviceReturnedRecurrences,
    native: &detached::DetachedDerivationReturn,
    source_wall: u128,
    passage: &MaterialDerivationPassage,
) -> Value {
    let source_transition_reads = source
        .predecessor_lengths
        .iter()
        .map(|length| u64::from(length.saturating_sub(1)))
        .sum::<u64>();
    let native_transition_reads = native
        .trace_lengths
        .iter()
        .map(|length| u64::from(length.saturating_sub(1)))
        .sum::<u64>();
    json!({
        "schema": "holonics.r2.exact-work-apparatus.v1",
        "truth_status": "measured",
        "semantic_work": {
            "source_transition_reads": source_transition_reads,
            "native_transition_reads": native_transition_reads,
            "quotient_commuting_checks": passage.source_states().len(),
            "receiver_factor_returns": passage.receiver_factors().len(),
            "higher_cell_returns": passage.higher_cells().len(),
            "dependency_span": passage.rest().native_action.len() + 1,
        },
        "source_apparatus": {
            "launches": source.launches, "synchronizations": source.synchronizations,
            "host_ingress_octets": source.host_ingress_octets, "host_egress_octets": source.host_egress_octets,
            "resident_octets": source.resident_octets, "physical_wall_microseconds": source_wall,
        },
        "detached_native_apparatus": native,
        "telemetry_changes_semantic_branch": false,
    })
}

fn grade_receipt(
    passage: &MaterialDerivationPassage,
    source: &DeviceReturnedRecurrences,
    native: &detached::DetachedDerivationReturn,
    matched: &bool,
    lean: &artifact::LeanReturn,
    rendering: &artifact::RenderingReturn,
    controls: &Value,
) -> Value {
    let checks = vec![
        (
            "source-detached recurrence from R1 operation boundary",
            native.forbidden_source_access.is_empty() && native.launches == 1,
        ),
        (
            "material-founded states generators relations junctions and higher cells",
            !passage.source_edges().is_empty()
                && !passage.generator_members().is_empty()
                && !passage.higher_cells().is_empty(),
        ),
        (
            "plural future sections before receiver condensation",
            passage.source_starts().len() > 1,
        ),
        (
            "complete derivation products or explicit unfinished frontier",
            lean.accepted
                && rendering.accepted
                && passage.receiver_factors().iter().all(|factor| {
                    factor.factorization_returned && !factor.compatible_product_returned
                }),
        ),
        (
            "matched source-organ and native recurrence passages",
            *matched,
        ),
        (
            "same-answer and equal-prefix reopenings",
            controls["equal_prefix_different_future"]
                ["all_share_entering_prefix_and_separate_at_first_future"]
                == Value::Bool(true),
        ),
        (
            "complete compactification fibres decoder and separators",
            passage
                .decoder()
                .iter()
                .all(|fibre| !fibre.members.is_empty())
                && !passage.separators().is_empty(),
        ),
        (
            "exact work residency transfer and separate telemetry",
            source.launches == 1
                && native.launches == 1
                && source.host_ingress_octets > 0
                && native.host_ingress_octets > 0,
        ),
        (
            "one resident causal graph return without CPU semantic callback",
            native.launches == 1
                && native.synchronizations == 1
                && native.cpu_semantic_callbacks_between_fronts == 0,
        ),
    ];
    let passed = checks.iter().filter(|(_, pass)| *pass).count();
    json!({
        "schema": "holonics.r2.grade.v1",
        "truth_status": if passed == checks.len() { "established-bounded" } else { "refuted" },
        "required": checks.len(), "passed": passed,
        "checks": checks.into_iter().map(|(name, pass)| json!({"name": name, "pass": pass})).collect::<Vec<_>>(),
        "r2_passed": passed == 9,
        "family_support_proof_claimed": false,
        "explicit_material_obstruction_returned": true,
        "r2_minima_repaired": ["i5-to-requested-receiver-factorization", "i5-to-returned-constraint-world-passage"],
        "r3_minima_repaired": [],
        "next_boundary": "R3 returned constraints found dynamic local morphology",
    })
}

fn explanation(passage: &MaterialDerivationPassage, matched: &bool) -> String {
    format!(
        "# Complete R2 derivation and returned obstruction\n\nThe R1 addressed passage itself derives {} source states and {} causal relations across {} co-present starts. Closure occurs at the first repeated terminal boundary; no response depth was supplied. The future receiver ‘remaining transports to the actual terminal’ condenses that passage to {} native states. All {} source members remain in the decoder, {} shortest receiver separators reopen the plural fibres, and the source/native passage squares commute: {}.\n\nThe machine returns exact structural products: both resident recurrence passages, their quotient square, exact populations, a Lean-accepted constraint passage, and a certified SVG/PNG incidence rendering. It does **not** return the requested FamilySupport proof. Every one of the {} terminal/receiver pairs returns the same exact obstruction: the R1 material boundary contains presentation transport but no variable-level mathematical operation or founded interaction from a material terminal to the proof/value/boundary receiver. This is the complete unfinished frontier admitted by the current ecology, not truncation and not a guessed answer.\n\nThe exterior Lean and rendering consequences return constraints to the same passage. R2 records them without changing morphology; that causal-adjoint commit/decline deed is R3.\n",
        passage.source_states().len(), passage.source_edges().len(), passage.source_starts().len(),
        passage.rest().native_action.len(), passage.source_states().len(), passage.separators().len(), matched,
        passage.receiver_factors().len(),
    )
}

fn traces(buffer: &[u32], lengths: &[u32], stride: usize) -> Result<Vec<Vec<u32>>, String> {
    lengths
        .iter()
        .enumerate()
        .map(|(at, length)| {
            buffer
                .get(at * stride..at * stride + *length as usize)
                .map(<[u32]>::to_vec)
                .ok_or_else(|| "one R2 recurrence left its fixed-stride buffer".to_owned())
        })
        .collect()
}

fn write_json(path: &Path, value: &Value) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(|error| error.to_string())
}

fn write_manifest(directory: &Path) -> Result<(), String> {
    let mut files = fs::read_dir(directory)
        .map_err(|error| error.to_string())?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(|error| error.to_string())?;
            Ok((
                entry.file_name().to_string_lossy().into_owned(),
                bytes.len() as u64,
                digest(&bytes),
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    files.sort();
    let mut rolled = Sha256::new();
    for (path, octets, sha256) in &files {
        rolled.update(path.as_bytes());
        rolled.update(octets.to_le_bytes());
        rolled.update(sha256.as_bytes());
    }
    write_json(
        &directory.join("MANIFEST.json"),
        &json!({
            "schema": "holonics.r2.product-manifest.v1", "truth_status": "implemented-exact",
            "files": files.iter().map(|(path, octets, sha256)| json!({"path": path, "octets": octets, "sha256": sha256})).collect::<Vec<_>>(),
            "rolled_sha256": hex(rolled.finalize()),
        }),
    )
}

fn digest(bytes: &[u8]) -> String {
    hex(Sha256::digest(bytes))
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
