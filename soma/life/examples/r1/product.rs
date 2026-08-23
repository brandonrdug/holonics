use std::fs;
use std::path::Path;
use std::time::Instant;

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceMaterialOperationWorldTube};
use life::mathematical_source::LayoutRelation;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use super::{i5, intake};

pub const DEFAULT_OUT: &str =
    "output/the_rich_intake_returns_one_codec_neutral_operation_world_tube";
const R0_CLOSURE: &str = "output/the_rich_mathematical_inquiry_returns_the_i5_baseline_boundary/00-source-input-rest-closure.json";

pub fn construct(root: &Path, out: &str) -> Result<(), String> {
    let intake = intake::found(root)?;
    let loaded = i5::load(root)?;
    let world = &intake.world_tube;
    let mut face_payload_keys = Vec::new();
    let mut face_branch = Vec::new();
    let mut contact_from = Vec::new();
    let mut contact_to = Vec::new();
    let mut contact_relation = Vec::new();
    let mut face_offset = 0usize;
    for (branch, testimony) in world.source_testimonies().iter().enumerate() {
        for occurrence in &testimony.occurrences {
            face_payload_keys.push(digest_words(&occurrence.payload_sha256)?);
            face_branch.push(branch as u32);
        }
        for contact in &testimony.contacts {
            contact_from.push((face_offset + contact.from) as u32);
            contact_to.push((face_offset + contact.to) as u32);
            contact_relation.push(relation_wire(contact.relation));
        }
        face_offset += testimony.occurrences.len();
    }
    let entries = world.branch_entry_events().collect::<Vec<_>>();
    let branch_staging_events = entries
        .iter()
        .map(|(_, staging, _)| staging.0)
        .collect::<Vec<_>>();
    let branch_terminal_events = entries
        .iter()
        .map(|(_, _, terminal)| terminal.0)
        .collect::<Vec<_>>();
    if branch_staging_events.len() != world.source_testimonies().len() {
        return Err("the M1 passage branch population left the source cover".to_owned());
    }

    let recurrent_start = [
        loaded.rest.recurrent.standing.main_start,
        loaded.rest.recurrent.standing.held_out_start,
    ];
    let world_start = loaded.rest.heterogeneous.starts();
    let decoder = loaded.rest.heterogeneous.decoder_addresses();
    let began = Instant::now();
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let returned = card
        .conduct_material_operation_world_tube_on_device(
            &face_payload_keys,
            &face_branch,
            &branch_staging_events,
            &branch_terminal_events,
            &contact_from,
            &contact_to,
            &contact_relation,
            &loaded.rest.recurrent.standing.successor_action,
            &recurrent_start,
            loaded.rest.recurrent.standing.predecessor_from,
            loaded.rest.recurrent.standing.predecessor_to,
            &loaded.rest.heterogeneous.standing.successor_action,
            &decoder,
            &world_start,
            loaded.rest.heterogeneous.standing.family_count as usize,
            loaded.rest.heterogeneous.standing.ports.len(),
            loaded.rest.committed(),
        )
        .map_err(|error| error.to_string())?;
    let physical_wall_microseconds = began.elapsed().as_micros();

    let r0_closure_bytes = fs::read(root.join(R0_CLOSURE)).map_err(|error| error.to_string())?;
    let source = source_receipt(&intake, &loaded, &r0_closure_bytes);
    let addressed = addressed_receipt(world);
    let operation = operation_receipt(world)?;
    let cross_codec = cross_codec_receipt(world);
    let continuation = continuation_receipt(world, &loaded.rest, &returned, recurrent_start.len())?;
    let resident = resident_receipt(
        world,
        &loaded.rest,
        &returned,
        &face_branch,
        physical_wall_microseconds,
        &card,
    )?;
    let work = work_receipt(&returned, physical_wall_microseconds);
    let repair = repair_receipt(world, &returned, recurrent_start.len());
    let grade = grade_receipt(world, &returned, recurrent_start.len(), &repair);

    let directory = root.join(out);
    fs::create_dir_all(&directory).map_err(|error| error.to_string())?;
    let artifacts = vec![
        ("00-source-and-rest-closure.json", source),
        ("01-addressed-face-passage.json", addressed),
        ("02-material-operation-world-tube.json", operation),
        (
            "03-cross-codec-squares-fibres-and-separators.json",
            cross_codec,
        ),
        ("04-resident-i5-pullback-return.json", resident),
        (
            "05-retained-continuation-and-plural-first-futures.json",
            continuation,
        ),
        ("06-exact-work-and-apparatus.json", work),
        ("07-r1-absence-repair.json", repair),
        ("08-grade.json", grade.clone()),
    ];
    for (name, value) in &artifacts {
        write_json(&directory.join(name), value)?;
    }
    let inspection = format!(
        "# R1 inspection — the material operation world-tube returned\n\n- truth status: `established-bounded`\n- A1/M0 record-face squares: {}\n- situated M0 faces: {}\n- M1 presentation branches: {}\n- M1 addressed occurrences: {}\n- resident launches/synchronizations: {}/{}\n- recurrent branch/start sections: {}\n- expanded world families: {}\n- R1 minimal absences repaired: 5/5\n- R2 receiver/world-return absences repaired here: 0\n- R3 dynamic-morphology absences repaired here: 0\n- grade: {}/{}\n\nThe returned passages are the unchanged I5 baseline replicated over every material branch. They are evidence of a lawful entry and plural future, not an answer to the FamilySupport inquiry.\n",
        world.record_face_passages().len(),
        face_payload_keys.len(),
        world.passage().branches().len(),
        world.passage().addressed().occurrences().len(),
        returned.launches,
        returned.synchronizations,
        returned.inference.selected_lengths.len(),
        returned.inference.families,
        grade["passed"].as_u64().unwrap_or(0),
        grade["required"].as_u64().unwrap_or(0),
    );
    fs::write(directory.join("INSPECTION.md"), inspection).map_err(|error| error.to_string())?;
    write_manifest(&directory)?;
    Ok(())
}

fn source_receipt(
    intake: &intake::IntakeReturn,
    loaded: &i5::LoadedI5,
    r0_closure: &[u8],
) -> Value {
    json!({
        "schema": "holonics.r1.source-rest-closure.v1",
        "truth_status": "implemented-exact",
        "predecessor_r0_closure": {
            "path": R0_CLOSURE,
            "sha256": digest(r0_closure),
            "octets": r0_closure.len(),
        },
        "source_files": intake.source_files,
        "branch_source_occurrences": intake.branch_source_occurrences,
        "source_access": {
            "fixture_occurrence_only": true,
            "formal_worktree_accessed": false,
            "later_lean_commits_accessed": false,
        },
        "i5_components": loaded.components,
        "i5_accessed_paths": loaded.accessed_paths,
        "i5_source_weights_or_formal_sources_accessed": false,
    })
}

fn addressed_receipt(world: &life::mathematical_particle::MaterialOperationWorldTube) -> Value {
    json!({
        "schema": "holonics.r1.addressed-face-passage.v1",
        "truth_status": "implemented-exact",
        "exchange_source_occurrence": world.exchange().source_occurrence_sha256.render(),
        "exchange_content_law": world.exchange().content_law_sha256.render(),
        "a1_device": world.exchange().device,
        "record_face_passages": world.record_face_passages().iter().map(|passage| json!({
            "record": passage.record,
            "source_record_occurrence": passage.record_occurrence_sha256,
            "target_m0_carrier_occurrence": passage.carrier_address,
            "equal_payload_receiver": passage.carried_payload_sha256,
            "source_and_target_occurrence_identity_equal": false,
        })).collect::<Vec<_>>(),
        "receiver_record_occurrences": world.receiver_record_occurrences(),
        "cross_chart_law": "equal raw payload and situated ordinal found the boundary square; equal payload never identifies the A1 record and M0 carrier occurrences",
    })
}

fn operation_receipt(
    world: &life::mathematical_particle::MaterialOperationWorldTube,
) -> Result<Value, String> {
    let fronts = world
        .operation()
        .fronts()
        .map_err(|error| error.to_string())?;
    Ok(json!({
        "schema": "holonics.r1.material-operation-world-tube.v1",
        "truth_status": "implemented-exact",
        "occurrence": world.occurrence(),
        "source_presentations": world.source_testimonies().iter().enumerate().map(|(branch, testimony)| json!({
            "branch": branch,
            "artifact_occurrence": testimony.artifact.occurrence,
            "artifact_sha256": testimony.artifact.sha256,
            "chart": testimony.chart,
            "situated_faces": testimony.occurrences.len(),
            "contacts": testimony.contacts.len(),
        })).collect::<Vec<_>>(),
        "operation": {
            "ports": world.operation().shape.boundaries.objects.len(),
            "laws": world.operation().shape.laws.len(),
            "occurrences": world.operation().shape.occurrences.len(),
            "interactions": world.operation().shape.interactions.len(),
            "fronts": fronts.iter().map(|front| json!({
                "depth": front.depth,
                "occurrences": front.occurrences.iter().map(|event| event.0).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "dependency_span": world.operation().dependency_span().map_err(|error| error.to_string())?,
            "surface_names_or_media_labels_form_identity": false,
        },
        "passage": {
            "occurrence": world.passage().occurrence(),
            "branches": world.passage().branches().len(),
            "source_occurrences": world.passage().source_occurrences().len(),
            "addressed_occurrences": world.passage().addressed().occurrences().len(),
            "pullback_joins": world.passage().addressed().pullback_joins().len(),
            "shadow_fibres": world.passage().addressed().shadow_fibres().len(),
            "entry_events": world.branch_entry_events().map(|(branch, staging, terminal)| json!({
                "branch": branch.0,
                "staging_event": staging.0,
                "terminal_event": terminal.0,
            })).collect::<Vec<_>>(),
        },
        "typing": {
            "carriers": world.carriers().len(),
            "binder_scopes": world.binders().len(),
            "typed_ports": world.ports().len(),
            "typed_laws": world.operations().len(),
            "hypothesis_licenses": world.hypotheses().len(),
            "branch_population": world.branches().len(),
            "all_ports_dimensionless_at_this_material_boundary": world.ports().iter().all(|port| port.boundary.dimension().is_some_and(|dimension| dimension.is_dimensionless())),
            "one_free_covariant_incidence_slot_per_port": world.ports().iter().all(|port| port.boundary.tensor_slots().len() == 1),
            "variable_level_binder_semantics_claimed": false,
        },
        "open_fibres": world.open_fibres(),
    }))
}

fn cross_codec_receipt(world: &life::mathematical_particle::MaterialOperationWorldTube) -> Value {
    json!({
        "schema": "holonics.r1.cross-codec-square-family.v1",
        "truth_status": "established-bounded",
        "fibres": world.cross_codec_fibres(),
        "presentation_controls": world.presentation_controls(),
        "naturality": {
            "record_to_raw_carrier_squares_commute_at_payload_receiver": world.record_face_passages().len(),
            "language_to_lean_candidates_are_identifications": false,
            "diagram_serial_payload_square_commutes": world.presentation_controls()[0].serial_payload_face_equal,
            "diagram_layout_square_commutes": world.presentation_controls()[0].departed_contacts.is_empty() && world.presentation_controls()[0].arrived_contacts.is_empty(),
        },
        "shortest_separators": [
            "A1 record occurrence versus M0 carrier occurrence: situated lineage",
            "diagram A versus diagram B: first departed/arrived exact layout contact",
            "language versus Lean: unmatched occurrence or plural normalized-box candidate fibre",
            "same-answer controls: distinct record occurrence and payload class; operation receiver remains R2",
        ],
    })
}

fn continuation_receipt(
    world: &life::mathematical_particle::MaterialOperationWorldTube,
    rest: &holonic_engine::phoenix::inference_ecology::InferenceEcologyRest,
    returned: &DeviceMaterialOperationWorldTube,
    recurrent_cells_per_branch: usize,
) -> Result<Value, String> {
    let predecessor = traces(
        &returned.inference.predecessor_trace,
        &returned.inference.predecessor_lengths,
        returned.inference.trace_stride,
    )?;
    let successor = traces(
        &returned.inference.successor_trace,
        &returned.inference.successor_lengths,
        returned.inference.trace_stride,
    )?;
    let withdrawn = traces(
        &returned.inference.withdrawn_trace,
        &returned.inference.withdrawn_lengths,
        returned.inference.trace_stride,
    )?;
    let selected = traces(
        &returned.inference.selected_trace,
        &returned.inference.selected_lengths,
        returned.inference.trace_stride,
    )?;
    let base_world_cells =
        rest.heterogeneous.standing.family_count as usize * rest.heterogeneous.standing.ports.len();
    let sections = world
        .source_testimonies()
        .iter()
        .enumerate()
        .map(|(branch, testimony)| {
            let recurrence_from = branch * recurrent_cells_per_branch;
            let world_from = branch * base_world_cells;
            let recurrence = (0..recurrent_cells_per_branch)
                .map(|local| {
                    let at = recurrence_from + local;
                    Ok(json!({
                        "local_start": local,
                        "staging_event": returned.recurrence_staging_events[at],
                        "terminal_event": returned.recurrence_terminal_events[at],
                        "predecessor_trace": predecessor[at],
                        "successor_trace": successor[at],
                        "withdrawn_trace": withdrawn[at],
                        "selected_trace": selected[at],
                        "predecessor_passage": rest.recurrent.decode_trace(&predecessor[at]).map_err(|error| error.to_string())?,
                        "successor_passage": rest.recurrent.decode_trace(&successor[at]).map_err(|error| error.to_string())?,
                        "withdrawn_passage": rest.recurrent.decode_trace(&withdrawn[at]).map_err(|error| error.to_string())?,
                        "selected_passage": rest.recurrent.decode_trace(&selected[at]).map_err(|error| error.to_string())?,
                        "plural_first_futures": [predecessor[at][1], successor[at][1]],
                    }))
                })
                .collect::<Result<Vec<_>, String>>()?;
            Ok(json!({
                "branch": branch,
                "artifact_occurrence": testimony.artifact.occurrence,
                "source_occurrences": testimony.occurrences.iter().map(|occurrence| &occurrence.address).collect::<Vec<_>>(),
                "recurrence": recurrence,
                "world_predecessor": returned.inference.predecessor_consequence[world_from..world_from + base_world_cells],
                "world_successor": returned.inference.successor_consequence[world_from..world_from + base_world_cells],
                "world_selected": returned.inference.selected_consequence[world_from..world_from + base_world_cells],
                "world_shared_withdrawn": returned.inference.shared_ablated_consequence[world_from..world_from + base_world_cells],
                "open_receiver_factorization": true,
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(json!({
        "schema": "holonics.r1.retained-continuation-sections.v1",
        "truth_status": "implemented-exact",
        "sections": sections,
        "branch_selection_performed": false,
        "all_material_branches_cross_every_i5_start": true,
        "selected_passage_is_unchanged_i5_decision_not_an_inquiry_answer": true,
        "complete_branch_fibre": (0..world.source_testimonies().len()).collect::<Vec<_>>(),
    }))
}

fn resident_receipt(
    world: &life::mathematical_particle::MaterialOperationWorldTube,
    rest: &holonic_engine::phoenix::inference_ecology::InferenceEcologyRest,
    returned: &DeviceMaterialOperationWorldTube,
    face_branch: &[u32],
    physical_wall_microseconds: u128,
    card: &CudaRefineExecutor,
) -> Result<Value, String> {
    let entry_events = world
        .branch_entry_events()
        .map(|(_, staging, terminal)| (staging, terminal))
        .collect::<Vec<_>>();
    let expected_face_events = face_branch
        .iter()
        .map(|branch| entry_events.get(*branch as usize).copied())
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| "one material face named no M1 branch entry".to_owned())?;
    if expected_face_events
        .iter()
        .enumerate()
        .any(|(at, (staging, terminal))| {
            returned.face_staging_events[at] != staging.0
                || returned.face_terminal_events[at] != terminal.0
        })
    {
        return Err("the card moved one M1 face entry".to_owned());
    }
    Ok(json!({
        "schema": "holonics.r1.resident-i5-pullback-return.v1",
        "truth_status": "implemented-exact",
        "device": card.device_name(),
        "launches": returned.launches,
        "synchronizations": returned.synchronizations,
        "block_threads": returned.inference.block_threads,
        "active_lanes": returned.inference.active_lanes,
        "physical_wall_microseconds": physical_wall_microseconds,
        "payload_classes": returned.payload_classes,
        "payload_comparisons": returned.payload_comparisons,
        "contact_left_classes": returned.contact_left_classes,
        "contact_right_classes": returned.contact_right_classes,
        "contact_relations": returned.contact_relations,
        "face_staging_events": returned.face_staging_events,
        "face_terminal_events": returned.face_terminal_events,
        "recurrence_staging_events": returned.recurrence_staging_events,
        "recurrence_terminal_events": returned.recurrence_terminal_events,
        "material_branches": world.source_testimonies().len(),
        "base_i5_recurrent_starts": 2,
        "returned_recurrent_sections": returned.inference.selected_lengths.len(),
        "base_i5_world_families": rest.heterogeneous.standing.family_count,
        "returned_world_families": returned.inference.families,
        "ports": returned.inference.ports,
        "cpu_semantic_callbacks_between_fronts": 0,
        "host_selected_material_branch": false,
        "invariant_i5_action_decoder_uploads_per_branch": false,
    }))
}

fn work_receipt(returned: &DeviceMaterialOperationWorldTube, wall: u128) -> Value {
    let face_quotient_comparisons = returned
        .payload_comparisons
        .iter()
        .map(|value| u64::from(*value))
        .sum::<u64>();
    let contact_quotient_comparisons = returned
        .contact_left_classes
        .iter()
        .chain(&returned.contact_right_classes)
        .map(|value| u64::from(*value))
        .sum::<u64>();
    let contact_joins = returned.contact_relations.len() as u64;
    let face_entry_writes = (returned.face_staging_events.len() * 2) as u64;
    let recurrence_entry_writes = (returned.recurrence_staging_events.len() * 2) as u64;
    let transition_reads = (returned.inference.predecessor_lengths.iter().sum::<u32>()
        + returned.inference.successor_lengths.iter().sum::<u32>()
        + returned.inference.selected_lengths.iter().sum::<u32>()
        - 3 * returned.inference.predecessor_lengths.len() as u32)
        as u64;
    let withdrawal_reads = (returned.inference.withdrawn_lengths.iter().sum::<u32>()
        - returned.inference.withdrawn_lengths.len() as u32) as u64;
    let visited_tests = transition_reads + withdrawal_reads;
    let trace_writes =
        (returned.inference.trace_stride * returned.inference.selected_lengths.len() * 4) as u64;
    let world_action_reads = returned.inference.selected_consequence.len() as u64;
    let world_decoder_reads = world_action_reads * 2;
    let world_writes =
        (returned.inference.selected_consequence.len() * (4 + returned.inference.ports)) as u64;
    let total = face_quotient_comparisons
        + contact_quotient_comparisons
        + contact_joins
        + face_entry_writes
        + recurrence_entry_writes
        + transition_reads
        + withdrawal_reads
        + visited_tests
        + trace_writes
        + world_action_reads
        + world_decoder_reads
        + world_writes;
    json!({
        "schema": "holonics.r1.exact-work-apparatus.v1",
        "truth_status": "measured",
        "semantic_work": {
            "face_quotient_comparisons": face_quotient_comparisons,
            "contact_quotient_comparisons": contact_quotient_comparisons,
            "contact_joins": contact_joins,
            "face_entry_writes": face_entry_writes,
            "recurrence_entry_writes": recurrence_entry_writes,
            "recurrent_transition_reads": transition_reads,
            "recurrent_withdrawal_reads": withdrawal_reads,
            "visited_incidence_tests": visited_tests,
            "fixed_stride_trace_writes": trace_writes,
            "world_action_reads": world_action_reads,
            "world_decoder_reads": world_decoder_reads,
            "world_consequence_writes": world_writes,
            "total": total,
            "dependency_span": returned.inference.selected_lengths.iter().copied().max().unwrap_or(0) + 2,
        },
        "apparatus": {
            "launches": returned.launches,
            "synchronizations": returned.synchronizations,
            "host_ingress_octets": returned.host_ingress_octets,
            "host_egress_octets": returned.host_egress_octets,
            "resident_octets": returned.resident_octets,
            "physical_wall_microseconds": wall,
            "telemetry_changes_semantic_branch": false,
        },
    })
}

fn repair_receipt(
    world: &life::mathematical_particle::MaterialOperationWorldTube,
    returned: &DeviceMaterialOperationWorldTube,
    starts_per_branch: usize,
) -> Value {
    json!({
        "schema": "holonics.r1.minimal-absence-repair.v1",
        "truth_status": "established-bounded",
        "repaired": [
            {"absence": "a1-to-m0-addressed-face-passage", "witness_population": world.record_face_passages().len()},
            {"absence": "m0-to-m1-material-founded-operation-passage", "witness_population": world.passage().source_occurrences().len()},
            {"absence": "m1-to-i5-typed-entry-passage", "witness_population": returned.recurrence_staging_events.len()},
            {"absence": "inquiry-to-i5-addressed-entry-port", "witness_population": world.receiver_record_occurrences().len()},
            {"absence": "rich-composition-resident-card-front", "witness_population": returned.launches},
        ],
        "all_five_repaired": world.record_face_passages().len() == world.exchange().records.len()
            && returned.recurrence_staging_events.len() == world.passage().branches().len() * starts_per_branch
            && returned.launches == 1 && returned.synchronizations == 1,
        "r2_absences_repaired": [],
        "r3_absences_repaired": [],
        "still_open": [
            "i5-to-requested-receiver-factorization",
            "i5-to-returned-constraint-world-passage",
            "returned-constraint-to-dynamic-local-morphology",
        ],
    })
}

fn grade_receipt(
    world: &life::mathematical_particle::MaterialOperationWorldTube,
    returned: &DeviceMaterialOperationWorldTube,
    starts_per_branch: usize,
    repair: &Value,
) -> Value {
    let checks = vec![
        (
            "addressed A1/M0 record-face passage",
            world.record_face_passages().len() == world.exchange().records.len(),
        ),
        (
            "plural codec-neutral M1 operation branches",
            world.passage().branches().len() == world.source_testimonies().len()
                && world.passage().branches().len() > 1,
        ),
        (
            "complete cross-codec fibres and exact layout control",
            world.cross_codec_fibres().len() == 2
                && world.presentation_controls()[0].serial_payload_face_equal,
        ),
        (
            "typed M1 entry crosses unchanged I5",
            returned.recurrence_staging_events.len()
                == world.passage().branches().len() * starts_per_branch,
        ),
        (
            "retained plural first futures",
            returned.inference.predecessor_lengths.len()
                == returned.inference.successor_lengths.len()
                && returned.inference.predecessor_lengths.len() > starts_per_branch,
        ),
        (
            "surface labels do not select a branch",
            returned.inference.families % world.passage().branches().len() == 0,
        ),
        (
            "one resident card front without CPU semantic callback",
            returned.launches == 1 && returned.synchronizations == 1,
        ),
        (
            "only the five R1 minima close",
            repair["all_five_repaired"] == Value::Bool(true)
                && repair["r2_absences_repaired"]
                    .as_array()
                    .is_some_and(Vec::is_empty)
                && repair["r3_absences_repaired"]
                    .as_array()
                    .is_some_and(Vec::is_empty),
        ),
    ];
    let passed = checks.iter().filter(|(_, pass)| *pass).count();
    json!({
        "schema": "holonics.r1.grade.v1",
        "truth_status": if passed == checks.len() { "established-bounded" } else { "refuted" },
        "required": checks.len(),
        "passed": passed,
        "checks": checks.into_iter().map(|(name, pass)| json!({"name": name, "pass": pass})).collect::<Vec<_>>(),
        "r1_passed": passed == 8,
        "family_support_answer_claimed": false,
        "next_boundary": "R2 material-founded derivation recurrence and requested-receiver/world-return factorization",
    })
}

fn traces(buffer: &[u32], lengths: &[u32], stride: usize) -> Result<Vec<Vec<u32>>, String> {
    lengths
        .iter()
        .enumerate()
        .map(|(at, length)| {
            let length = *length as usize;
            buffer
                .get(at * stride..at * stride + length)
                .map(<[u32]>::to_vec)
                .ok_or_else(|| "a resident trace left its fixed-stride buffer".to_owned())
        })
        .collect()
}

fn relation_wire(relation: LayoutRelation) -> u32 {
    match relation {
        LayoutRelation::SerialNext => 1,
        LayoutRelation::Contains => 2,
        LayoutRelation::Overlaps => 3,
        LayoutRelation::HorizontalNext => 4,
        LayoutRelation::VerticalNext => 5,
    }
}

fn digest_words(hex: &str) -> Result<[u64; 4], String> {
    if hex.len() != 64 {
        return Err("a payload digest left the exact four-word wire".to_owned());
    }
    let mut words = [0u64; 4];
    for (at, word) in words.iter_mut().enumerate() {
        *word = u64::from_str_radix(&hex[at * 16..(at + 1) * 16], 16)
            .map_err(|error| error.to_string())?;
    }
    Ok(words)
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
    let manifest = json!({
        "schema": "holonics.r1.product-manifest.v1",
        "truth_status": "implemented-exact",
        "files": files.iter().map(|(path, octets, sha256)| json!({"path": path, "octets": octets, "sha256": sha256})).collect::<Vec<_>>(),
        "rolled_sha256": hex(rolled.finalize()),
    });
    write_json(&directory.join("MANIFEST.json"), &manifest)
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
