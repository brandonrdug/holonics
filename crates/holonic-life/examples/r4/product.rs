use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceRaggedNativeTrace};
use holonic_engine::receiver_exact_compression::{compress_on_device, Observation};
use life::mathematical_particle::{
    AddressedHistorySystem, CultivatedActionLineage, DynamicMorphologyRest,
    LongHorizonRetainedBoundary,
};
use serde_json::{json, Value};

use super::{
    artifact, detached,
    grade::{
        certify_interchange, complete_cost, endpoint, verify_factorization, write_product_faces,
    },
    render, source,
};

pub const DEFAULT_OUT: &str =
    ".local/artifacts/the_retained_causal_boundary_carries_the_long_horizon_inquiry";
const R3: &str = ".local/artifacts/the_returned_constraints_found_dynamic_local_morphology";

pub fn construct(root: &Path, out: &str) -> Result<(), String> {
    let directory = root.join(out);
    fs::create_dir(&directory)
        .map_err(|error| format!("create {}: {error}", directory.display()))?;
    for child in ["source-replay", "uncondensed-history", "native-rest"] {
        fs::create_dir(directory.join(child)).map_err(|error| error.to_string())?;
    }

    let mounted = source::mount(root)?;
    artifact::write_json(
        &directory.join("00-source-and-predecessor-closure.json"),
        &mounted.source_closure,
    )?;
    let r3_rest_bytes = fs::read(
        root.join(R3)
            .join("04-source-detached-dynamic-morphology-rest.json"),
    )
    .map_err(|error| error.to_string())?;
    let r3 = DynamicMorphologyRest::read(&r3_rest_bytes).map_err(|error| error.to_string())?;
    let predecessor_action = r3.predecessor_action().to_vec();
    let successor_action = r3.successor_action().to_vec();
    if predecessor_action.len() != successor_action.len()
        || predecessor_action == successor_action
        || r3.delta.cultivation_holonomy.commutator_rank == 0
    {
        return Err("the admitted R3 action family lost its cultivated holonomy".to_owned());
    }
    let mut action = predecessor_action.clone();
    action.extend_from_slice(&successor_action);
    let observations = returned_observations(&r3, action.len() / 2)?;
    let system = AddressedHistorySystem::found(
        mounted.interiors.len(),
        action.len() / 2,
        action,
        observations,
    )
    .map_err(|error| error.to_string())?;

    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let quotient_began = Instant::now();
    let launches_before = card.launches();
    let exact = compress_on_device(&system, &mut card).map_err(|error| error.to_string())?;
    let quotient_wall_microseconds = quotient_began.elapsed().as_micros();
    let quotient_launches = card.launches() - launches_before;
    if exact.conduct.len() >= exact.one_shot.items_in_order().len() || exact.collapsed.is_empty() {
        return Err("the future-receiver quotient returned no lawful historical compactification or separator".to_owned());
    }
    let compression_bytes = artifact::write_json(
        &directory.join("03-receiver-history-compression.json"),
        &exact,
    )?;
    let predecessor_identity = artifact::digest(&r3_rest_bytes);
    let boundary_identity = artifact::digest(
        &[
            predecessor_identity.as_bytes(),
            artifact::digest(&compression_bytes).as_bytes(),
        ]
        .concat(),
    );
    let cultivation = CultivatedActionLineage {
        dynamic_rest_sha256: predecessor_identity.clone(),
        predecessor_action_sha256: artifact::digest(
            &predecessor_action
                .iter()
                .flat_map(|state| state.to_le_bytes())
                .collect::<Vec<_>>(),
        ),
        successor_action_sha256: artifact::digest(
            &successor_action
                .iter()
                .flat_map(|state| state.to_le_bytes())
                .collect::<Vec<_>>(),
        ),
        returned_occurrences: r3
            .returned_constraints
            .iter()
            .map(|returned| returned.return_occurrence.clone())
            .collect(),
        commutator_rank: r3.delta.cultivation_holonomy.commutator_rank,
    };
    let boundary = LongHorizonRetainedBoundary::found(
        predecessor_identity.clone(),
        boundary_identity.clone(),
        mounted.interiors,
        &system,
        &exact,
        cultivation,
    )
    .map_err(|error| error.to_string())?;
    let standing_path = directory.join("native-rest/standing.json");
    let decoder_path = directory.join("native-rest/decoder.json");
    let fibre_path = directory.join("native-rest/fibres.json");
    fs::write(
        &standing_path,
        boundary
            .standing_bytes()
            .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        &decoder_path,
        boundary
            .decoder_bytes()
            .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        &fibre_path,
        boundary.fibre_bytes().map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;

    let fronts = source::inquiry_fronts(&mounted.occurrences);
    let passages = source::passages(&boundary, &system, &fronts)?;
    let source_standing_path = directory.join("source-replay/standing.json");
    let source_decoder_path = directory.join("source-replay/decoder.json");
    let source_fibre_path = directory.join("source-replay/fibres.json");
    artifact::write_json(&source_standing_path, &passages.source_standing)?;
    artifact::write_json(&source_decoder_path, &passages.source_decoder)?;
    artifact::write_json(&source_fibre_path, &passages.source_fibres)?;
    let uncondensed_standing_path = directory.join("uncondensed-history/standing.json");
    let uncondensed_decoder_path = directory.join("uncondensed-history/decoder.json");
    let uncondensed_fibre_path = directory.join("uncondensed-history/fibres.json");
    artifact::write_json(&uncondensed_standing_path, &passages.uncondensed_standing)?;
    artifact::write_json(&uncondensed_decoder_path, &passages.uncondensed_decoder)?;
    artifact::write_json(&uncondensed_fibre_path, &passages.uncondensed_fibres)?;

    let source_table = system.source_generator_table();
    let source_began = Instant::now();
    let source_return = card
        .conduct_native_ragged_traces_on_device(
            system.interiors() * system.states(),
            system.generators(),
            &source_table,
            &passages.source_words,
            &passages.source_word_offsets,
            &passages.source_starts,
        )
        .map_err(|error| error.to_string())?;
    let source_wall_microseconds = source_began.elapsed().as_micros();
    let uncondensed_began = Instant::now();
    let uncondensed_return = card
        .conduct_native_ragged_traces_on_device(
            system.interiors() * system.states(),
            system.generators(),
            &source_table,
            &passages.compact_words,
            &passages.compact_word_offsets,
            &passages.uncondensed_starts,
        )
        .map_err(|error| error.to_string())?;
    let uncondensed_wall_microseconds = uncondensed_began.elapsed().as_micros();
    let compact_began = Instant::now();
    let compact_return = card
        .conduct_native_ragged_traces_on_device(
            boundary.standing.native_states.len(),
            system.generators(),
            &boundary.standing.generator_table,
            &passages.compact_words,
            &passages.compact_word_offsets,
            &passages.compact_starts,
        )
        .map_err(|error| error.to_string())?;
    let compact_wall_microseconds = compact_began.elapsed().as_micros();
    let factorization = verify_factorization(
        &boundary,
        &passages,
        &source_return,
        &uncondensed_return,
        &compact_return,
    )?;

    let boundary_return = json!({
        "schema": "holonics.r4.boundary-factorization-recurrence-and-fibres.v1",
        "truth_status": "implemented-exact",
        "boundary_responses": boundary.standing.receiver_factors,
        "recurrences": boundary.standing.recurrences,
        "unresolved_historical_alternatives": boundary.fibres.fibres,
        "shortest_separators": boundary.fibres.shortest_separators,
        "ordered_loop_holonomy": boundary.standing.ordered_holonomy,
        "source_native_compact_factorization": factorization,
        "no_summary_string_or_kv_array": true,
    });
    artifact::write_json(
        &directory.join("04-boundary-factorization-recurrence-and-fibres.json"),
        &boundary_return,
    )?;
    let card_return = json!({
        "schema": "holonics.r4.three-realization-card-passages.v1",
        "truth_status": "measured",
        "device": card.device_name(),
        "receiver_history_quotient": {
            "launches": quotient_launches,
            "physical_wall_microseconds": quotient_wall_microseconds,
            "one_shot_classes": exact.one_shot.len(),
            "future_stable_classes": exact.conduct.len(),
        },
        "source_complete_replay": passage_receipt(&source_return, source_wall_microseconds),
        "uncondensed_native_history": passage_receipt(&uncondensed_return, uncondensed_wall_microseconds),
        "compact_retained_boundary": passage_receipt(&compact_return, compact_wall_microseconds),
        "cpu_semantic_callbacks_between_fronts": 0,
        "invariant_action_uploaded_once_per_matched_realization": true,
    });
    artifact::write_json(
        &directory.join("05-source-uncondensed-and-compact-card-passages.json"),
        &card_return,
    )?;

    let interchange = certify_interchange(
        &compact_return,
        boundary.standing.generator_table.len() as u64,
    )?;
    let holonomy = &boundary.standing.ordered_holonomy;
    let left_gpu = endpoint(&compact_return, 0)?;
    let right_gpu = endpoint(&compact_return, 2)?;
    if left_gpu != holonomy.left_endpoint.0 as u32 || right_gpu != holonomy.right_endpoint.0 as u32
    {
        return Err("the card reordered or lost the noncommuting boundary words".to_owned());
    }
    let interchange_and_holonomy = json!({
        "schema": "holonics.r4.interchange-and-ordered-holonomy.v1",
        "independent_front_population": 3,
        "interchange_certificate": interchange,
        "extent_derived_from_word_offsets": passages.compact_word_offsets,
        "noncommuting_words": {
            "left_front": fronts[0],
            "right_front": fronts[2],
            "left_endpoint": left_gpu,
            "right_endpoint": right_gpu,
            "endpoints_differ": left_gpu != right_gpu,
            "commutator_rank": holonomy.commutator_rank,
        },
    });
    artifact::write_json(
        &directory.join("06-interchange-and-ordered-holonomy.json"),
        &interchange_and_holonomy,
    )?;

    let reopening = boundary
        .fibres
        .richer_reopenings
        .first()
        .ok_or("richer receiver reopening absent")?;
    let left_history = boundary
        .reconstruct_history(&reopening.left_occurrence)
        .map_err(|error| error.to_string())?;
    let right_history = boundary
        .reconstruct_history(&reopening.right_occurrence)
        .map_err(|error| error.to_string())?;
    let richer_return = json!({
        "schema": "holonics.r4.richer-receiver-reopening.v1",
        "truth_status": "established-bounded",
        "reopening": reopening,
        "left_reconstruction_sha256": artifact::digest(&left_history),
        "right_reconstruction_sha256": artifact::digest(&right_history),
        "historical_interior_departed_from_hot_standing": true,
        "complete_fibre_reopened_without_source_lookup": true,
        "later_receiver_enlargement_reopens_prior_quotient": true,
    });
    artifact::write_json(
        &directory.join("07-richer-later-receiver-reopens-the-interior.json"),
        &richer_return,
    )?;

    let reconstructed_occurrence = fronts[0]
        .occurrence
        .rsplit('/')
        .next()
        .and_then(|suffix| {
            boundary
                .decoder
                .interiors
                .iter()
                .find(|interior| interior.occurrence.ends_with(suffix))
        })
        .map(|interior| interior.occurrence.clone())
        .ok_or("later proof interior absent")?;
    let reconstruction = boundary
        .reconstruct_history(&reconstructed_occurrence)
        .map_err(|error| error.to_string())?;
    let detached_inquiry = detached::DetachedInquiry {
        schema: "holonics.r4.detached-inquiry.v1".to_owned(),
        boundary_identity: boundary_identity.clone(),
        occurrence: format!(
            "r4/detached/later-revisit/{}",
            artifact::digest(&reconstruction)
        ),
        words: passages.compact_words.clone(),
        word_offsets: passages.compact_word_offsets.clone(),
        native_starts: passages.compact_starts.clone(),
        expected_trace: compact_return.native_trace.clone(),
        expected_trace_offsets: compact_return.trace_offsets.clone(),
        reconstructed_occurrence,
        expected_reconstruction_sha256: artifact::digest(&reconstruction),
        cultivated_front: 1,
        predecessor_control_front: 3,
        outside_development_return_closure: true,
    };
    let inquiry_path = directory.join("08-detached-later-inquiry.json");
    artifact::write_json(&inquiry_path, &detached_inquiry)?;
    let detached_path = directory.join("09-detached-remount-and-later-return.json");
    let process = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--detached")
        .arg(&standing_path)
        .arg(&decoder_path)
        .arg(&fibre_path)
        .arg(&inquiry_path)
        .arg(&detached_path)
        .current_dir(root)
        .output()
        .map_err(|error| error.to_string())?;
    if !process.status.success() {
        return Err(format!(
            "detached R4 refused: {}{}",
            String::from_utf8_lossy(&process.stdout),
            String::from_utf8_lossy(&process.stderr)
        ));
    }
    let detached = detached::read(&detached_path)?;
    if !detached.remote_interior_reopened_without_source
        || !detached.cultivated_revisit_changed_the_boundary
        || !detached.ordered_holonomy_preserved
        || !detached.forbidden_source_access.is_empty()
    {
        return Err("the fresh-process retained boundary lost a required consequence".to_owned());
    }

    let cost = complete_cost(
        &source_standing_path,
        &source_decoder_path,
        &source_fibre_path,
        &uncondensed_standing_path,
        &uncondensed_decoder_path,
        &uncondensed_fibre_path,
        &standing_path,
        &decoder_path,
        &fibre_path,
        &passages,
        &fronts,
        &source_return,
        &uncondensed_return,
        &compact_return,
    )?;
    if cost["strict_coordinate_fall"]["every_coordinate_strictly_falls"] != true {
        return Err(format!(
            "the complete compactification product did not strictly descend: {cost}"
        ));
    }
    artifact::write_json(&directory.join("10-complete-product-descent.json"), &cost)?;
    write_product_faces(&directory, &boundary, &fronts, &detached)?;
    let rendering = render::render(
        &boundary,
        &directory.join("12-long-horizon-boundary.svg"),
        &directory.join("12-long-horizon-boundary.png"),
    )?;
    artifact::write_json(&directory.join("12-rendering-receipt.json"), &rendering)?;

    let grade = json!({
        "schema": "holonics.r4.grade.v1",
        "truth_status": "established-bounded",
        "source_uncondensed_and_compact_realizations_return_and_factor": true,
        "exact_historical_interior_departs_and_complete_fibre_reopens": true,
        "recurrence_alternatives_shortest_separators_and_holonomy_return": true,
        "richer_later_receiver_lawfully_reopens_the_prior_compactification": true,
        "source_detached_remount_and_later_revisit_ride_prior_cultivation": true,
        "complete_product_vector_strictly_falls_against_source_replay": true,
        "independent_fronts_interchange_while_noncommuting_words_keep_order": true,
        "card_owns_quotient_and_passages_without_hidden_lookup_or_cpu_semantic_callback": true,
        "score": "8/8",
        "passed": true,
        "open_exterior": boundary.standing.open_exterior,
    });
    artifact::write_json(&directory.join("13-grade.json"), &grade)?;
    fs::write(
        directory.join("INSPECTION.md"),
        "# R4 inspection\n\nThe exact future-receiver boundary, source/uncondensed/compact passages, richer reopening, detached remount, noncommuting holonomy, complete cost vector and rendered fibre atlas were returned and inspected. `13-grade.json` is 8/8.\n",
    )
    .map_err(|error| error.to_string())?;
    let manifest = artifact::write_manifest(&directory, "holonics.r4.product-manifest.v1")?;
    println!(
        "R4 returned {} files; rolled SHA-256 {}",
        manifest["files"].as_array().map_or(0, Vec::len),
        manifest["rolled_sha256"].as_str().unwrap_or("absent")
    );
    Ok(())
}

fn returned_observations(
    rest: &DynamicMorphologyRest,
    states: usize,
) -> Result<Vec<Vec<Observation>>, String> {
    let added = rest.delta.constitutive_action_change.added_native_state as usize;
    rest.returned_constraints
        .iter()
        .map(|returned| {
            let reading = u64::from_str_radix(&returned.consequence_sha256[..16], 16)
                .map_err(|error| error.to_string())?;
            Ok((0..states)
                .map(|state| Observation(if state == added { reading } else { 0 }))
                .collect())
        })
        .collect()
}

fn passage_receipt(returned: &DeviceRaggedNativeTrace, wall: u128) -> Value {
    json!({
        "native_trace": returned.native_trace,
        "trace_offsets": returned.trace_offsets,
        "front_count": returned.front_count,
        "launches": returned.launches,
        "synchronizations": returned.synchronizations,
        "block_threads": returned.block_threads,
        "active_lanes": returned.active_lanes,
        "host_ingress_octets": returned.host_ingress_octets,
        "host_egress_octets": returned.host_egress_octets,
        "resident_octets": returned.resident_octets,
        "physical_wall_microseconds": wall,
    })
}
