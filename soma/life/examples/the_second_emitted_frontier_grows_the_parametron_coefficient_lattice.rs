//! Cross exactly the four addressed second-emission obstructions in one foreign construction
//! passage. The predecessor eight-node rest remains immutable; the returned columns enlarge its
//! exact coefficient incidence and the resulting rest contains no foreign tower.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    phoenix::{
        alpha_rest::AthenaAlphaNativeRest,
        foreign_potential_rest::{
            AddressedPotentialSectionObstruction, ForeignPotentialComplexRest,
        },
        foreign_section_descent::{CarrierSectionRest, ForeignReachableSectionRest},
        streamed::InterventionSite,
        tower::Intervention,
    },
    receiver_exact_compression::ItemId,
};
use life::{
    athena_receiver_history::AthenaReceiverHistoryCongruence,
    athena_returned_defect::CandidateRequest,
};
use serde::Serialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const PRODUCT: &str =
    "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const CONTINUATION: &str =
    "output/the_exchange_return_cultivates_athena_gemma/product/continuation";
const ALPHA_REST: &str = concat!(
    "output/the_receiver_history_quotient_condenses_and_athena_alpha_speaks/",
    "athena-alpha.rest"
);
const REQUESTS: &str =
    "output/the_candidate_departs_before_sibling_testimony_returns/candidate-input.json";
const CONGRUENCE: &str = concat!(
    "output/the_receiver_history_congruence_replaces_the_trigram_table/",
    "00-receiver-history-congruence.json"
);
const PREDECESSOR_SECTION: &str = concat!(
    "output/the_emitted_successors_grow_the_parametron_coefficient_lattice/",
    "expanded-reachable-section.rest"
);
const PREDECESSOR_GRADE: &str = concat!(
    "output/the_emitted_successors_grow_the_parametron_coefficient_lattice/",
    "03-grade.json"
);
const POTENTIAL: &str = concat!(
    "output/the_eight_node_parametron_rest_returns_athena_alpha/product/",
    "potential.rest"
);
const OBSTRUCTIONS: &str = concat!(
    "output/the_second_emission_returns_its_out_of_section_receipt/",
    "00-addressed-out-of-section.json"
);
const OUTPUT: &str =
    "output/the_second_emitted_frontier_grows_the_parametron_coefficient_lattice";

#[derive(Debug, Serialize)]
struct SuccessorLineage {
    parent_history_address: String,
    parent_coefficient_node: usize,
    parent_native_history_state: u64,
    emitted_native_address: u32,
    emitted_surface: String,
    successor_history_address: String,
    successor_coefficient_node: usize,
    successor_native_history_state: u64,
    native_word_population: usize,
    foreign_receiver_quotient_class: usize,
}

fn main() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing station output {}", output.display()));
    }
    let started = Instant::now();
    let requests: Vec<CandidateRequest> = read_json(Path::new(REQUESTS))?;
    let predecessor = ForeignReachableSectionRest::read(
        &fs::read(PREDECESSOR_SECTION).map_err(display)?,
    )
    .map_err(display)?;
    let potential = ForeignPotentialComplexRest::read(&fs::read(POTENTIAL).map_err(display)?)
        .map_err(display)?;
    let obstructions: Vec<AddressedPotentialSectionObstruction> =
        read_json(Path::new(OBSTRUCTIONS))?;
    let predecessor_grade: Value = read_json(Path::new(PREDECESSOR_GRADE))?;
    if predecessor.history_addresses != potential.history_addresses
        || predecessor.native_history_states != potential.native_history_states
        || obstructions.is_empty()
    {
        return Err("predecessor section, potential and returned obstruction disagree".to_owned());
    }

    let congruence = AthenaReceiverHistoryCongruence::read(
        &fs::read(CONGRUENCE).map_err(display)?,
    )?;
    let source_by_proposal = congruence
        .sections
        .iter()
        .map(|section| (section.family_occurrence.as_str(), ItemId(section.source_item)))
        .collect::<BTreeMap<_, _>>();
    let request_by_proposal = requests
        .iter()
        .map(|request| (request.proposal.as_str(), request))
        .collect::<BTreeMap<_, _>>();

    let alpha = AthenaAlphaNativeRest::read(&fs::read(ALPHA_REST).map_err(display)?)
        .map_err(display)?;
    let mount_started = Instant::now();
    let session = alpha
        .mount(PRODUCT, CONTINUATION)
        .map_err(display)?
        .into_session();
    let cold_mount_elapsed_seconds = mount_started.elapsed().as_secs_f64();
    eprintln!(
        "authenticated one continuing ProductSession in {cold_mount_elapsed_seconds:.6} seconds"
    );

    let mut occupied_states = predecessor
        .native_history_states
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut successor_rows = Vec::with_capacity(obstructions.len());
    let mut receiver_class_by_native_word = BTreeMap::<Vec<u32>, usize>::new();
    let mut lineages = Vec::with_capacity(obstructions.len());
    for obstruction in obstructions {
        if obstruction.foreign_fallback_permitted
            || predecessor
                .history_addresses
                .contains(&obstruction.requested_history_address)
        {
            return Err("the second-emission occurrence is not an outside-section refusal".to_owned());
        }
        let parent = predecessor
            .history_addresses
            .iter()
            .position(|address| address == &obstruction.predecessor_history_address)
            .ok_or_else(|| {
                format!(
                    "parent {} is absent from the predecessor section",
                    obstruction.predecessor_history_address
                )
            })?;
        let certificate = &potential.receiver_certificates[parent];
        if certificate.history_address != obstruction.predecessor_history_address
            || certificate.cultivated_selected_native_addresses.as_slice()
                != [obstruction.emitted_native_address]
        {
            return Err("the obstruction is not carried by the predecessor receiver face".to_owned());
        }
        let (root, emitted_word) = addressed_native_suffix(&obstruction.requested_history_address)?;
        let request = request_by_proposal
            .get(root)
            .ok_or_else(|| format!("root history {root} has no candidate request"))?;
        let _source = source_by_proposal
            .get(root)
            .ok_or_else(|| format!("root history {root} has no situated source item"))?;
        let faces = request
            .history_faces
            .iter()
            .map(|face| (face.speaker.as_str(), face.text.as_str()))
            .collect::<Vec<_>>();
        let presented = session.present_exterior_exchange(&faces)?;
        let mut native = session.encode(&presented.text)?;
        native.extend(emitted_word);
        let receiver_class = match receiver_class_by_native_word.get(&native) {
            Some(existing) => *existing,
            None => {
                let next = successor_rows.len();
                receiver_class_by_native_word.insert(native.clone(), next);
                successor_rows.push(native.clone());
                next
            }
        };
        let successor_state = least_unoccupied(&mut occupied_states)?;
        let successor_node = predecessor
            .history_addresses
            .len()
            .checked_add(lineages.len())
            .ok_or("successor coefficient extent overflow")?;
        lineages.push(SuccessorLineage {
            parent_history_address: obstruction.predecessor_history_address,
            parent_coefficient_node: parent,
            parent_native_history_state: predecessor.native_history_states[parent],
            emitted_native_address: obstruction.emitted_native_address,
            emitted_surface: obstruction.emitted_surface,
            successor_history_address: obstruction.requested_history_address,
            successor_coefficient_node: successor_node,
            successor_native_history_state: successor_state,
            native_word_population: native.len(),
            foreign_receiver_quotient_class: receiver_class,
        });
    }

    let returned = session.capture_native_partitioned_layer_sections_with_intervention(
        &successor_rows,
        InterventionSite::Nowhere,
        &Intervention::None,
    )?;
    let receiver = returned
        .cultivated
        .base
        .receiver_faces
        .as_ref()
        .ok_or("the partitioned layer-section receiver returned no faces")?;
    let receiver_classes = successor_rows.len();
    let width = predecessor
        .sections
        .first()
        .map(|section| section.rows)
        .ok_or("predecessor section word is empty")?;
    if receiver.layers.len() + 1 != predecessor.sections.len()
        || receiver
            .layers
            .iter()
            .any(|layer| layer.layer_terminal.len() != receiver_classes * width)
        || receiver.final_normed.len() != receiver_classes * width
        || receiver
            .layers
            .iter()
            .flat_map(|layer| &layer.layer_terminal)
            .chain(&receiver.final_normed)
            .any(|(lower, upper)| lower != upper)
    {
        return Err("second successor carrier family is empty, ragged, or non-point".to_owned());
    }

    let mut sections = Vec::with_capacity(predecessor.sections.len());
    for (at, old) in predecessor.sections.iter().enumerate() {
        let returned_rows = if at < receiver.layers.len() {
            &receiver.layers[at].layer_terminal
        } else {
            &receiver.final_normed
        };
        let mut columns = integer_columns(old);
        for lineage in &lineages {
            let begin = lineage.foreign_receiver_quotient_class * width;
            columns.push(returned_rows[begin..begin + width].to_vec());
        }
        sections.push(
            CarrierSectionRest::from_columns(old.address.clone(), old.grain, &columns)
                .map_err(display)?,
        );
    }
    let mut history_addresses = predecessor.history_addresses.clone();
    history_addresses.extend(
        lineages
            .iter()
            .map(|lineage| lineage.successor_history_address.clone()),
    );
    let mut native_history_states = predecessor.native_history_states.clone();
    native_history_states.extend(
        lineages
            .iter()
            .map(|lineage| lineage.successor_native_history_state),
    );
    let expanded = ForeignReachableSectionRest::seal(
        history_addresses,
        native_history_states,
        sections,
    )
    .map_err(display)?;
    let expanded_bytes = expanded.canonical_bytes().map_err(display)?;
    let mounted = ForeignReachableSectionRest::read(&expanded_bytes)
        .map_err(display)?
        .mount()
        .map_err(display)?;
    let ranks = mounted
        .maps
        .iter()
        .map(|map| map.entering_rank)
        .collect::<BTreeSet<_>>();
    let first_new = predecessor.history_addresses.len();
    let new_nodes_separated = (first_new..first_new + lineages.len()).all(|right| {
        (0..right).any(|left| {
            mounted.maps.iter().any(|map| {
                map.shortest_history_separators.iter().any(|separator| {
                    (separator.left_history == left && separator.right_history == right)
                        || (separator.left_history == right && separator.right_history == left)
                })
            })
        })
    });
    let prior_staged = predecessor_grade["successor_partition_capture_staged_octets"]
        .as_u64()
        .ok_or("predecessor grade has no plural staging census")?;
    let staged = returned.receipt.apparatus_census.streamed.staged_octets;
    let serial_equivalent = staged
        .checked_mul(lineages.len() as u64)
        .ok_or("serial staging comparison overflow")?;
    let grade = json!({
        "schema":"holonics.second-emitted-frontier-parametron-growth-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "predecessor_coefficient_nodes":predecessor.history_addresses.len(),
        "emitted_successor_occurrence_population":lineages.len(),
        "foreign_receiver_quotient_class_population":receiver_classes,
        "receiver_equal_occurrence_population":lineages.len().saturating_sub(receiver_classes),
        "expanded_coefficient_nodes":mounted.rest().history_addresses.len(),
        "captured_layer_sections":receiver.layers.len(),
        "carrier_width":width,
        "carrier_width_authored_as_capacity":false,
        "one_partitioned_foreign_passage":true,
        "foreign_passage_factors_through_exact_native_word_quotient":true,
        "input_partition_rows":returned.receipt.input.presentation.received_rows,
        "input_partition_boundaries":returned.receipt.input.presentation.partition_boundaries,
        "reachable_ranks":ranks,
        "every_enlarged_naturality_square_commutes":mounted.maps.iter().all(|map| map.naturality_commutes),
        "every_successor_node_has_a_current_separator":new_nodes_separated,
        "complete_coefficient_fibres_retained":mounted.maps.iter().all(|map| map.complete_coefficient_kernel.len() == map.entering.columns() - map.entering_rank),
        "prior_plural_capture_staged_octets":prior_staged,
        "second_plural_capture_staged_octets":staged,
        "avoided_serial_staging_octets":serial_equivalent.saturating_sub(staged),
        "tower_deed_launches":returned.receipt.apparatus_census.tower_deed_launches,
        "total_deed_launches":returned.cultivated.total_deed_launches,
        "terminal_synchronizations":returned.receipt.execution.terminal_synchronizations,
        "cpu_semantic_replay_after_device":false,
        "cold_mount_elapsed_seconds":format!("{cold_mount_elapsed_seconds:.9}"),
        "expanded_rest_octets":expanded_bytes.len(),
        "expanded_rest_sha256":sha(&expanded_bytes),
        "foreign_tower_octets_in_expanded_rest":0,
        "passed":mounted.maps.iter().all(|map| map.naturality_commutes)
            && new_nodes_separated
            && staged <= prior_staged
            && returned.receipt.input.presentation.received_rows == receiver_classes
            && returned.receipt.source_access.forbidden.is_empty(),
    });

    fs::create_dir_all(&output).map_err(display)?;
    fs::write(output.join("expanded-reachable-section.rest"), &expanded_bytes).map_err(display)?;
    write_json(output.join("00-successor-lineage.json"), &lineages)?;
    write_json(output.join("01-runtime-receipt.json"), &returned.receipt)?;
    write_json(
        output.join("02-successor-predecessor-potential.json"),
        &returned.cultivated.base.potential,
    )?;
    write_json(output.join("03-grade.json"), &grade)?;
    write_json(
        output.join("04-expensive-invocation.json"),
        &json!({
            "schema":"holonics.expensive-invocation.v1",
            "command":"target/release/examples/the_second_emitted_frontier_grows_the_parametron_coefficient_lattice",
            "purpose":"cross the four returned second-emission obstructions in one plural foreign construction passage and enlarge the exact Complex Parametron incidence",
            "elapsed_seconds":format!("{:.9}",started.elapsed().as_secs_f64()),
            "exit_status":if grade["passed"] == true {0} else {1},
            "foreign_capture_replayed":true,
            "predecessor_rest_sha256":predecessor.identity_sha256,
        }),
    )?;
    write_inspection(&output, &grade)?;
    write_manifest(&output)?;
    if grade["passed"] != true {
        return Err("the second-emitted-frontier lattice grade refused".to_owned());
    }
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    Ok(())
}

fn addressed_native_suffix(address: &str) -> Result<(&str, Vec<u32>), String> {
    let mut parts = address.split("/emission/");
    let root = parts.next().filter(|root| !root.is_empty()).ok_or("empty root occurrence")?;
    let emitted = parts
        .map(|part| part.parse::<u32>().map_err(display))
        .collect::<Result<Vec<_>, _>>()?;
    if emitted.is_empty() {
        return Err("successor occurrence carries no emitted suffix".to_owned());
    }
    Ok((root, emitted))
}

fn integer_columns(section: &CarrierSectionRest) -> Vec<Vec<(i64, i64)>> {
    (0..section.columns)
        .map(|column| {
            (0..section.rows)
                .map(|row| {
                    let value = section.entries[row * section.columns + column];
                    (value, value)
                })
                .collect()
        })
        .collect()
}

fn least_unoccupied(occupied: &mut BTreeSet<u64>) -> Result<u64, String> {
    let next = (0..=u64::MAX)
        .find(|candidate| !occupied.contains(candidate))
        .ok_or("the locked receiver address chart is exhausted")?;
    occupied.insert(next);
    Ok(next)
}

fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn write_inspection(output: &Path, grade: &Value) -> Result<(), String> {
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The second emitted frontier grows the Parametron coefficient lattice\n\n[established-bounded; implemented-exact; measured] The exact four-occurrence obstruction family crossed one block-diagonal foreign construction passage. Every layer returned one carrier row per exact native-word class; the enlarged incidence retains naturality, complete fibres and a separator for every new node without storing the tower.\n\n[open] The new columns must descend through the receiver/history and support square before they can enter frozen inference.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(grade).map_err(display)?
        ),
    )
    .map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut rows = fs::read_dir(output)
        .map_err(display)?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(display)?;
            Ok(json!({
                "path":entry.file_name().to_string_lossy(),
                "octets":bytes.len(),
                "sha256":sha(&bytes),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    rows.sort_by_key(|row| row["path"].as_str().unwrap_or_default().to_owned());
    write_json(
        output.join("MANIFEST.json"),
        &json!({"schema":"holonics.return-manifest.v1","files":rows}),
    )
}

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
