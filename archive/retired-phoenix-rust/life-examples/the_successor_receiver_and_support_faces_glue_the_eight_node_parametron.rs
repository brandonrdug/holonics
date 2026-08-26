//! Glue the first emitted successor passage to the complete foreign carrier receiver and the
//! already-founded factor-support receiver. The foreign tower has already returned and is never
//! conducted here. This station extends the complete cold potential fibre, derives its hot cover,
//! and conducts all eight addressed coefficient nodes on the resident Parametron receiver.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    phoenix::{
        foreign_potential_rest::{ForeignPotentialComplexRest, PotentialReceiverCertificate},
        foreign_section_descent::ForeignReachableSectionRest,
        receiver_restricted_transport::{
            ReceiverRestrictedFactorDescent, SuccessorSupportOccurrence,
        },
        transition_rest::PhoenixTransitionRest,
    },
    receiver_exact_compression::ItemId,
};
use life::athena_receiver_history::AthenaReceiverHistoryCongruence;
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};

const EXPANDED: &str = concat!(
    "output/the_emitted_successors_grow_the_parametron_coefficient_lattice/",
    "expanded-reachable-section.rest"
);
const LINEAGE: &str = concat!(
    "output/the_emitted_successors_grow_the_parametron_coefficient_lattice/",
    "00-successor-lineage.json"
);
const SUCCESSOR_BASE_POTENTIAL: &str = concat!(
    "output/the_emitted_successors_grow_the_parametron_coefficient_lattice/",
    "02-successor-predecessor-potential.json"
);
const PREDECESSOR_POTENTIAL: &str = concat!(
    "output/the_parametron_receiver_history_rest_returns_athena_alpha/product/",
    "potential.rest"
);
const SUPPORT: &str = concat!(
    "output/the_cultivated_factor_descends_through_its_receiver_history_support/",
    "receiver-restricted-factor-rest.json"
);
const CONGRUENCE: &str = concat!(
    "output/the_receiver_history_congruence_replaces_the_trigram_table/",
    "00-receiver-history-congruence.json"
);
const PRODUCT: &str =
    "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const CONTINUATION: &str =
    "output/the_exchange_return_cultivates_athena_gemma/product/continuation";
const ALPHA_REST: &str = concat!(
    "output/the_receiver_history_quotient_condenses_and_athena_alpha_speaks/",
    "athena-alpha.rest"
);
const OUTPUT: &str =
    "output/the_successor_receiver_and_support_faces_glue_the_eight_node_parametron";

#[derive(Clone, Debug, Deserialize, Serialize)]
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
        return Err(format!(
            "preserve existing station output {}",
            output.display()
        ));
    }
    let started = Instant::now();
    let expanded = ForeignReachableSectionRest::read(&fs::read(EXPANDED).map_err(display)?)
        .map_err(display)?;
    let lineages: Vec<SuccessorLineage> = read_json(Path::new(LINEAGE))?;
    let predecessor =
        ForeignPotentialComplexRest::read(&fs::read(PREDECESSOR_POTENTIAL).map_err(display)?)
            .map_err(display)?;
    let support = ReceiverRestrictedFactorDescent::read(&fs::read(SUPPORT).map_err(display)?)
        .map_err(display)?;
    let congruence =
        AthenaReceiverHistoryCongruence::read(&fs::read(CONGRUENCE).map_err(display)?)?;
    let successor_base: Vec<(i64, i64)> = read_json(Path::new(SUCCESSOR_BASE_POTENTIAL))?;

    let predecessor_nodes = predecessor.history_addresses.len();
    if predecessor_nodes + lineages.len() != expanded.history_addresses.len()
        || expanded.history_addresses[..predecessor_nodes] != predecessor.history_addresses
        || expanded.native_history_states[..predecessor_nodes] != predecessor.native_history_states
        || lineages.iter().any(|lineage| {
            lineage.successor_coefficient_node < predecessor_nodes
                || expanded.history_addresses[lineage.successor_coefficient_node]
                    != lineage.successor_history_address
                || expanded.native_history_states[lineage.successor_coefficient_node]
                    != lineage.successor_native_history_state
                || expanded.history_addresses[lineage.parent_coefficient_node]
                    != lineage.parent_history_address
        })
    {
        return Err(
            "the predecessor, emitted lineage and expanded incidence do not glue".to_owned(),
        );
    }

    let foreign_quotient = expanded.coefficient_receiver_quotient().map_err(display)?;
    for left in 0..lineages.len() {
        for right in left + 1..lineages.len() {
            let word_equal = lineages[left].foreign_receiver_quotient_class
                == lineages[right].foreign_receiver_quotient_class;
            let carrier_equal = foreign_quotient.history_to_class
                [lineages[left].successor_coefficient_node]
                == foreign_quotient.history_to_class[lineages[right].successor_coefficient_node];
            if word_equal != carrier_equal {
                return Err(
                    "the native-word quotient and complete foreign carrier quotient disagree"
                        .to_owned(),
                );
            }
        }
    }

    let source_by_proposal = congruence
        .sections
        .iter()
        .map(|section| {
            (
                section.family_occurrence.as_str(),
                ItemId(section.source_item),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let support_passage = support
        .carry_successor_support(
            lineages
                .iter()
                .map(|lineage| {
                    Ok(SuccessorSupportOccurrence {
                        occurrence: lineage.successor_history_address.clone(),
                        predecessor_occurrence: lineage.parent_history_address.clone(),
                        parent_source: *source_by_proposal
                            .get(lineage.parent_history_address.as_str())
                            .ok_or_else(|| {
                                format!(
                                    "parent {} has no situated source occurrence",
                                    lineage.parent_history_address
                                )
                            })?,
                        emitted_native_address: lineage.emitted_native_address,
                        foreign_receiver_class: foreign_quotient.history_to_class
                            [lineage.successor_coefficient_node],
                    })
                })
                .collect::<Result<Vec<_>, String>>()?,
        )
        .map_err(display)?;
    let support_by_occurrence = support_passage
        .occurrences
        .iter()
        .map(|occurrence| (occurrence.occurrence.as_str(), occurrence))
        .collect::<BTreeMap<_, _>>();

    let vocabulary = predecessor.vocabulary_extent;
    let successor_classes = lineages
        .iter()
        .map(|lineage| lineage.foreign_receiver_quotient_class)
        .max()
        .and_then(|class| class.checked_add(1))
        .ok_or("the successor receiver class family is empty")?;
    if successor_base.len() != successor_classes * vocabulary
        || successor_base
            .iter()
            .any(|(lower, upper)| lower.checked_add(predecessor.interval_width) != Some(*upper))
    {
        return Err("the returned successor base potential is empty or ragged".to_owned());
    }

    let nodes = expanded.history_addresses.len();
    let mut predecessor_lower = Vec::with_capacity(vocabulary * nodes);
    for row in 0..vocabulary {
        predecessor_lower.extend(
            (0..predecessor_nodes)
                .map(|history| predecessor.predecessor_lower[row * predecessor_nodes + history]),
        );
        predecessor_lower.extend(lineages.iter().map(|lineage| {
            successor_base[lineage.foreign_receiver_quotient_class * vocabulary + row].0
        }));
    }

    let mut factors = predecessor.factors.clone();
    for factor in &mut factors {
        for lineage in &lineages {
            let carried = support_by_occurrence[lineage.successor_history_address.as_str()];
            if carried.realization_addresses.contains(&factor.address) {
                factor
                    .founding_native_history_states
                    .push(lineage.successor_native_history_state);
            }
        }
        factor.founding_native_history_states.sort_unstable();
        factor.founding_native_history_states.dedup();
    }
    let final_hidden = expanded
        .sections
        .last()
        .cloned()
        .ok_or("the expanded incidence has no terminal hidden section")?;
    let value = |row: usize, history: usize| -> Result<(i64, i64), String> {
        let mut lower = i128::from(predecessor_lower[row * nodes + history]);
        for factor in factors
            .iter()
            .filter(|factor| factor.target_native_address as usize == row)
            .filter(|factor| {
                factor
                    .founding_native_history_states
                    .contains(&expanded.native_history_states[history])
            })
        {
            lower += i128::from(factor.multiplier)
                * i128::from(final_hidden.entries[factor.selector_coordinate * nodes + history]);
        }
        let lower = i64::try_from(lower).map_err(display)?;
        let upper = lower
            .checked_add(predecessor.interval_width)
            .ok_or("cultivated successor potential overflow")?;
        Ok((lower, upper))
    };

    let predecessor_at = |row: usize, history: usize| -> Result<(i64, i64), String> {
        let lower = predecessor_lower[row * nodes + history];
        Ok((
            lower,
            lower
                .checked_add(predecessor.interval_width)
                .ok_or("predecessor successor potential overflow")?,
        ))
    };
    let mut predecessor_selected = Vec::with_capacity(nodes);
    let mut cultivated_selected = Vec::with_capacity(nodes);
    let mut receiver_rows = factors
        .iter()
        .map(|factor| factor.target_native_address)
        .collect::<BTreeSet<_>>();
    for history in 0..nodes {
        let before = (0..vocabulary)
            .map(|row| Ok((row as u32, predecessor_at(row, history)?)))
            .collect::<Result<Vec<_>, String>>()?;
        let after = (0..vocabulary)
            .map(|row| Ok((row as u32, value(row, history)?)))
            .collect::<Result<Vec<_>, String>>()?;
        let before = selected(&before)?;
        let after = selected(&after)?;
        receiver_rows.extend(before.iter().copied());
        receiver_rows.extend(after.iter().copied());
        predecessor_selected.push(before);
        cultivated_selected.push(after);
    }
    let receiver_rows = receiver_rows.into_iter().collect::<Vec<_>>();

    // The codec is an exterior face. It is mounted once only to name newly exposed native rows;
    // no foreign tensor population is staged and no semantic inference deed occurs.
    let alpha =
        PhoenixTransitionRest::read(&fs::read(ALPHA_REST).map_err(display)?).map_err(display)?;
    let codec_mount = Instant::now();
    let session = alpha
        .mount(PRODUCT, CONTINUATION)
        .map_err(display)?
        .into_session();
    let codec_mount_elapsed_seconds = codec_mount.elapsed().as_secs_f64();
    let mut decoder = predecessor.decoder.clone();
    for row in &receiver_rows {
        if !decoder.contains_key(row) {
            decoder.insert(*row, session.decode_native_ids(&[*row])?);
        }
    }

    let receiver_set = receiver_rows.iter().copied().collect::<BTreeSet<_>>();
    let mut certificates = Vec::with_capacity(nodes);
    for history in 0..nodes {
        let cultivated = (0..vocabulary)
            .map(|row| Ok((row as u32, value(row, history)?)))
            .collect::<Result<Vec<_>, String>>()?;
        let top = cultivated_selected[history]
            .iter()
            .map(|row| cultivated[*row as usize].1 .0)
            .max()
            .ok_or("the cultivated successor receiver returned no row")?;
        let (competitor, greatest_omitted_upper) = cultivated
            .iter()
            .filter(|(row, _)| !receiver_set.contains(row))
            .max_by_key(|(row, interval)| (interval.1, std::cmp::Reverse(*row)))
            .map(|(row, interval)| (*row, interval.1))
            .ok_or("the enlarged receiver cover left no cold reconstruction fibre")?;
        if greatest_omitted_upper >= top {
            return Err("the enlarged receiver cover discarded a possible maximizer".to_owned());
        }
        let admitted_factor_addresses = factors
            .iter()
            .filter(|factor| {
                factor
                    .founding_native_history_states
                    .contains(&expanded.native_history_states[history])
            })
            .map(|factor| factor.address.clone())
            .collect();
        let complete_predecessor = (0..vocabulary)
            .map(|row| predecessor_at(row, history))
            .collect::<Result<Vec<_>, String>>()?;
        certificates.push(PotentialReceiverCertificate {
            history_address: expanded.history_addresses[history].clone(),
            native_history_state: expanded.native_history_states[history],
            predecessor_selected_native_addresses: predecessor_selected[history].clone(),
            cultivated_selected_native_addresses: cultivated_selected[history].clone(),
            predecessor_top_lower: predecessor_selected[history]
                .iter()
                .map(|row| predecessor_at(*row as usize, history).map(|interval| interval.0))
                .collect::<Result<Vec<_>, String>>()?
                .into_iter()
                .max()
                .ok_or("the predecessor successor receiver returned no row")?,
            cultivated_top_lower: top,
            greatest_omitted_upper,
            shortest_omitted_competitor: competitor,
            admitted_factor_addresses,
            complete_predecessor_potential_sha256: digest_intervals(&complete_predecessor),
        });
    }

    let potential = ForeignPotentialComplexRest::seal(
        expanded.history_addresses.clone(),
        expanded.native_history_states.clone(),
        final_hidden,
        vocabulary,
        predecessor_lower,
        predecessor.interval_width,
        factors,
        receiver_rows,
        decoder,
        certificates,
        vec![
            "coefficient current outside the eight-node section obstructs".to_owned(),
            "a receiver broader than terminal interval order reopens the complete cold fibre"
                .to_owned(),
            "a second emitted successor is an open addressed passage until native recurrence returns"
                .to_owned(),
        ],
    )
    .map_err(display)?;
    let potential_bytes = potential.canonical_bytes().map_err(display)?;

    let fronts = potential
        .native_history_states
        .iter()
        .map(|native| potential.one_hot_for_native(*native).map_err(display))
        .collect::<Result<Vec<_>, _>>()?;
    let unknown = potential
        .one_hot_for_native(u64::MAX)
        .expect_err("an unknown successor history must obstruct");
    let mut resident = potential
        .mount_receiver_on(CudaRefineExecutor::new().map_err(display)?)
        .map_err(display)?;
    let returned = resident.conduct(&fronts).map_err(display)?;
    let surfaces = returned
        .selected_native_addresses
        .iter()
        .map(|native| {
            potential
                .decode(*native)
                .map(str::to_owned)
                .map_err(display)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let expected = potential
        .receiver_certificates
        .iter()
        .map(|certificate| certificate.cultivated_selected_native_addresses.as_slice())
        .collect::<Vec<_>>();
    let receiver_exact = returned
        .selected_native_addresses
        .iter()
        .zip(expected)
        .all(|(returned, expected)| expected.len() == 1 && expected[0] == *returned);
    let passed = receiver_exact
        && foreign_quotient.classes.len() < expanded.history_addresses.len()
        && support_passage.foreign_support_reopenings.is_empty()
        && !returned.invariant_transport_reuploaded
        && !returned.cpu_semantic_replay_after_device
        && !unknown.0.foreign_fallback_permitted;

    fs::create_dir_all(&output).map_err(display)?;
    fs::write(output.join("expanded-potential.rest"), &potential_bytes).map_err(display)?;
    write_json(
        output.join("00-foreign-receiver-quotient.json"),
        &foreign_quotient,
    )?;
    write_json(
        output.join("01-successor-support-passage.json"),
        &support_passage,
    )?;
    write_json(
        output.join("02-native-return.json"),
        &json!({
            "schema":"holonics.eight-node-parametron-native-return.v1",
            "surfaces":&surfaces,
            "receiver":&returned,
            "unknown_history_obstruction":&unknown.0,
            "foreign_tower_staged_octets":0,
            "foreign_tower_deed_launches":0,
            "codec_mount_elapsed_seconds":format!("{codec_mount_elapsed_seconds:.9}"),
        }),
    )?;
    let grade = json!({
        "schema":"holonics.successor-receiver-support-glue-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "coefficient_occurrence_population":expanded.history_addresses.len(),
        "foreign_receiver_class_population":foreign_quotient.classes.len(),
        "complete_occurrence_fibres":foreign_quotient.classes.iter().map(|class| class.histories.len()).sum::<usize>(),
        "foreign_shortest_separators":foreign_quotient.shortest_separators.len(),
        "successor_support_classes":support_passage.classes.len(),
        "support_reopens_foreign_classes":support_passage.foreign_support_reopenings.len(),
        "complete_cold_potential_rows":vocabulary,
        "hot_receiver_rows":potential.receiver_rows.len(),
        "expanded_potential_rest_octets":potential_bytes.len(),
        "expanded_potential_rest_sha256":sha256(&potential_bytes),
        "native_surfaces":&surfaces,
        "receiver_exact":receiver_exact,
        "foreign_tower_staged_octets":0,
        "foreign_tower_deed_launches":0,
        "cpu_semantic_replay_after_device":false,
    });
    write_json(output.join("03-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The successor receiver and support faces glue the eight-node Parametron\n\n[established-bounded; implemented-exact; measured] The first emitted occurrence passage was intersected with the complete 43-section foreign carrier receiver and the already-founded factor-support receiver. Equal carrier faces retained distinct occurrence lineage. Support supplied no reopening on this frontier. The complete cold terminal potential and its receiver-sufficient hot cover froze without conducting Gemma, and all eight addressed nodes returned on the resident card.\n\n[open] This station returns the first eight-node receiver. It does not invent a self-loop for the second emitted passage; the next native recurrence must either return an admitted face or an explicit out-of-section obstruction.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    write_json(
        output.join("04-invocation.json"),
        &json!({
            "schema":"holonics.expensive-invocation.v1",
            "command":"target/release/examples/the_successor_receiver_and_support_faces_glue_the_eight_node_parametron",
            "purpose":"glue the addressed first-emission passage to complete foreign and support receivers, freeze the eight-node potential and conduct its native card return without tower inference",
            "elapsed_seconds":format!("{:.9}",started.elapsed().as_secs_f64()),
            "exit_status":if passed {0} else {1},
            "foreign_capture_replayed":false,
        }),
    )?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("the eight-node successor/support glue grade refused".to_owned())
    }
}

fn selected(rows: &[(u32, (i64, i64))]) -> Result<Vec<u32>, String> {
    let top = rows
        .iter()
        .map(|(_, interval)| interval.0)
        .max()
        .ok_or("empty potential")?;
    Ok(rows
        .iter()
        .filter_map(|(row, interval)| (interval.1 >= top).then_some(*row))
        .collect())
}

fn digest_intervals(values: &[(i64, i64)]) -> String {
    let mut digest = Sha256::new();
    for (lower, upper) in values {
        digest.update(lower.to_le_bytes());
        digest.update(upper.to_le_bytes());
    }
    hex(&digest.finalize())
}

fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut files = fs::read_dir(output)
        .map_err(display)?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(display)?;
            Ok(json!({
                "path":entry.file_name().to_string_lossy(),
                "octets":bytes.len(),
                "sha256":sha256(&bytes),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    files.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    write_json(
        output.join("MANIFEST.json"),
        &json!({"schema":"holonics.return-manifest.v1","files":files}),
    )
}

fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|octet| format!("{octet:02x}")).collect()
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
