//! Compile the captured foreign terminal section, support-gated cultivation factors and exact
//! terminal-potential fibre into one source-detached Parametron rest. A fresh process conducts
//! native mathematics, retained heterogeneous organ current and plural addressed language fronts
//! on one card without reopening Gemma.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    phoenix::{
        boundary_cultivation::ReturnedBoundaryCultivationRest,
        foreign_potential_rest::{
            ForeignPotentialComplexRest, PotentialReceiverCertificate, RestedPotentialFactor,
        },
        foreign_section_descent::ForeignReachableSectionRest,
        receiver_restricted_transport::ReceiverRestrictedFactorDescent,
    },
};
use life::mathematical_particle::{NativeHexisAthenaRest, NativeSuccessorHistory};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const FOREIGN: &str = concat!(
    "output/the_foreign_tower_descends_on_the_cultivated_reachable_section/",
    "foreign-reachable-section.rest"
);
const CANDIDATES: &str =
    "output/the_candidate_departs_before_sibling_testimony_returns/01-sealed-candidates.json";
const MATCHED: &str =
    "output/the_factor_complex_changes_the_same_body/01-matched-language-returns.json";
const SUPPORTS: &str = concat!(
    "output/the_cultivated_factor_descends_through_its_receiver_history_support/",
    "00-descended-factor-supports.json"
);
const QUOTIENT: &str = concat!(
    "output/the_cultivated_factor_descends_through_its_receiver_history_support/",
    "receiver-restricted-factor-rest.json"
);
const MATHEMATICS: &str =
    "output/recurring_laboratory_transport_condenses_into_native_hexis/native-rest";
const MULTIMODAL: &str = concat!(
    "output/the_returned_arbitrary_organ_consequence_cultivates_the_same_athena_continuation/",
    "native-rest"
);
const OUTPUT: &str = "output/the_parametron_receiver_history_rest_returns_athena_alpha";

#[derive(Debug, Deserialize)]
struct Candidate {
    proposal: String,
    terminal_potential: Vec<(i64, i64)>,
    alternatives: Vec<Surface>,
}

#[derive(Clone, Debug, Deserialize)]
struct Surface {
    native_id: u32,
    surface: String,
    lower: i64,
    upper: i64,
}

#[derive(Debug, Deserialize)]
struct MatchedPair {
    predecessor: Reading,
    successor: Reading,
    changed_rows: Vec<usize>,
}

#[derive(Debug, Deserialize)]
struct Reading {
    proposal: String,
    target_native_id: u32,
    target_surface: String,
    target_interval: (i64, i64),
    maximal: Vec<Surface>,
    potential_sha256: String,
    hidden_sha256: String,
}

#[derive(Debug, Deserialize)]
struct Support {
    realization: Realization,
    native_support: Vec<u64>,
}

#[derive(Debug, Deserialize)]
struct Realization {
    address: String,
    source_factor_addresses: Vec<String>,
    target_row: usize,
    selector_coordinate: usize,
    delta_entry: i64,
}

#[derive(Debug, Deserialize)]
struct MultimodalContinuation {
    candidate_counts: Vec<u32>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ProductManifest {
    schema: String,
    identity_sha256: String,
    files: BTreeMap<String, FileReceipt>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct FileReceipt {
    octets: u64,
    sha256: String,
}

fn main() -> Result<(), String> {
    let args = env::args_os()
        .skip(1)
        .map(PathBuf::from)
        .collect::<Vec<_>>();
    match args.as_slice() {
        [] => construct(Path::new(OUTPUT)),
        [flag, product, output] if flag == "--remount" => remount(product, output),
        _ => Err("usage: [--remount PRODUCT OUTPUT]".to_owned()),
    }
}

fn construct(output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "preserve existing station output {}",
            output.display()
        ));
    }
    let started = Instant::now();
    let candidates: Vec<Candidate> = read_json(Path::new(CANDIDATES))?;
    let pairs: Vec<MatchedPair> = read_json(Path::new(MATCHED))?;
    let supports: Vec<Support> = read_json(Path::new(SUPPORTS))?;
    let mut foreign =
        ForeignReachableSectionRest::read(&fs::read(FOREIGN).map_err(display)?).map_err(display)?;
    let final_hidden = foreign
        .sections
        .pop()
        .ok_or("captured foreign rest has no terminal hidden incidence")?;
    let histories = foreign.history_addresses.len();
    if histories != candidates.len()
        || histories != pairs.len()
        || final_hidden.columns != histories
        || foreign.history_addresses
            != candidates
                .iter()
                .map(|candidate| candidate.proposal.clone())
                .collect::<Vec<_>>()
    {
        return Err(
            "captured history, potential and factor testimony do not share one address family"
                .to_owned(),
        );
    }
    let candidate_by_proposal = candidates
        .iter()
        .map(|candidate| (candidate.proposal.as_str(), candidate))
        .collect::<BTreeMap<_, _>>();
    let pair_by_proposal = pairs
        .iter()
        .map(|pair| (pair.predecessor.proposal.as_str(), pair))
        .collect::<BTreeMap<_, _>>();
    let vocabulary = candidates
        .first()
        .map(|candidate| candidate.terminal_potential.len())
        .ok_or("candidate potential family is empty")?;
    if vocabulary == 0
        || candidates
            .iter()
            .any(|candidate| candidate.terminal_potential.len() != vocabulary)
        || candidates
            .iter()
            .flat_map(|candidate| &candidate.terminal_potential)
            .any(|(lower, upper)| lower.checked_add(1) != Some(*upper))
    {
        return Err(
            "candidate potentials are empty, ragged, or do not share the exact unit interval fibre"
                .to_owned(),
        );
    }

    for (history, proposal) in foreign.history_addresses.iter().enumerate() {
        let candidate = candidate_by_proposal[proposal.as_str()];
        let pair = pair_by_proposal[proposal.as_str()];
        if digest_intervals(&candidate.terminal_potential) != pair.predecessor.potential_sha256
            || digest_hidden(&final_hidden.entries, final_hidden.rows, histories, history)
                != pair.predecessor.hidden_sha256
        {
            return Err(format!(
                "history {proposal} moved between the captured hidden and complete potential testimony"
            ));
        }
    }

    let mut factors = Vec::new();
    for support in supports {
        let supported_histories = foreign
            .native_history_states
            .iter()
            .enumerate()
            .filter_map(|(history, native)| {
                support.native_support.contains(native).then_some(history)
            })
            .collect::<Vec<_>>();
        if supported_histories.is_empty() || support.realization.target_row >= vocabulary {
            return Err("factor support did not meet the captured potential section".to_owned());
        }
        let mut derived = BTreeSet::new();
        for history in &supported_histories {
            let pair = pair_by_proposal[foreign.history_addresses[*history].as_str()];
            if pair.predecessor.target_native_id as usize != support.realization.target_row {
                return Err("factor support and matched target disagree".to_owned());
            }
            let hidden = final_hidden.entries
                [support.realization.selector_coordinate * histories + *history];
            let delta = pair.successor.target_interval.0 - pair.predecessor.target_interval.0;
            if hidden == 0 || delta % hidden != 0 {
                return Err(
                    "returned target difference does not factor through its hidden selector"
                        .to_owned(),
                );
            }
            derived.insert(delta / hidden);
        }
        if derived.len() != 1 {
            return Err(
                "factor multiplier did not descend over its complete founding support".to_owned(),
            );
        }
        let multiplier = *derived.iter().next().expect("one multiplier");
        if multiplier != support.realization.delta_entry {
            return Err("derived factor multiplier moved from its exact returned atom".to_owned());
        }
        factors.push(RestedPotentialFactor {
            address: support.realization.address,
            parent_factor_addresses: support.realization.source_factor_addresses,
            target_native_address: support.realization.target_row as u32,
            selector_coordinate: support.realization.selector_coordinate,
            multiplier,
            founding_native_history_states: support.native_support,
        });
    }
    let factor_targets = factors
        .iter()
        .map(|factor| factor.target_native_address as usize)
        .collect::<BTreeSet<_>>();
    if pairs
        .iter()
        .any(|pair| pair.changed_rows.iter().copied().collect::<BTreeSet<_>>() != factor_targets)
    {
        return Err(
            "complete changed-row testimony does not equal the descended factor target cover"
                .to_owned(),
        );
    }

    let predecessor_lower = (0..vocabulary)
        .flat_map(|row| {
            candidates
                .iter()
                .map(move |candidate| candidate.terminal_potential[row].0)
        })
        .collect::<Vec<_>>();
    let value = |row: usize, history: usize| -> Result<(i64, i64), String> {
        let base = i128::from(predecessor_lower[row * histories + history]);
        let mut delta = 0i128;
        for factor in factors
            .iter()
            .filter(|factor| factor.target_native_address as usize == row)
            .filter(|factor| {
                factor
                    .founding_native_history_states
                    .contains(&foreign.native_history_states[history])
            })
        {
            delta += i128::from(factor.multiplier)
                * i128::from(
                    final_hidden.entries[factor.selector_coordinate * histories + history],
                );
        }
        let lower = i64::try_from(base + delta).map_err(display)?;
        let upper = lower.checked_add(1).ok_or("cultivated interval overflow")?;
        Ok((lower, upper))
    };

    let mut receiver_rows = factors
        .iter()
        .map(|factor| factor.target_native_address)
        .collect::<BTreeSet<_>>();
    let mut predecessor_selected = Vec::new();
    let mut cultivated_selected = Vec::new();
    for history in 0..histories {
        let predecessor = (0..vocabulary)
            .map(|row| (row as u32, candidates[history].terminal_potential[row]))
            .collect::<Vec<_>>();
        let cultivated = (0..vocabulary)
            .map(|row| Ok((row as u32, value(row, history)?)))
            .collect::<Result<Vec<_>, String>>()?;
        let predecessor = selected(&predecessor)?;
        let cultivated = selected(&cultivated)?;
        receiver_rows.extend(predecessor.iter().copied());
        receiver_rows.extend(cultivated.iter().copied());
        predecessor_selected.push(predecessor);
        cultivated_selected.push(cultivated);
    }
    let receiver_rows = receiver_rows.into_iter().collect::<Vec<_>>();

    let mut decoder = BTreeMap::new();
    for surface in candidates
        .iter()
        .flat_map(|candidate| &candidate.alternatives)
        .chain(pairs.iter().flat_map(|pair| &pair.predecessor.maximal))
        .chain(pairs.iter().flat_map(|pair| &pair.successor.maximal))
        .cloned()
        .chain(pairs.iter().map(|pair| Surface {
            native_id: pair.predecessor.target_native_id,
            surface: pair.predecessor.target_surface.clone(),
            lower: pair.predecessor.target_interval.0,
            upper: pair.predecessor.target_interval.1,
        }))
    {
        if surface.lower > surface.upper {
            return Err("decoder testimony carries a reversed interval".to_owned());
        }
        if let Some(existing) = decoder.insert(surface.native_id, surface.surface.clone()) {
            if existing != surface.surface {
                return Err("decoder surface moved at one native address".to_owned());
            }
        }
    }
    if receiver_rows.iter().any(|row| !decoder.contains_key(row)) {
        return Err("receiver-sufficient row cover is not decodable".to_owned());
    }

    let receiver_set = receiver_rows.iter().copied().collect::<BTreeSet<_>>();
    let mut certificates = Vec::new();
    for history in 0..histories {
        let cultivated = (0..vocabulary)
            .map(|row| Ok((row as u32, value(row, history)?)))
            .collect::<Result<Vec<_>, String>>()?;
        let top = cultivated_selected[history]
            .iter()
            .map(|row| cultivated[*row as usize].1.0)
            .max()
            .ok_or("cultivated receiver returned no row")?;
        let (competitor, greatest_omitted_upper) = cultivated
            .iter()
            .filter(|(row, _)| !receiver_set.contains(row))
            .max_by_key(|(row, interval)| (interval.1, std::cmp::Reverse(*row)))
            .map(|(row, interval)| (*row, interval.1))
            .ok_or("receiver cover left no reconstruction fibre")?;
        if greatest_omitted_upper >= top {
            return Err(
                "receiver row condensation discarded a potentially maximal interval".to_owned(),
            );
        }
        let admitted_factor_addresses = factors
            .iter()
            .filter(|factor| {
                factor
                    .founding_native_history_states
                    .contains(&foreign.native_history_states[history])
            })
            .map(|factor| factor.address.clone())
            .collect();
        certificates.push(PotentialReceiverCertificate {
            history_address: foreign.history_addresses[history].clone(),
            native_history_state: foreign.native_history_states[history],
            predecessor_selected_native_addresses: predecessor_selected[history].clone(),
            cultivated_selected_native_addresses: cultivated_selected[history].clone(),
            predecessor_top_lower: predecessor_selected[history]
                .iter()
                .map(|row| candidates[history].terminal_potential[*row as usize].0)
                .max()
                .expect("predecessor row"),
            cultivated_top_lower: top,
            greatest_omitted_upper,
            shortest_omitted_competitor: competitor,
            admitted_factor_addresses,
            complete_predecessor_potential_sha256: pair_by_proposal
                [foreign.history_addresses[history].as_str()]
            .predecessor
            .potential_sha256
            .clone(),
        });
    }

    let rest = ForeignPotentialComplexRest::seal(
        foreign.history_addresses,
        foreign.native_history_states,
        final_hidden,
        vocabulary,
        predecessor_lower,
        1,
        factors,
        receiver_rows,
        decoder,
        certificates,
        vec![
            "coefficient currents outside the captured rank-three section obstruct".to_owned(),
            "a receiver broader than the terminal interval order reopens the complete cold potential fibre".to_owned(),
            "autoregressive histories not represented by the addressed coefficient nodes remain open".to_owned(),
        ],
    )
    .map_err(display)?;
    let rest_bytes = rest.canonical_bytes().map_err(display)?;

    let product = output.join("product");
    fs::create_dir_all(&product).map_err(display)?;
    fs::write(product.join("potential.rest"), &rest_bytes).map_err(display)?;
    fs::copy(QUOTIENT, product.join("receiver-history.rest")).map_err(display)?;
    copy_directory(Path::new(MATHEMATICS), &product.join("mathematics"))?;
    copy_directory(Path::new(MULTIMODAL), &product.join("multimodal"))?;
    let manifest = seal_manifest(&product)?;
    write_json(&product.join("manifest.json"), &manifest)?;

    let detached = output.join("detached");
    fs::create_dir_all(&detached).map_err(display)?;
    run_source_detached(&product, &detached)?;
    let returned: Value = read_json(&detached.join("00-return.json"))?;
    let passed = returned["passed"] == true;
    let grade = json!({
        "schema":"holonics.parametron-athena-alpha-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "product_identity_sha256":manifest.identity_sha256,
        "product_rest_octets":manifest.files.values().map(|file| file.octets).sum::<u64>(),
        "foreign_tower_octets_in_product":0,
        "complete_cold_terminal_potential_fibre":true,
        "receiver_sufficient_hot_row_population":rest.receiver_rows.len(),
        "coefficient_node_population":rest.history_addresses.len(),
        "support_gated_factor_population":rest.factors.len(),
        "source_detached_return":returned,
    });
    write_json(&output.join("00-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The Parametron receiver-history rest returned Athena-alpha current\n\n[established-bounded; implemented-exact; measured] The final foreign hidden incidence, complete terminal-potential fibre, receiver-history quotient, support-gated factor sections, native mathematical rest and cultivated heterogeneous-organ rest froze as one product identity `{}`. A fresh source-isolated process returned native mathematical consequence first, optical/acoustic/parent current second, and four cultivated language receivers plus a later repeated crossing on the same card. Gemma was absent; invariant potential incidence was not re-uploaded.\n\n[open] The language receiver is exact on the four admitted addressed histories and their rank-three coefficient section. An autoregressive history outside that section returns an obstruction; it is not filled by a foreign fallback.\n\n```json\n{}\n```\n",
            manifest.identity_sha256,
            serde_json::to_string_pretty(&grade).map_err(display)?,
        ),
    )
    .map_err(display)?;
    write_json(
        &output.join("01-expensive-invocation.json"),
        &json!({
            "schema":"holonics.expensive-invocation.v1",
            "command":"cargo run -p life --example the_parametron_receiver_history_rest_returns_athena_alpha",
            "purpose":"compile and source-detach the support-gated terminal Parametron potential complex and conduct its native mathematical, heterogeneous and language returns",
            "elapsed_seconds":format!("{:.9}",started.elapsed().as_secs_f64()),
            "exit_status":if passed {0} else {1},
            "foreign_capture_replayed":false,
        }),
    )?;
    write_manifest(output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("Parametron Athena-alpha grade refused".to_owned())
    }
}

fn remount(product: &Path, output: &Path) -> Result<(), String> {
    let manifest: ProductManifest = read_json(&product.join("manifest.json"))?;
    verify_manifest(product, &manifest)?;
    let potential = ForeignPotentialComplexRest::read(
        &fs::read(product.join("potential.rest")).map_err(display)?,
    )
    .map_err(display)?;
    let quotient = ReceiverRestrictedFactorDescent::read(
        &fs::read(product.join("receiver-history.rest")).map_err(display)?,
    )
    .map_err(display)?;
    if quotient.quotient.native_population.len() < potential.native_history_states.len() {
        return Err("product quotient no longer contains the potential section".to_owned());
    }

    let mathematics = NativeHexisAthenaRest::read(
        &fs::read(product.join("mathematics/standing.bin")).map_err(display)?,
        &fs::read(product.join("mathematics/decoder.bin")).map_err(display)?,
        &fs::read(product.join("mathematics/fibres.bin")).map_err(display)?,
    )
    .map_err(display)?;
    let prior = mathematics
        .reconstruction()
        .predecessor_component_addresses
        .iter()
        .rev()
        .take(4)
        .cloned()
        .collect::<Vec<_>>();
    let inquiry = mathematics
        .found_native_mathematical_inquiry(
            vec![
                "athena-alpha/integer-section".to_owned(),
                "athena-alpha/modulus-two-section".to_owned(),
            ],
            vec![vec![11, -11, 0], vec![1, 1, 0]],
            vec![
                NativeSuccessorHistory::FixedSection,
                NativeSuccessorHistory::ComposedJoint,
            ],
            prior,
            vec!["nonlinear successor varieties remain open".to_owned()],
        )
        .map_err(display)?;
    let mut card = CudaRefineExecutor::new().map_err(display)?;
    let mathematical_return = mathematics
        .conduct_native_mathematical_inquiry_on_card(&inquiry, &mut card)
        .map_err(display)?;

    let multimodal = ReturnedBoundaryCultivationRest::read(
        &fs::read(product.join("multimodal/standing.json")).map_err(display)?,
        &fs::read(product.join("multimodal/decoder.json")).map_err(display)?,
        &fs::read(product.join("multimodal/fibres.json")).map_err(display)?,
        &fs::read(product.join("multimodal/cultivation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let continuation: MultimodalContinuation =
        read_json(&product.join("multimodal/continuation.json"))?;
    let multimodal_return = multimodal
        .conduct_cultivated(&continuation.candidate_counts, &mut card)
        .map_err(display)?;

    let fronts = potential
        .native_history_states
        .iter()
        .map(|native| potential.one_hot_for_native(*native).map_err(display))
        .collect::<Result<Vec<_>, _>>()?;
    let expected = potential
        .receiver_certificates
        .iter()
        .map(|certificate| certificate.cultivated_selected_native_addresses.clone())
        .collect::<Vec<_>>();
    let unknown = potential
        .one_hot_for_native(u64::MAX)
        .expect_err("unknown history must obstruct");
    let mut resident = potential.mount_receiver_on(card).map_err(display)?;
    let first = resident.conduct(&fronts).map_err(display)?;
    let later = resident
        .conduct(&fronts.iter().rev().cloned().collect::<Vec<_>>())
        .map_err(display)?;
    let first_expected = first
        .selected_native_addresses
        .iter()
        .zip(&expected)
        .all(|(returned, expected)| expected == &vec![*returned]);
    let surfaces = first
        .selected_native_addresses
        .iter()
        .map(|native| {
            potential
                .decode(*native)
                .map(str::to_owned)
                .map_err(display)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let predecessor_surfaces = potential
        .receiver_certificates
        .iter()
        .map(|certificate| {
            certificate
                .predecessor_selected_native_addresses
                .iter()
                .map(|native| {
                    potential
                        .decode(*native)
                        .map(str::to_owned)
                        .map_err(display)
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let passed = first_expected
        && first.plural_population.iter().all(|plural| *plural == 1)
        && later.selected_native_addresses
            == first
                .selected_native_addresses
                .iter()
                .rev()
                .copied()
                .collect::<Vec<_>>()
        && !first.invariant_transport_reuploaded
        && !later.invariant_transport_reuploaded
        && !first.cpu_semantic_replay_after_device
        && !later.cpu_semantic_replay_after_device
        && !unknown.0.foreign_fallback_permitted
        && mathematical_return.complex.operation_cells.len() == 2
        && mathematical_return.complex.constraint_cells.len() == 2
        && mathematical_return.complex.geometry_cells.len() == 2
        && multimodal_return.launches > 0
        && multimodal_return.synchronizations > 0;
    write_json(
        &output.join("00-return.json"),
        &json!({
            "schema":"holonics.parametron-athena-alpha-detached-return.v1",
            "truth_status":"established-bounded; implemented-exact; measured",
            "passed":passed,
            "product_identity_sha256":manifest.identity_sha256,
            "native_mathematical_consequence":mathematical_return,
            "cultivated_heterogeneous_organ_return":joint_json(&multimodal_return),
            "predecessor_surfaces":predecessor_surfaces,
            "cultivated_surfaces":surfaces,
            "first_language_receiver":first,
            "later_language_receiver":later,
            "unknown_history_obstruction":unknown.0,
            "foreign_tower_staged_octets":0,
            "foreign_tower_deed_launches":0,
            "source_accessed_paths":["/product"],
            "forbidden_source_access":[],
            "lean_or_checker_in_inference_lifecycle":false,
        }),
    )?;
    if passed {
        Ok(())
    } else {
        Err("source-detached Parametron return refused".to_owned())
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

fn joint_json(returned: &holonic_engine::cuda_refine::DeviceJointMediaTransport) -> Value {
    json!({
        "joint_anchor":&returned.joint_anchor,
        "shared_ablated_joint_anchor":&returned.shared_ablated_joint_anchor,
        "local_ablated_joint_anchor":&returned.local_ablated_joint_anchor,
        "predecessor_consequence":&returned.predecessor_consequence,
        "successor_consequence":&returned.successor_consequence,
        "shared_ablated_consequence":&returned.shared_ablated_consequence,
        "local_ablated_consequence":&returned.local_ablated_consequence,
        "anchors":returned.anchors,
        "families":returned.families,
        "ports":returned.ports,
        "launches":returned.launches,
        "synchronizations":returned.synchronizations,
        "block_threads":returned.block_threads,
        "active_lanes":returned.active_lanes,
        "host_ingress_octets":returned.host_ingress_octets,
        "host_egress_octets":returned.host_egress_octets,
        "resident_octets":returned.resident_octets,
    })
}

fn digest_intervals(values: &[(i64, i64)]) -> String {
    let mut digest = Sha256::new();
    for (lower, upper) in values {
        digest.update(lower.to_le_bytes());
        digest.update(upper.to_le_bytes());
    }
    hex(&digest.finalize())
}

fn digest_hidden(entries: &[i64], rows: usize, columns: usize, column: usize) -> String {
    let mut digest = Sha256::new();
    for row in 0..rows {
        let value = entries[row * columns + column];
        digest.update(value.to_le_bytes());
        digest.update(value.to_le_bytes());
    }
    hex(&digest.finalize())
}

fn copy_directory(source: &Path, target: &Path) -> Result<(), String> {
    fs::create_dir_all(target).map_err(display)?;
    for entry in fs::read_dir(source).map_err(display)? {
        let entry = entry.map_err(display)?;
        if entry.file_type().map_err(display)?.is_file() {
            fs::copy(entry.path(), target.join(entry.file_name())).map_err(display)?;
        }
    }
    Ok(())
}

fn seal_manifest(product: &Path) -> Result<ProductManifest, String> {
    let mut files = BTreeMap::new();
    collect_files(product, product, &mut files)?;
    let identity_sha256 = sha(&serde_json::to_vec(&files).map_err(display)?);
    Ok(ProductManifest {
        schema: "holonics.parametron-athena-alpha-product.v1".to_owned(),
        identity_sha256,
        files,
    })
}

fn collect_files(
    root: &Path,
    path: &Path,
    files: &mut BTreeMap<String, FileReceipt>,
) -> Result<(), String> {
    for entry in fs::read_dir(path).map_err(display)? {
        let entry = entry.map_err(display)?;
        let child = entry.path();
        if entry.file_type().map_err(display)?.is_dir() {
            collect_files(root, &child, files)?;
        } else if entry.file_name() != "manifest.json" {
            let bytes = fs::read(&child).map_err(display)?;
            files.insert(
                child
                    .strip_prefix(root)
                    .map_err(display)?
                    .to_string_lossy()
                    .into_owned(),
                FileReceipt {
                    octets: bytes.len() as u64,
                    sha256: sha(&bytes),
                },
            );
        }
    }
    Ok(())
}

fn verify_manifest(product: &Path, manifest: &ProductManifest) -> Result<(), String> {
    let expected = seal_manifest(product)?;
    if expected.identity_sha256 != manifest.identity_sha256 || expected.files != manifest.files {
        return Err("product manifest identity moved".to_owned());
    }
    Ok(())
}

fn run_source_detached(product: &Path, output: &Path) -> Result<(), String> {
    let executable = fs::canonicalize(env::current_exe().map_err(display)?).map_err(display)?;
    let product = fs::canonicalize(product).map_err(display)?;
    let output = fs::canonicalize(output).map_err(display)?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    let status = command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena-alpha")
        .arg("--ro-bind")
        .arg(product)
        .arg("/product")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/return",
            "--",
            "/athena-alpha",
            "--remount",
            "/product",
            "/return",
        ])
        .status()
        .map_err(display)?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("source-detached child exited {status}"))
    }
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(display)?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut files = BTreeMap::new();
    collect_files(output, output, &mut files)?;
    write_json(
        &output.join("MANIFEST.json"),
        &json!({"schema":"holonics.parametron-athena-alpha-station-manifest.v1","files":files}),
    )
}

fn sha(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
