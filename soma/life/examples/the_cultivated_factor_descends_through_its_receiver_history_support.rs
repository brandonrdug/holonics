//! Bind every cultivated Phoenix factor to the receiver-history sections which founded it.
//!
//! This deed consumes the already-returned congruence and factor cover. It does not replay Gemma.
//! The card refines the quotient with one exact support face per realization, and the returned
//! rest admits only those factors whose complete native fibre lies inside that support.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    phoenix::{
        receiver_restricted_transport::{HistorySupportedFactor, ReceiverRestrictedFactorDescent},
        session_factor_complex::TowerFactorRealization,
    },
    receiver_exact_compression::ItemId,
};
use life::athena_receiver_history::AthenaReceiverHistoryCongruence;
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};

const CONGRUENCE: &str = concat!(
    "output/the_receiver_history_congruence_replaces_the_trigram_table/",
    "00-receiver-history-congruence.json"
);
const BOUND_FACTORS: &str =
    "output/the_factor_complex_changes_the_same_body/00-bound-factor-cover.json";
const OUTPUT: &str = "output/the_cultivated_factor_descends_through_its_receiver_history_support";

const OWNER_CLOSURE: &str = concat!(
    include_str!("../../../crates/holonic-engine/src/phoenix/receiver_restricted_transport.rs"),
    include_str!("../../../crates/holonic-engine/src/phoenix/session_factor_complex.rs"),
    include_str!("../src/athena_receiver_history.rs"),
    include_str!("../src/athena_receiver_history/types.rs"),
);

#[derive(Debug, Deserialize)]
struct BoundFactors {
    selectors: Vec<Selector>,
    realizations: Vec<TowerFactorRealization>,
}

#[derive(Debug, Deserialize)]
struct Selector {
    proposals: Vec<String>,
    realization_address: String,
}

#[derive(Debug, Serialize)]
struct ReturnedSupportSection {
    proposal: String,
    source: ItemId,
    native: holonic_engine::receiver_history_compression::NativeStateId,
    reconstruction_fibre: BTreeSet<ItemId>,
    admitted_realizations: BTreeSet<String>,
    expected_realization: String,
    exact: bool,
}

fn main() -> Result<(), String> {
    let started = Instant::now();
    let congruence_bytes = fs::read(CONGRUENCE).map_err(|error| error.to_string())?;
    let congruence = AthenaReceiverHistoryCongruence::read(&congruence_bytes)?;
    let bound: BoundFactors = read_json(Path::new(BOUND_FACTORS))?;
    let realization_by_address = bound
        .realizations
        .into_iter()
        .map(|realization| (realization.address.clone(), realization))
        .collect::<BTreeMap<_, _>>();
    let source_by_occurrence = congruence
        .sections
        .iter()
        .map(|section| {
            (
                section.family_occurrence.as_str(),
                ItemId(section.source_item),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let mut supported = Vec::new();
    for selector in &bound.selectors {
        let realization = realization_by_address
            .get(&selector.realization_address)
            .ok_or_else(|| {
                format!(
                    "selector {} names no returned realization",
                    selector.realization_address
                )
            })?
            .clone();
        let founding_sources = selector
            .proposals
            .iter()
            .map(|proposal| {
                source_by_occurrence
                    .get(proposal.as_str())
                    .copied()
                    .ok_or_else(|| format!("proposal {proposal} names no causal section"))
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        supported.push(HistorySupportedFactor {
            realization,
            founding_sources,
        });
    }
    if supported.len() != realization_by_address.len() {
        return Err("the selector/support relation does not cover every realization".to_owned());
    }

    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let descent =
        ReceiverRestrictedFactorDescent::found_on_device(&congruence.native, supported, &mut card)
            .map_err(|error| error.to_string())?;
    let rest = descent
        .canonical_bytes()
        .map_err(|error| error.to_string())?;
    let remounted =
        ReceiverRestrictedFactorDescent::read(&rest).map_err(|error| error.to_string())?;
    if remounted != descent {
        return Err("the source-detached factor-support rest changed on remount".to_owned());
    }

    let expected_by_proposal = bound
        .selectors
        .iter()
        .flat_map(|selector| {
            selector
                .proposals
                .iter()
                .map(|proposal| (proposal.as_str(), selector.realization_address.as_str()))
        })
        .collect::<BTreeMap<_, _>>();
    let mut returned = Vec::new();
    for (proposal, expected) in expected_by_proposal {
        let source = source_by_occurrence[proposal];
        let admitted = descent
            .admit_source(source)
            .map_err(|obstruction| format!("founded source obstructed: {obstruction:?}"))?;
        let exact = admitted.realization_addresses == BTreeSet::from([expected.to_owned()]);
        returned.push(ReturnedSupportSection {
            proposal: proposal.to_owned(),
            source,
            native: admitted.native,
            reconstruction_fibre: admitted.reconstruction_fibre,
            admitted_realizations: admitted.realization_addresses,
            expected_realization: expected.to_owned(),
            exact,
        });
    }
    returned.sort_by_key(|section| section.source);

    let supported_sources = descent
        .factors
        .iter()
        .flat_map(|factor| factor.founding_sources.iter().copied())
        .collect::<BTreeSet<_>>();
    let control_source = congruence
        .native
        .source_population
        .iter()
        .find(|source| !supported_sources.contains(source))
        .copied()
        .ok_or("the factor support left no control section")?;
    let control = descent
        .admit_source(control_source)
        .map_err(|obstruction| format!("known control obstructed: {obstruction:?}"))?;
    let outside_source = ItemId(
        congruence
            .native
            .source_population
            .iter()
            .map(|source| source.0)
            .max()
            .ok_or("the source population is empty")?
            .checked_add(1)
            .ok_or("source address overflow")?,
    );
    let obstruction = descent
        .admit_source(outside_source)
        .expect_err("an out-of-section source must obstruct");

    let output = PathBuf::from(OUTPUT);
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    fs::write(output.join("receiver-restricted-factor-rest.json"), &rest)
        .map_err(|error| error.to_string())?;
    write_json(
        &output.join("00-descended-factor-supports.json"),
        &descent.factors,
    )?;
    write_json(&output.join("01-returned-support-sections.json"), &returned)?;
    write_json(
        &output.join("02-control-and-obstruction.json"),
        &json!({
            "known_control": control,
            "outside_obstruction": obstruction,
            "foreign_fallback_permitted": false,
        }),
    )?;
    let rest_sha256 = sha256(&rest);
    let closure_sha256 = sha256(OWNER_CLOSURE.as_bytes());
    let grade = json!({
        "schema": "holonics.receiver-restricted-factor-descent-grade.v1",
        "truth_status": "established-bounded; implemented-exact; measured",
        "inherited_native_states": congruence.native.native_population.len(),
        "refined_native_states": descent.quotient.native_population.len(),
        "complete_reconstruction_fibres": descent.quotient.reconstruction_fibres.len(),
        "factor_support_population": descent.factors.len(),
        "founding_source_population": supported_sources.len(),
        "support_separators": descent.factors.len(),
        "returned_founding_sections": returned.len(),
        "every_founding_section_admits_exactly_its_factor": returned.iter().all(|section| section.exact),
        "control_admits_no_factor": control.realization_addresses.is_empty(),
        "unknown_source_obstructs": !obstruction.foreign_fallback_permitted,
        "generator_naturality_squares": descent.quotient.generators.len(),
        "source_detached_rest_octets": rest.len(),
        "source_detached_rest_sha256": rest_sha256,
        "resident_device": descent.apparatus.device,
        "resident_launches": descent.apparatus.launches,
        "cpu_device_partition_equal": descent.apparatus.cpu_device_partition_equal,
        "cpu_semantic_replay_after_device": descent.apparatus.cpu_semantic_replay_after_device,
        "foreign_tower_staged_octets": 0,
        "foreign_tower_deed_launches": 0,
        "passed": returned.iter().all(|section| section.exact)
            && control.realization_addresses.is_empty()
            && !obstruction.foreign_fallback_permitted
            && descent.apparatus.launches > 0
            && descent.apparatus.cpu_device_partition_equal
            && !descent.apparatus.cpu_semantic_replay_after_device,
    });
    write_json(&output.join("03-grade.json"), &grade)?;
    write_json(
        &output.join("04-invocation.json"),
        &json!({
            "command": "cargo run -p life --example the_cultivated_factor_descends_through_its_receiver_history_support",
            "purpose": "refine the admitted receiver-history quotient by exact factor-support faces without replaying the foreign tower",
            "code_closure_sha256": closure_sha256,
            "elapsed_seconds": format!("{:.9}", started.elapsed().as_secs_f64()),
            "exit_status": 0,
        }),
    )?;
    write_inspection(&output, &grade, &descent, &returned, control_source)?;
    write_manifest(&output)?;
    if grade["passed"] != true {
        return Err("the receiver-restricted factor descent grade refused".to_owned());
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn write_inspection(
    output: &Path,
    grade: &serde_json::Value,
    descent: &ReceiverRestrictedFactorDescent,
    returned: &[ReturnedSupportSection],
    control_source: ItemId,
) -> Result<(), String> {
    let mut text =
        String::from("# The cultivated factor descends through its receiver-history support\n\n");
    text.push_str("[established-bounded; implemented-exact; measured] The former global factor application was not a lawful descent: it forgot the causal sections which founded each realization. The returned quotient now carries one exact support receiver per realization and refines until every original receiver, support face, and generator square factors.\n\n");
    text.push_str(&format!(
        "The card returned {} refined native states, {} complete fibres, {} generator squares, and {} support separators. All {} founding sections admitted exactly their addressed factor. Control source `{}` admitted no factor; an unknown source returned an obstruction with no foreign fallback. No Gemma tensor was staged and no tower deed ran.\n\n",
        descent.quotient.native_population.len(),
        descent.quotient.reconstruction_fibres.len(),
        descent.quotient.generators.len(),
        descent.factors.len(),
        returned.len(),
        control_source.0,
    ));
    text.push_str("[open] This closes the native-history/factor-support square only. It does not yet claim that every foreign Gemma layer map has descended through its reachable activation quotient, nor that Athena alpha has returned the final nontrivial mathematical and conversational surfaces.\n\n");
    text.push_str("```json\n");
    text.push_str(&serde_json::to_string_pretty(grade).map_err(|error| error.to_string())?);
    text.push_str("\n```\n");
    fs::write(output.join("INSPECTION.md"), text).map_err(|error| error.to_string())
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    let bytes = fs::read(path).map_err(|error| format!("{}: {error}", path.display()))?;
    serde_json::from_slice(&bytes).map_err(|error| format!("{}: {error}", path.display()))
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(|error| error.to_string())
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut entries = fs::read_dir(output)
        .map_err(|error| error.to_string())?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(|error| error.to_string())?;
            Ok(json!({
                "path": entry.file_name().to_string_lossy(),
                "octets": bytes.len(),
                "sha256": sha256(&bytes),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    entries.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    write_json(
        &output.join("MANIFEST.json"),
        &json!({
            "schema": "holonics.receiver-restricted-factor-descent-manifest.v1",
            "entries": entries,
        }),
    )
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
