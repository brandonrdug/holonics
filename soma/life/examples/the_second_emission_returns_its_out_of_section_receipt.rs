//! Resolve the already-returned terminal faces of the eight-node product as addressed successor
//! occurrences. The unchanged GPU return is reused by identity; no semantic deed is replayed.

use std::{collections::BTreeSet, fs, path::PathBuf};

use holonic_engine::phoenix::foreign_potential_rest::{
    AddressedPotentialSectionObstruction, AddressedPotentialSuccessor,
    ForeignPotentialComplexRest,
};
use serde::Serialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const POTENTIAL: &str = concat!(
    "output/the_eight_node_parametron_rest_returns_athena_alpha/product/",
    "potential.rest"
);
const RETURNED: &str = concat!(
    "output/the_eight_node_parametron_rest_returns_athena_alpha/detached/",
    "00-return.json"
);
const OUTPUT: &str = "output/the_second_emission_returns_its_out_of_section_receipt";

fn main() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing station output {}", output.display()));
    }
    let potential = ForeignPotentialComplexRest::read(&fs::read(POTENTIAL).map_err(display)?)
        .map_err(display)?;
    let returned: Value = serde_json::from_slice(&fs::read(RETURNED).map_err(display)?)
        .map_err(display)?;
    let selected = returned["first_language_receiver"]["selected_native_addresses"]
        .as_array()
        .ok_or("the bound native return omitted selected addresses")?;
    if selected.len() != potential.history_addresses.len() {
        return Err("the bound native return and rested coefficient nodes moved".to_owned());
    }

    let parents = potential
        .history_addresses
        .iter()
        .map(|address| format!("{address}/emission/"))
        .collect::<Vec<_>>();
    let leaf_indices = potential
        .history_addresses
        .iter()
        .enumerate()
        .filter_map(|(history, _)| {
            (!potential
                .history_addresses
                .iter()
                .any(|candidate| candidate.starts_with(&parents[history])))
            .then_some(history)
        })
        .collect::<Vec<_>>();
    let mut obstructions = Vec::<AddressedPotentialSectionObstruction>::new();
    for history in leaf_indices {
        let emitted = u32::try_from(
            selected[history]
                .as_u64()
                .ok_or("selected native address left the unsigned carrier")?,
        )
        .map_err(display)?;
        match potential
            .addressed_successor(&potential.history_addresses[history], emitted)
            .map_err(display)?
        {
            AddressedPotentialSuccessor::OutOfSection(obstruction) => {
                obstructions.push(obstruction)
            }
            AddressedPotentialSuccessor::Admitted { .. } => {
                return Err("a leaf occurrence unexpectedly resolved inside the rested section".to_owned())
            }
        }
    }
    let unique = obstructions
        .iter()
        .map(|obstruction| obstruction.requested_history_address.as_str())
        .collect::<BTreeSet<_>>();
    let passed = obstructions.len() == 4
        && unique.len() == obstructions.len()
        && obstructions
            .iter()
            .all(|obstruction| !obstruction.foreign_fallback_permitted);
    fs::create_dir_all(&output).map_err(display)?;
    write_json(output.join("00-addressed-out-of-section.json"), &obstructions)?;
    let grade = json!({
        "schema":"holonics.second-emission-out-of-section-grade.v1",
        "truth_status":"established-bounded; implemented-exact",
        "passed":passed,
        "source_potential_identity_sha256":potential.identity_sha256,
        "reused_native_return_sha256":sha(&fs::read(RETURNED).map_err(display)?),
        "addressed_successor_population":obstructions.len(),
        "unique_successor_population":unique.len(),
        "foreign_fallback_permitted":false,
        "semantic_deed_replayed":false,
        "foreign_tower_deed_launches":0,
        "foreign_tower_staged_octets":0,
    });
    write_json(output.join("01-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The second emission returns its out-of-section receipt\n\n[established-bounded; implemented-exact] The four leaf occurrences of the eight-node rest issued their already-returned native faces as exact addressed successors. Every successor lies outside the current coefficient section and forbids inference-time foreign fallback. The prior GPU return was reused by closure identity; no semantic deed or foreign transport was replayed.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("the addressed second-emission grade refused".to_owned())
    }
}

fn write_json(path: impl AsRef<std::path::Path>, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(display)?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(display)
}

fn write_manifest(output: &std::path::Path) -> Result<(), String> {
    let mut files = fs::read_dir(output)
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
    files.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    write_json(
        output.join("MANIFEST.json"),
        &json!({"schema":"holonics.return-manifest.v1","files":files}),
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
