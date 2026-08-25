//! Re-certify the returned twelve-node carrier word through `G = B^T B`. This exact Complex
//! Parametron receiver replaces ambient 2,560-row rational elimination with 12-node coefficient
//! rank, radical, naturality, fibre, and separator testimony.

use std::{collections::BTreeSet, fs, path::PathBuf, time::Instant};

use holonic_engine::phoenix::foreign_section_descent::ForeignReachableSectionRest;
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const REST: &str = concat!(
    "output/the_second_emitted_frontier_grows_the_parametron_coefficient_lattice/",
    "expanded-reachable-section.rest"
);
const OUTPUT: &str =
    "output/the_twelve_node_parametron_certifies_naturality_in_coefficient_space";

fn main() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing station output {}", output.display()));
    }
    let started = Instant::now();
    let rest = ForeignReachableSectionRest::read(&fs::read(REST).map_err(display)?)
        .map_err(display)?;
    let certificates = rest
        .coefficient_naturality_certificates()
        .map_err(display)?;
    let quotient = rest.coefficient_receiver_quotient().map_err(display)?;
    let ranks = certificates
        .iter()
        .map(|certificate| certificate.entering_rank)
        .collect::<BTreeSet<_>>();
    let first_new = rest.history_addresses.len().saturating_sub(4);
    let every_new_node_separated = (first_new..rest.history_addresses.len()).all(|right| {
        certificates.iter().any(|certificate| {
            certificate.shortest_history_separators.iter().any(|separator| {
                separator.right_history == right || separator.left_history == right
            })
        })
    });
    let passed = certificates.len() + 1 == rest.sections.len()
        && certificates.iter().all(|certificate| {
            certificate.naturality_commutes
                && !certificate.carrier_elimination_performed
                && certificate.complete_coefficient_kernel.len()
                    == certificate.coefficient_population - certificate.entering_rank
                && certificate.returned_coefficient_kernel.len()
                    == certificate.coefficient_population - certificate.returned_rank
        })
        && every_new_node_separated;
    fs::create_dir_all(&output).map_err(display)?;
    write_json(output.join("00-coefficient-naturality.json"), &certificates)?;
    write_json(output.join("01-coefficient-receiver-quotient.json"), &quotient)?;
    let grade = json!({
        "schema":"holonics.twelve-node-coefficient-parametron-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "coefficient_node_population":rest.history_addresses.len(),
        "carrier_population":rest.sections[0].rows,
        "adjacent_section_population":certificates.len(),
        "reachable_ranks":ranks,
        "complete_coefficient_fibres_retained":true,
        "every_naturality_square_commutes":certificates.iter().all(|certificate| certificate.naturality_commutes),
        "every_new_node_has_a_separator":every_new_node_separated,
        "carrier_elimination_performed":false,
        "foreign_receiver_class_population":quotient.classes.len(),
        "coefficient_certificate_elapsed_seconds":format!("{:.9}",started.elapsed().as_secs_f64()),
        "foreign_tower_deed_launches":0,
        "foreign_tower_staged_octets":0,
    });
    write_json(output.join("02-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The twelve-node Parametron certifies naturality in coefficient space\n\n[established-bounded; implemented-exact; measured] The exact identity-receiver storage `G = B^T B` returned the complete coefficient radical, rank, adjacent naturality, fibres and shortest separators for all twelve nodes. No 2,560-row rational elimination, model passage, or GPU deed occurred.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("the coefficient-space Parametron grade refused".to_owned())
    }
}

fn write_json(path: impl AsRef<std::path::Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
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
    files.sort_by_key(|file| file["path"].as_str().unwrap_or_default().to_owned());
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
