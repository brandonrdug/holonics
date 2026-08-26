//! Remount the exact reachable-section descent as one resident native word, conduct two later
//! successor fronts, and exhibit an unknown-history obstruction without reopening Gemma.

use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::phoenix::foreign_section_descent::{
    ForeignReachableSectionRest, ResidentForeignSectionRefusal,
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const SOURCE: &str = concat!(
    "output/the_foreign_tower_descends_on_the_cultivated_reachable_section/",
    "foreign-reachable-section.rest"
);
const OUTPUT: &str = "output/the_descended_foreign_section_word_remains_resident";

fn main() -> Result<(), String> {
    let started = Instant::now();
    let bytes = fs::read(SOURCE).map_err(|error| error.to_string())?;
    let rest = ForeignReachableSectionRest::read(&bytes).map_err(|error| error.to_string())?;
    let native_histories = rest.native_history_states.clone();
    let history_population = native_histories.len();
    let final_section = rest
        .sections
        .last()
        .ok_or("the reachable-section rest has no terminal section")?
        .clone();
    let mut resident = rest.mount_resident().map_err(|error| error.to_string())?;
    let classes = resident.classes().to_vec();
    let maps = resident.maps().len();

    let first = resident
        .conduct_native_history_states(&native_histories)
        .map_err(|error| error.to_string())?;
    let mut reversed = native_histories.clone();
    reversed.reverse();
    let later = resident
        .conduct_native_history_states(&reversed)
        .map_err(|error| error.to_string())?;
    let exact_terminal_reconstruction = first.histories.iter().all(|returned| {
        returned.final_section
            == (0..final_section.rows)
                .map(|row| {
                    final_section.entries[row * final_section.columns + returned.history_index]
                })
                .collect::<Vec<_>>()
    });
    let unknown = native_histories
        .iter()
        .copied()
        .max()
        .and_then(|state| state.checked_add(1))
        .ok_or("the native history state aperture cannot form a control")?;
    let obstruction = match resident.conduct_native_history_states(&[unknown]) {
        Err(ResidentForeignSectionRefusal::OutOfSection(obstruction)) => obstruction,
        Err(other) => return Err(format!("the unknown-history control returned {other}")),
        Ok(_) => return Err("the unknown native history entered the resident word".to_owned()),
    };

    let output = PathBuf::from(OUTPUT);
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    write_json(&output.join("00-history-classes.json"), &classes)?;
    write_json(
        &output.join("01-resident-successor-returns.json"),
        &json!({
            "first": first,
            "later": later,
            "unknown": obstruction,
        }),
    )?;
    let grade = json!({
        "schema": "holonics.resident-foreign-section-word-grade.v1",
        "truth_status": "established-bounded; implemented-exact; measured",
        "receiver_status": "phase-locked finite control only",
        "productive_prequotient_transport": false,
        "history_population": history_population,
        "complete_future_classes": classes.len(),
        "descended_maps": maps,
        "strict_future_history_quotient": classes.len() < history_population,
        "exact_terminal_reconstruction": exact_terminal_reconstruction,
        "first_successor_launches": first.apparatus.launches,
        "later_successor_launches": later.apparatus.launches,
        "first_successor_synchronizations": first.apparatus.synchronizations,
        "later_successor_synchronizations": later.apparatus.synchronizations,
        "mount_invariant_ingress_octets": first.apparatus.mount_host_ingress_octets,
        "first_successor_ingress_octets": first.apparatus.successor_host_ingress_octets,
        "later_successor_ingress_octets": later.apparatus.successor_host_ingress_octets,
        "resident_invariant_octets": first.apparatus.resident_invariant_octets,
        "invariant_transport_reuploaded_on_first_successor": first.apparatus.invariant_transport_reuploaded,
        "invariant_transport_reuploaded_on_later_successor": later.apparatus.invariant_transport_reuploaded,
        "foreign_tower_staged_octets_during_successors": 0,
        "foreign_tower_launches_during_successors": 0,
        "cpu_semantic_replay_after_device": first.apparatus.cpu_semantic_replay_after_device || later.apparatus.cpu_semantic_replay_after_device,
        "out_of_section_obstructs_without_foreign_fallback": !obstruction.foreign_fallback_permitted,
        "device": first.apparatus.device,
        "passed": exact_terminal_reconstruction
            && first.apparatus.launches == 1
            && later.apparatus.launches == 1
            && !first.apparatus.invariant_transport_reuploaded
            && !later.apparatus.invariant_transport_reuploaded
            && !first.apparatus.cpu_semantic_replay_after_device
            && !later.apparatus.cpu_semantic_replay_after_device
            && !obstruction.foreign_fallback_permitted,
    });
    write_json(&output.join("02-grade.json"), &grade)?;
    write_json(
        &output.join("03-expensive-invocation.json"),
        &json!({
            "command": "cargo run -p life --example the_descended_foreign_section_word_remains_resident",
            "purpose": "mount the captured exact foreign-section quotient once and measure two later resident successor passages without foreign replay",
            "elapsed_seconds": format!("{:.9}", started.elapsed().as_secs_f64()),
            "exit_status": if grade["passed"] == true { 0 } else { 1 },
            "source_rest_sha256": sha256(&bytes),
        }),
    )?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The locked foreign-section receiver remains resident\n\n[established-bounded; implemented-exact; measured] The four cultivated history occurrences crossed the finite phase-locked receiver twice after one device mount. Each later passage transferred only its addressed native starting states; the invariant table and word remained resident, the declared terminal receiver faces reconstructed, and the unknown-history control returned an out-of-section obstruction without reopening Gemma.\n\n[definition] This is a binary/future-class receiver control, not the productive pre-quotient foreign carrier. It intentionally discards complex coefficient amplitude and phase. Productive residency is graded by the separate oriented-incidence Complex Parametron deed.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
        ),
    )
    .map_err(|error| error.to_string())?;
    write_manifest(&output)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    if grade["passed"] == true {
        Ok(())
    } else {
        Err("the resident foreign-section word grade refused".to_owned())
    }
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(|error| error.to_string())
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
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
            "schema": "holonics.resident-foreign-section-word-manifest.v1",
            "entries": entries,
        }),
    )
}
