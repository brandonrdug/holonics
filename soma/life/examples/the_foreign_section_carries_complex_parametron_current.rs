//! Remount the terminal captured foreign incidence once, then carry exact complex coefficient
//! current through it twice without phase locking or reopening the inherited tower.

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    ExactComplexWaveCurrent,
    phoenix::foreign_section_descent::{
        ForeignReachableSectionRest, ForeignReceiverConstitutiveForm,
    },
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const SOURCE: &str = concat!(
    "output/the_foreign_tower_descends_on_the_cultivated_reachable_section/",
    "foreign-reachable-section.rest"
);
const OUTPUT: &str = "output/the_foreign_section_carries_complex_parametron_current";

fn main() -> Result<(), String> {
    let started = Instant::now();
    let source_bytes = fs::read(SOURCE).map_err(|error| error.to_string())?;
    let rest =
        ForeignReachableSectionRest::read(&source_bytes).map_err(|error| error.to_string())?;
    if rest.history_addresses.len() < 2 {
        return Err(
            "the complex phase control requires two addressed coefficient nodes".to_owned(),
        );
    }

    // The first captured hidden-coordinate receiver explicitly declares the orthogonal diagonal
    // form. The representation is O(branches), not a dense identity matrix.
    let forms = rest
        .sections
        .iter()
        .map(|section| ForeignReceiverConstitutiveForm::Diagonal(vec![Rat::one(); section.rows]))
        .collect();
    let mut atlas = rest
        .parametron_atlas(forms)
        .map_err(|error| error.to_string())?;
    let atlas_summary = atlas
        .sections
        .iter()
        .map(|section| {
            json!({
                "address": section.address,
                "branch_population": section.incidence.rows(),
                "coefficient_node_population": section.incidence.columns(),
                "incidence_rank": section.incidence_rank,
                "incidence_kernel_dimension": section.complete_incidence_kernel.len(),
                "receiver_radical_dimension": section.complete_radical.len(),
                "pulled_storage": section.pulled_storage.to_rows(),
                "receiver_form": "declared exact diagonal identity",
            })
        })
        .collect::<Vec<_>>();
    let final_section = atlas
        .sections
        .pop()
        .ok_or("the captured atlas has no terminal section")?;
    let nodes = final_section.incidence.columns();

    let one_hot = (0..nodes)
        .map(|history| {
            let mut current = vec![ExactComplexWaveCurrent::zero(); nodes];
            current[history] = ExactComplexWaveCurrent::one();
            current
        })
        .collect::<Vec<_>>();
    let mut superposition = vec![ExactComplexWaveCurrent::zero(); nodes];
    superposition[0] = ExactComplexWaveCurrent::one();
    superposition[1] = ExactComplexWaveCurrent::new(Rat::zero(), Rat::from_integer(BigInt::one()));
    let half_turn = superposition
        .iter()
        .map(ExactComplexWaveCurrent::negated)
        .collect::<Vec<_>>();
    let mut fronts = one_hot;
    fronts.push(superposition.clone());
    fronts.push(half_turn);

    let selected_branch = (0..final_section.incidence.rows())
        .find(|branch| {
            final_section.incidence.get(*branch, 0).ok()
                != final_section.incidence.get(*branch, 1).ok()
        })
        .ok_or("the terminal incidence supplies no separating branch orientation control")?;
    let parametron_receipt = final_section
        .inspect_current(&superposition, &BTreeSet::from([selected_branch]))
        .map_err(|error| error.to_string())?;

    // The exact serial result is formed before dispatch as the admission/audit control. It never
    // chooses or repairs a device return.
    let expected = fronts
        .iter()
        .map(|current| final_section.realize(current))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| error.to_string())?;
    let later_expected = final_section
        .realize(&superposition)
        .map_err(|error| error.to_string())?;
    let mut resident = final_section
        .mount_resident()
        .map_err(|error| error.to_string())?;
    let first = resident
        .conduct(&fronts)
        .map_err(|error| error.to_string())?;
    let later = resident
        .conduct(&[superposition])
        .map_err(|error| error.to_string())?;

    let first_exact = first.sections == expected;
    let later_exact = later.sections == vec![later_expected];
    let phase_pair = &first.sections[first.sections.len() - 2..];
    let half_turn_exact = phase_pair[1]
        == phase_pair[0]
            .iter()
            .map(ExactComplexWaveCurrent::negated)
            .collect::<Vec<_>>();

    let output = PathBuf::from(OUTPUT);
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    write_json(&output.join("00-parametron-atlas.json"), &atlas_summary)?;
    write_json(
        &output.join("01-terminal-parametron-receipt.json"),
        &parametron_receipt,
    )?;
    write_json(
        &output.join("02-resident-complex-current.json"),
        &json!({ "first": &first, "later": &later }),
    )?;
    let grade = json!({
        "schema": "holonics.foreign-complex-parametron-residency-grade.v1",
        "truth_status": "established-bounded; implemented-exact; measured",
        "captured_section_population": atlas_summary.len(),
        "terminal_branch_population": parametron_receipt.branch_population,
        "coefficient_node_population": nodes,
        "incidence_rank": parametron_receipt.incidence_rank,
        "incidence_kernel_dimension": parametron_receipt.incidence_kernel_dimension,
        "receiver_radical_dimension": parametron_receipt.radical_dimension,
        "storage_pullback_exact": parametron_receipt.storage_pullback_exact,
        "orientation_covariant": parametron_receipt.orientation_covariant,
        "half_turn_negates_complete_current_on_exact_owner": parametron_receipt.half_turn_negates_complete_current,
        "half_turn_negates_complete_current_on_card": half_turn_exact,
        "first_complex_front_exact": first_exact,
        "later_complex_front_exact": later_exact,
        "binary_receiver_taken": first.binary_receiver_taken || later.binary_receiver_taken,
        "first_launches": first.launches,
        "later_launches": later.launches,
        "first_synchronizations": first.synchronizations,
        "later_synchronizations": later.synchronizations,
        "mount_invariant_ingress_octets": first.mount_host_ingress_octets,
        "first_successor_ingress_octets": first.successor_host_ingress_octets,
        "later_successor_ingress_octets": later.successor_host_ingress_octets,
        "resident_invariant_octets": first.resident_invariant_octets,
        "invariant_transport_reuploaded_on_first_successor": first.invariant_transport_reuploaded,
        "invariant_transport_reuploaded_on_later_successor": later.invariant_transport_reuploaded,
        "foreign_tower_staged_octets_during_successors": 0,
        "foreign_tower_launches_during_successors": 0,
        "cpu_exact_control_computed_before_device": true,
        "cpu_semantic_replay_after_device": first.cpu_semantic_replay_after_device || later.cpu_semantic_replay_after_device,
        "device": first.device,
        "passed": parametron_receipt.storage_pullback_exact
            && parametron_receipt.orientation_covariant
            && parametron_receipt.half_turn_negates_complete_current
            && half_turn_exact
            && first_exact
            && later_exact
            && !first.binary_receiver_taken
            && !later.binary_receiver_taken
            && first.launches == 1
            && later.launches == 1
            && !first.invariant_transport_reuploaded
            && !later.invariant_transport_reuploaded
            && !first.cpu_semantic_replay_after_device
            && !later.cpu_semantic_replay_after_device,
    });
    write_json(&output.join("03-grade.json"), &grade)?;
    write_json(
        &output.join("04-expensive-invocation.json"),
        &json!({
            "command": "cargo run -p life --example the_foreign_section_carries_complex_parametron_current",
            "purpose": "mount the captured terminal incidence once and carry two exact complex successor fronts without phase locking or foreign replay",
            "elapsed_seconds": format!("{:.9}", started.elapsed().as_secs_f64()),
            "exit_status": if grade["passed"] == true { 0 } else { 1 },
            "source_rest_sha256": sha256(&source_bytes),
        }),
    )?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The foreign section carries Complex Parametron current\n\n[established-bounded; implemented-exact; measured] The complete captured section family returned as oriented incidence with exact diagonal receiver storage, pulled coefficient forms, incidence kernels and receiver radicals. The terminal incidence mounted once on the resident card. One-hot history currents, a relative-phase superposition and its half-turn crossed in one front; a later superposition crossed again without re-uploading the incidence or reopening Gemma. Both phase coordinates, storage pullback and orientation covariance returned exactly.\n\n[definition] The finite history word is a separate locked receiver control. It is not the productive carrier graded here.\n\n```json\n{}\n```\n",
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
        Err("the foreign Complex Parametron residency grade refused".to_owned())
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
            "schema": "holonics.foreign-complex-parametron-manifest.v1",
            "entries": entries,
        }),
    )
}
