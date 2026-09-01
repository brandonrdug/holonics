//! H5 — withdraw the ordinary-material standing by recoverable ownership transfer, restore it
//! exactly, withdraw it again, then apply the complete H3N reverse factor word and recover K3.

use std::{fs, path::PathBuf, time::Instant};

use life::athena_native::{NativeEcologyRest, NativeCirculationRest};
use serde_json::json;
use sha2::{Digest, Sha256};

const H4_REST: &str = concat!(
    "output/the_ordinary_material_crosses_one_native_relational_potential_and_brandon_returns_h4/",
    "athena-native-circulation.rest"
);
const K3_REST: &str = concat!(
    "output/the_one_connected_athena_native_ecology_returns_dependent_sections_k3/",
    "athena-native.rest"
);
const OUTPUT: &str = "output/the_complete_native_reverse_word_recovers_the_k3_predecessor_h5";

fn main() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing H5 return {}", output.display()));
    }
    fs::create_dir_all(&output).map_err(display)?;
    let started = Instant::now();

    let h4_bytes = fs::read(H4_REST).map_err(display)?;
    let h4_identity = NativeCirculationRest::read(&h4_bytes)
        .map_err(display)?
        .identity()
        .to_owned();
    let (cultivated, withdrawn, first_withdrawal) = NativeCirculationRest::read(&h4_bytes)
        .map_err(display)?
        .withdraw_relational_standing()
        .map_err(display)?;
    let (restored_h4, restoration) =
        NativeCirculationRest::restore_relational_standing(cultivated, withdrawn)
            .map_err(display)?;
    let restored_h4_bytes = restored_h4.canonical_bytes().map_err(display)?;
    let h4_restoration_identity = restored_h4.identity() == h4_identity;
    let h4_restoration_wire = restored_h4_bytes == h4_bytes;

    // Continue from the restored owner. The second withdrawal returns the same cultivated owner
    // and another move-owned reconstruction fibre; the exterior H4 rest remains the deposited
    // reconstruction artifact while the live reverse proceeds to K3.
    let (cultivated, _relational_reconstruction_fibre, second_withdrawal) = restored_h4
        .withdraw_relational_standing()
        .map_err(display)?;
    let (recovered_k3, factor_withdrawal) = cultivated.withdraw().map_err(display)?;
    let recovered_k3_bytes = recovered_k3.canonical_bytes().map_err(display)?;
    let declared_k3_bytes = fs::read(K3_REST).map_err(display)?;
    let declared_k3 = NativeEcologyRest::read(&declared_k3_bytes).map_err(display)?;
    let recovered_k3_wire_equal = recovered_k3_bytes == declared_k3_bytes;
    let recovered_k3_identity_equal = recovered_k3.wire_sha256().map_err(display)?
        == declared_k3.wire_sha256().map_err(display)?;

    let ingress = recovered_k3
        .realization
        .ingress_sections
        .first()
        .cloned()
        .ok_or("recovered K3 has no ingress")?;
    let receiver = *recovered_k3
        .realization
        .receiver_family
        .iter()
        .next()
        .ok_or("recovered K3 has no receiver")?;
    let recovered_return = recovered_k3.conduct(&ingress, receiver).map_err(display)?;
    let declared_return = declared_k3.conduct(&ingress, receiver).map_err(display)?;
    let recovered_k3_conduct_equal = recovered_return == declared_return;

    let passed = h4_restoration_identity
        && h4_restoration_wire
        && first_withdrawal.move_owned_reconstruction_fibre
        && second_withdrawal.move_owned_reconstruction_fibre
        && factor_withdrawal.complete_reverse_word_applied
        && factor_withdrawal.forward_then_inverse_identity
        && factor_withdrawal.inverse_then_forward_identity
        && recovered_k3_wire_equal
        && recovered_k3_identity_equal
        && recovered_k3_conduct_equal;

    fs::write(
        output.join("recovered-k3-athena-native.rest"),
        &recovered_k3_bytes,
    )
    .map_err(display)?;
    fs::write(
        output.join("00-grade.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "soma-life.athena-complete-native-reverse-h5-grade.v1",
            "truth_status": if passed {
                "established-bounded; implemented-exact; measured"
            } else {
                "counterexample; implemented-exact; measured"
            },
            "passed": passed,
            "h4_identity_sha256": h4_identity,
            "h4_restoration_identity": h4_restoration_identity,
            "h4_restoration_wire": h4_restoration_wire,
            "first_relational_withdrawal": first_withdrawal,
            "relational_restoration": restoration,
            "second_relational_withdrawal": second_withdrawal,
            "factor_withdrawal": factor_withdrawal,
            "recovered_k3_wire_equal": recovered_k3_wire_equal,
            "recovered_k3_identity_equal": recovered_k3_identity_equal,
            "recovered_k3_conduct_equal": recovered_k3_conduct_equal,
            "foreign_execution_present": false,
            "soulkiller_present": false,
            "source_exchange_present": false,
            "wall_milliseconds": started.elapsed().as_millis(),
        }))
        .map_err(display)?,
    )
    .map_err(display)?;
    write_manifest(&output)?;
    println!(
        "{}",
        fs::read_to_string(output.join("00-grade.json")).map_err(display)?
    );
    if passed {
        Ok(())
    } else {
        Err("H5 complete native reverse refused".to_owned())
    }
}

fn write_manifest(output: &PathBuf) -> Result<(), String> {
    let mut entries = fs::read_dir(output)
        .map_err(display)?
        .map(|entry| entry.map_err(display))
        .collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|entry| entry.file_name());
    let files = entries
        .into_iter()
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(display)?;
            Ok(json!({
                "path": entry.file_name().to_string_lossy(),
                "octets": bytes.len(),
                "sha256": render_hex(&Sha256::digest(&bytes)),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    fs::write(
        output.join("MANIFEST.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "soma-life.athena-complete-native-reverse-h5-manifest.v1",
            "files": files,
        }))
        .map_err(display)?,
    )
    .map_err(display)
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn render_hex(value: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(value.len() * 2);
    for octet in value {
        out.push(HEX[(octet >> 4) as usize] as char);
        out.push(HEX[(octet & 15) as usize] as char);
    }
    out
}
