use std::fs;

use athena_alpha::{AthenaAlphaApplication, BASE_CONFIGURATION};
use holonic_engine::native_ecology::holonic_intelligence::COMPLETE_GEMMA4_EXCITATION_SCHEMA;
use life::native_intelligence::NativeCirculationConfiguration;
use serde_json::json;
use sha2::{Digest, Sha256};
use tempfile::tempdir;

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn returned(name: &str, entering: &[u8], returned: &[u8]) -> serde_json::Value {
    json!({
        "occurrence": format!("foreign-return/{name}"),
        "source_sha256": digest(entering),
        "entering_bf16": format!("{name}-in.bf16"),
        "entering_sha256": digest(entering),
        "returned_bf16": format!("{name}-out.bf16"),
        "returned_sha256": digest(returned),
        "complete_layer_count": 1
    })
}

#[test]
fn complete_gemma_receipt_founds_one_source_neutral_generation_zero_application() {
    let temporary = tempdir().expect("temporary");
    let families = [
        ("text", 0x3f80u16, 0x4000u16),
        ("vision", 0x4000u16, 0x4040u16),
        ("audio", 0x4080u16, 0x40a0u16),
    ];
    let mut returns = Vec::new();
    for (name, entering, returned_word) in families {
        let entering = entering.to_le_bytes();
        let returned_bytes = returned_word.to_le_bytes();
        fs::write(temporary.path().join(format!("{name}-in.bf16")), entering).expect("entering");
        fs::write(
            temporary.path().join(format!("{name}-out.bf16")),
            returned_bytes,
        )
        .expect("returned");
        returns.push(returned(name, &entering, &returned_bytes));
    }
    let receipt = json!({
        "schema": COMPLETE_GEMMA4_EXCITATION_SCHEMA,
        "text": {"returns": [returns[0].clone()]},
        "vision": {"returns": [returns[1].clone()]},
        "audio": {"returns": [returns[2].clone()]},
        "video": {"temporal_frame_lineage": false, "frame_returns": []}
    });
    fs::write(
        temporary.path().join("receipt.json"),
        serde_json::to_vec(&receipt).expect("receipt wire"),
    )
    .expect("receipt");

    let configuration: NativeCirculationConfiguration =
        serde_json::from_str(BASE_CONFIGURATION).expect("configuration");
    let admission =
        AthenaAlphaApplication::from_complete_gemma4_receipt(temporary.path(), configuration)
            .expect("admission");
    assert_eq!(admission.application.generation(), 0);
    assert_eq!(
        admission.application.package().manifest.lineage.generation,
        0
    );
    let snapshot = admission.application.snapshot().expect("snapshot");
    assert!(snapshot.commits.is_empty());
    assert_eq!(
        snapshot.package_wire,
        admission
            .application
            .package()
            .canonical_bytes()
            .expect("package wire")
    );
    assert_eq!(admission.departed.cold_witness.excitations.len(), 3);
    assert!(admission
        .departed
        .cold_witness
        .open_exterior
        .iter()
        .any(|open| open.contains("video")));
    assert!(!admission.departed.insufficiency.retained_fibre.is_empty());
    let hot = String::from_utf8(snapshot.package_wire)
        .expect("UTF-8 package")
        .to_ascii_lowercase();
    for forbidden in [
        "foreign-return/text",
        "foreign-return/vision",
        "foreign-return/audio",
        "source_sha256",
    ] {
        assert!(!hot.contains(forbidden), "hot package retained {forbidden}");
    }
}
