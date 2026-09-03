use std::fs;
use std::path::Path;
use std::process::Command;

use holonic_engine::native_ecology::holonic_intelligence::COMPLETE_GEMMA4_EXCITATION_SCHEMA;
use holonics_workbench::{render_human, WorkbenchResponse};
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
        "occurrence": format!("cli-return/{name}"),
        "source_sha256": digest(entering),
        "entering_bf16": format!("{name}-in.bf16"),
        "entering_sha256": digest(entering),
        "returned_bf16": format!("{name}-out.bf16"),
        "returned_sha256": digest(returned),
        "complete_layer_count": 1
    })
}

fn fixture(root: &Path) {
    let mut returns = Vec::new();
    for (name, entering, returned_word) in [
        ("text", 0x3f80u16, 0x4000u16),
        ("vision", 0x4000u16, 0x4040u16),
        ("audio", 0x4080u16, 0x40a0u16),
    ] {
        let entering = entering.to_le_bytes();
        let returned_bytes = returned_word.to_le_bytes();
        fs::write(root.join(format!("{name}-in.bf16")), entering).expect("entering");
        fs::write(root.join(format!("{name}-out.bf16")), returned_bytes).expect("returned");
        returns.push(returned(name, &entering, &returned_bytes));
    }
    fs::write(
        root.join("receipt.json"),
        serde_json::to_vec(&json!({
            "schema": COMPLETE_GEMMA4_EXCITATION_SCHEMA,
            "text": {"returns": [returns[0].clone()]},
            "vision": {"returns": [returns[1].clone()]},
            "audio": {"returns": [returns[2].clone()]},
            "video": {"temporal_frame_lineage": false, "frame_returns": []}
        }))
        .expect("receipt"),
    )
    .expect("receipt file");
}

fn run(current_dir: Option<&Path>, arguments: &[&str]) -> WorkbenchResponse {
    let mut command = Command::new(env!("CARGO_BIN_EXE_holonics"));
    if let Some(current_dir) = current_dir {
        command.current_dir(current_dir);
    }
    let output = command
        .arg("--format")
        .arg("json")
        .args(arguments)
        .output()
        .expect("holonics");
    assert!(
        output.status.success(),
        "command {arguments:?} refused:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("response")
}

#[test]
fn cli_returns_the_complete_actual_receipt_to_successor_artifact_lifecycle() {
    let temporary = tempdir().expect("temporary");
    let receipt = temporary.path().join("receipt");
    let workspace = temporary.path().join("workspace");
    fs::create_dir(&receipt).expect("receipt root");
    fixture(&receipt);
    let root = workspace.to_str().expect("root");
    let receipt = receipt.to_str().expect("receipt");

    run(None, &["workspace", "create", root, "first-athena"]);
    let lift = run(
        Some(&workspace),
        &["workspace", "lift-gemma-receipt", receipt],
    );
    assert_eq!(
        lift.events[0].payload.as_ref().expect("payload")["value"]["foreign_execution"],
        false
    );
    run(
        Some(&workspace),
        &["workspace", "define-experiment", "primary"],
    );
    let conduct = run(Some(&workspace), &["workspace", "conduct", "primary"]);
    let conduct_human = render_human(&conduct.events);
    assert!(conduct_human.contains("ACTIVE CIRCULATION"));
    assert!(conduct_human.contains("Actual successors"));
    assert!(conduct_human.contains("WRITTEN ARTIFACTS"));
    run(
        Some(&workspace),
        &[
            "workspace",
            "stage-return",
            "100",
            "--admitted",
            "--diagnostic",
            "workspace-world-admitted",
        ],
    );
    let commit = run(Some(&workspace), &["workspace", "commit"]);
    let current = commit.events[0].payload.as_ref().expect("payload")["current_snapshot"]
        .as_str()
        .expect("current snapshot");
    assert!(Path::new(current).is_file());
    let evaluation = run(Some(&workspace), &["workspace", "evaluate", "primary"]);
    assert_eq!(
        evaluation.events[0].payload.as_ref().expect("payload")["value"]["restoration_exact"],
        true
    );
    let onnx = run(Some(&workspace), &["workspace", "export", "onnx"]);
    assert!(
        onnx.events[0].payload.as_ref().expect("payload")["written_artifacts"]
            .as_array()
            .expect("artifacts")
            .iter()
            .all(|path| Path::new(path.as_str().expect("path")).is_file())
    );
    run(Some(&workspace), &["workspace", "export", "safetensors"]);
    let inspect = run(Some(&workspace), &["workspace", "inspect"]);
    let manifest = &inspect.events[0].payload.as_ref().expect("payload")["value"]["manifest"];
    assert_eq!(manifest["current"]["generation"], 1);
    assert_eq!(
        manifest["completed_runs"].as_array().expect("runs").len(),
        1
    );
    assert_eq!(
        manifest["evaluations"]
            .as_array()
            .expect("evaluations")
            .len(),
        1
    );
    assert_eq!(manifest["exports"].as_array().expect("exports").len(), 4);
    let inspect_human = render_human(&inspect.events);
    assert!(inspect_human.contains("VARIANT STATE"));
    assert!(inspect_human.contains("Generation                         1"));
    assert!(inspect_human.contains("Experiments                        primary"));
    assert!(inspect_human.contains("Open capabilities"));
    assert!(inspect_human.contains("raw-model-directory-lift-open"));

    let help = Command::new(env!("CARGO_BIN_EXE_holonics"))
        .arg("--help")
        .output()
        .expect("help");
    let help = String::from_utf8(help.stdout).expect("help UTF-8");
    assert!(help.contains("workspace"));
    assert!(help.contains("diagnostic"));
    assert!(!help.contains("tui"));
}
