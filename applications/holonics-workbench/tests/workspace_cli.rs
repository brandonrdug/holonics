use std::fs;
use std::path::Path;
use std::process::Command;

use athena_alpha::AthenaAlphaApplication;
use holonic_engine::native_spool::fixture;
use holonics_workbench::{render_human, WorkbenchResponse};
use life::native_intelligence::NativeCirculationConfiguration;
use tempfile::tempdir;

/// Write one generation-zero snapshot of the engine's declared native body. Nothing is lifted: the
/// shipped `workspace import-snapshot` command founds the workspace from it.
fn declared_snapshot(path: &Path) {
    let mut configuration: NativeCirculationConfiguration =
        serde_json::from_str(athena_alpha::BASE_CONFIGURATION).expect("configuration");
    configuration.address.receiver = fixture::FIXTURE_RECEIVER;
    let admission =
        AthenaAlphaApplication::from_dismantling_return(fixture::detached_returned(), configuration)
            .expect("declared admission");
    fs::write(
        path,
        admission
            .application
            .snapshot()
            .expect("snapshot")
            .canonical_bytes()
            .expect("snapshot wire"),
    )
    .expect("declared snapshot");
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
fn cli_returns_the_complete_snapshot_to_successor_artifact_lifecycle() {
    let temporary = tempdir().expect("temporary");
    let source = temporary.path().join("declared.snapshot.json");
    let workspace = temporary.path().join("workspace");
    declared_snapshot(&source);
    let root = workspace.to_str().expect("root");
    let source = source.to_str().expect("snapshot");

    run(None, &["workspace", "create", root, "first-athena"]);
    let imported = run(
        Some(&workspace),
        &["workspace", "import-snapshot", source],
    );
    assert_eq!(
        imported.events[0].payload.as_ref().expect("payload")["value"]["generation"],
        0
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
