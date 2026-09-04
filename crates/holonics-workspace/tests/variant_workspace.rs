use std::fs;
use std::path::Path;

use holonics_hna::AthenaAlphaApplication;
use holonic_engine::{native_spool::fixture, EventId};
use holonics_workspace::{ArtifactKind, VariantWorkspace};
use life::native_intelligence::{ExportCodecKind, NativeCirculationConfiguration};
use serde_json::json;
use tempfile::tempdir;

/// Write one generation-zero snapshot of the engine's declared native body and return the ingress
/// ordinal of the occurrence which carries an actual successor. Nothing is lifted here: the
/// workspace founds itself from a snapshot the way it founds itself from any other snapshot.
fn declared_snapshot(path: &Path) -> usize {
    let mut configuration: NativeCirculationConfiguration =
        serde_json::from_str(holonics_hna::BASE_CONFIGURATION).expect("configuration");
    configuration.address.receiver = fixture::FIXTURE_RECEIVER;
    let admission =
        AthenaAlphaApplication::from_dismantling_return(fixture::detached_returned(), configuration)
            .expect("declared admission");
    let ingress = admission
        .application
        .package()
        .hot()
        .realization()
        .ingress_sections
        .iter()
        .position(|address| address.occurrence == EventId(1))
        .expect("the declared body admits occurrence 1 as an ingress");
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
    ingress
}

#[test]
fn declared_snapshot_workspace_reopens_runs_commits_evaluates_and_exports() {
    let temporary = tempdir().expect("temporary");
    let source = temporary.path().join("declared.snapshot.json");
    let ingress = declared_snapshot(&source);
    let root = temporary.path().join("variant");

    let mut workspace = VariantWorkspace::create(&root, "first-athena").expect("workspace");
    let imported = workspace.import_snapshot(&source).expect("import");
    assert_eq!(imported.value.generation, 0);
    assert!(imported
        .written_artifacts
        .iter()
        .all(|path| path.starts_with(&root)));
    let snapshot0 = imported.current_snapshot.expect("generation zero snapshot");
    assert!(snapshot0.is_file());

    let experiment = workspace
        .define_experiment("primary", ingress, None)
        .expect("experiment");
    assert_eq!(experiment.value.receiver, fixture::FIXTURE_RECEIVER);
    let run = workspace.conduct("primary").expect("conduct");
    assert_eq!(run.value.run.boundary_history.len(), 1);
    assert_eq!(run.value.boundary.generation, 0);
    drop(workspace);

    let mut workspace = VariantWorkspace::open(&root).expect("reopen active run");
    assert!(workspace.continue_active(99).is_err());
    assert!(workspace.manifest().active_run.is_some());
    let staged = workspace
        .stage_world_return(EventId(100), true, b"test-world-admitted".to_vec())
        .expect("stage return");
    assert!(staged
        .written_artifacts
        .iter()
        .any(|path| path.ends_with("candidate.json")));
    drop(workspace);

    let mut workspace = VariantWorkspace::open(&root).expect("reopen candidate");
    let committed = workspace.commit().expect("commit");
    assert_eq!(committed.value.successor_lineage.generation, 1);
    let snapshot1 = committed.current_snapshot.expect("generation one snapshot");
    assert_ne!(snapshot1, snapshot0);
    assert!(snapshot1.is_file());
    assert!(workspace.manifest().active_run.is_none());
    assert_eq!(workspace.manifest().completed_runs.len(), 1);
    drop(workspace);

    let mut workspace = VariantWorkspace::open(&root).expect("source-detached reopen");
    let evaluation = workspace.evaluate("primary").expect("evaluation");
    assert_eq!(evaluation.value.current.generation, 1);
    assert_eq!(
        evaluation
            .value
            .cultivation_separates_current_from_withdrawn,
        Some(true)
    );
    assert_eq!(evaluation.value.restoration_exact, Some(true));
    assert!(evaluation.value.current_snapshot_unchanged);
    let onnx = workspace.export(ExportCodecKind::Onnx).expect("ONNX");
    assert!(onnx.value.complete_package_round_trip);
    assert_eq!(onnx.value.artifact.kind, ArtifactKind::Onnx);
    let safetensors = workspace
        .export(ExportCodecKind::Safetensors)
        .expect("Safetensors");
    assert!(safetensors.value.complete_package_round_trip);
    assert_eq!(safetensors.value.artifact.kind, ArtifactKind::Safetensors);
    assert!(workspace
        .manifest()
        .open_capabilities
        .contains("raw-model-directory-lift-open"));
    assert!(workspace
        .manifest()
        .open_capabilities
        .contains("qualitative-emission-codec-open"));
}

#[test]
fn imported_native_snapshot_reopens_and_continues_an_actual_successor() {
    let temporary = tempdir().expect("temporary");
    let source = temporary.path().join("source.snapshot.json");
    let ingress = declared_snapshot(&source);
    let root = temporary.path().join("variant");
    let mut workspace = VariantWorkspace::create(&root, "continue-control").expect("workspace");
    workspace.import_snapshot(&source).expect("import");
    workspace
        .define_experiment("primary", ingress, None)
        .expect("experiment");
    workspace.conduct("primary").expect("conduct");
    drop(workspace);

    let mut workspace = VariantWorkspace::open(&root).expect("reopen");
    let continued = workspace.continue_active(0).expect("actual successor");
    assert_eq!(continued.value.run.boundary_history.len(), 2);
    assert_eq!(continued.value.boundary.generation, 0);
}

#[test]
fn decline_and_failed_operations_preserve_the_explicit_workspace() {
    let temporary = tempdir().expect("temporary");
    let source = temporary.path().join("declared.snapshot.json");
    let ingress = declared_snapshot(&source);
    let root = temporary.path().join("variant");
    let mut workspace = VariantWorkspace::create(&root, "decline-control").expect("workspace");
    workspace.import_snapshot(&source).expect("import");
    workspace
        .define_experiment("primary", ingress, None)
        .expect("experiment");
    let before = fs::read(
        workspace
            .inspect()
            .expect("inspect")
            .current_snapshot
            .expect("snapshot"),
    )
    .expect("snapshot bytes");
    workspace.conduct("primary").expect("conduct");
    assert!(workspace.conduct("primary").is_err());
    let decline = workspace.decline().expect("decline");
    assert_eq!(
        decline.value.generation_before,
        decline.value.generation_after
    );
    let after = fs::read(decline.current_snapshot.expect("snapshot")).expect("snapshot bytes");
    assert_eq!(after, before);
    assert!(workspace.manifest().active_run.is_none());
    assert!(VariantWorkspace::create(&root, "overwrite").is_err());

    let manifest_bytes = fs::read(root.join("workspace.json")).expect("manifest");
    let mut manifest: serde_json::Value =
        serde_json::from_slice(&manifest_bytes).expect("manifest JSON");
    manifest["current"]["generation"] = json!(99);
    fs::write(
        root.join("workspace.json"),
        serde_json::to_vec(&manifest).expect("manifest wire"),
    )
    .expect("tamper generation");
    assert!(VariantWorkspace::open(&root).is_err());

    let mut manifest: serde_json::Value =
        serde_json::from_slice(&manifest_bytes).expect("manifest JSON");
    manifest["unknown"] = json!(true);
    fs::write(
        root.join("workspace.json"),
        serde_json::to_vec(&manifest).expect("manifest wire"),
    )
    .expect("tamper");
    assert!(VariantWorkspace::open(&root).is_err());
}
