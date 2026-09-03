use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        Bf16ExcitationDismantling, ExteriorModality, ForeignBf16Excitation,
        COMPLETE_GEMMA4_EXCITATION_SCHEMA,
    },
    receiver_exact_compression::ReceiverId,
    soulkiller::dismantle,
    BoundaryId, EventId,
};
use holonics_application::{ArtifactKind, VariantWorkspace};
use life::native_intelligence::{ExportCodecKind, NativeCirculationConfiguration};
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
        "occurrence": format!("actual-return/{name}"),
        "source_sha256": digest(entering),
        "entering_bf16": format!("{name}-in.bf16"),
        "entering_sha256": digest(entering),
        "returned_bf16": format!("{name}-out.bf16"),
        "returned_sha256": digest(returned),
        "complete_layer_count": 1
    })
}

fn gemma_receipt(root: &Path) {
    let families = [
        ("text", 0x3f80u16, 0x4000u16),
        ("vision", 0x4000u16, 0x4040u16),
        ("audio", 0x4080u16, 0x40a0u16),
    ];
    let mut returns = Vec::new();
    for (name, entering, returned_word) in families {
        let entering = entering.to_le_bytes();
        let returned_bytes = returned_word.to_le_bytes();
        fs::write(root.join(format!("{name}-in.bf16")), entering).expect("entering");
        fs::write(root.join(format!("{name}-out.bf16")), returned_bytes).expect("returned");
        returns.push(returned(name, &entering, &returned_bytes));
    }
    fs::write(
        root.join("receipt.json"),
        serde_json::to_vec_pretty(&json!({
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

#[test]
fn actual_receipt_workspace_reopens_runs_commits_evaluates_and_exports() {
    let temporary = tempdir().expect("temporary");
    let receipt = temporary.path().join("actual-receipt");
    fs::create_dir(&receipt).expect("receipt root");
    gemma_receipt(&receipt);
    let root = temporary.path().join("variant");

    let mut workspace = VariantWorkspace::create(&root, "first-athena").expect("workspace");
    let lifted = workspace
        .lift_gemma_receipt(&receipt, ReceiverId(7))
        .expect("lift");
    assert_eq!(lifted.value.generation, 0);
    assert_eq!(lifted.value.cold_excitation_population, 3);
    assert!(!lifted.value.foreign_execution);
    assert!(lifted
        .written_artifacts
        .iter()
        .all(|path| path.starts_with(&root)));
    let snapshot0 = lifted.current_snapshot.expect("generation zero snapshot");
    assert!(snapshot0.is_file());

    let experiment = workspace
        .define_experiment("primary", 0, None)
        .expect("experiment");
    assert_eq!(experiment.value.receiver, ReceiverId(7));
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
    let returned = dismantle(Bf16ExcitationDismantling {
        receiver: ReceiverId(7),
        excitations: vec![
            ForeignBf16Excitation {
                event: EventId(1),
                predecessor: None,
                entering_boundary: BoundaryId(2),
                emitting_boundary: BoundaryId(3),
                source_occurrence: "cold/one".to_owned(),
                exterior_modality: ExteriorModality::Text,
                entering_codewords: vec![0x3f80],
                returned_codewords: vec![0x4000],
                interventions: BTreeSet::from(["withdraw/one".to_owned()]),
                receiver_consequences: BTreeSet::from(["return/one".to_owned()]),
            },
            ForeignBf16Excitation {
                event: EventId(2),
                predecessor: Some(EventId(1)),
                entering_boundary: BoundaryId(4),
                emitting_boundary: BoundaryId(5),
                source_occurrence: "cold/two".to_owned(),
                exterior_modality: ExteriorModality::Text,
                entering_codewords: vec![0x4000],
                returned_codewords: vec![0x4040],
                interventions: BTreeSet::from(["withdraw/two".to_owned()]),
                receiver_consequences: BTreeSet::from(["return/two".to_owned()]),
            },
        ],
    })
    .expect("dismantle");
    let configuration: NativeCirculationConfiguration =
        serde_json::from_str(athena_alpha::BASE_CONFIGURATION).expect("configuration");
    let admission =
        athena_alpha::AthenaAlphaApplication::from_dismantling_return(returned, configuration)
            .expect("application");
    let snapshot = admission.application.snapshot().expect("snapshot");
    let source = temporary.path().join("source.snapshot.json");
    fs::write(&source, snapshot.canonical_bytes().expect("snapshot wire")).expect("snapshot file");
    let root = temporary.path().join("variant");
    let mut workspace = VariantWorkspace::create(&root, "continue-control").expect("workspace");
    workspace.import_snapshot(&source).expect("import");
    workspace
        .define_experiment("primary", 0, None)
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
    let receipt = temporary.path().join("actual-receipt");
    fs::create_dir(&receipt).expect("receipt root");
    gemma_receipt(&receipt);
    let root = temporary.path().join("variant");
    let mut workspace = VariantWorkspace::create(&root, "decline-control").expect("workspace");
    workspace
        .lift_gemma_receipt(&receipt, ReceiverId(7))
        .expect("lift");
    workspace
        .define_experiment("primary", 0, None)
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
