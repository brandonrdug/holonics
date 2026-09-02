use std::fs;
use std::process::Command;

use holonics_workbench::{
    AthenaCommand, EngineCommand, ErosCommand, EventLevel, ExportCodecArgument, SoulkillerCommand,
    WorkbenchCommand, WorkbenchEvent, WorkbenchRuntime,
};
use tempfile::tempdir;

#[test]
fn eros_soulkiller_engine_and_cli_return_shared_structured_events() {
    let temporary = tempdir().expect("temporary");
    let material = temporary.path().join("material");
    fs::create_dir(&material).expect("material directory");
    fs::write(material.join("one.md"), b"alpha beta alpha\n").expect("material one");
    fs::write(material.join("two.md"), b"beta gamma beta\n").expect("material two");
    let config = temporary.path().join("config.json");
    fs::write(
        &config,
        br#"{"model_type":"bounded-demo","hidden_size":16,"unknown":{"retained":true}}"#,
    )
    .expect("config");
    let index = temporary.path().join("model.safetensors.index.json");
    fs::write(
        &index,
        br#"{"metadata":{"total_size":32},"weight_map":{"a.weight":"one.safetensors","b.weight":"two.safetensors"}}"#,
    )
    .expect("index");
    let snapshot = temporary.path().join("alpha.snapshot.json");
    let onnx = temporary.path().join("alpha.onnx");

    let mut runtime = WorkbenchRuntime::new();
    for command in [
        WorkbenchCommand::Status,
        WorkbenchCommand::Capabilities,
        WorkbenchCommand::Eros(ErosCommand::Mouth {
            directory: material.clone(),
            extension: "md".to_owned(),
            radius: 2,
            scales: 2,
            octet_budget: 1_000,
        }),
        WorkbenchCommand::Eros(ErosCommand::Atlas {
            directory: material,
            extension: "md".to_owned(),
            octet_budget: 1_000,
        }),
        WorkbenchCommand::Soulkiller(SoulkillerCommand::Config { path: config }),
        WorkbenchCommand::Soulkiller(SoulkillerCommand::Index { path: index }),
        WorkbenchCommand::Athena(AthenaCommand::DemoOpen {
            session: "alpha".to_owned(),
        }),
        WorkbenchCommand::Athena(AthenaCommand::Snapshot {
            session: "alpha".to_owned(),
            path: snapshot.clone(),
        }),
        WorkbenchCommand::Engine(EngineCommand::Package {
            path: snapshot.clone(),
        }),
        WorkbenchCommand::Engine(EngineCommand::Export {
            package: snapshot,
            codec: ExportCodecArgument::Onnx,
            path: onnx.clone(),
        }),
        WorkbenchCommand::Soulkiller(SoulkillerCommand::Onnx { path: onnx }),
    ] {
        let events = runtime.execute(command);
        assert_eq!(events.len(), 1);
        assert_ne!(events[0].level, EventLevel::Obstruction, "{events:?}");
        assert!(events[0].payload.is_some());
    }

    let direct = {
        let mut runtime = WorkbenchRuntime::new();
        runtime.execute(WorkbenchCommand::Status)
    };
    let output = Command::new(env!("CARGO_BIN_EXE_holonics"))
        .args(["--json", "status"])
        .output()
        .expect("CLI status");
    assert!(output.status.success());
    let cli = String::from_utf8(output.stdout)
        .expect("UTF-8")
        .lines()
        .map(|line| serde_json::from_str::<WorkbenchEvent>(line).expect("event"))
        .collect::<Vec<_>>();
    assert_eq!(cli, direct);

    let help = Command::new(env!("CARGO_BIN_EXE_holonics"))
        .arg("--help")
        .output()
        .expect("CLI help");
    let help = String::from_utf8(help.stdout).expect("help UTF-8");
    for command in [
        "athena",
        "eros",
        "soulkiller",
        "engine",
        "capabilities",
        "tui",
    ] {
        assert!(help.contains(command), "help omitted {command}");
    }
}

#[test]
fn missing_and_malformed_exterior_material_refuses_without_execution() {
    let temporary = tempdir().expect("temporary");
    let malformed = temporary.path().join("bad.json");
    fs::write(&malformed, b"{not-json").expect("malformed");
    let mut runtime = WorkbenchRuntime::new();
    for command in [
        WorkbenchCommand::Soulkiller(SoulkillerCommand::Config { path: malformed }),
        WorkbenchCommand::Soulkiller(SoulkillerCommand::Onnx {
            path: temporary.path().join("absent.onnx"),
        }),
        WorkbenchCommand::Eros(ErosCommand::Atlas {
            directory: temporary.path().join("absent"),
            extension: "md".to_owned(),
            octet_budget: 10,
        }),
    ] {
        let event = runtime.execute(command).remove(0);
        assert_eq!(event.level, EventLevel::Obstruction);
    }
}
