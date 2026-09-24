use std::fs;
use std::io::Write;
use std::process::{Command, Stdio};

use holonics_workbench::{
    DiagnosticCommand, EventLevel, SoulkillerCommand, WorkbenchCommand, WorkbenchEvent,
    WorkbenchRequest, WorkbenchResponse, WorkbenchRuntime,
};
use tempfile::tempdir;

#[test]
fn diagnostic_soulkiller_and_cli_return_shared_structured_events() {
    let temporary = tempdir().expect("temporary");
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

    let mut runtime = WorkbenchRuntime::new();
    for command in [
        diagnostic(DiagnosticCommand::Status),
        diagnostic(DiagnosticCommand::Capabilities),
        diagnostic(DiagnosticCommand::Soulkiller(SoulkillerCommand::Config {
            path: config,
        })),
        diagnostic(DiagnosticCommand::Soulkiller(SoulkillerCommand::Index {
            path: index,
        })),
    ] {
        let events = runtime.execute(command);
        assert_eq!(events.len(), 1);
        assert_ne!(events[0].level, EventLevel::Obstruction, "{events:?}");
        assert!(events[0].payload.is_some());
    }

    let direct = {
        let mut runtime = WorkbenchRuntime::new();
        runtime.execute(diagnostic(DiagnosticCommand::Status))
    };
    let output = Command::new(env!("CARGO_BIN_EXE_holonics"))
        .args(["--format", "jsonl", "diagnostic", "status"])
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
    for command in ["hna", "diagnostic", "run"] {
        assert!(help.contains(command), "help omitted {command}");
    }
}

#[test]
fn cli_shorthand_and_structured_stdin_share_one_response_envelope() {
    let binary = env!("CARGO_BIN_EXE_holonics");
    let direct = Command::new(binary)
        .args(["--format", "json", "diagnostic", "status"])
        .output()
        .expect("direct status");
    assert!(direct.status.success());
    let direct: WorkbenchResponse =
        serde_json::from_slice(&direct.stdout).expect("direct response");

    let mut child = Command::new(binary)
        .args(["--format", "json", "run", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("structured status");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(
            &serde_json::to_vec(&WorkbenchRequest::new(diagnostic(
                DiagnosticCommand::Status,
            )))
            .expect("request wire"),
        )
        .expect("request input");
    let structured = child.wait_with_output().expect("structured output");
    assert!(structured.status.success());
    let structured: WorkbenchResponse =
        serde_json::from_slice(&structured.stdout).expect("structured response");
    assert_eq!(structured, direct);

    let mut invalid = Command::new(binary)
        .args(["--format", "json", "run", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("invalid request");
    invalid
        .stdin
        .take()
        .expect("stdin")
        .write_all(b"{not-json")
        .expect("invalid input");
    let invalid = invalid.wait_with_output().expect("invalid output");
    assert_eq!(invalid.status.code(), Some(2));
    let invalid: WorkbenchResponse =
        serde_json::from_slice(&invalid.stdout).expect("invalid response");
    assert!(invalid.obstructed());

    let malformed_cli = Command::new(binary)
        .args(["--format", "json", "diagnostic", "soulkiller", "not-a-command"])
        .output()
        .expect("malformed CLI");
    assert_eq!(malformed_cli.status.code(), Some(2));
    let malformed_cli: WorkbenchResponse =
        serde_json::from_slice(&malformed_cli.stdout).expect("malformed CLI response");
    assert!(malformed_cli.obstructed());

    let noninteractive = Command::new(binary)
        .stdin(Stdio::null())
        .output()
        .expect("noninteractive no-command control");
    assert!(noninteractive.status.success());
    assert!(String::from_utf8_lossy(&noninteractive.stdout).contains("diagnostic"));
    assert!(!String::from_utf8_lossy(&noninteractive.stderr).contains("panicked"));
}

#[test]
fn missing_and_malformed_exterior_material_refuses_without_execution() {
    let temporary = tempdir().expect("temporary");
    let malformed = temporary.path().join("bad.json");
    fs::write(&malformed, b"{not-json").expect("malformed");
    let mut runtime = WorkbenchRuntime::new();
    for command in [
        diagnostic(DiagnosticCommand::Soulkiller(SoulkillerCommand::Config {
            path: malformed,
        })),
        diagnostic(DiagnosticCommand::Soulkiller(SoulkillerCommand::Onnx {
            path: temporary.path().join("absent.onnx"),
        })),
    ] {
        let event = runtime.execute(command).remove(0);
        assert_eq!(event.level, EventLevel::Obstruction);
    }
}

fn diagnostic(command: DiagnosticCommand) -> WorkbenchCommand {
    WorkbenchCommand::Diagnostic(command)
}
