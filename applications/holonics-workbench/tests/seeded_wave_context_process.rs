use holonics_hna::{HnaStreamCommand, HnaStreamRequest, HNA_STREAM_REQUEST_SCHEMA};
use serde_json::Value;
use std::process::{Command, Output};
use tempfile::tempdir;

fn request(command: HnaStreamCommand) -> String {
    serde_json::to_string(&HnaStreamRequest {
        schema: HNA_STREAM_REQUEST_SCHEMA.into(),
        command,
    })
    .unwrap()
}

fn run(
    source: &std::path::Path,
    input: &std::path::Path,
    checkpoint: &std::path::Path,
    resume: bool,
) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_holonics"));
    command.args(["hna", "wave-session"]).arg(source);
    if resume {
        command.arg("--resume");
    } else {
        command.arg("--seed");
    }
    command
        .args(["--input"])
        .arg(input)
        .args(["--checkpoint"])
        .arg(checkpoint);
    command.output().unwrap()
}

#[test]
#[ignore = "requires CUDA; verifies seeded contextual source reception across processes"]
fn seeded_wave_context_survives_checkpoint_and_predicts_held_out_sources() {
    let directory = tempdir().unwrap();
    let seed = directory.path().join("seed.json");
    std::fs::write(&seed, r#"{"schema":"org.holonics.hna.applied-wave-seed.v1","symbols":["a","b","x"],"seed":"ax","grain":64}"#).unwrap();
    let prefix = directory.path().join("prefix.jsonl");
    let mut lines = Vec::new();
    for _ in 0..8 {
        for (context, observed) in [("ax", "a"), ("bx", "b")] {
            lines.push(request(HnaStreamCommand::ActuateText {
                text: context.into(),
            }));
            lines.push(request(HnaStreamCommand::ReceiveNextSymbol {
                text: observed.into(),
            }));
        }
    }
    std::fs::write(&prefix, lines.join("\n") + "\n").unwrap();
    let checkpoint = directory.path().join("prepared.wave");
    let first = run(&seed, &prefix, &checkpoint, false);
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let first_receipt: Value = serde_json::from_slice(&first.stderr).unwrap();
    assert!(first_receipt["checkpoint_octets"].as_u64().is_some());

    let held_out = directory.path().join("held-out.jsonl");
    let queries = [("aax", "a"), ("bbx", "b")];
    std::fs::write(
        &held_out,
        queries
            .iter()
            .flat_map(|(context, _)| {
                [
                    request(HnaStreamCommand::ActuateText {
                        text: (*context).into(),
                    }),
                    request(HnaStreamCommand::EmitSymbol {
                        full_emission: false,
                        retain_comparison: false,
                    }),
                ]
            })
            .collect::<Vec<_>>()
            .join("\n")
            + "\n",
    )
    .unwrap();
    let next_checkpoint = directory.path().join("continued.wave");
    let second = run(&checkpoint, &held_out, &next_checkpoint, true);
    assert!(
        second.status.success(),
        "{}",
        String::from_utf8_lossy(&second.stderr)
    );
    let events: Vec<Value> = String::from_utf8(second.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let emitted: Vec<&Value> = events
        .iter()
        .filter(|event| event["event"] == "symbol-emitted")
        .collect();
    assert_eq!(emitted.len(), 2);
    assert_eq!(emitted[0]["value"]["text"], "a");
    assert_eq!(emitted[1]["value"]["text"], "b");
    let receipt: Value = serde_json::from_slice(&second.stderr).unwrap();
    assert!(receipt["checkpoint_octets"].as_u64().is_some());
    assert_eq!(receipt["checkpoint_error"], Value::Null);
    assert_eq!(receipt["inspect"]["observations"], 16);
}
