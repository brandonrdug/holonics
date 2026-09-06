//! Actual process-boundary controls. These test the public native CLI, not a CPU learner.
use holonics::hna::native::{CurrentWire, NativeSavedSession};
use holonics::hna::{HnaStreamCommand, HnaStreamRequest, HNA_STREAM_REQUEST_SCHEMA};
use std::{
    fs,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
};

fn seed() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/native/phase-seed.json")
}
fn request(command: HnaStreamCommand) -> Vec<u8> {
    let mut bytes = serde_json::to_vec(&HnaStreamRequest {
        schema: HNA_STREAM_REQUEST_SCHEMA.into(),
        command,
    })
    .unwrap();
    bytes.push(b'\n');
    bytes
}
fn run(source: &Path, resume: bool, input: &Path, checkpoint: &Path) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_holonics"));
    cmd.args(["hna", "native-session"])
        .arg(source)
        .arg("--input")
        .arg(input)
        .arg("--checkpoint")
        .arg(checkpoint);
    if resume {
        cmd.arg("--resume");
    }
    cmd.output().unwrap()
}
fn receipt(output: &Output) -> serde_json::Value {
    serde_json::from_slice(&output.stderr).unwrap()
}
fn success(output: &Output) {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[ignore = "requires CUDA; separate processes retain partial input, complete native state and further development"]
fn split_input_process_continuation_matches_the_entire_uninterrupted_artifact() {
    let dir = tempfile::tempdir().unwrap();
    let full = include_bytes!("../examples/native/current-requests.jsonl");
    let third = full
        .iter()
        .enumerate()
        .filter(|(_, b)| **b == b'\n')
        .nth(1)
        .unwrap()
        .0
        + 1;
    let cut = third + 40;
    let input = dir.path().join("whole.jsonl");
    fs::write(&input, full).unwrap();
    let prefix = dir.path().join("prefix.jsonl");
    fs::write(&prefix, &full[..cut]).unwrap();
    let suffix = dir.path().join("suffix.jsonl");
    fs::write(&suffix, &full[cut..]).unwrap();
    let whole = dir.path().join("whole.hna");
    success(&run(&seed(), false, &input, &whole));
    let partial = dir.path().join("partial.hna");
    let stopped = run(&seed(), false, &prefix, &partial);
    assert_eq!(stopped.status.code(), Some(1));
    let r = receipt(&stopped);
    assert_eq!(r["persistent"], true);
    assert_eq!(r["anatomy"]["occurrences"], 1);
    let saved = NativeSavedSession::read(&partial).unwrap();
    assert_eq!(saved.transport().input, &full[third..cut]);
    assert_eq!(saved.source_slots(), &[Some(0)]);
    let continued = dir.path().join("continued.hna");
    success(&run(&partial, true, &suffix, &continued));
    assert_eq!(
        fs::read(&whole).unwrap(),
        fs::read(&continued).unwrap(),
        "compare complete artifact, not just a returned face"
    );
    let mut future = request(HnaStreamCommand::ReceiveCurrent {
        current: CurrentWire::integers(2, -1),
        source: Some(1),
    });
    future.extend(request(HnaStreamCommand::Close));
    let later = dir.path().join("later.jsonl");
    fs::write(&later, future).unwrap();
    let a = dir.path().join("whole-later.hna");
    let b = dir.path().join("continued-later.hna");
    success(&run(&whole, true, &later, &a));
    success(&run(&continued, true, &later, &b));
    assert_eq!(fs::read(&a).unwrap(), fs::read(&b).unwrap());
    assert_eq!(NativeSavedSession::read(&b).unwrap().occurrences(), 3);
}

#[test]
#[ignore = "requires CUDA; actual broken stdout saves produced event and remount never repeats its native effect"]
fn broken_output_process_replays_delivery_not_native_development() {
    let dir = tempfile::tempdir().unwrap();
    let stopped = dir.path().join("broken.hna");
    let first = request(HnaStreamCommand::ReceiveCurrent {
        current: CurrentWire::integers(1, 0),
        source: None,
    });
    let second = request(HnaStreamCommand::ReceiveCurrent {
        current: CurrentWire::integers(0, 1),
        source: Some(0),
    });
    let mut child = Command::new(env!("CARGO_BIN_EXE_holonics"))
        .args(["hna", "native-session"])
        .arg(seed())
        .arg("--checkpoint")
        .arg(&stopped)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    input.write_all(&first).unwrap();
    input.flush().unwrap();
    let mut line = String::new();
    output.read_line(&mut line).unwrap();
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&line).unwrap()["event"],
        "current-received"
    );
    drop(output); // The second native action executes only after this pipe has actually closed.
    input.write_all(&second).unwrap();
    input.flush().unwrap();
    drop(input);
    let result = child.wait_with_output().unwrap();
    assert_eq!(result.status.code(), Some(1));
    let r = receipt(&result);
    assert_eq!(r["persistent"], true);
    assert_eq!(r["anatomy"]["occurrences"], 2);
    let saved = NativeSavedSession::read(&stopped).unwrap();
    assert_eq!(saved.occurrences(), 2);
    let pending = saved.transport().output.as_ref().unwrap();
    let held: serde_json::Value = serde_json::from_slice(pending).unwrap();
    assert_eq!(held["sequence"], 2);
    let close = request(HnaStreamCommand::Close);
    let close_path = dir.path().join("close.jsonl");
    fs::write(&close_path, &close).unwrap();
    let resumed = dir.path().join("resumed.hna");
    let result = run(&stopped, true, &close_path, &resumed);
    success(&result);
    let events = String::from_utf8(result.stdout)
        .unwrap()
        .lines()
        .map(|s| serde_json::from_str::<serde_json::Value>(s).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(events.len(), 2);
    assert_eq!(events[0], held);
    assert_eq!(events[1]["event"], "connection-closed");
    assert_eq!(NativeSavedSession::read(&resumed).unwrap().occurrences(), 2);
    let mut full = first;
    full.extend(second);
    full.extend(close);
    let whole_input = dir.path().join("whole.jsonl");
    fs::write(&whole_input, full).unwrap();
    let whole = dir.path().join("whole.hna");
    success(&run(&seed(), false, &whole_input, &whole));
    assert_eq!(fs::read(&whole).unwrap(), fs::read(&resumed).unwrap());
}
