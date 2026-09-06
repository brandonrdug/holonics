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

fn wave_run(source: &Path, resume: bool, cycles: Option<usize>, checkpoint: &Path) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_holonics"));
    command
        .args(["hna", "wave-control"])
        .arg(source)
        .arg("--format")
        .arg("json")
        .arg("--checkpoint")
        .arg(checkpoint);
    if resume {
        command.arg("--resume");
    }
    if let Some(cycles) = cycles {
        command.arg("--cycles").arg(cycles.to_string());
    }
    command.output().unwrap()
}
fn wave_payload(output: &Output) -> serde_json::Value {
    serde_json::from_slice::<serde_json::Value>(&output.stdout).unwrap()["events"][0]["payload"]
        .clone()
}

#[test]
#[ignore = "requires CUDA; paired world/native process continuation preserves every actuation and complete artifact"]
fn wave_application_process_cut_preserves_world_native_state_and_later_actuation() {
    let dir = tempfile::tempdir().unwrap();
    let spec = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/native/wave-control.json");
    let whole_path = dir.path().join("whole-wave.hna");
    let whole = wave_run(&spec, false, None, &whole_path);
    success(&whole);
    let cut_path = dir.path().join("cut-wave.hna");
    let first = wave_run(&spec, false, Some(3), &cut_path);
    success(&first);
    let first = wave_payload(&first);
    assert_eq!(first["complete"], false);
    assert_eq!(first["persistent"], true);
    let next_path = dir.path().join("next-wave.hna");
    let next = wave_run(&cut_path, true, None, &next_path);
    success(&next);
    let whole = wave_payload(&whole);
    let next = wave_payload(&next);
    assert_eq!(next["complete"], true);
    let mut cycles = first["cycles"].as_array().unwrap().clone();
    cycles.extend(next["cycles"].as_array().unwrap().clone());
    assert_eq!(serde_json::Value::Array(cycles), whole["cycles"]);
    assert_eq!(next["final_world_state"], whole["final_world_state"]);
    assert_eq!(fs::read(whole_path).unwrap(), fs::read(next_path).unwrap());
    assert_eq!(next["anatomy"]["occurrences"], 9);
    assert_eq!(
        next["anatomy"]["census"]["deed_launches"], 6,
        "five new receptions plus one gauge, not a replay"
    );
}

#[test]
#[ignore = "requires CUDA; refused receiving rest preserves the actual exterior effect across processes"]
fn wave_process_refusal_retains_pending_receiving_without_reenacting_world() {
    let dir = tempfile::tempdir().unwrap();
    let mut spec: serde_json::Value =
        serde_json::from_slice(include_bytes!("../examples/native/wave-control.json")).unwrap();
    spec["cycles"] = 2.into();
    spec["interventions"] = serde_json::json!([]);
    spec["world"]["couplings"][0] =
        serde_json::to_value(CurrentWire::integers(i64::MAX, 0)).unwrap();
    let input = dir.path().join("aperture.json");
    fs::write(&input, serde_json::to_vec(&spec).unwrap()).unwrap();
    let first_path = dir.path().join("pending-wave.hna");
    let first = wave_run(&input, false, None, &first_path);
    assert_eq!(first.status.code(), Some(1));
    let first = wave_payload(&first);
    assert_eq!(first["persistent"], true);
    assert_eq!(first["cycles"].as_array().unwrap().len(), 1);
    let next_path = dir.path().join("still-pending.hna");
    let next = wave_run(&first_path, true, None, &next_path);
    assert_eq!(next.status.code(), Some(1));
    let next = wave_payload(&next);
    assert_eq!(next["cycles"].as_array().unwrap().len(), 0);
    assert_eq!(next["final_world_state"], first["final_world_state"]);
    assert_eq!(next["pending_receive"], first["pending_receive"]);
    assert_eq!(next["anatomy"]["occurrences"], 1);
    assert_eq!(next["anatomy"]["census"]["deed_launches"], 0);
    assert_eq!(fs::read(first_path).unwrap(), fs::read(next_path).unwrap());
}
