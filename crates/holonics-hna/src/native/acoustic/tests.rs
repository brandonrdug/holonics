use super::*;
use crate::native::{
    with_native_session, CurrentWire, JunctionSpec, NativeModelSpec, NATIVE_MODEL_SPEC_SCHEMA,
};
use life::mathematical_source::ExactAcousticOccurrence;
use std::path::Path;

fn spec() -> NativeModelSpec {
    NativeModelSpec {
        schema: NATIVE_MODEL_SPEC_SCHEMA.to_owned(),
        nodes: vec![JunctionSpec {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: CurrentWire::integers(1, 0),
            initial_held: CurrentWire::integers(1, 0),
        }],
    }
}

fn occurrence(bytes: &[u8]) -> ExactAcousticOccurrence {
    ExactAcousticOccurrence::from_wav_bytes(
        bytes,
        "test-acoustic-occurrence",
        "memory://test-acoustic-occurrence",
        2,
        2,
        4,
    )
    .unwrap()
}

fn wav_bytes() -> Vec<u8> {
    let samples = [1_i16, -2, 3, 4];
    let data_len = (samples.len() * 2) as u32;
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"RIFF");
    bytes.extend_from_slice(&(36 + data_len).to_le_bytes());
    bytes.extend_from_slice(b"WAVEfmt ");
    bytes.extend_from_slice(&16_u32.to_le_bytes());
    bytes.extend_from_slice(&1_u16.to_le_bytes());
    bytes.extend_from_slice(&1_u16.to_le_bytes());
    bytes.extend_from_slice(&16_000_u32.to_le_bytes());
    bytes.extend_from_slice(&32_000_u32.to_le_bytes());
    bytes.extend_from_slice(&2_u16.to_le_bytes());
    bytes.extend_from_slice(&16_u16.to_le_bytes());
    bytes.extend_from_slice(b"data");
    bytes.extend_from_slice(&data_len.to_le_bytes());
    for sample in samples {
        bytes.extend_from_slice(&sample.to_le_bytes());
    }
    bytes
}

fn run_options(samples: Option<usize>, checkpoint: Option<&Path>) -> AcousticRunOptions {
    AcousticRunOptions {
        samples,
        checkpoint: checkpoint.map(Path::to_path_buf),
    }
}

#[test]
#[ignore = "requires resident GPU execution"]
fn packet_split_checkpoint_resume_matches_one_packet() {
    let bytes = wav_bytes();
    let source = occurrence(&bytes);
    let full = run_acoustic_with_options(
        &spec(),
        &source,
        &bytes,
        32_768,
        Some(vec![CurrentWire::integers(1, 0)]),
        &run_options(None, None),
    )
    .unwrap();

    let directory = tempfile::tempdir().unwrap();
    let checkpoint = directory.path().join("acoustic.checkpoint");
    let first = run_acoustic_with_options(
        &spec(),
        &source,
        &bytes,
        32_768,
        Some(vec![CurrentWire::integers(1, 0)]),
        &run_options(Some(1), Some(&checkpoint)),
    )
    .unwrap();
    assert_eq!(first.cursor, 1);
    let resumed = resume_acoustic(&checkpoint, &run_options(None, None)).unwrap();
    assert_eq!(resumed.cursor, full.cursor);
    assert_eq!(
        serde_json::to_vec(&resumed.steps).unwrap(),
        serde_json::to_vec(&full.steps).unwrap()
    );
}

#[test]
#[ignore = "requires resident GPU execution"]
fn invalid_gain_population_and_pcm_divisor_refuse_before_native_advance() {
    let bytes = wav_bytes();
    let source = occurrence(&bytes);
    with_native_session(&spec(), |session| {
        let bad_gain =
            AcousticApplication::found(&spec(), &source, &bytes, 32_768, Some(Vec::new()), session)
                .unwrap_err();
        assert!(bad_gain.to_string().contains("gain population"));
        assert_eq!(session.occurrence_count(), 0);

        let bad_divisor =
            AcousticApplication::found(&spec(), &source, &bytes, 0, None, session).unwrap_err();
        assert!(bad_divisor.to_string().contains("divisor"));
        assert_eq!(session.occurrence_count(), 0);
        Ok(())
    })
    .unwrap();
}

#[test]
#[ignore = "requires resident GPU; process cut at zero performs no occurrence"]
fn zero_sample_cut_and_complete_checkpoint_match_uninterrupted_execution() {
    let bytes = wav_bytes();
    let source = occurrence(&bytes);
    let directory = tempfile::tempdir().unwrap();
    let initial = directory.path().join("initial.hna");
    let full_path = directory.path().join("full.hna");
    let resumed_path = directory.path().join("resumed.hna");
    let gains = Some(vec![CurrentWire::integers(1, 0)]);
    let zero = run_acoustic_with_options(
        &spec(),
        &source,
        &bytes,
        32768,
        gains.clone(),
        &run_options(Some(0), Some(&initial)),
    )
    .unwrap();
    assert_eq!(zero.cursor, 0);
    assert!(zero.steps.is_empty());
    assert!(zero.checkpoint_error.is_none());
    let full = run_acoustic_with_options(
        &spec(),
        &source,
        &bytes,
        32768,
        gains,
        &run_options(None, Some(&full_path)),
    )
    .unwrap();
    let continued = resume_acoustic(&initial, &run_options(None, Some(&resumed_path))).unwrap();
    assert!(full.complete && continued.complete);
    assert_eq!(
        std::fs::read(full_path).unwrap(),
        std::fs::read(resumed_path).unwrap()
    );
}

#[test]
#[ignore = "requires resident GPU; a first-sample refusal keeps source and pending current"]
fn first_sample_refusal_remounts_without_losing_or_replaying_input() {
    let bytes = wav_bytes();
    let source = occurrence(&bytes);
    let mut model = spec();
    model.nodes[0].incoming_admittance = 2;
    model.nodes[0].initial_held = CurrentWire::integers(i64::MAX, 0);
    let directory = tempfile::tempdir().unwrap();
    let first = directory.path().join("refused.hna");
    let second = directory.path().join("still-refused.hna");
    let refused = run_acoustic_with_options(
        &model,
        &source,
        &bytes,
        32768,
        None,
        &run_options(None, Some(&first)),
    )
    .unwrap();
    assert_eq!(refused.cursor, 0);
    assert!(refused.interruption.is_some());
    assert!(refused.checkpoint_error.is_none());
    let saved = AcousticSavedApplication::read(&first).unwrap();
    assert_eq!(saved.application().occurrence(), &source);
    let retried = resume_acoustic(&first, &run_options(None, Some(&second))).unwrap();
    assert_eq!(retried.cursor, 0);
    assert!(retried.interruption.is_some());
    assert!(retried.checkpoint_error.is_none());
    assert_eq!(
        serde_json::to_vec(&refused.pending).unwrap(),
        serde_json::to_vec(&retried.pending).unwrap()
    );
    assert_eq!(
        std::fs::read(first).unwrap(),
        std::fs::read(second).unwrap()
    );
}
