use super::*;
use crate::native::{CurrentWire, JunctionSpec, NATIVE_MODEL_SPEC_SCHEMA, NativeModelSpec};
use life::mathematical_source::ExactAcousticOccurrence;

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

fn wav() -> Vec<u8> {
    let samples = [1_i16, -2];
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

#[test]
#[ignore = "requires resident GPU execution"]
fn curated_audio_then_transcript_uses_one_continuing_source_chain() {
    let bytes = wav();
    let occurrence = ExactAcousticOccurrence::from_wav_bytes(
        &bytes,
        "speech-audio",
        "memory://speech-audio",
        2,
        2,
        2,
    )
    .unwrap();
    let full_directory = tempfile::tempdir().unwrap();
    let full_checkpoint = full_directory.path().join("whole.hna");
    let run = run_speech_with_options(
        &spec(),
        &occurrence,
        &bytes,
        32_768,
        Some(vec![CurrentWire::integers(1, 0)]),
        b"ok",
        256,
        &SpeechRunOptions {
            occurrences: None,
            checkpoint: Some(full_checkpoint.clone()),
        },
    )
    .unwrap();
    assert!(run.complete);
    assert_eq!(run.acoustic_cursor, 2);
    assert_eq!(run.transcript_cursor, 2);
    assert_eq!(
        run.transcript_steps[0].received_from,
        Some(run.acoustic_steps.last().unwrap().source)
    );
    assert_eq!(
        run.transcript_steps[1].received_from,
        Some(run.transcript_steps[0].source)
    );

    for cut in [0, 2, 3, 4] {
        let directory = tempfile::tempdir().unwrap();
        let checkpoint = directory.path().join("speech.checkpoint");
        let partial = run_speech_with_options(
            &spec(),
            &occurrence,
            &bytes,
            32_768,
            Some(vec![CurrentWire::integers(1, 0)]),
            b"ok",
            256,
            &SpeechRunOptions {
                occurrences: Some(cut),
                checkpoint: Some(checkpoint.clone()),
            },
        )
        .unwrap();
        if cut == 2 {
            assert_eq!(partial.acoustic_cursor, 2);
            assert_eq!(partial.transcript_cursor, 0);
        }
        if cut == 3 {
            assert_eq!(partial.transcript_cursor, 1);
        }
        let final_checkpoint = directory.path().join("continued.hna");
        let resumed = resume_speech(
            &checkpoint,
            &SpeechRunOptions {
                occurrences: None,
                checkpoint: Some(final_checkpoint.clone()),
            },
        )
        .unwrap();
        assert_eq!(
            std::fs::read(&full_checkpoint).unwrap(),
            std::fs::read(final_checkpoint).unwrap()
        );
        assert!(resumed.complete);
        assert_eq!(
            serde_json::to_vec(&resumed.transcript_steps).unwrap(),
            serde_json::to_vec(&run.transcript_steps).unwrap()
        );
    }

    let unlinked = run_speech_with_options(
        &spec(),
        &occurrence,
        &bytes,
        32_768,
        None,
        b"ok",
        256,
        &SpeechRunOptions::default(),
    )
    .unwrap();
    assert!(
        unlinked
            .acoustic_steps
            .iter()
            .chain(&unlinked.transcript_steps)
            .all(|step| step.received_from.is_none())
    );
    assert_ne!(
        serde_json::to_vec(&unlinked.transcript_steps).unwrap(),
        serde_json::to_vec(&run.transcript_steps).unwrap()
    );
}

#[test]
#[ignore = "requires resident GPU execution"]
fn empty_transcript_is_refused_before_native_mount_advances() {
    let bytes = wav();
    let occurrence = ExactAcousticOccurrence::from_wav_bytes(
        &bytes,
        "speech-audio",
        "memory://speech-audio",
        2,
        2,
        2,
    )
    .unwrap();
    let result = run_speech_with_options(
        &spec(),
        &occurrence,
        &bytes,
        32_768,
        None,
        &[],
        256,
        &SpeechRunOptions::default(),
    );
    assert!(result.is_err());
}

#[test]
#[ignore = "requires resident GPU; invalid pending application data must not reach the native deed"]
fn pending_text_requires_completed_sound_and_the_exact_declared_return() {
    let bytes = wav();
    let occurrence = ExactAcousticOccurrence::from_wav_bytes(
        &bytes,
        "pending-speech",
        "memory://pending-speech",
        1,
        1,
        1,
    )
    .unwrap();
    with_native_session(&spec(), |session| {
        let mut app = SpeechExposureApplication::found(
            &spec(),
            &occurrence,
            &bytes,
            32768,
            Some(vec![CurrentWire::integers(1, 0)]),
            b"ok",
            256,
            session,
        )?;
        app.pending = Some(SpeechPendingReceive {
            transcript_byte: 0,
            current: CurrentWire::integers(0, 0),
            source: None,
            detail: None,
        });
        assert!(app.advance_one(session).is_err());
        assert_eq!(session.occurrence_count(), 0);
        app.pending = None;
        app.advance_one(session)?;
        app.advance_one(session)?;
        let (current, source) = app.transcript_current_for(0)?;
        app.pending = Some(SpeechPendingReceive {
            transcript_byte: 0,
            current: CurrentWire::integers(999, 0),
            source,
            detail: None,
        });
        assert!(app.advance_one(session).is_err());
        assert_eq!(session.occurrence_count(), 2);
        app.pending.as_mut().unwrap().current = current.clone();
        app.pending.as_mut().unwrap().source = None;
        assert!(app.advance_one(session).is_err());
        assert_eq!(session.occurrence_count(), 2);
        app.pending.as_mut().unwrap().source = source;
        app.advance_one(session)?;
        assert_eq!(session.occurrence_count(), 3);
        assert!(app.pending().is_none());
        Ok(())
    })
    .unwrap();
}
