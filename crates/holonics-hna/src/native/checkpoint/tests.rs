use super::*;
use crate::{HnaStreamCommand, HnaStreamRequest, HNA_STREAM_REQUEST_SCHEMA};
use std::io::Cursor;
const SEED: &[u8] = include_bytes!(
    "../../../../../applications/holonics-workbench/examples/native/phase-seed.json"
);
fn input(command: HnaStreamCommand) -> Vec<u8> {
    let mut bytes = serde_json::to_vec(&HnaStreamRequest {
        schema: HNA_STREAM_REQUEST_SCHEMA.into(),
        command,
    })
    .unwrap();
    bytes.push(b'\n');
    bytes
}
struct BlockedWriter {
    bytes: Vec<u8>,
}
impl Write for BlockedWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if self.bytes.len() >= 3 {
            return Err(io::ErrorKind::BrokenPipe.into());
        }
        let n = (3 - self.bytes.len()).min(bytes.len());
        self.bytes.extend_from_slice(&bytes[..n]);
        Ok(n)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
#[ignore = "requires CUDA; exact native artifact, pending output and future old-source reception"]
fn native_artifact_restores_pending_output_without_repeating_development() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("saved.hna");
    let seed = NativeModelSpec::read(SEED).unwrap();
    let (held, expected) = with_native_session(&seed, |session| {
        let first = session.receive(&CurrentWire::integers(1, 0), None)?;
        session.rechart(&[CurrentWire::integers(0, 1), CurrentWire::integers(1, 0)])?;
        let mut stream = HnaStream::new();
        let mut blocked = BlockedWriter { bytes: Vec::new() };
        assert!(stream
            .pump_native(
                session,
                &mut Cursor::new(input(HnaStreamCommand::ReceiveCurrent {
                    current: CurrentWire::integers(0, 1),
                    source: Some(first.source)
                })),
                &mut blocked
            )
            .is_err());
        assert_eq!(session.inspect().occurrences, 2);
        let expected = session.body.rest(
            &session
                .sources
                .iter()
                .map(Option::as_ref)
                .collect::<Vec<_>>(),
        )?;
        let held = stream.state().clone();
        session.checkpoint_stream(&path, stream.state())?;
        assert!(session.checkpoint(&path).is_err());
        Ok((held, expected))
    })
    .unwrap();
    let saved = NativeSavedSession::read(&path).unwrap();
    assert_eq!(saved.ecology, expected);
    assert_eq!(*saved.transport(), held);
    assert_eq!(saved.application_state(), None);
    assert_eq!(saved.nodes(), 2);
    saved
        .with_session(|session, stream| {
            let before = session.inspect();
            let mut output = Vec::new();
            stream.open_new_connection();
            stream
                .pump_native(session, &mut Cursor::new(Vec::<u8>::new()), &mut output)
                .unwrap();
            assert_eq!(output, held.output.unwrap());
            assert_eq!(session.inspect().occurrences, before.occurrences);
            assert_eq!(session.inspect().census.deed_launches, 0);
            let old = session.receive(&CurrentWire::integers(1, 0), Some(1))?;
            assert_eq!(old.native_received_from, Some(1));
            assert_eq!(old.frame.ordinal, 1);
            assert_eq!(session.inspect().occurrences, 3);
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; opaque application continuation is exercised at the native mount boundary"]
fn application_artifact_is_v2_and_plain_session_refuses_to_discard_it() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("application.hna");
    let seed = NativeModelSpec::read(SEED).unwrap();
    let application = b"opaque-wave-state-v1".to_vec();
    with_native_session(&seed, |session| {
        session.checkpoint_application(&path, &HnaStreamState::default(), &application)?;
        Ok(())
    })
    .unwrap();

    let saved = NativeSavedSession::read(&path).unwrap();
    assert_eq!(saved.application_state(), Some(application.as_slice()));
    assert_eq!(saved.nodes(), 2);
    let plain = saved.with_session(|_, _| Ok(())).unwrap_err();
    assert!(plain.to_string().contains("application state"));

    let saved = NativeSavedSession::read(&path).unwrap();
    saved
        .with_application_session(|_, _, received| {
            assert_eq!(received, application);
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; partial native input is retained and effects occur once after completion"]
fn native_artifact_retains_partial_input_and_refuses_corrupt_files() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("partial.hna");
    let seed = NativeModelSpec::read(SEED).unwrap();
    let request = input(HnaStreamCommand::ReceiveCurrent {
        current: CurrentWire::integers(1, 0),
        source: None,
    });
    let cut = request.len() / 2;
    with_native_session(&seed, |session| {
        let mut stream = HnaStream::new();
        assert!(matches!(
            stream.pump_native(session, &mut Cursor::new(&request[..cut]), &mut Vec::new()),
            Err(crate::HnaStreamError::IncompleteInput)
        ));
        session.checkpoint_stream(&path, stream.state())?;
        Ok(())
    })
    .unwrap();
    assert!(crate::checkpoint::read_session_checkpoint(&path).is_err());
    NativeSavedSession::read(&path)
        .unwrap()
        .with_session(|session, stream| {
            assert_eq!(session.inspect().occurrences, 0);
            stream
                .pump_native(session, &mut Cursor::new(&request[cut..]), &mut Vec::new())
                .unwrap();
            assert_eq!(session.inspect().occurrences, 1);
            assert_eq!(stream.state().sequence, 1);
            Ok(())
        })
        .unwrap();
    let bytes = std::fs::read(&path).unwrap();
    let malformed = dir.path().join("malformed.hna");
    for cut in [0, 1, bytes.len() / 2, bytes.len() - 1] {
        std::fs::write(&malformed, &bytes[..cut]).unwrap();
        assert!(NativeSavedSession::read(&malformed).is_err());
    }
    let mut changed = bytes;
    changed[MAGIC.len() + 10] ^= 1;
    std::fs::write(&malformed, changed).unwrap();
    match NativeSavedSession::read(&malformed) {
        Err(error) => assert!(error.to_string().contains("checksum")),
        Ok(_) => panic!("corrupted native state was accepted"),
    }
}
