use super::*;
use crate::alpha::text_codec::{with_text_field, with_text_field_source, TextSymbol};
use holonic_engine::native_ecology::constitutive_fibre::NativeMaterialTransportSource;

#[test]
#[ignore = "requires CUDA; text-field checkpoint owns the exact session and supplied shared sources"]
fn saved_text_field_restores_live_source_and_application_state_without_replay() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("field.hna");
    with_text_field_source(72, NativeMaterialTransportSource::CompleteCurrent, |field| {
        let mut session = TextFieldSession::on(field)?;
        session.receive(TextSymbol::Octet(b'A'))?;
        let anchor = session.retain_part_source()?;
        session.receive(TextSymbol::EndPart)?;
        session.checkpoint(&path, &[&anchor], b"application-state")?;
        assert!(session
            .checkpoint(&path, &[], b"must not overwrite")
            .is_err());
        Ok(())
    })
    .unwrap();
    let saved = SavedTextField::read(&path).unwrap();
    assert_eq!(saved.occurrences(), 2);
    saved
        .with_session_archived(
            dir.path().join("historical-sections"),
            |session, _stream, anchors, application| {
                assert_eq!(application, b"application-state");
                assert_eq!(anchors.len(), 1);
                assert_eq!(session.field().occurrence_count(), 2);
                let before = session.field().census();
                session.begin_part(Some(&anchors[0]))?;
                session.receive(TextSymbol::Octet(b'B'))?;
                assert_eq!(session.field().occurrence_count(), 3);
                assert_eq!(
                    session.field().census().deed_launches - before.deed_launches,
                    1
                );
                assert_eq!(session.field().lineage(2).unwrap().received_from, Some(0));
                assert_eq!(session.field().history_placement().restored_sources, 1);
                Ok(())
            },
        )
        .unwrap();
    let mut bytes = std::fs::read(&path).unwrap();
    let at = bytes.len() / 2;
    bytes[at] ^= 1;
    let corrupt = dir.path().join("corrupt.hna");
    std::fs::write(&corrupt, bytes).unwrap();
    assert!(SavedTextField::read(corrupt).is_err());
}

#[test]
#[ignore = "requires CUDA; pending native symbol and interrupted delivery survive together"]
fn checkpoint_retains_staged_input_and_a_partly_written_output() {
    struct Blocked {
        bytes: Vec<u8>,
    }
    impl Write for Blocked {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if self.bytes.len() == 3 {
                return Err(io::ErrorKind::BrokenPipe.into());
            }
            let count = (3 - self.bytes.len()).min(bytes.len());
            self.bytes.extend_from_slice(&bytes[..count]);
            Ok(count)
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pending.hna");
    let output = b"already-produced-frame\n".to_vec();
    with_text_field(72, |field| {
        let mut session = TextFieldSession::on(field)?;
        session.receive(TextSymbol::Octet(b'A'))?;
        session.stage(TextSymbol::Octet(b'B'))?;
        let mut stream = HnaStream::from_state(HnaStreamState {
            sequence: 1,
            output: Some(output.clone()),
            ..Default::default()
        })
        .unwrap();
        let mut blocked = Blocked { bytes: Vec::new() };
        assert!(stream.drain_pending(&mut blocked).is_err());
        assert_eq!(stream.state().output_accepted, 3);
        session.checkpoint_stream(&path, stream.state(), &[], b"pending-symbol")?;
        Ok(())
    })
    .unwrap();
    SavedTextField::read(&path)
        .unwrap()
        .with_session(|session, stream, _, application| {
            assert_eq!(application, b"pending-symbol");
            assert_eq!(session.pending_symbol(), Some(TextSymbol::Octet(b'B')));
            assert_eq!(session.field().occurrence_count(), 1);
            stream.open_new_connection();
            let mut delivered = Vec::new();
            stream.drain_pending(&mut delivered).unwrap();
            assert_eq!(delivered, output);
            assert_eq!(session.field().census().deed_launches, 0);
            session.retry_pending()?;
            assert_eq!(session.field().occurrence_count(), 2);
            assert_eq!(session.pending_symbol(), None);
            assert_eq!(session.field().lineage(1).unwrap().received_from, Some(0));
            Ok(())
        })
        .unwrap();
}
