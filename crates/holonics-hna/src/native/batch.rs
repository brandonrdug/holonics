//! Packet delivery into one continuing native session. This API admits exterior ingress only;
//! packet boundaries do not create returned-source contact or parallel semantic independence.
use super::*;
use holonic_engine::resident_section::ObstructionLineage;

pub struct NativeBatchReceive {
    pub committed: Vec<NativeSessionStep>,
    pub refused_at: Option<usize>,
    pub obstruction: ObstructionLineage,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spec() -> NativeModelSpec {
        NativeModelSpec {
            schema: NATIVE_MODEL_SPEC_SCHEMA.into(),
            nodes: vec![
                JunctionSpec {
                    incoming_admittance: 1,
                    held_admittance: 1,
                    incoming_transport: CurrentWire::integers(1, 0),
                    initial_held: CurrentWire::integers(0, 0),
                },
                JunctionSpec {
                    incoming_admittance: 1,
                    held_admittance: 1,
                    incoming_transport: CurrentWire::integers(0, 1),
                    initial_held: CurrentWire::integers(0, 0),
                },
            ],
        }
    }
    fn form(session: &mut NativeSession<'_>) -> Result<(), NativeSessionError> {
        let a = session.receive(&CurrentWire::integers(1, 0), None)?;
        let b = session.receive(&CurrentWire::integers(0, 1), Some(a.source))?;
        session.receive(&CurrentWire::integers(2, 3), Some(b.source))?;
        session.rechart(&[CurrentWire::integers(0, 1), CurrentWire::integers(-1, 0)])?;
        Ok(())
    }

    #[test]
    #[ignore = "requires resident GPU execution"]
    fn batch_and_scalar_preserve_complete_returns_old_sources_and_rest() {
        let inputs: Vec<_> = (0..19)
            .map(|i| CurrentWire::integers(i - 8, 3 - i))
            .collect();
        let directory = tempfile::tempdir().unwrap();
        let scalar_path = directory.path().join("scalar.hna");
        let batch_path = directory.path().join("batch.hna");
        let scalar = with_native_session(&spec(), |session| {
            form(session)?;
            let steps = inputs
                .iter()
                .map(|c| session.receive(c, None))
                .collect::<Result<Vec<_>, _>>()?;
            // Return a source which predates rechart and the whole packet.
            let old = session.receive(&CurrentWire::integers(7, -2), Some(2))?;
            session.checkpoint(&scalar_path)?;
            Ok((steps, old))
        })
        .unwrap();
        let batched = with_native_session(&spec(), |session| {
            form(session)?;
            let before = session.inspect().census;
            let batch = session.receive_unlinked_batch(&inputs)?;
            assert_eq!(batch.refused_at, None);
            assert!(batch.obstruction.is_empty());
            assert_eq!(
                session.inspect().census.synchronizations - before.synchronizations,
                1
            );
            let old = session.receive(&CurrentWire::integers(7, -2), Some(2))?;
            session.checkpoint(&batch_path)?;
            Ok((batch.committed, old))
        })
        .unwrap();
        assert_eq!(
            serde_json::to_vec(&scalar).unwrap(),
            serde_json::to_vec(&batched).unwrap()
        );
        assert_eq!(
            std::fs::read(&scalar_path).unwrap(),
            std::fs::read(&batch_path).unwrap()
        );
        let next = NativeSavedSession::read(&batch_path)
            .unwrap()
            .with_session(|session, _| {
                session.receive_unlinked_batch(&[CurrentWire::integers(4, -3)])
            })
            .unwrap();
        assert_eq!(next.committed[0].native_occurrence, 23);
    }

    #[test]
    #[ignore = "requires resident GPU execution"]
    fn arithmetic_refusal_preserves_exact_prefix_and_blocks_suffix() {
        let mut model = spec();
        model.nodes[0].incoming_admittance = 2;
        let inputs = [
            CurrentWire::integers(0, 0),
            CurrentWire::integers(i64::MAX, 0),
            CurrentWire::integers(1, 0),
        ];
        let directory = tempfile::tempdir().unwrap();
        let expected = directory.path().join("expected.hna");
        let actual = directory.path().join("actual.hna");
        let scalar = with_native_session(&model, |session| {
            let first = session.receive(&inputs[0], None)?;
            assert!(session.receive(&inputs[1], None).is_err());
            session.checkpoint(&expected)?;
            Ok(first)
        })
        .unwrap();
        with_native_session(&model, |session| {
            let returned = session.receive_unlinked_batch(&inputs)?;
            assert_eq!(returned.refused_at, Some(1));
            assert_eq!(returned.committed.len(), 1);
            assert_eq!(returned.obstruction.refusals.len(), 2);
            assert!(returned.obstruction.refusals[0].origin);
            assert!(!returned.obstruction.refusals[1].origin);
            assert_eq!(
                serde_json::to_vec(&scalar)?,
                serde_json::to_vec(&returned.committed[0])?
            );
            session.checkpoint(&actual)?;
            assert_eq!(session.occurrence_count(), 1);
            let retry = session.receive_unlinked_batch(&inputs[1..])?;
            assert_eq!(retry.refused_at, Some(0));
            assert!(retry.committed.is_empty());
            Ok(())
        })
        .unwrap();
        assert_eq!(
            std::fs::read(expected).unwrap(),
            std::fs::read(actual).unwrap()
        );
    }
}

impl NativeSession<'_> {
    /// Validate the complete input chart before dispatch. Device arithmetic refusal returns the
    /// committed prefix and unexecuted suffix boundary. Driver uncertainty returns an error and
    /// prevents retry/checkpoint against the potentially changed owner.
    pub fn receive_unlinked_batch(
        &mut self,
        currents: &[CurrentWire],
    ) -> Result<NativeBatchReceive, NativeSessionError> {
        let native = currents
            .iter()
            .map(CurrentWire::native)
            .collect::<Result<Vec<_>, _>>()?;
        let end = self
            .sources
            .len()
            .checked_add(native.len())
            .and_then(|n| u64::try_from(n).ok())
            .ok_or_else(|| {
                NativeSessionError::Application("session source coordinates exhausted".into())
            })?;
        let _ = end;
        self.sources
            .try_reserve(native.len())
            .map_err(|e| NativeSessionError::Application(e.to_string()))?;
        let mut committed = Vec::new();
        committed
            .try_reserve(native.len())
            .map_err(|e| NativeSessionError::Application(e.to_string()))?;
        let returned = self.body.advance_unlinked_batch(&native)?;
        for step in returned.steps {
            let next = self.sources.len() as u64;
            committed.push(self.commit_return(step, None, next));
        }
        Ok(NativeBatchReceive {
            committed,
            refused_at: returned.refused_at,
            obstruction: returned.obstruction,
        })
    }
}
