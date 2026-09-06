use super::*;
use crate::{HnaStream, HnaStreamCommand, HnaStreamRequest, HNA_STREAM_REQUEST_SCHEMA};
use std::io::{self, Cursor, Write};

const SEED: &[u8] =
    include_bytes!("../../../../applications/holonics-workbench/examples/native/phase-seed.json");
const WAVE: &[u8] =
    include_bytes!("../../../../applications/holonics-workbench/examples/native/wave-control.json");

#[test]
fn exact_wire_has_no_json_number_or_float_loss() {
    let rational = RationalWire {
        numerator: "9007199254740993".into(),
        denominator: "7".into(),
    };
    let bytes = serde_json::to_vec(&rational).unwrap();
    assert!(std::str::from_utf8(&bytes)
        .unwrap()
        .contains("\"9007199254740993\""));
    let decoded: RationalWire = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(decoded.rational().unwrap(), rational.rational().unwrap());
    let current = CurrentWire {
        real: RationalWire {
            numerator: "1".into(),
            denominator: "3".into(),
        },
        imaginary: RationalWire {
            numerator: "1".into(),
            denominator: "2".into(),
        },
    };
    assert_eq!(
        current.native().unwrap().current(),
        current.current().unwrap()
    );
    assert!(RationalWire {
        numerator: "1".into(),
        denominator: "0".into()
    }
    .rational()
    .is_err());
    assert!(RationalWire {
        numerator: "1".into(),
        denominator: "-2".into()
    }
    .rational()
    .is_err());
    assert!(RationalWire {
        numerator: "0.5".into(),
        denominator: "1".into()
    }
    .rational()
    .is_err());
}

#[test]
fn seed_and_world_contract_refuse_malformed_material_before_mount() {
    let seed = NativeModelSpec::read(SEED).unwrap();
    assert_eq!(seed.nodes.len(), 2);
    let mut invalid = seed.clone();
    invalid.nodes[0].incoming_admittance = 0;
    assert!(with_native_session::<()>(&invalid, |_| panic!("invalid seed mounted")).is_err());
    let mut world: WaveControlSpec = serde_json::from_slice(WAVE).unwrap();
    world.validate().unwrap();
    world.world.state_rotation = CurrentWire::integers(1, 1);
    assert!(run_wave_control(&world).is_err());
}

#[test]
#[ignore = "requires CUDA; public native session preserves handles and refusal state"]
fn public_session_owns_handles_across_rechart_and_refusal() {
    with_native_session(&NativeModelSpec::read(SEED).unwrap(), |session| {
        let first = session.receive(&CurrentWire::integers(1, 0), None)?;
        let before = session.inspect();
        let relation = session.relation_snapshot()?;
        assert!(session
            .receive(&CurrentWire::integers(1, 0), Some(999))
            .is_err());
        assert_eq!(session.inspect().occurrences, before.occurrences);
        assert!(session
            .receive(
                &CurrentWire::integers(i64::MAX, i64::MAX),
                Some(first.source)
            )
            .is_err());
        assert_eq!(session.inspect().available_sources, vec![first.source]);
        assert_eq!(
            session.relation_snapshot()?.paired_basis,
            relation.paired_basis
        );
        assert_eq!(session.inspect().occurrences, 1);
        session.rechart(&[CurrentWire::integers(0, 1), CurrentWire::integers(1, 0)])?;
        let received = session.receive(&CurrentWire::integers(1, 0), Some(first.source))?;
        assert_eq!(received.received_from, Some(0));
        assert_eq!(received.frame.ordinal, 1);
        assert_eq!(received.successor_rank, 1);
        assert!(session
            .receive(&CurrentWire::integers(1, 0), Some(first.source))
            .is_err());
        assert_eq!(session.inspect().occurrences, 2);
        Ok(())
    })
    .unwrap();
}

#[test]
#[ignore = "requires CUDA; application source coordinates are independent of native occurrence ordinals"]
fn delivered_source_coordinate_is_not_inferred_from_the_native_counter() {
    with_native_session(&NativeModelSpec::read(SEED).unwrap(), |session| {
        // An actual internal occurrence was not issued as a handle on this exterior session.
        session
            .body
            .advance(&mut NativeCurrentOccurrence::entering(
                NativePhaseCurrent::unit(),
            ))?;
        let first = session.receive(&CurrentWire::integers(1, 0), None)?;
        assert_eq!(first.source, 0);
        assert_eq!(first.native_occurrence, 1);
        let second = session.receive(&CurrentWire::integers(1, 0), Some(first.source))?;
        assert_eq!(second.source, 1);
        assert_eq!(second.native_occurrence, 2);
        assert_eq!(second.received_from, Some(0));
        assert_eq!(second.native_received_from, Some(1));
        let difference = second.received_difference.unwrap();
        assert_eq!(difference.source, Some(0));
        assert_eq!(difference.native_source_occurrence, 1);
        Ok(())
    })
    .unwrap();
}

struct BlockedWriter {
    bytes: Vec<u8>,
    blocked: bool,
}
impl Write for BlockedWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if self.blocked && self.bytes.len() >= 3 {
            return Err(io::ErrorKind::WouldBlock.into());
        }
        let n = if self.blocked {
            (3 - self.bytes.len()).min(bytes.len())
        } else {
            bytes.len()
        };
        self.bytes.extend_from_slice(&bytes[..n]);
        Ok(n)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
#[ignore = "requires CUDA; existing stream delivery does not repeat native effects"]
fn native_stream_backpressure_retains_the_actual_output() {
    with_native_session(&NativeModelSpec::read(SEED).unwrap(), |session| {
        let commands = [
            HnaStreamCommand::ReceiveCurrent {
                current: CurrentWire::integers(1, 0),
                source: None,
            },
            HnaStreamCommand::Rechart {
                gauges: vec![CurrentWire::integers(0, 1), CurrentWire::integers(1, 0)],
            },
            HnaStreamCommand::ReceiveCurrent {
                current: CurrentWire::integers(1, 0),
                source: Some(0),
            },
            HnaStreamCommand::InspectRelation,
            HnaStreamCommand::Close,
        ];
        let mut input = Vec::new();
        for command in commands {
            input.extend(serde_json::to_vec(&HnaStreamRequest {
                schema: HNA_STREAM_REQUEST_SCHEMA.into(),
                command,
            })?);
            input.push(b'\n');
        }
        let mut input = Cursor::new(input);
        let mut output = BlockedWriter {
            bytes: Vec::new(),
            blocked: true,
        };
        let mut stream = HnaStream::new();
        assert!(matches!(
            stream.pump_native(session, &mut input, &mut output),
            Err(crate::HnaStreamError::Output(_))
        ));
        assert_eq!(session.inspect().occurrences, 1);
        assert_eq!(stream.state().sequence, 1);
        assert!(stream.state().output.is_some());
        output.blocked = false;
        stream
            .pump_native(session, &mut input, &mut output)
            .map_err(|e| NativeSessionError::Application(e.to_string()))?;
        assert_eq!(session.inspect().occurrences, 2);
        assert_eq!(session.inspect().frame, 1);
        assert_eq!(stream.state().sequence, 5);
        let events = std::str::from_utf8(&output.bytes)
            .unwrap()
            .lines()
            .map(|s| serde_json::from_str::<serde_json::Value>(s).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(events.len(), 5);
        assert_eq!(events[0]["event"], "current-received");
        assert_eq!(events[2]["value"]["received_from"], 0);
        assert_eq!(events[3]["event"], "relation");
        Ok(())
    })
    .unwrap();
}

#[test]
#[ignore = "requires CUDA; real application actuation and independent world-state consequences"]
fn application_uses_native_conduct_in_new_conditions_and_retains_open_cases() {
    let spec: WaveControlSpec = serde_json::from_slice(WAVE).unwrap();
    let result = run_wave_control(&spec).unwrap();
    assert!(result.interruption.is_none(), "{:?}", result.interruption);
    assert_eq!(result.cycles.len(), spec.cycles);
    assert!(matches!(
        result.cycles[0].native.receiver,
        ReceiverWire::OutsideDomain { .. }
    ));
    assert!(result.cycles[0].actuation.is_none());
    let rotation = spec.world.state_rotation.current().unwrap();
    let mut state = spec.world.initial_state.current().unwrap();
    let mut control = state.clone();
    let mut commanded = 0;
    let mut new_condition = 0;
    let mut sources = Vec::new();
    for cycle in &result.cycles {
        let measured = cycle.measured_current.current().unwrap();
        let residual = cycle.residual.current().unwrap();
        if let Some(action) = &cycle.actuation {
            assert_eq!(action.current().unwrap(), measured);
            assert!(residual.is_zero());
            commanded += 1;
            assert!(!sources.contains(&cycle.native.root_source_currents));
            if cycle.cycle > 5 {
                new_condition += 1;
            }
        } else {
            assert_eq!(residual, measured);
        }
        state = rotation.multiply(&state).add(&residual);
        control = rotation.multiply(&control).add(&measured);
        assert_eq!(cycle.world_state.current().unwrap(), state);
        assert_eq!(cycle.unactuated_state.current().unwrap(), control);
        sources.push(cycle.native.root_source_currents.clone());
    }
    assert!(commanded >= 2);
    assert!(new_condition >= 2);
    assert_ne!(
        state, control,
        "actual native actuation must change the independently evolving exterior"
    );
    assert_eq!(result.anatomy.occurrences, spec.cycles + 1);
    assert_eq!(result.anatomy.frame, 1);
    assert_eq!(result.final_native.successor_rank, 4);
    assert!(!result.persistent);
}

#[test]
#[ignore = "requires CUDA; unsupported commands neither change native state nor publish a false artifact"]
fn native_stream_refuses_inherited_commands_and_unimplemented_checkpoint() {
    let directory = tempfile::tempdir().unwrap();
    let checkpoint = directory.path().join("must-not-exist.hna");
    with_native_session(&NativeModelSpec::read(SEED).unwrap(), |session| {
        let commands = [
            HnaStreamCommand::ReceiveCurrent {
                current: CurrentWire::integers(1, 0),
                source: None,
            },
            HnaStreamCommand::Advance {
                occurrence: crate::HnaOccurrence {
                    row_addresses: vec![1],
                    history: vec![],
                },
                full_emission: false,
            },
            HnaStreamCommand::SupplyInputMaterial {
                path: directory.path().join("no-inherited-material"),
            },
            HnaStreamCommand::Checkpoint {
                path: checkpoint.clone(),
            },
            HnaStreamCommand::Inspect,
            HnaStreamCommand::Close,
        ];
        let mut bytes = Vec::new();
        for command in commands {
            bytes.extend(serde_json::to_vec(&HnaStreamRequest {
                schema: HNA_STREAM_REQUEST_SCHEMA.into(),
                command,
            })?);
            bytes.push(b'\n');
        }
        let mut output = Vec::new();
        HnaStream::new()
            .pump_native(session, &mut Cursor::new(bytes), &mut output)
            .map_err(|e| NativeSessionError::Application(e.to_string()))?;
        let events = std::str::from_utf8(&output)
            .unwrap()
            .lines()
            .map(|s| serde_json::from_str::<serde_json::Value>(s).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(events.len(), 6);
        assert_eq!(events[1]["event"], "refused");
        assert_eq!(events[2]["event"], "refused");
        assert_eq!(events[3]["event"], "checkpoint-refused-or-unconfirmed");
        assert!(!events.iter().any(|e| e["event"] == "checkpoint-published"));
        assert!(!checkpoint.exists());
        assert_eq!(session.inspect().occurrences, 1);
        assert_eq!(session.inspect().available_sources, vec![0]);
        Ok(())
    })
    .unwrap();
}

#[test]
#[ignore = "requires CUDA; interruption retains an already-enacted exterior step"]
fn application_retains_world_effect_and_pending_current_when_native_reception_refuses() {
    let mut spec: WaveControlSpec = serde_json::from_slice(WAVE).unwrap();
    spec.cycles = 2;
    spec.interventions.clear();
    spec.world.couplings[0] = CurrentWire::integers(i64::MAX, 0);
    let result = run_wave_control(&spec).unwrap();
    assert_eq!(
        result.interruption.as_ref().unwrap().stage,
        "native-reception"
    );
    assert_eq!(result.cycles.len(), 1);
    let pending = result.pending_receive.unwrap();
    assert_eq!(pending.current, result.cycles[0].measured_current);
    assert_eq!(pending.source, 0);
    assert_eq!(result.anatomy.available_sources, vec![0]);
    assert_eq!(result.final_world_state, result.cycles[0].world_state);
}
