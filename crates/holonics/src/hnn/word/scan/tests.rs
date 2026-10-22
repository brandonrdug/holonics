use super::*;
use crate::hnn::constitution::Constitution;
use crate::hnn::field::Current;
use crate::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial, ResonatorOperands};
use crate::hnn::tests::support::{contact, small_field};
use crate::ratio::rat;

fn field(exact: bool) -> Field {
    let base = small_field(&[2, 2], vec![contact(0, 1, 1, 0)], 1);
    let mut declaration = base.declaration().clone();
    declaration.receivers[0].aperture = 4;
    let field = Field::declare(declaration).unwrap();
    if exact {
        field.with_exact_word()
    } else {
        field
    }
}

fn material(field: &Field) -> Constitution {
    Constitution::initial(field, 1 << 16)
        .unwrap()
        .with_channel(
            0,
            ExactRatMatrix::new(vec![
                vec![integer(1), Rat::zero()],
                vec![Rat::zero(), Rat::zero()],
            ])
            .unwrap(),
            ExactRatMatrix::identity(2).unwrap(),
            ExactRatMatrix::zero(2, 2).unwrap(),
        )
        .unwrap()
}

fn pumped(width: usize, saturated: bool) -> ResonatorMaterial {
    let law = ResonatorMaterial::new(
        ExactRatMatrix::shaped(
            width,
            width,
            (0..width)
                .map(|i| {
                    (0..width)
                        .map(|j| {
                            if i == j && i % 2 == 0 {
                                integer(1)
                            } else {
                                Rat::zero()
                            }
                        })
                        .collect()
                })
                .collect(),
        )
        .unwrap(),
        ExactRatMatrix::identity(width).unwrap(),
        ExactRatMatrix::zero(width, width).unwrap(),
        Some(
            PumpDeclaration::new(
                rat(1, 8),
                crate::holon::parametron::Carrier::new(integer(1), Rat::zero()).unwrap(),
                PumpStep::Quarter,
            )
            .unwrap(),
        ),
    )
    .unwrap();
    if saturated {
        law.with_symmetric_saturation(rat(1, 16)).unwrap()
    } else {
        law
    }
}

fn opening<'f>(field: &'f Field, theta: &Constitution, loaded: Option<bool>) -> Word<'f> {
    let current = Current::at_rest(field);
    let mut ops = Operands::at_cut(field, theta, &current).unwrap();
    if let Some(saturated) = loaded {
        let loaded = ResonatorOperands::at_cut(
            0,
            &pumped(field.ring(0).width(), saturated),
            ops.rings()[0].admittance(),
            ops.step(),
            None,
        )
        .unwrap();
        ops.resonators_mut()[0] = Some(loaded);
    }
    let mut state = EndChange::rest(field, &ops);
    state.storage[0][0] = integer(1);
    state.storage[0][1] = integer(-1);
    if field.word_lattice().is_none() {
        state.arrivals[0] = [
            vec![rat(1, 3), rat(2, 5), Rat::zero(), Rat::zero()],
            vec![rat(-3, 7), rat(1, 11), Rat::zero(), Rat::zero()],
        ];
        state.states[0] = [vec![rat(1, 7), rat(-2, 9)], vec![rat(3, 5), rat(-7, 4)]];
    }
    let tick = 5;
    if loaded.is_some() {
        state.resonators[0] = Some([
            vec![rat(1, 7), rat(-2, 9), rat(1, 11), rat(-1, 13)],
            vec![rat(3, 5), rat(-7, 4), rat(2, 3), rat(-1, 5)],
        ]);
        state.resonator_phases[0] = Some(ops.resonators()[0].as_ref().unwrap().phase_at(tick - 1));
    }
    let injection = field
        .rings()
        .iter()
        .map(|r| zeros(r.width()))
        .collect::<Vec<_>>();
    Word::continuing(field, ops, &state, &injection, tick).unwrap()
}

fn same_word(actual: &Word<'_>, serial: &Word<'_>) {
    // The complete producing prefixes are the oracle, not only the final storage image.
    assert_eq!(actual.recorded(), serial.recorded());
    assert_eq!(actual.resonances(), serial.resonances());
    assert_eq!(actual.clock(), serial.clock());
    assert_eq!(actual.carried, serial.carried);
    assert_eq!(actual.field_balances(), serial.field_balances());
    assert_eq!(actual.partings(), serial.partings());
    assert_eq!(
        actual.reception_end().unwrap(),
        serial.reception_end().unwrap()
    );
    assert_eq!(actual.released().unwrap(), serial.released().unwrap());
}

#[test]
fn scanned_word_keeps_every_pumped_singular_prefix_and_receipt_under_partitions() {
    let field = field(true);
    let theta = material(&field);
    let phases = ReceivingPhases::declare(
        &field,
        &theta,
        &Current::at_rest(&field),
        &field.receivers()[0],
    )
    .unwrap();
    assert!(phases.junction_steps() > 2);
    let mut serial = opening(&field, &theta, Some(false));
    let anchors = serial.forward(&phases).unwrap();
    for partitions in [1, 2, 7, 64] {
        let mut actual = opening(&field, &theta, Some(false));
        let start = std::time::Instant::now();
        let (got, span) = actual.forward_scanned(&phases, partitions).unwrap();
        assert_eq!(got, anchors);
        same_word(&actual, &serial);
        assert_eq!(span.scanned_ticks, phases.junction_steps() - 1);
        assert_eq!(span.serial_ticks, 0);
        println!(
            "span partitions={partitions} scanned={} serial={} elapsed_ns={}",
            span.scanned_ticks,
            span.serial_ticks,
            start.elapsed().as_nanos()
        );
    }
}

#[test]
fn scanned_word_keeps_actual_split_and_saturation_departures_without_replay() {
    for (exact, loaded) in [(false, None), (true, Some(true))] {
        let field = field(exact);
        let theta = material(&field);
        let phases = ReceivingPhases::declare(
            &field,
            &theta,
            &Current::at_rest(&field),
            &field.receivers()[0],
        )
        .unwrap();
        let mut serial = opening(&field, &theta, loaded);
        let anchors = serial.forward(&phases).unwrap();
        for partitions in [1, 2, 7, 64] {
            let mut actual = opening(&field, &theta, loaded);
            let (got, span) = actual.forward_scanned(&phases, partitions).unwrap();
            assert_eq!(got, anchors);
            same_word(&actual, &serial);
            assert_eq!(
                span.scanned_ticks + span.serial_ticks,
                phases.junction_steps() - 1
            );
            assert!(span.serial_ticks > 0);
            if exact {
                assert_eq!(span.scanned_ticks, 0);
            } else {
                assert!(span.branch_departures > 0);
            }
        }
    }
}

#[test]
fn scanned_word_refuses_zero_partitions_before_any_motion() {
    let field = field(true);
    let theta = material(&field);
    let phases = ReceivingPhases::declare(
        &field,
        &theta,
        &Current::at_rest(&field),
        &field.receivers()[0],
    )
    .unwrap();
    let mut word = opening(&field, &theta, None);
    let before = word.change().unwrap();
    assert!(word.forward_scanned(&phases, 0).is_err());
    assert_eq!(word.change().unwrap(), before);
    assert_eq!(word.ticks(), 0);
}

#[test]
fn scanned_word_keeps_zero_and_single_full_tick_boundaries() {
    for receiver in [0, 1] {
        let base = field(true);
        let mut declaration = base.declaration().clone();
        declaration.receivers[0].ring = receiver;
        declaration.receivers[0].aperture = 1;
        // The new receiver owns its own declared material lattices as well.
        declaration.lattice.clear();
        let field = Field::declare(declaration.by_lattice_rule()).unwrap().with_exact_word();
        let theta = material(&field);
        let phases = ReceivingPhases::declare(
            &field,
            &theta,
            &Current::at_rest(&field),
            &field.receivers()[0],
        )
        .unwrap();
        assert_eq!(phases.junction_steps(), receiver + 1);
        let mut serial = opening(&field, &theta, Some(false));
        let anchors = serial.forward(&phases).unwrap();
        for partitions in [1, 2, 7, 64] {
            let mut actual = opening(&field, &theta, Some(false));
            let (got, span) = actual.forward_scanned(&phases, partitions).unwrap();
            assert_eq!(got, anchors);
            same_word(&actual, &serial);
            assert_eq!(span.serial_ticks, receiver);
            assert_eq!(span.scanned_ticks, 0);
        }
    }
}
