use super::*;
use crate::embedding_fiber::ResidentReadout;

fn seed(nodes: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero()
        };
        nodes
    ]
}
fn input(at: i64) -> Vec<NativePhaseCurrent> {
    vec![
        NativePhaseCurrent::new(at + 1, 1, 1).unwrap(),
        NativePhaseCurrent::new(1, 2 - at, 1).unwrap(),
    ]
}
fn dot(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> ExactComplexWaveCurrent {
    a.iter()
        .zip(b)
        .fold(ExactComplexWaveCurrent::zero(), |sum, (a, b)| {
            sum.add(&a.conjugate().multiply(b))
        })
}

#[test]
#[ignore = "requires CUDA; full internal-current source and older-prefix pairings agree with the existing decoder"]
fn complete_sources_keep_complex_phase_births_recharts_and_late_returns() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(2), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport().unwrap();
    let mut receiver = NativeCurrentHistorySourceReceiver::on_empty(&body).unwrap();
    let mut latest = None;
    let mut anchor = None;
    let mut carriers = Vec::new();
    let mut complete = Vec::new();
    let mut exact = Vec::new();
    for at in 0..8 {
        if at == 4 {
            body.rechart(&[NativePhaseCurrent::new(0, 1, 1).unwrap(); 2])
                .unwrap();
        }
        if at == 6 {
            body.replace_incoming_transport(0, NativePhaseCurrent::new(-1, 0, 1).unwrap())
                .unwrap();
        }
        let mut occurrence = if at == 3 || at == 7 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), input(at))
        } else if at == 5 || at == 0 {
            NativeFieldOccurrence::entering(input(at))
        } else {
            NativeFieldOccurrence::through(latest.take().unwrap(), input(at))
        };
        let step = body.advance_resident(&mut occurrence).unwrap();
        if at == 0 {
            anchor = Some(body.retain_source(&step.source).unwrap());
        }
        latest = Some(step.source);
        let before = body.rest(&[], &[]).unwrap();
        let carrier = receiver.receive_completed(&body).unwrap();
        assert_eq!(
            body.rest(&[], &[]).unwrap(),
            before,
            "source construction does not develop the field"
        );
        let reading = receiver.inspect(&carrier).unwrap();
        let observed = body
            .inspect_junction_enclosure(at as usize)
            .unwrap()
            .unwrap();
        assert_eq!(reading.outgoing_center, observed.outgoing.center);
        assert_eq!(reading.prefix_center, observed.potential_prefix.center);
        let internal = body.inspect_internal_current_enclosures().unwrap().unwrap();
        let mut vector = observed.outgoing.center;
        vector.extend(internal.iter().map(|c| c.current.center[0].clone()));
        assert_eq!(reading.numerical_norm_square, dot(&vector, &vector).real);
        assert!(
            reading.numerical_norm_square >= Rat::zero()
                && reading.source_radius >= observed.outgoing.radius
        );
        let mut exact_vector = body
            .inspect_exact_junction(at as usize)
            .unwrap()
            .unwrap()
            .outgoing;
        exact_vector.extend(
            body.inspect_internal_currents()
                .unwrap()
                .unwrap()
                .into_iter()
                .map(|i| i.current),
        );
        let difference = exact_vector
            .iter()
            .zip(&vector)
            .map(|(a, b)| a.subtract(b))
            .collect::<Vec<_>>();
        assert!(
            dot(&difference, &difference).real <= &reading.source_radius * &reading.source_radius
        );
        assert!(
            &reading.numerical_norm_upper * &reading.numerical_norm_upper
                >= reading.numerical_norm_square
        );
        exact.push(exact_vector);
        complete.push(vector);
        carriers.push(carrier);
    }
    let mut nonreal = 0;
    for (i, a) in carriers.iter().enumerate() {
        for (j, b) in carriers.iter().enumerate() {
            let actual = receiver.pairing(a, b).unwrap();
            assert_eq!(actual.center[0], dot(&complete[i], &complete[j]));
            assert!(actual.radius >= Rat::zero());
            let error = dot(&exact[i], &exact[j]).subtract(&actual.center[0]);
            assert!(error.norm_square() <= &actual.radius * &actual.radius);
            nonreal += usize::from(!actual.center[0].imaginary.is_zero());
        }
    }
    assert!(nonreal > 0);
}

#[test]
#[ignore = "requires CUDA; exact birth squares exceed 128 bits in the ordinary 72-bit current chart"]
fn birth_square_and_norm_keep_their_wider_numerators() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    let mut receiver = NativeCurrentHistorySourceReceiver::on_empty(&body).unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::new(1024, 1, 1).unwrap(),
        ]))
        .unwrap();
    receiver.receive_completed(&body).unwrap();
    body.advance_resident(&mut NativeFieldOccurrence::through(
        first.source,
        vec![NativePhaseCurrent::new(1, -1024, 1).unwrap()],
    ))
    .unwrap();
    let source = receiver.receive_completed(&body).unwrap();
    let state = surface.read_out(&receiver.state).unwrap();
    assert!(integer(&state[12..17]).unwrap().bits() > 128);
    let reading = receiver.inspect(&source).unwrap();
    let mut full = body
        .inspect_junction_enclosure(1)
        .unwrap()
        .unwrap()
        .outgoing
        .center;
    full.extend(
        body.inspect_internal_current_enclosures()
            .unwrap()
            .unwrap()
            .into_iter()
            .map(|i| i.current.center[0].clone()),
    );
    assert_eq!(reading.numerical_norm_square, dot(&full, &full).real);
    assert_eq!(
        receiver.pairing(&source, &source).unwrap().center[0].real,
        reading.numerical_norm_square
    );
}

#[test]
#[ignore = "requires CUDA; unsupported contact representation and receiver chronology preserve the field"]
fn unsupported_contact_chart_refuses_without_rollback_or_source_fabrication() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    let mut receiver = NativeCurrentHistorySourceReceiver::on_empty(&body).unwrap();
    assert!(receiver.receive_completed(&body).is_err());
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::new(1, 0, 2).unwrap(),
        ]))
        .unwrap();
    receiver.receive_completed(&body).unwrap();
    let before_receiver = surface.detach_section(&receiver.state, 64).unwrap();
    body.advance_resident(&mut NativeFieldOccurrence::through(
        first.source,
        vec![NativePhaseCurrent::new(1, 0, 3).unwrap()],
    ))
    .unwrap();
    let before_body = body.rest(&[], &[]).unwrap();
    assert!(receiver.receive_completed(&body).is_err());
    assert_eq!(receiver.next, 1);
    assert_eq!(
        surface.detach_section(&receiver.state, 64).unwrap(),
        before_receiver
    );
    assert_eq!(body.rest(&[], &[]).unwrap(), before_body);
    assert_eq!(body.occurrence_count(), 2);
}

#[test]
#[ignore = "requires CUDA; the full internal source separates a reachable dark current behind exactly zero outgoing current"]
fn equal_zero_outgoing_sources_retain_opposite_nonzero_internal_currents() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    let mut receiver = NativeCurrentHistorySourceReceiver::on_empty(&body).unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
        ]))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    receiver.receive_completed(&body).unwrap();
    // Two actual receptions at the same retained source make d=(0,1,-1) twice.
    for _ in 0..2 {
        body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![NativePhaseCurrent::unit()],
        ))
        .unwrap();
        receiver.receive_completed(&body).unwrap();
    }
    // This declared exact current cancels the boundary-visible sum of the two internal
    // currents. Subsequent zero occurrences leave their opposite orientations circulating.
    body.advance_resident(&mut NativeFieldOccurrence::entering(vec![
        NativePhaseCurrent::new(-9, 0, 10).unwrap(),
    ]))
    .unwrap();
    receiver.receive_completed(&body).unwrap();
    let mut sources = Vec::new();
    let mut internal = Vec::new();
    for _ in 0..3 {
        body.advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::zero(),
        ]))
        .unwrap();
        let source = receiver.receive_completed(&body).unwrap();
        if body.occurrence_count() >= 6 {
            let exact = body
                .inspect_exact_junction(body.occurrence_count() - 1)
                .unwrap()
                .unwrap();
            assert!(exact
                .outgoing
                .iter()
                .all(|v| v == &ExactComplexWaveCurrent::zero()));
            assert!(exact
                .held_current
                .iter()
                .all(|v| v == &ExactComplexWaveCurrent::zero()));
            let currents = body.inspect_internal_currents().unwrap().unwrap();
            assert_eq!(currents.len(), 2);
            internal.push(currents.into_iter().map(|c| c.current).collect::<Vec<_>>());
            sources.push(source);
        }
    }
    let third = Rat::new(1.into(), 3.into());
    assert_eq!(internal[0][0].real, third);
    assert_eq!(internal[0][1].real, -&third);
    assert_eq!(internal[1][0].real, -&third);
    assert_eq!(internal[1][1].real, third);
    let negative = receiver.pairing(&sources[0], &sources[1]).unwrap();
    let positive = receiver.pairing(&sources[0], &sources[0]).unwrap();
    assert!(&negative.center[0].real + &negative.radius < Rat::zero());
    assert!(&positive.center[0].real - &positive.radius > Rat::zero());
    let truth = ExactComplexWaveCurrent::new(Rat::new((-2).into(), 9.into()), Rat::zero());
    assert!(
        truth.subtract(&negative.center[0]).norm_square() <= &negative.radius * &negative.radius
    );
}
