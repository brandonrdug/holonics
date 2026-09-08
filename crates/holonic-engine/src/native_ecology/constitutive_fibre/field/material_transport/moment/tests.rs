use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

fn seed(n: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero()
        };
        n
    ]
}
fn dot(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> ExactComplexWaveCurrent {
    a.iter()
        .zip(b)
        .fold(ExactComplexWaveCurrent::zero(), |s, (a, b)| {
            s.add(&a.conjugate().multiply(b))
        })
}
fn difference(
    a: &[ExactComplexWaveCurrent],
    b: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    a.iter().zip(b).map(|(a, b)| a.subtract(b)).collect()
}
fn kernel(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> Rat {
    dot(a, b)
        .add(&ExactComplexWaveCurrent::new(Rat::one(), Rat::zero()))
        .norm_square()
        / ((Rat::one() + dot(a, a).real) * (Rat::one() + dot(b, b).real))
}
fn assert_ball(v: &[ExactComplexWaveCurrent], ball: &NativeFieldCurrentBall) {
    let error: Rat = difference(v, &ball.center)
        .iter()
        .map(ExactComplexWaveCurrent::norm_square)
        .sum();
    assert!(
        error <= &ball.radius * &ball.radius,
        "actual current escapes native ball"
    );
}
fn evaluate(
    factors: &[(Vec<ExactComplexWaveCurrent>, Vec<ExactComplexWaveCurrent>)],
    x: &[ExactComplexWaveCurrent],
    n: usize,
) -> Vec<ExactComplexWaveCurrent> {
    let mut sum = vec![ExactComplexWaveCurrent::zero(); n];
    for (beta, source) in factors {
        let k = kernel(source, x);
        for (s, b) in sum.iter_mut().zip(beta) {
            *s = s.add(&b.scaled(&k));
        }
    }
    sum
}
fn operator_norm_square(
    factors: &[(Vec<ExactComplexWaveCurrent>, Vec<ExactComplexWaveCurrent>)],
) -> Rat {
    factors
        .iter()
        .flat_map(|(a, x)| {
            factors
                .iter()
                .map(move |(b, y)| dot(a, b).real * kernel(x, y))
        })
        .sum()
}
/// The oracle reconstructs the small physical current in an exterior exact-rational chart.
/// Neither its source population nor its ideal operator is supplied to native development.
fn verify(body: &NativeConstitutiveField<'_>) {
    let n = body.nodes();
    let end = body.occurrence_count() - 1;
    let trace = body.decode_junction_residual_trace(end).unwrap();
    let numeric_trace = (0..=end)
        .map(|at| body.inspect_junction_enclosure(at).unwrap().unwrap())
        .collect::<Vec<_>>();
    let mut contacts = Vec::new();
    let mut sources: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
    let mut forwards: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
    let mut factors = Vec::new();
    let mut numeric_sources: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
    let mut numeric_factors = Vec::new();
    for at in 0..=end {
        if let Some(d) = body.junction_contact(at).unwrap() {
            contacts.push((at, d));
        }
        let mut x = trace[at].outgoing.clone();
        let mut numeric_x = numeric_trace[at].outgoing.center.clone();
        for (birth, d) in &contacts {
            let zero = vec![ExactComplexWaveCurrent::zero(); 3 * n];
            let prior = if *birth == 0 {
                &zero
            } else {
                &trace[*birth - 1].potential_prefix
            };
            x.push(
                dot(d, &difference(&trace[at].potential_prefix, prior)).scaled(&Rat::from_integer(
                    (if at % 2 == 0 { 1 } else { -1 }).into(),
                )),
            );
            let prior = if *birth == 0 {
                &zero
            } else {
                &numeric_trace[*birth - 1].potential_prefix.center
            };
            numeric_x.push(
                dot(
                    d,
                    &difference(&numeric_trace[at].potential_prefix.center, prior),
                )
                .scaled(&Rat::from_integer(
                    (if at % 2 == 0 { 1 } else { -1 }).into(),
                )),
            );
        }
        let reading = body.inspect_moment_material_transport(at).unwrap().unwrap();
        let y = body
            .inspect_incoming(at)
            .unwrap()
            .iter()
            .map(|p| p.current())
            .collect::<Vec<_>>();
        assert_ball(&y, &reading.observed);
        if let Some(s) = body.history[at].lineage.received_from {
            let old = evaluate(&factors, &sources[s], n);
            assert_ball(&old, reading.contemporary_source_forward.as_ref().unwrap());
            assert_ball(
                &difference(&y, &forwards[s]),
                reading.returned_difference.as_ref().unwrap(),
            );
            assert_ball(
                &difference(&old, &forwards[s]),
                reading.chronological_current.as_ref().unwrap(),
            );
            assert_ball(
                &difference(&y, &old),
                reading.contemporary_difference.as_ref().unwrap(),
            );
            let beta = difference(&y, &old)
                .iter()
                .map(|b| b.scaled(&Rat::new(1.into(), 2.into())))
                .collect();
            factors.push((beta, sources[s].clone()));
            numeric_factors.push((
                reading.numerical_return_factor.clone(),
                numeric_sources[s].clone(),
            ));
            let target = &reading.observed.center;
            let approximate = &reading.contemporary_source_forward.as_ref().unwrap().center;
            for (i, beta) in reading.numerical_return_factor.iter().enumerate() {
                let ideal = target[i]
                    .subtract(&approximate[i])
                    .scaled(&Rat::new(1.into(), 2.into()));
                assert_eq!(beta.subtract(&ideal), reading.beta_rounding_residual[i]);
            }
        }
        let forward = evaluate(&factors, &x, n);
        assert_ball(&forward, &reading.forward);
        let numeric = body
            .inspect_exact_numerical_moment_forward(at, at)
            .unwrap()
            .unwrap();
        assert_eq!(numeric, evaluate(&numeric_factors, &numeric_x, n));
        let mut error_factors = factors.clone();
        error_factors.extend(numeric_factors.iter().map(|(beta, x)| {
            (
                beta.iter()
                    .map(|b| b.scaled(&Rat::from_integer((-1).into())))
                    .collect(),
                x.clone(),
            )
        }));
        let coefficient_error = operator_norm_square(&error_factors);
        assert!(
            coefficient_error >= Rat::zero()
                && coefficient_error <= &reading.coefficient_error * &reading.coefficient_error
        );
        assert!(
            operator_norm_square(&numeric_factors)
                <= &reading.coefficient_norm_upper * &reading.coefficient_norm_upper
        );
        for i in 0..n {
            let defect = numeric[i].subtract(&reading.grid_kernel_forward[i]);
            let lo = &reading.kernel_evaluation_lower[i];
            let hi = &reading.kernel_evaluation_upper[i];
            assert!(lo.real <= defect.real && defect.real <= hi.real);
            assert!(lo.imaginary <= defect.imaginary && defect.imaginary <= hi.imaginary);
        }
        assert_eq!(
            exact::source_pair(&reading.source, &reading.source),
            Rat::one()
        );
        sources.push(x);
        numeric_sources.push(numeric_x);
        forwards.push(forward);
    }
}

#[test]
#[ignore = "requires CUDA; normalized moment conduct matches an independent physical rational current and delayed-source oracle"]
fn moment_return_retains_phase_chronology_and_oriented_error() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(2), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::HomogeneousMoment)
        .unwrap();
    let mut latest = None;
    let mut anchor = None;
    for at in 0..6 {
        if at == 3 {
            body.rechart(&[NativePhaseCurrent::new(0, 1, 1).unwrap(); 2])
                .unwrap();
        }
        let input = vec![
            NativePhaseCurrent::new(at + 1, 1, 1).unwrap(),
            NativePhaseCurrent::new(2, 1 - at, 1).unwrap(),
        ];
        let mut occurrence = if at == 0 || at == 4 {
            NativeFieldOccurrence::entering(input)
        } else if at == 3 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), input)
        } else {
            NativeFieldOccurrence::through(latest.take().unwrap(), input)
        };
        let before = body.census();
        let next = body.advance_resident(&mut occurrence).unwrap();
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
        if at == 0 {
            anchor = Some(body.retain_source(&next.source).unwrap());
        }
        latest = Some(next.source);
    }
    verify(&body);
    body.read_material_transport_pairs(5, 1).unwrap().unwrap();
    assert!(body.inspect_material_transport_state().is_err());
    assert!(
        body.inspect_complete_material_transport(5)
            .unwrap()
            .is_none()
    );
}

#[test]
#[ignore = "requires CUDA; actual opposite hidden currents keep their reference-relative phase in the source"]
fn homogeneous_reference_distinguishes_opposite_dark_sources() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::HomogeneousMoment)
        .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
        ]))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    for _ in 0..2 {
        body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![NativePhaseCurrent::unit()],
        ))
        .unwrap();
    }
    body.advance_resident(&mut NativeFieldOccurrence::entering(vec![
        NativePhaseCurrent::new(-9, 0, 10).unwrap(),
    ]))
    .unwrap();
    for _ in 0..3 {
        body.advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::zero(),
        ]))
        .unwrap();
    }
    let a = body.inspect_moment_material_transport(5).unwrap().unwrap();
    let b = body.inspect_moment_material_transport(6).unwrap().unwrap();
    let cross = exact::source_pair(&a.source, &b.source);
    let expected = Rat::new(49.into(), 121.into());
    let e = (&a.source.source_radius + &b.source.source_radius) * Rat::from_integer(2.into());
    assert!(&expected - &e <= cross && cross <= &expected + &e);
    assert!(cross < Rat::one());
    for at in [5, 6] {
        assert!(
            body.inspect_exact_junction(at)
                .unwrap()
                .unwrap()
                .outgoing
                .iter()
                .all(|v| v == &ExactComplexWaveCurrent::zero())
        );
    }
    verify(&body);
}

#[test]
#[ignore = "requires CUDA; opposing actual returns cancel in the numerical operator norm before its scalar bound"]
fn operator_norm_keeps_the_signed_cross_current() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::HomogeneousMoment)
        .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
        ]))
        .unwrap();
    let source = body.retain_source(&first.source).unwrap();
    let mut triangle = Rat::zero();
    for at in 1..=8 {
        let incoming = NativePhaseCurrent::new(if at % 2 == 1 { 1 } else { -1 }, 0, 1).unwrap();
        body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &source,
            vec![incoming],
        ))
        .unwrap();
        let report = body.inspect_moment_material_transport(at).unwrap().unwrap();
        triangle += num_traits::Signed::abs(&report.numerical_return_factor[0].real);
        let exact = body
            .inspect_exact_numerical_moment_forward(at, 0)
            .unwrap()
            .unwrap();
        // All coefficients have the identical unit-norm Q source, so this is the full norm.
        assert_eq!(
            report.coefficient_norm_upper,
            num_traits::Signed::abs(&exact[0].real)
        );
        assert!(report.coefficient_norm_upper < Rat::one());
    }
    assert!(triangle > Rat::from_integer(4.into()));
}

#[test]
#[ignore = "requires CUDA; a homogeneous-moment refusal after encoder staging preserves the entire old owner"]
fn late_source_chart_refusal_keeps_old_field_coefficients_and_capability() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::HomogeneousMoment)
        .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::new(1, 0, 2).unwrap(),
        ]))
        .unwrap();
    let before = body.rest(&[Some(&first.source)], &[]).unwrap();
    let mut incoming =
        NativeFieldOccurrence::through(first.source, vec![NativePhaseCurrent::unit()]);
    assert!(body.advance_resident(&mut incoming).is_err());
    assert_eq!(body.occurrence_count(), 1);
    let after = body.rest(&[incoming.source_ref()], &[]).unwrap();
    assert_eq!(before, after);
}

#[test]
#[ignore = "requires CUDA; moment source coefficients, birth moments and old-source expression continue after archived remount"]
fn moment_material_state_and_delayed_source_survive_archived_remount() {
    fn prefix(
        body: &mut NativeConstitutiveField<'_>,
    ) -> (NativeFieldEmission, NativeFieldSourceAnchor) {
        let first = body
            .advance_resident(&mut NativeFieldOccurrence::entering(vec![
                NativePhaseCurrent::unit(),
            ]))
            .unwrap();
        let anchor = body.retain_source(&first.source).unwrap();
        let second = body
            .advance_resident(&mut NativeFieldOccurrence::through(
                first.source,
                vec![NativePhaseCurrent::new(0, 1, 1).unwrap()],
            ))
            .unwrap();
        let third = body
            .advance_resident(&mut NativeFieldOccurrence::through(
                second.source,
                vec![NativePhaseCurrent::new(1, 1, 1).unwrap()],
            ))
            .unwrap();
        (third.source, anchor)
    }
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::HomogeneousMoment)
        .unwrap();
    let (last, anchor) = prefix(&mut body);
    let saved = body.rest(&[Some(&last)], &[Some(&anchor)]).unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    drop(body);
    let mut reference =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    reference
        .enable_material_transport_source(NativeMaterialTransportSource::HomogeneousMoment)
        .unwrap();
    let (_, reference_anchor) = prefix(&mut reference);
    reference
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &reference_anchor,
            vec![NativePhaseCurrent::new(2, -1, 1).unwrap()],
        ))
        .unwrap();
    let expected = reference.rest(&[], &[]).unwrap();
    drop(reference);
    let archive = std::env::temp_dir().join(format!(
        "holonics-moment-material-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let rest = NativeFieldRest::read(&mut &bytes[..], bytes.len() as u64).unwrap();
    let before = surface.census();
    let (mut resumed, _, anchors) =
        NativeConstitutiveField::remount_with_history_archive(&surface, rest, &archive).unwrap();
    assert_eq!(resumed.census().deed_launches, before.deed_launches);
    assert_eq!(
        resumed.material_transport_source(),
        Some(NativeMaterialTransportSource::HomogeneousMoment)
    );
    resumed
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            anchors[0].as_ref().unwrap(),
            vec![NativePhaseCurrent::new(2, -1, 1).unwrap()],
        ))
        .unwrap();
    assert_eq!(resumed.rest(&[], &[]).unwrap(), expected);
    resumed
        .inspect_exact_numerical_moment_forward(3, 3)
        .unwrap()
        .unwrap();
    drop(resumed);
    std::fs::remove_file(archive).unwrap();
}
