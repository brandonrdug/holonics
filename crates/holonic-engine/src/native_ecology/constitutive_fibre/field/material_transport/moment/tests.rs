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

/// Parity law (moment material): every device moment reading and coefficient bound contains the
/// exact rational current and operator reconstructed on the host by `verify`.
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
