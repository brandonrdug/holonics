use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

fn seed() -> Vec<NativeJunctionSeed> {
    vec![NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    }]
}
fn p(r: i64, i: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, 1).unwrap()
}
fn dot(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> ExactComplexWaveCurrent {
    a.iter()
        .zip(b)
        .fold(ExactComplexWaveCurrent::zero(), |s, (a, b)| {
            s.add(&a.conjugate().multiply(b))
        })
}
fn kernel(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> Rat {
    dot(a, b).norm_square() / (dot(a, a).real * dot(b, b).real)
}
type Factor = (Vec<ExactComplexWaveCurrent>, Vec<ExactComplexWaveCurrent>);
fn eval(f: &[Factor], x: &[ExactComplexWaveCurrent], n: usize) -> Vec<ExactComplexWaveCurrent> {
    let mut out = vec![ExactComplexWaveCurrent::zero(); n];
    for (b, s) in f {
        let k = kernel(s, x);
        for (o, b) in out.iter_mut().zip(b) {
            *o = o.add(&b.scaled(&k));
        }
    }
    out
}
fn sub(
    a: &[ExactComplexWaveCurrent],
    b: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    a.iter().zip(b).map(|(a, b)| a.subtract(b)).collect()
}
fn ball(x: &[ExactComplexWaveCurrent], b: &NativeFieldCurrentBall) {
    let e: Rat = sub(x, &b.center)
        .iter()
        .map(ExactComplexWaveCurrent::norm_square)
        .sum();
    assert!(e <= &b.radius * &b.radius, "escaped native current ball");
}
fn norm_operator(f: &[Factor]) -> Rat {
    f.iter()
        .flat_map(|(a, x)| f.iter().map(move |(b, y)| dot(a, b).real * kernel(x, y)))
        .sum()
}
fn lifted(
    s: &[ExactComplexWaveCurrent],
    c: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    let mut a = vec![ExactComplexWaveCurrent::new(
        Rat::from_integer(1.into()),
        Rat::zero(),
    )];
    a.extend_from_slice(s);
    let mut b = vec![ExactComplexWaveCurrent::new(
        Rat::from_integer(1.into()),
        Rat::zero(),
    )];
    b.extend_from_slice(c);
    a.iter()
        .flat_map(|a| b.iter().map(move |b| a.multiply(b)))
        .collect()
}
// Independent exact-current and exact-operator reference. It is never used by a native event.
fn verify(body: &NativeConstitutiveField<'_>) {
    let end = body.occurrence_count() - 1;
    let n = body.nodes();
    let trace = body.decode_junction_residual_trace(end).unwrap();
    let numerical = (0..=end)
        .map(|i| body.inspect_junction_enclosure(i).unwrap().unwrap())
        .collect::<Vec<_>>();
    let contacts = (0..=end)
        .filter_map(|i| body.junction_contact(i).unwrap().map(|d| (i, d)))
        .collect::<Vec<_>>();
    let zero = vec![ExactComplexWaveCurrent::zero(); 3 * n];
    let mut contexts = Vec::new();
    let mut nc = Vec::new();
    for at in 0..=end {
        let mut x = trace[at].outgoing.clone();
        let mut nx = numerical[at].outgoing.center.clone();
        for (birth, d) in &contacts {
            if *birth > at {
                x.push(ExactComplexWaveCurrent::zero());
                nx.push(ExactComplexWaveCurrent::zero());
                continue;
            }
            let before = if *birth == 0 {
                &zero
            } else {
                &trace[*birth - 1].potential_prefix
            };
            let nb = if *birth == 0 {
                &zero
            } else {
                &numerical[*birth - 1].potential_prefix.center
            };
            let sign = Rat::from_integer((if at % 2 == 0 { 1 } else { -1 }).into());
            x.push(dot(d, &sub(&trace[at].potential_prefix, before)).scaled(&sign));
            nx.push(dot(d, &sub(&numerical[at].potential_prefix.center, nb)).scaled(&sign));
        }
        contexts.push(x);
        nc.push(nx);
    }
    let mut exact: Vec<Factor> = Vec::new();
    let mut numeric: Vec<Factor> = Vec::new();
    let mut inputs: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
    let mut ninputs: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
    let mut outputs: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
    let mut actual_outputs: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
    let mut first_sources: Vec<(Vec<ExactComplexWaveCurrent>, usize)> = Vec::new();
    for at in 0..=end {
        let r = body
            .inspect_contextual_material_transport(at)
            .unwrap()
            .unwrap();
        let source = body.root_junction_source(at).unwrap();
        assert_eq!(source, r.visible_source.exact);
        let output = lifted(&source, &contexts[at]);
        let nout = lifted(&r.visible_source.center, &nc[at]);
        let y = body
            .inspect_incoming(at)
            .unwrap()
            .iter()
            .map(|v| v.current())
            .collect::<Vec<_>>();
        ball(&y, &r.observed);
        let mut inp = Vec::new();
        let mut ninp = Vec::new();
        if let Some(s) = r.source_occurrence {
            let old_source = body.root_junction_source(s).unwrap();
            let profile = r.input_source.as_ref().unwrap();
            assert_eq!(profile.exact, old_source);
            inp = lifted(&old_source, &contexts[at - 1]);
            ninp = lifted(&profile.center, &nc[at - 1]);
            let reference = first_sources
                .iter()
                .find(|(x, _)| x == &old_source)
                .map(|(_, i)| *i)
                .unwrap_or_else(|| {
                    first_sources.push((old_source, at));
                    at
                });
            assert_eq!(r.reference_receiving_occurrence, Some(reference));
            assert_eq!(r.input_context_occurrence, Some(at - 1));
            let old = eval(&exact, &inp, n);
            let original_now = eval(&exact, &outputs[s], n);
            ball(&old, r.effective_source_forward.as_ref().unwrap());
            ball(
                &original_now,
                r.original_source_at_current_map.as_ref().unwrap(),
            );
            ball(
                &sub(&y, &actual_outputs[s]),
                r.returned_difference.as_ref().unwrap(),
            );
            ball(
                &sub(&original_now, &actual_outputs[s]),
                r.parameter_change.as_ref().unwrap(),
            );
            ball(
                &sub(&old, &original_now),
                r.condition_change.as_ref().unwrap(),
            );
            let ba = sub(&y, &old)
                .iter()
                .map(|v| v.scaled(&Rat::new(1.into(), 2.into())))
                .collect::<Vec<_>>();
            exact.push((ba, inp.clone()));
            numeric.push((r.ordinary_factor.clone(), ninp.clone()));
            if reference < at {
                let dy = sub(
                    &y,
                    &body
                        .inspect_incoming(reference)
                        .unwrap()
                        .iter()
                        .map(|v| v.current())
                        .collect::<Vec<_>>(),
                );
                let diff = sub(&eval(&exact, &inp, n), &eval(&exact, &inputs[reference], n));
                ball(&dy, r.contextual_return.as_ref().unwrap());
                ball(
                    &diff,
                    r.contextual_forward_after_ordinary_return.as_ref().unwrap(),
                );
                ball(&sub(&dy, &diff), r.contextual_residual.as_ref().unwrap());
                let gain = Rat::from_integer(3.into())
                    - Rat::from_integer(2.into()) * kernel(&inp, &inputs[reference]);
                let bc = sub(&dy, &diff)
                    .iter()
                    .map(|v| v.scaled(&(Rat::from_integer(1.into()) / &gain)))
                    .collect::<Vec<_>>();
                exact.push((bc.clone(), inp.clone()));
                exact.push((
                    bc.iter().map(ExactComplexWaveCurrent::negated).collect(),
                    inputs[reference].clone(),
                ));
                numeric.push((r.contextual_factor.clone(), ninp.clone()));
                numeric.push((
                    r.contextual_factor
                        .iter()
                        .map(ExactComplexWaveCurrent::negated)
                        .collect(),
                    ninputs[reference].clone(),
                ));
            }
        }
        let forward = eval(&exact, &output, n);
        ball(&forward, &r.forward);
        let mut defect = exact.clone();
        defect.extend(numeric.iter().map(|(b, x)| {
            (
                b.iter().map(ExactComplexWaveCurrent::negated).collect(),
                x.clone(),
            )
        }));
        let error = norm_operator(&defect);
        assert!(error >= Rat::zero() && error <= &r.coefficient_error * &r.coefficient_error);
        assert!(norm_operator(&numeric) <= &r.coefficient_norm_upper * &r.coefficient_norm_upper);
        let nforward = eval(&numeric, &nout, n);
        let wire = body.inspect_material_transport_wire(at).unwrap().unwrap();
        let [_, _, _, _, raw, _, _] = offsets(n);
        let scale = BigInt::one() << (2 * body.transport_grain().unwrap());
        for j in 0..2 * n {
            let center = Rat::new(
                integer(&wire.intervals[raw + 5 * j..raw + 5 * j + 5]).unwrap(),
                scale.clone(),
            );
            let upper = Rat::new(
                integer(&wire.intervals[raw + 5 * (2 * n + j)..raw + 5 * (2 * n + j) + 5]).unwrap(),
                scale.clone(),
            );
            let lower = -Rat::new(
                integer(&wire.intervals[raw + 5 * (4 * n + j)..raw + 5 * (4 * n + j) + 5]).unwrap(),
                scale.clone(),
            );
            let actual = if j % 2 == 0 {
                &nforward[j / 2].real
            } else {
                &nforward[j / 2].imaginary
            };
            let d = actual - center;
            assert!(lower <= d && d <= upper);
        }
        inputs.push(inp);
        ninputs.push(ninp);
        outputs.push(output);
        actual_outputs.push(forward);
    }
}

/// Parity law (contextual material): every device reading (forward, returned, parameter and
/// condition change, contextual return and coefficient bounds) contains the exact rational
/// current and operator reconstructed on the host by `verify`.
#[test]
#[ignore = "requires CUDA; contextual material readings contain the exact host reference"]
fn contextual_material_readings_contain_the_exact_host_reference() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seed(), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::BilinearContextual)
        .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![p(1, 0)]))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    let mut last = Some(first.source);
    for (at, input) in [
        (1, p(0, 1)),
        (2, p(-1, 0)),
        (3, p(1, 1)),
        (4, p(1, 0)),
        (5, p(-1, 1)),
        (6, p(0, 1)),
    ] {
        if at == 3 {
            body.rechart(&[p(0, 1)]).unwrap();
        }
        let mut occurrence = if at == 5 {
            NativeFieldOccurrence::entering(vec![input])
        } else if at == 3 {
            NativeFieldOccurrence::through(last.take().unwrap(), vec![input])
        } else {
            NativeFieldOccurrence::through_anchor(&anchor, vec![input])
        };
        let before = body.census();
        let next = body.advance_resident(&mut occurrence).unwrap();
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
        last = Some(next.source);
    }
    verify(&body);
}
