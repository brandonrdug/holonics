use super::*;
use crate::embedding_fiber::ResidentReadout;

fn phase(r: i64, i: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, 1).unwrap()
}
fn seed(nodes: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        nodes
    ]
}

fn coordinates(v: &[ExactComplexWaveCurrent]) -> Vec<Rat> {
    v.iter()
        .flat_map(|z| [z.real.clone(), z.imaginary.clone()])
        .collect()
}
fn context(r: &NativeContextualMaterialReading) -> Vec<Rat> {
    let c = r.operative_context.as_ref().unwrap();
    coordinates(&c.outgoing_center)
        .into_iter()
        .chain(coordinates(&c.internal_center))
        .collect()
}
// Independent quotient rule on the scalar reproducing kernel, with exact rationals.
// This does not use the GPU's factored pullback formula or its dyadic ratio implementation.
fn kernel_derivative(a: &[Rat], b: &[Rat], coordinate: usize) -> (Rat, Rat) {
    let zero = Rat::zero();
    let mut re = Rat::one();
    let mut im = Rat::zero();
    for j in (0..a.len().min(b.len())).step_by(2) {
        re += &a[j] * &b[j] + &a[j + 1] * &b[j + 1];
        im += &a[j] * &b[j + 1] - &a[j + 1] * &b[j];
    }
    let na = Rat::one() + a.iter().map(|x| x * x).sum::<Rat>();
    let nb = Rat::one() + b.iter().map(|x| x * x).sum::<Rat>();
    let numerator = &re * &re + &im * &im;
    let j = coordinate & !1;
    let ar = a.get(j).unwrap_or(&zero);
    let ai = a.get(j + 1).unwrap_or(&zero);
    let (dr, di) = if coordinate % 2 == 0 {
        (ar.clone(), -ai)
    } else {
        (ai.clone(), ar.clone())
    };
    let two = Rat::from_integer(2.into());
    let dn = &two * (&re * dr + &im * di);
    let db = &two * &b[coordinate];
    let derivative = (dn * &nb - &numerator * db) / (&na * &nb * &nb);
    (numerator / (&na * &nb), derivative)
}
fn reference(
    rows: &[NativeContextualMaterialReading],
    source: usize,
    r: &[Rat],
    visible: bool,
    j: usize,
) -> Rat {
    let sq = coordinates(&rows[source].visible_source.center);
    let cq = context(&rows[source]);
    if !visible && j>=cq.len(){return Rat::zero();}
    let mut answer = Rat::zero();
    for (at, row) in rows.iter().enumerate().take(source + 1) {
        if row.source_occurrence.is_none() {
            continue;
        }
        let reference = row.reference_receiving_occurrence.unwrap_or(at);
        for reflected in [false, true] {
            if reflected && reference == at {
                continue;
            }
            let q = if reflected { reference } else { at };
            let s = coordinates(&rows[q].input_source.as_ref().unwrap().center);
            let c = context(&rows[q - 1]);
            let alpha: Rat = row
                .ordinary_factor
                .iter()
                .zip(&row.contextual_factor)
                .enumerate()
                .map(|(j, (a, b))| {
                    if reflected {
                        -&b.real * &r[2 * j] - &b.imaginary * &r[2 * j + 1]
                    } else {
                        (&a.real + &b.real) * &r[2 * j]
                            + (&a.imaginary + &b.imaginary) * &r[2 * j + 1]
                    }
                })
                .sum();
            let (ks, ds) = kernel_derivative(&s, &sq, if visible { j } else { 0 });
            let (kc, dc) = kernel_derivative(&c, &cq, if visible { 0 } else { j });
            answer += alpha * if visible { ds * kc } else { ks * dc };
        }
    }
    answer
}

/// Material-pullback parity: for every metric and every corner of the covector box, the device
/// pullback of the contextual material source contains the exact host quotient-rule derivative
/// of the scalar reproducing kernel through the actual producing factors.
#[test]
#[ignore = "requires CUDA; actual producing factors against independent exact quotient derivatives"]
fn material_source_pullback_keeps_both_arguments_and_the_producing_cut() {
    let source_kind = NativeMaterialTransportSource::OperativeContextual;
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let make = || {
        let mut f = NativeConstitutiveField::found_with_enclosed_junction(
            &surface,
            seed(2),
            ResidentGrain(72),
        )
        .unwrap();
        f.enable_material_transport_source(source_kind)
            .unwrap();
        f
    };
    let mut field = make();
    let mut previous = None;
    let mut anchor = None;
    let mut first_anchor = None;
    let inputs = [
        [(1, 1), (0, 1)],
        [(0, 1), (1, 0)],
        [(1, 1), (0, 1)],
        [(1, 0), (0, -1)],
        [(0, 1), (1, 0)],
        [(0, 0), (1, 1)],
    ];
    for (at, values) in inputs.into_iter().enumerate() {
        let current = values.into_iter().map(|(r, i)| phase(r, i)).collect();
        let mut event = if at == 5 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), current)
        } else if at == 2 {
            NativeFieldOccurrence::through_anchor(first_anchor.as_ref().unwrap(), current)
        } else if let Some(p) = previous.take() {
            NativeFieldOccurrence::through(p, current)
        } else {
            NativeFieldOccurrence::entering(current)
        };
        let next = field.advance_resident(&mut event).unwrap();
        if at == 0 {
            first_anchor = Some(field.retain_source(&next.source).unwrap());
        }
        if at == 3 {
            anchor = Some(field.retain_source(&next.source).unwrap());
        }
        previous = Some(next.source);
    }
    let rows = (0..6)
        .map(|i| {
            field
                .inspect_contextual_material_transport(i)
                .unwrap()
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert!(
        rows.iter()
            .enumerate()
            .any(|(i, r)| r.reference_receiving_occurrence.is_some_and(|q| q < i)),
        "exercise reflected factors"
    );
    let mut certified_internal = false;
    let mut certified_visible = false;
    let mut phase_consequence = false;
    for receiving in [4, 5] {
        let normalized = field
            .normalized_material_return(receiving, 2, SeriesAperture(32))
            .unwrap()
            .unwrap();
        assert_eq!(normalized.source.occurrence, 3);
        let q = normalized.inspect().unwrap();
        for metric in [
            NativeMaterialPullbackMetric::RelativeEntropy,
            NativeMaterialPullbackMetric::SquaredProbability,
            NativeMaterialPullbackMetric::SquaredCurrent,
        ] {
            let before = field.census();
            let resident = if metric == NativeMaterialPullbackMetric::SquaredCurrent {
                field
                    .pull_back_material_current(receiving)
                    .unwrap()
                    .unwrap()
            } else {
                field
                    .pull_back_material_source(&normalized, metric)
                    .unwrap()
            };
            assert_eq!(field.census().section_read_outs, before.section_read_outs);
            let result = resident.inspect().unwrap();
            // Plan phase 7: a power-preserving pullback onto every returned coordinate.
            let element = resident.receiver_element();
            assert_eq!(
                element.power(),
                &holonics::law::receiver::ReceiverPower::Pullback
            );
            assert_eq!(
                element.read_ports(),
                result.visible_source.len()
                    + result.outgoing_current.len()
                    + result.internal_current.len()
            );
            assert_eq!(result.source.occurrence, 3);
            assert_eq!(result.receiving.occurrence, receiving);
            let intervals: Vec<ExactInterval> = match metric {
                NativeMaterialPullbackMetric::RelativeEntropy
                | NativeMaterialPullbackMetric::SquaredProbability => {
                    let values = if metric == NativeMaterialPullbackMetric::RelativeEntropy {
                        &q.returned_difference
                    } else {
                        &q.potential_pullback
                    };
                    values
                        .iter()
                        .flat_map(|x| {
                            [
                                x.clone(),
                                ExactInterval::new(Rat::zero(), Rat::zero()).unwrap(),
                            ]
                        })
                        .collect()
                }
                NativeMaterialPullbackMetric::SquaredCurrent => {
                    let error = &rows[receiving].observed.radius + &rows[3].forward.radius;
                    coordinates(&rows[receiving].observed.center)
                        .iter()
                        .zip(coordinates(&rows[3].forward.center))
                        .map(|(y, p)| ExactInterval::new(y - &p - &error, y - p + &error).unwrap())
                        .collect()
                }
            };
            // Every corner of the complete real/imaginary covector box.
            for mask in 0..16 {
                let r = intervals
                    .iter()
                    .enumerate()
                    .map(|(j, x)| {
                        if mask & (1 << j) == 0 {
                            x.lower.clone()
                        } else {
                            x.upper.clone()
                        }
                    })
                    .collect::<Vec<_>>();
                for (visible, values) in [
                    (true, result.visible_source.clone()),
                    (
                        false,
                        result
                            .outgoing_current
                            .iter()
                            .chain(&result.internal_current)
                            .cloned()
                            .collect(),
                    ),
                ] {
                    for (j, bound) in values.iter().enumerate() {
                        let exact = reference(&rows, 3, &r, visible, j);
                        if metric == NativeMaterialPullbackMetric::SquaredCurrent {
                            let real_only = r
                                .iter()
                                .enumerate()
                                .map(|(j, v)| if j % 2 == 0 { v.clone() } else { Rat::zero() })
                                .collect::<Vec<_>>();
                            let wrong = reference(&rows, 3, &real_only, visible, j);
                            phase_consequence |= wrong < bound.lower || wrong > bound.upper;
                        }
                        assert!(
                            bound.lower <= exact && exact <= bound.upper,
                            "metric {metric:?}, visible {visible}, coordinate {j}: {exact} outside {bound:?}"
                        );
                    }
                }
            }
            certified_internal |= result
                .internal_current
                .iter()
                .any(|x| x.lower > Rat::zero() || x.upper < Rat::zero());
            certified_visible |= result
                .visible_source
                .iter()
                .any(|x| x.lower > Rat::zero() || x.upper < Rat::zero());
            let foreign = make();
            assert!(matches!(
                foreign.pull_back_material_source(&normalized, metric),
                Err(ConstitutiveFibreError::ForeignOccurrence)
            ));
        }
    }
    assert!(
        phase_consequence,
        "the imaginary material return must have a separating source consequence"
    );
    assert!(certified_visible,"the visible query must return");
    assert!(certified_internal, "the full query must reach its internal argument");
}
