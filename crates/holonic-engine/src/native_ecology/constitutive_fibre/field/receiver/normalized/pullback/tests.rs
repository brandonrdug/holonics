use super::super::tests::{phase, seed};
use super::*;
use crate::embedding_fiber::ResidentReadout;

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

#[test]
#[ignore = "requires CUDA; actual producing factors against independent exact quotient derivatives"]
fn material_source_pullback_keeps_both_arguments_and_the_producing_cut() {
    check_pullback(NativeMaterialTransportSource::OperativeContextual);
}
#[test]
#[ignore="requires CUDA; outgoing receiver projection and complete producing contact adjoint"]
fn operative_boundary_source_returns_through_the_retained_interior(){
    check_pullback(NativeMaterialTransportSource::OperativeBoundary);
}
fn check_pullback(source_kind:NativeMaterialTransportSource){
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
    if source_kind==NativeMaterialTransportSource::OperativeBoundary {
        let before=field.stage_operative_contacts().unwrap().inspect().unwrap();
        assert!(!before.internal.center.is_empty());
        assert!(before.internal.center.iter().any(|z|!z.norm_square().is_zero()));
        let query=field.pull_back_material_current(5).unwrap().unwrap();
        assert!(query.inspect().unwrap().internal_current.iter().all(|v|v.lower.is_zero() && v.upper.is_zero()));
        let response=field.material_contact_response(query).unwrap();
        let reaction=response.inspect().unwrap();
        assert!(!reaction.incoming_internal.center.is_empty());
        assert!(reaction.incoming_internal.center.iter().any(|z|!z.norm_square().is_zero()));
        field.apply_material_contact_realization(&response,NativeContactRealization::DyadicDeposit).unwrap();
        let after=field.stage_operative_contacts().unwrap().inspect().unwrap();
        assert_ne!(before.contacts,after.contacts);
        let saved=field.rest(&[previous.as_ref()],&[]).unwrap();
        let mut bytes=vec![];saved.write(&mut bytes).unwrap();
        let saved=NativeFieldRest::read(&mut bytes.as_slice(),bytes.len() as u64).unwrap();
        assert_eq!(saved.material_transport_source(),Some(source_kind));
        let expected=field.advance_resident(&mut NativeFieldOccurrence::through(previous.take().unwrap(),vec![phase(1,-1),phase(0,1)])).unwrap();
        let expected=field.rest(&[Some(&expected.source)],&[]).unwrap();
        drop(response);drop(field);
        let (mut field,mut sources,_)=NativeConstitutiveField::remount(&surface,saved).unwrap();
        let next=field.advance_resident(&mut NativeFieldOccurrence::through(sources[0].take().unwrap(),vec![phase(1,-1),phase(0,1)])).unwrap();
        assert_eq!(field.rest(&[Some(&next.source)],&[]).unwrap(),expected);
    } else {assert!(certified_internal,"the full query must reach its internal argument");}
}

#[test]
#[ignore = "requires CUDA; a zero observed tensor packet is in the current metric domain"]
fn material_current_pullback_accepts_zero_observation_without_a_probability_face() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(2), ResidentGrain(72))
            .unwrap();
    field
        .enable_material_transport_chart(
            NativeMaterialTransportSource::OperativeContextual,
            NativeMaterialTarget::TensorProduct { factor_width: 2 },
        )
        .unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            phase(1, 1),
            phase(1, 0),
        ]))
        .unwrap();
    assert!(field.pull_back_material_current(0).unwrap().is_none());
    let second = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![phase(0, 1), phase(1, 1)],
        ))
        .unwrap();
    let third = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            second.source,
            vec![phase(0, 0), phase(0, 0)],
        ))
        .unwrap();
    assert!(
        field
            .normalized_material_return(2, 2, SeriesAperture(32))
            .is_err()
    );
    let before = field.census();
    let pulled = field.pull_back_material_current(2).unwrap().unwrap();
    assert_eq!(field.census().section_read_outs, before.section_read_outs);
    let reading = pulled.inspect().unwrap();
    assert_eq!(reading.metric, NativeMaterialPullbackMetric::SquaredCurrent);
    assert_eq!((reading.group_width, reading.series_terms), (0, 0));
    let response = field.material_contact_response(pulled).unwrap();
    field
        .apply_material_contact_realization(&response, NativeContactRealization::DyadicDeposit)
        .unwrap();
    assert_eq!(field.operative_return_count(), Some(1));
    let saved = field.rest(&[Some(&third.source)], &[]).unwrap();
    let next = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            third.source,
            vec![phase(1, 0), phase(0, -1)],
        ))
        .unwrap();
    let expected = field.rest(&[Some(&next.source)], &[]).unwrap();
    drop(response);
    drop(field);
    let (mut field, mut sources, _) = NativeConstitutiveField::remount(&surface, saved).unwrap();
    let next = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            sources[0].take().unwrap(),
            vec![phase(1, 0), phase(0, -1)],
        ))
        .unwrap();
    assert_eq!(field.rest(&[Some(&next.source)], &[]).unwrap(), expected);
}
