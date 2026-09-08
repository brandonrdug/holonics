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
                .zip(r)
                .map(|((a, b), r)| {
                    if reflected {
                        -&b.real * r
                    } else {
                        (&a.real + &b.real) * r
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
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let make = || {
        let mut f = NativeConstitutiveField::found_with_enclosed_junction(
            &surface,
            seed(2),
            ResidentGrain(72),
        )
        .unwrap();
        f.enable_material_transport_source(NativeMaterialTransportSource::OperativeContextual)
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
        ] {
            let before = field.census();
            let resident = field
                .pull_back_material_source(&normalized, metric)
                .unwrap();
            assert_eq!(field.census().section_read_outs, before.section_read_outs);
            let result = resident.inspect().unwrap();
            assert_eq!(result.source.occurrence, 3);
            assert_eq!(result.receiving.occurrence, receiving);
            let intervals = match metric {
                NativeMaterialPullbackMetric::RelativeEntropy => &q.returned_difference,
                NativeMaterialPullbackMetric::SquaredProbability => &q.potential_pullback,
            };
            // Every corner of the two-dimensional covector box, not just its centre.
            for mask in 0..4 {
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
        certified_internal && certified_visible,
        "both query arguments must return nonzero conduct"
    );
}
