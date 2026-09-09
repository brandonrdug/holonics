use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::SeriesAperture;
use num_traits::Zero;
fn phase(r: i64, i: i64, d: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, d).unwrap()
}
fn make<'c>(s: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
    let seeds = vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: phase(1, 0, 1),
            initial_held: phase(0, 0, 1)
        };
        6
    ];
    let mut f =
        NativeConstitutiveField::found_with_enclosed_junction(s, seeds, ResidentGrain(72)).unwrap();
    f.enable_material_transport_chart(
        NativeMaterialTransportSource::OperativeLinear,
        NativeMaterialTarget::TensorProduct { factor_width: 2 },
    )
    .unwrap();
    f
}
fn current(f: &NativeConstitutiveField<'_>, at: usize) -> Vec<ExactComplexWaveCurrent> {
    let words = wides(&f.inspect_junction(at).unwrap().unwrap().intervals).unwrap();
    let d = 6 * f.nodes();
    let scale = BigInt::one() << 72usize;
    words[d + 1..2 * d + 1]
        .chunks_exact(2)
        .map(|v| {
            ExactComplexWaveCurrent::new(
                Rat::new(v[0].into(), scale.clone()),
                Rat::new(v[1].into(), scale.clone()),
            )
        })
        .collect()
}
fn transpose(
    matrix: &[Vec<ExactComplexWaveCurrent>],
    r: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    (0..matrix[0].len())
        .map(|j| {
            matrix
                .iter()
                .zip(r)
                .fold(ExactComplexWaveCurrent::zero(), |v, (m, r)| {
                    v.add(&m[j].conjugate().multiply(r))
                })
        })
        .collect()
}
#[test]
#[ignore = "requires CUDA; finite operator, tensor phase, historical adjoint, development and restart"]
fn operative_linear_material_has_a_bounded_operator_and_the_producing_return() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut f = make(&surface);
    let archive = std::env::temp_dir().join(format!(
        "holonics-linear-history-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    f.enable_history_archive(&archive).unwrap();
    let inputs = [
        vec![
            phase(1, 1, 3),
            phase(0, 1, 1),
            phase(1, 0, 1),
            phase(1, 1, 1),
            phase(1, -1, 1),
            phase(0, 0, 1),
        ],
        vec![
            phase(1, 0, 1),
            phase(0, 0, 1),
            phase(0, 0, 1),
            phase(0, 1, 1),
            phase(1, 0, 1),
            phase(0, 0, 1),
        ],
        vec![
            phase(0, 0, 1),
            phase(0, 1, 1),
            phase(1, 0, 1),
            phase(0, 0, 1),
            phase(1, 0, 1),
            phase(0, 0, 1),
        ],
        vec![
            phase(1, 0, 1),
            phase(0, 0, 1),
            phase(1, 0, 1),
            phase(0, 0, 1),
            phase(0, 0, 1),
            phase(0, 1, 1),
        ],
        vec![
            phase(0, 0, 1),
            phase(1, 0, 1),
            phase(0, 0, 1),
            phase(1, 0, 1),
            phase(0, 0, 1),
            phase(1, 0, 1),
        ],
    ];
    let mut previous = None;
    let mut anchor = None;
    let mut waves: Vec<Vec<ExactComplexWaveCurrent>> = vec![];
    let mut matrices = vec![];
    let mut exact = zeros(8, 18);
    for (at, input) in inputs.into_iter().enumerate() {
        let source = if at == 4 { Some(1) } else { at.checked_sub(1) };
        let observed = (0..8)
            .map(|word| {
                (0..3).fold(ExactComplexWaveCurrent::one(), |v, j| {
                    v.multiply(&input[2 * j + ((word >> j) & 1)].current())
                })
            })
            .collect::<Vec<_>>();
        let mut event = if at == 4 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), input)
        } else if let Some(old) = previous.take() {
            NativeFieldOccurrence::through(old, input)
        } else {
            NativeFieldOccurrence::entering(input)
        };
        let before = f.census();
        let next = f.advance_resident(&mut event).unwrap();
        assert_eq!(f.census().section_read_outs, before.section_read_outs);
        if at == 1 {
            anchor = Some(f.retain_source(&next.source).unwrap());
        }
        previous = Some(next.source);
        if let Some(source) = source {
            let delta = exact_delta(&exact, &waves[source], &observed);
            add_matrix(&mut exact, &delta);
        }
        waves.push(current(&f, at));
        let state = f.inspect_material_transport_state().unwrap().unwrap();
        assert_eq!(
            (state.coefficients.len(), state.coefficients[0].len()),
            (8, 18)
        );
        let error: Rat = state
            .coefficients
            .iter()
            .flatten()
            .zip(exact.iter().flatten())
            .map(|(a, b)| a.subtract(b).norm_square())
            .sum();
        assert!(
            error <= &state.radius * &state.radius,
            "operator defect must enclose exact coercive updates"
        );
        let report = f.inspect_material_transport(at).unwrap().unwrap();
        assert!(report.forward.contains(&apply(&exact, &waves[at])));
        assert!(report.observed.contains(&observed));
        let signs = f.read_material_transport_pairs(at, 4).unwrap().unwrap();
        for (pair, values) in report.forward.center.chunks_exact(2).enumerate() {
            let difference = &values[1].real - &values[0].real;
            let mask = 1u64 << pair;
            if &difference * &difference
                > Rat::from_integer(2.into()) * &report.forward.radius * &report.forward.radius
            {
                assert_ne!(
                    if difference > Rat::zero() {
                        signs.positive
                    } else {
                        signs.negative
                    } & mask,
                    0
                );
            } else {
                assert_ne!(signs.unresolved & mask, 0);
            }
        }
        matrices.push(state.coefficients);
    }
    let report = f.inspect_material_transport(4).unwrap().unwrap();
    let source_report = f.inspect_material_transport(1).unwrap().unwrap();
    let r = subtract(&report.observed.center, &source_report.forward.center);
    let expected = transpose(&matrices[1], &r);
    let wrong = transpose(&matrices[4], &r);
    f.archive_history_before(4).unwrap();
    let before = f.census();
    let query = f.pull_back_material_current(4).unwrap().unwrap();
    assert_eq!(f.census().section_read_outs, before.section_read_outs);
    let read = query.inspect().unwrap();
    assert_eq!(read.source.occurrence, 1);
    assert!(
        read.visible_source
            .iter()
            .chain(&read.internal_current)
            .all(|v| v.lower.is_zero() && v.upper.is_zero())
    );
    let components = |v: &[ExactComplexWaveCurrent]| {
        v.iter()
            .flat_map(|z| [z.real.clone(), z.imaginary.clone()])
            .collect::<Vec<_>>()
    };
    let expected = components(&expected);
    let wrong = components(&wrong);
    assert!(
        read.outgoing_current
            .iter()
            .zip(&expected)
            .all(|(a, x)| a.lower <= *x && *x <= a.upper)
    );
    assert!(
        read.outgoing_current
            .iter()
            .zip(&wrong)
            .any(|(a, x)| *x < a.lower || *x > a.upper),
        "today's matrix must not replace the producer"
    );
    let normalized = f
        .normalized_material_return(4, 8, SeriesAperture(32))
        .unwrap()
        .unwrap();
    for metric in [
        NativeMaterialPullbackMetric::RelativeEntropy,
        NativeMaterialPullbackMetric::SquaredProbability,
    ] {
        let result = f
            .pull_back_material_source(&normalized, metric)
            .unwrap()
            .inspect()
            .unwrap();
        assert_eq!(result.source.occurrence, 1);
        assert!(
            result
                .internal_current
                .iter()
                .all(|v| v.lower.is_zero() && v.upper.is_zero())
        );
    }
    let response = f.material_contact_response(query).unwrap();
    f.apply_material_contact_realization(&response, NativeContactRealization::DyadicDeposit)
        .unwrap();
    let saved = f.rest(&[previous.as_ref()], &[anchor.as_ref()]).unwrap();
    let mut bytes = vec![];
    saved.write(&mut bytes).unwrap();
    let saved = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let incoming = vec![phase(1, 0, 1); 6];
    let next = f
        .advance_resident(&mut NativeFieldOccurrence::through(
            previous.take().unwrap(),
            incoming.clone(),
        ))
        .unwrap();
    let expected = f.rest(&[Some(&next.source)], &[]).unwrap();
    drop(response);
    drop(f);
    let (mut f, mut sources, _) = NativeConstitutiveField::remount(&surface, saved).unwrap();
    let next = f
        .advance_resident(&mut NativeFieldOccurrence::through(
            sources[0].take().unwrap(),
            incoming,
        ))
        .unwrap();
    assert_eq!(f.rest(&[Some(&next.source)], &[]).unwrap(), expected);
    std::fs::remove_file(archive).unwrap();
}
