use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::SeriesAperture;

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
        2
    ];
    let mut f =
        NativeConstitutiveField::found_with_enclosed_junction(s, seeds, ResidentGrain(72)).unwrap();
    f.enable_material_transport_source(NativeMaterialTransportSource::OperativeNormal)
        .unwrap();
    f
}
fn transpose(
    m: &[Vec<ExactComplexWaveCurrent>],
    r: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    (0..m[0].len())
        .map(|j| {
            m.iter()
                .zip(r)
                .fold(ExactComplexWaveCurrent::zero(), |a, (m, r)| {
                    a.add(&m[j].conjugate().multiply(r))
                })
        })
        .collect()
}
fn contains(error: &Rat, a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) {
    let square: Rat = a
        .iter()
        .zip(b)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    assert!(
        square <= error * error,
        "normal error {square} exceeds {}",
        error * error
    );
}

#[test]
#[ignore = "requires CUDA; exact accumulated normal statistics, material fit, historical adjoint and restart"]
fn normal_material_retains_geometry_and_reconstructs_its_producing_operator() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut f = make(&surface);
    let inputs = [
        vec![phase(1, 1, 3), phase(2, -1, 5)],
        vec![phase(0, 1, 1), phase(1, 0, 2)],
        vec![phase(-1, 0, 3), phase(0, 1, 2)],
        vec![phase(1, 0, 1), phase(0, -1, 1)],
    ];
    let mut last = None;
    let mut anchor = None;
    let mut xs = Vec::<Vec<ExactComplexWaveCurrent>>::new();
    let mut h = vec![vec![ExactComplexWaveCurrent::zero(); 6]; 6];
    for i in 0..6 {
        h[i][i] = ExactComplexWaveCurrent::one();
    }
    let mut b = vec![vec![ExactComplexWaveCurrent::zero(); 6]; 2];
    let mut cy = Rat::zero();
    let mut original = None;
    for (at, input) in inputs.into_iter().enumerate() {
        let x = at.checked_sub(1).map(|source| {
            f.inspect_operative_reflection(source)
                .unwrap()
                .unwrap()
                .outgoing
                .center
        });
        let mut event = if let Some(source) = last.take() {
            NativeFieldOccurrence::through(source, input)
        } else {
            NativeFieldOccurrence::entering(input)
        };
        let before = f.census();
        let next = f.advance_resident(&mut event).unwrap();
        assert_eq!(f.census().section_read_outs, before.section_read_outs);
        if at == 1 {
            anchor = Some(f.retain_source(&next.source).unwrap());
        }
        last = Some(next.source);
        let report = f.inspect_normal_material_transport(at).unwrap().unwrap();
        if let Some(x) = x {
            for i in 0..6 {
                for j in 0..6 {
                    h[i][j] = h[i][j].add(&x[i].multiply(&x[j].conjugate()));
                }
            }
            for i in 0..2 {
                for j in 0..6 {
                    b[i][j] = b[i][j].add(&report.observed.center[i].multiply(&x[j].conjugate()));
                }
            }
            cy += report
                .observed
                .center
                .iter()
                .map(ExactComplexWaveCurrent::norm_square)
                .sum::<Rat>();
            xs.push(x);
        }
        let state = f.inspect_normal_material_state().unwrap();
        assert_eq!(state.source_normal, h);
        assert_eq!(state.cross_source, b);
        assert_eq!(state.target_energy, cy);
        let residual: Rat = state.normal_residual().unwrap().iter().flatten().map(|v|v.real.abs()+v.imaginary.abs()).sum();
        assert!(residual <= state.normal_residual_upper);
        // The existing exact paired inverse supplies H^-1 B* in its smaller contact chart.
        let mut exact = vec![];
        for row in &b {
            let rhs = row
                .iter()
                .map(|v| v.conjugate().scaled(&Rat::new(1.into(), 2.into())))
                .collect::<Vec<_>>();
            let solved = PairedJunctionLinearization::at(
                xs.clone(),
                &rhs,
                &vec![ExactComplexWaveCurrent::zero(); xs.len()],
            )
            .unwrap();
            exact.extend(
                solved
                    .potential()
                    .iter()
                    .map(ExactComplexWaveCurrent::conjugate),
            );
        }
        contains(
            &state.material.radius,
            &state
                .material
                .coefficients
                .iter()
                .flatten()
                .cloned()
                .collect::<Vec<_>>(),
            &exact,
        );
        assert!(state.material.radius < Rat::new(1.into(), 1_000_000.into()));
        if at == 1 {
            original = Some((state.material.coefficients, report.forward));
        }
        if at == 2 {
            let q = f.pull_back_material_current(at).unwrap().unwrap();
            let r = f.material_contact_response(q).unwrap();
            f.apply_material_contact_realization(&r, NativeContactRealization::DyadicDeposit)
                .unwrap();
        }
    }
    let saved = f.rest(&[last.as_ref()], &[anchor.as_ref()]).unwrap();
    let mut bytes = vec![];
    saved.write(&mut bytes).unwrap();
    let final_input = vec![phase(1, -1, 2), phase(1, 2, 3)];
    let next = f
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            anchor.as_ref().unwrap(),
            final_input.clone(),
        ))
        .unwrap();
    let at = next.lineage.occurrence;
    let report = f.inspect_normal_material_transport(at).unwrap().unwrap();
    let (old, forward) = original.unwrap();
    let r = report
        .observed
        .center
        .iter()
        .zip(&forward.center)
        .map(|(a, b)| a.subtract(b))
        .collect::<Vec<_>>();
    let expected = transpose(&old, &r);
    let q = f.pull_back_material_current(at).unwrap().unwrap();
    let read = q.inspect().unwrap();
    for (x, interval) in expected
        .iter()
        .flat_map(|v| [&v.real, &v.imaginary])
        .zip(&read.outgoing_current)
    {
        assert!(*x >= interval.lower && *x <= interval.upper);
    }
    assert!(
        read.visible_source
            .iter()
            .chain(&read.internal_current)
            .all(|v| v.lower.is_zero() && v.upper.is_zero())
    );
    let response = f.material_contact_response(q).unwrap();
    f.apply_material_contact_realization(&response, NativeContactRealization::DyadicDeposit)
        .unwrap();
    let expected = f.rest(&[Some(&next.source)], &[anchor.as_ref()]).unwrap();
    drop(response);
    drop(next);
    drop(last);
    drop(anchor);
    drop(f);
    let saved = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let (mut f, _, anchors) = NativeConstitutiveField::remount(&surface, saved).unwrap();
    let next = f
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            anchors[0].as_ref().unwrap(),
            final_input,
        ))
        .unwrap();
    let normalized = f
        .normalized_material_return(next.lineage.occurrence, 2, SeriesAperture(32))
        .unwrap()
        .unwrap();
    let q = f
        .pull_back_material_source(&normalized, NativeMaterialPullbackMetric::SquaredCurrent)
        .unwrap();
    let response = f.material_contact_response(q).unwrap();
    f.apply_material_contact_realization(&response, NativeContactRealization::DyadicDeposit)
        .unwrap();
    assert_eq!(
        f.rest(&[Some(&next.source)], &[anchors[0].as_ref()])
            .unwrap(),
        expected
    );
}

#[test]
#[ignore = "requires CUDA; normal material has an independent joint target and complete complex return"]
fn normal_material_joint_target_keeps_phase_and_native_return() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
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
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seeds, ResidentGrain(72))
            .unwrap();
    f.enable_material_transport_chart(
        NativeMaterialTransportSource::OperativeNormal,
        NativeMaterialTarget::TensorProduct { factor_width: 2 },
    )
    .unwrap();
    let input = |word: usize, imaginary: bool| {
        (0..6)
            .map(|i| {
                if ((word >> (i / 2)) & 1) == i % 2 {
                    if imaginary && i / 2 == 0 {
                        phase(0, 1, 1)
                    } else {
                        phase(1, 0, 1)
                    }
                } else {
                    phase(0, 0, 1)
                }
            })
            .collect()
    };
    let mut last = None;
    for (at, (word, imaginary)) in [(2, false), (5, false), (7, true)].into_iter().enumerate() {
        let mut event = match last.take() {
            Some(source) => NativeFieldOccurrence::through(source, input(word, imaginary)),
            None => NativeFieldOccurrence::entering(input(word, imaginary)),
        };
        let next = f.advance_resident(&mut event).unwrap();
        last = Some(next.source);
        let report = f.inspect_normal_material_transport(at).unwrap().unwrap();
        assert_eq!(report.forward.center.len(), 8);
        assert_eq!(
            report.observed.center[word],
            if imaginary {
                ExactComplexWaveCurrent::new(Rat::zero(), Rat::one())
            } else {
                ExactComplexWaveCurrent::one()
            }
        );
        if at > 0 {
            let q = f.pull_back_material_current(at).unwrap().unwrap();
            assert_eq!(q.inspect().unwrap().outgoing_current.len(), 36);
            let r = f.material_contact_response(q).unwrap();
            f.apply_material_contact_realization(&r, NativeContactRealization::DyadicDeposit)
                .unwrap();
        }
    }
    let state = f.inspect_normal_material_state().unwrap();
    assert_eq!(state.material.coefficients.len(), 8);
    assert_eq!(state.source_normal.len(), 18);
    let report = f
        .read_material_packet_quadrature(2, NativePacketQuadrature::Imaginary)
        .unwrap()
        .unwrap();
    assert_eq!(report.target_dimension, 8);
    let rest = f.rest(&[last.as_ref()], &[]).unwrap();
    drop(last);
    drop(f);
    let (f, _, _) = NativeConstitutiveField::remount(&surface, rest).unwrap();
    assert_eq!(
        serde_json::to_value(f.inspect_normal_material_state().unwrap()).unwrap(),
        serde_json::to_value(state).unwrap()
    );
}
