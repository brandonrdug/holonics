use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

fn material(nodes: usize) -> Vec<NativeJunctionSeed> {
    (0..nodes)
        .map(|_| NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        })
        .collect()
}
fn phase(a: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(a, 0, 1).unwrap()
}

#[test]
#[ignore = "requires CUDA; native contextual coefficients and old/current returned differences"]
fn transport_uses_the_retained_context_and_reconstructs_its_exact_coefficients() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(1),
        ResidentGrain(72),
    )
    .unwrap();
    field.enable_material_transport().unwrap();
    let before = field.census();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1)]))
        .unwrap();
    assert_eq!(field.census().section_read_outs, before.section_read_outs);
    let anchor = field.retain_source(&first.source).unwrap();
    let initial = field.inspect_material_transport(0).unwrap().unwrap();
    assert!(initial
        .forward
        .center
        .iter()
        .all(ExactComplexWaveCurrent::is_zero));
    assert_eq!(initial.forward.radius, Rat::zero());
    assert!(initial.returned_difference.is_none());
    let second = field
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![phase(1)],
        ))
        .unwrap();
    let one = field.inspect_exact_material_transport(1).unwrap().unwrap();
    assert_eq!(
        one.coefficients[0][1],
        ExactComplexWaveCurrent::new(Rat::new(1.into(), 2.into()), Rat::zero())
    );
    field
        .advance_resident(&mut NativeFieldOccurrence::through(
            second.source,
            vec![phase(2)],
        ))
        .unwrap();
    field
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![phase(3)],
        ))
        .unwrap();
    let reading = field.inspect_material_transport(3).unwrap().unwrap();
    let returned = &reading.returned_difference.as_ref().unwrap().center;
    let chronology = &reading.chronological_current.as_ref().unwrap().center;
    assert_eq!(
        subtract(returned, chronology),
        reading.contemporary_difference.as_ref().unwrap().center
    );
    assert!(chronology.iter().any(|x| !x.is_zero()));
    let exact = field.inspect_exact_material_transport(3).unwrap().unwrap();
    assert!(reading.forward.contains(&exact.forward));
    let residual = field
        .inspect_material_transport_residual(3)
        .unwrap()
        .unwrap();
    assert_eq!(residual.parameter_update.len(), 1);
    assert_eq!(residual.parameter_update[0].len(), 3);
}

#[test]
#[ignore = "requires CUDA; arithmetic refusal retains the coefficient owner and source"]
fn transport_refusal_keeps_coefficients_and_can_retry_the_actual_source() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(1),
        ResidentGrain(72),
    )
    .unwrap();
    field.enable_material_transport().unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(1)]))
        .unwrap();
    let before = field.inspect_material_transport_state().unwrap();
    let covariance = field.inspect_junction_covariance().unwrap();
    let mut incoming = NativeFieldOccurrence::through(first.source, vec![phase(i64::MAX)]);
    assert!(matches!(
        field.advance_resident(&mut incoming),
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    assert_eq!(field.occurrence_count(), 1);
    assert!(field.pending_lineage().is_none());
    assert_eq!(field.inspect_material_transport_state().unwrap(), before);
    assert_eq!(field.inspect_junction_covariance().unwrap(), covariance);
    field
        .advance_resident(&mut NativeFieldOccurrence::through(
            incoming.take_source().unwrap(),
            vec![phase(1)],
        ))
        .unwrap();
    assert_eq!(field.occurrence_count(), 2);
}

#[test]
#[ignore = "requires CUDA; equal raw endpoints retain different contextual transports"]
fn equal_raw_sources_with_distinct_contexts_form_different_native_transports() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut left = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(1),
        ResidentGrain(72),
    )
    .unwrap();
    let mut right = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(1),
        ResidentGrain(72),
    )
    .unwrap();
    left.enable_material_transport().unwrap();
    right.enable_material_transport().unwrap();
    let mut ls = None;
    let mut rs = None;
    let mut la = None;
    let mut ra = None;
    for (at, value) in [1, 2, 1, 1, 2].into_iter().enumerate() {
        let mut lo = match ls.take() {
            Some(s) => NativeFieldOccurrence::through(s, vec![phase(value)]),
            None => NativeFieldOccurrence::entering(vec![phase(value)]),
        };
        let mut ro = match rs.take() {
            Some(s) => NativeFieldOccurrence::through(s, vec![phase(value)]),
            None => NativeFieldOccurrence::entering(vec![phase(value)]),
        };
        let l = left.advance_resident(&mut lo).unwrap();
        let r = right.advance_resident(&mut ro).unwrap();
        if at == 1 {
            la = Some(left.retain_source(&l.source).unwrap());
        }
        if at == 4 {
            ra = Some(right.retain_source(&r.source).unwrap());
        }
        ls = Some(l.source);
        rs = Some(r.source);
    }
    let first = left.inspect_source(1).unwrap();
    let second = right.inspect_source(4).unwrap();
    assert_eq!(&first.intervals[..5], &second.intervals[..5]);
    assert_eq!(
        left.inspect_material_transport_state().unwrap(),
        right.inspect_material_transport_state().unwrap()
    );
    left.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        la.as_ref().unwrap(),
        vec![phase(3)],
    ))
    .unwrap();
    right
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            ra.as_ref().unwrap(),
            vec![phase(3)],
        ))
        .unwrap();
    // The old raw-source encoder cannot distinguish this parent choice; the new material
    // transport receives the distinct historical contextual fields and does distinguish it.
    assert_eq!(
        left.inspect_junction(5).unwrap(),
        right.inspect_junction(5).unwrap()
    );
    let a = left.inspect_material_transport_state().unwrap().unwrap();
    let b = right.inspect_material_transport_state().unwrap().unwrap();
    let distance = a
        .coefficients
        .iter()
        .zip(&b.coefficients)
        .flat_map(|(a, b)| a.iter().zip(b))
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum::<Rat>();
    assert!(distance > (&a.radius + &b.radius) * (&a.radius + &b.radius));
    let af=left.inspect_material_transport(5).unwrap().unwrap().forward;
    let bf=right.inspect_material_transport(5).unwrap().unwrap().forward;
    let distance=af.center.iter().zip(&bf.center).map(|(a,b)|a.subtract(b).norm_square()).sum::<Rat>();
    assert!(distance > (&af.radius+&bf.radius)*(&af.radius+&bf.radius));
}

#[test]
#[ignore = "requires CUDA; later transport normalization refusal does not commit the staged encoder"]
fn transport_failure_after_encoder_staging_preserves_the_whole_old_owner() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let nodes = 18;
    let mut encoder = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(nodes),
        ResidentGrain(120),
    )
    .unwrap();
    encoder
        .set_junction_solver(NativeFieldJunctionSolver::BalancedPairs)
        .unwrap();
    let first = encoder
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(2); nodes]))
        .unwrap();
    encoder
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![phase(1); nodes],
        ))
        .expect("the encoder itself completes");
    let mut body = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(nodes),
        ResidentGrain(120),
    )
    .unwrap();
    body.set_junction_solver(NativeFieldJunctionSolver::BalancedPairs)
        .unwrap();
    body.enable_material_transport().unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![phase(2); nodes]))
        .unwrap();
    let held = body.inspect_held().unwrap();
    let relation = body.inspect_relation().unwrap();
    let covariance = body.inspect_junction_covariance().unwrap();
    let transport = body.inspect_material_transport_state().unwrap();
    let mut next = NativeFieldOccurrence::through(first.source, vec![phase(1); nodes]);
    assert!(matches!(
        body.advance_resident(&mut next),
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    assert_eq!(body.occurrence_count(), 1);
    assert!(body.pending_lineage().is_none());
    assert_eq!(body.inspect_held().unwrap(), held);
    assert_eq!(body.inspect_relation().unwrap(), relation);
    assert_eq!(body.inspect_junction_covariance().unwrap(), covariance);
    assert_eq!(body.inspect_material_transport_state().unwrap(), transport);
    assert!(next.take_source().is_some());
}

#[test]
#[ignore = "requires CUDA; complex parameter adjoint and source-frame rechart preserve the root transport"]
fn complex_return_uses_the_conjugate_source_and_survives_rechart() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut plain = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(1),
        ResidentGrain(72),
    )
    .unwrap();
    let mut charted = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        material(1),
        ResidentGrain(72),
    )
    .unwrap();
    plain.enable_material_transport().unwrap();
    charted.enable_material_transport().unwrap();
    let p = NativePhaseCurrent::new(1, 1, 1).unwrap();
    let ps = plain
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![p]))
        .unwrap();
    let cs = charted
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![p]))
        .unwrap();
    charted
        .rechart(&[NativePhaseCurrent::new(0, 1, 1).unwrap()])
        .unwrap();
    let y = NativePhaseCurrent::new(-1, 2, 1).unwrap();
    plain
        .advance_resident(&mut NativeFieldOccurrence::through(ps.source, vec![y]))
        .unwrap();
    charted
        .advance_resident(&mut NativeFieldOccurrence::through(cs.source, vec![y]))
        .unwrap();
    assert_eq!(
        plain.inspect_material_transport_state().unwrap(),
        charted.inspect_material_transport_state().unwrap()
    );
    assert_eq!(
        plain.inspect_material_transport(1).unwrap(),
        charted.inspect_material_transport(1).unwrap()
    );
    let exact = charted
        .inspect_exact_material_transport(1)
        .unwrap()
        .unwrap();
    assert_eq!(
        exact.coefficients[0][1],
        ExactComplexWaveCurrent::new(Rat::new(1.into(), 3.into()), Rat::one())
    );
}
