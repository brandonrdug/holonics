use super::*;
use crate::{dimensional_wave::ExactComplexWaveCurrent, embedding_fiber::ResidentReadout};

fn phase(r: i64, i: i64, d: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, d).unwrap()
}
fn points<'c>(s: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            values.len(),
            ResidentGrain(0),
            64,
            values.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn current<'a, 'c>(s: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::integers(s).unwrap()
}
fn value(r: &ResidentConstitutiveReturn<'_>) -> ExactComplexWaveCurrent {
    match r.inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Unique { current } => {
            ExactComplexWaveCurrent::new(current[0].clone(), current[1].clone())
        }
        other => panic!("expected current: {other:?}"),
    }
}
fn world<'c>(s: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
    NativeConstitutiveField::found(
        s,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
    )
    .unwrap()
}
fn observe(
    world: &mut NativeConstitutiveField<'_>,
    source: NativePhaseCurrent,
    condition: NativePhaseCurrent,
) -> ExactComplexWaveCurrent {
    // An actual exterior intervention changes the native field's physical incidence. Its held
    // branch is measured; no source/condition multiplication supplies the teacher's answer here.
    world.replace_incoming_transport(0, condition).unwrap();
    world
        .advance_status(&mut NativeFieldOccurrence::entering(vec![source]))
        .unwrap()
        .held_successor[0]
        .clone()
}
fn calibrate<'c>(
    s: &'c ResidentSurface<'c>,
    body: &mut ResidentConstitutiveFibre<'c>,
    world: &mut NativeConstitutiveField<'c>,
    mut pooled: Option<&mut ResidentConstitutiveFibre<'c>>,
) {
    for (x, c) in [
        ([0, 0], [1, 0]),
        ([0, 0], [0, 1]),
        ([1, 0], [1, 0]),
        ([0, 1], [1, 0]),
        ([1, 0], [-1, 0]),
        ([0, 1], [-1, 0]),
    ] {
        let measured = observe(world, phase(x[0], x[1], 1), phase(c[0], c[1], 1));
        let words = NativePhaseCurrent::from_current(&measured).unwrap().words();
        let xs = points(s, &x);
        let cs = points(s, &c);
        let ys = points(s, &words);
        let before = body.census();
        body.advance_bilinear_contact(
            current(&xs),
            current(&cs),
            Some(ResidentConstitutiveCurrent::rational(&ys).unwrap()),
        )
        .unwrap();
        assert_eq!(body.census().section_read_outs, before.section_read_outs);
        assert_eq!(
            body.census().ingress_octets - before.ingress_octets,
            std::mem::size_of::<u32>() as u64
        );
        if let Some(pooled) = pooled.as_deref_mut() {
            pooled
                .advance_resident(
                    current(&xs),
                    Some(ResidentConstitutiveCurrent::rational(&ys).unwrap()),
                )
                .unwrap();
        }
    }
}

#[test]
#[ignore = "requires CUDA; measured native conditions recover a reusable phase action"]
fn independently_measured_condition_resolves_the_pooled_local_relation() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    let mut pooled = ResidentConstitutiveFibre::found(&s, 2, 2).unwrap();
    calibrate(&s, &mut body, &mut w, Some(&mut pooled));
    assert!(matches!(
        pooled.advance(&[1, 0], None).unwrap().predecessor_reading,
        ConstitutiveReading::Plural { .. }
    ));
    let x = points(&s, &[2, 3]);
    let c = points(&s, &[3, 4, 5]);
    let before = body.census();
    let predicted = body
        .advance_bilinear_contact(
            current(&x),
            ResidentConstitutiveCurrent::rational(&c).unwrap(),
            None,
        )
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(
        predicted.source_chart(),
        ConstitutiveSourceChart::BilinearContact {
            source_complex: 1,
            condition_complex: 1
        }
    );
    // The withheld physical return is obtained only after native prediction.
    let actual = observe(&mut w, phase(2, 3, 1), phase(3, 4, 5));
    assert_eq!(value(&predicted), actual);
    assert_eq!(
        actual,
        ExactComplexWaveCurrent::new(
            Rat::new((-6).into(), 5.into()),
            Rat::new(17.into(), 5.into())
        )
    );
}

#[test]
#[ignore = "requires CUDA; recovered phase action drives successive resident wave currents"]
fn emitted_current_rides_the_learned_conditional_action() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let start = points(&s, &[1, 0]);
    let condition = points(&s, &[3, 4, 5]);
    let condition = ResidentConstitutiveCurrent::rational(&condition).unwrap();
    let before = body.census();
    let first = body
        .advance_bilinear_contact(current(&start), condition, None)
        .unwrap();
    let second = body
        .advance_bilinear_contact(first.current(), condition, None)
        .unwrap();
    let third = body
        .advance_bilinear_contact(second.current(), condition, None)
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(
        body.census().ingress_octets - before.ingress_octets,
        3 * std::mem::size_of::<u32>() as u64
    );
    assert_eq!(value(&first), phase(3, 4, 5).current());
    assert_eq!(value(&second), phase(-7, 24, 25).current());
    assert_eq!(value(&third), phase(-117, 44, 125).current());
    for emitted in [&first, &second, &third] {
        assert_eq!(value(emitted).norm_square(), Rat::from_integer(1.into()));
    }
}

#[test]
#[ignore = "requires CUDA; simultaneous port changes retain the mixed finite difference"]
fn the_learned_joint_return_is_not_the_sum_of_two_separate_changes() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let x0 = points(&s, &[1, 0]);
    let x1 = points(&s, &[1, 1]);
    let c0 = points(&s, &[1, 0]);
    let c1 = points(&s, &[0, 1]);
    let base = body
        .advance_bilinear_contact(current(&x0), current(&c0), None)
        .unwrap();
    let dx = body
        .advance_bilinear_contact(current(&x1), current(&c0), None)
        .unwrap();
    let dc = body
        .advance_bilinear_contact(current(&x0), current(&c1), None)
        .unwrap();
    let both = body
        .advance_bilinear_contact(current(&x1), current(&c1), None)
        .unwrap();
    let mixed = value(&both)
        .subtract(&value(&dx))
        .subtract(&value(&dc))
        .add(&value(&base));
    assert_eq!(mixed, phase(-1, -1, 1).current());
    assert_ne!(
        value(&both),
        value(&dx).add(&value(&dc)).subtract(&value(&base))
    );
}

#[test]
#[ignore = "requires CUDA; contact chart and refusal preserve one continuing relation"]
fn contact_shape_and_late_refusal_cannot_deposit_or_bypass_the_source_law() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    assert!(body.advance(&[1, 0, 0, 0, 0, 0], Some(&[1, 0])).is_err());
    let forged = points(&s, &[1, 0, 0, 0, 0, 0]);
    assert!(body.advance_resident(current(&forged), None).is_err());
    let x = points(&s, &[i64::MAX, 1]);
    let c = points(&s, &[i64::MAX, 1]);
    let y = points(&s, &[1, 0]);
    let before = body.inspect_relation().unwrap();
    assert!(
        body.advance_bilinear_contact(current(&x), current(&c), Some(current(&y)))
            .is_err()
    );
    assert_eq!(body.inspect_relation().unwrap(), before);
    assert_eq!(body.occurrences(), 0);
    let x = points(&s, &[1, 0]);
    let c = points(&s, &[0, 1]);
    let bad = points(&s, &[1, 0, -1]);
    assert!(
        body.advance_bilinear_contact(
            current(&x),
            current(&c),
            Some(ResidentConstitutiveCurrent::rational(&bad).unwrap())
        )
        .is_err()
    );
    assert_eq!(body.inspect_relation().unwrap(), before);
    assert_eq!(body.occurrences(), 0);
    body.advance_bilinear_contact(current(&x), current(&c), Some(current(&y)))
        .unwrap();
    assert_eq!(body.occurrences(), 1);
}

#[test]
#[ignore = "requires CUDA; every mixed complex incidence and rational denominator crosses"]
fn multiple_ports_keep_all_mixed_terms_and_the_declared_axis_roles() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 2, 2, 1).unwrap();
    let x = points(&s, &[1, 1, 2, -1, 2]);
    let c = points(&s, &[-1, 2, 3, 1, 3]);
    let y = points(&s, &[11, -7, 5]);
    body.advance_bilinear_contact(
        ResidentConstitutiveCurrent::rational(&x).unwrap(),
        ResidentConstitutiveCurrent::rational(&c).unwrap(),
        Some(ResidentConstitutiveCurrent::rational(&y).unwrap()),
    )
    .unwrap();
    // Independent Gaussian-rational products, then a common denominator of thirty with y.
    let numerator = [3, 3, 6, -3, -2, 4, 6, 2, -3, 1, 0, 5, 2, 4, 7, -1];
    let expected = numerator
        .into_iter()
        .map(|v| v * 5)
        .chain([66, -42])
        .collect::<Vec<i64>>();
    let basis = body.inspect_relation().unwrap();
    assert_eq!(
        basis.intervals[..18],
        expected.iter().map(|v| (*v, *v)).collect::<Vec<_>>()
    );
    let mut roles = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 3, 1).unwrap();
    let swapped_source = points(&s, &[1, 0, 2, 0, 3, 0]);
    let swapped_condition = points(&s, &[1, 0]);
    assert!(
        roles
            .advance_bilinear_contact(current(&swapped_source), current(&swapped_condition), None)
            .is_err()
    );
    assert_eq!(roles.occurrences(), 0);
}
