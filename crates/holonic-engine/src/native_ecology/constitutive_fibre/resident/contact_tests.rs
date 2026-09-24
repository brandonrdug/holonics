//! Shared measured-world fixtures for the resident parity tests; this module holds no tests.
use super::*;
use crate::dimensional_wave::ExactComplexWaveCurrent;

pub(super) fn phase(r: i64, i: i64, d: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, d).unwrap()
}
pub(super) fn points<'c>(s: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
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
pub(super) fn current<'a, 'c>(s: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::integers(s).unwrap()
}
pub(super) fn value(r: &ResidentConstitutiveReturn<'_>) -> ExactComplexWaveCurrent {
    match r.inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Unique { current } => {
            ExactComplexWaveCurrent::new(current[0].clone(), current[1].clone())
        }
        other => panic!("expected current: {other:?}"),
    }
}
pub(super) fn world<'c>(s: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
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
pub(super) fn observe(
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
pub(super) fn calibrate<'c>(
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
