use super::*;
use crate::embedding_fiber::ResidentReadout;
fn point<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            v.len(),
            ResidentGrain(0),
            64,
            v.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn value(r: &ResidentConstitutiveReturn<'_>) -> Vec<Rat> {
    let ConstitutiveReading::Unique { current } = r.inspect().unwrap().predecessor_reading else {
        panic!("expected supported point")
    };
    current
}

#[test]
#[ignore = "requires CUDA; an actual bounded context contrast becomes native generative current and changes the same field successor"]
fn captured_context_ray_contacts_and_reenters_the_same_ecology() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let seed = vec![NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    }];
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seed, ResidentGrain(72)).unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::HomogeneousMoment)
        .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
        ]))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        &anchor,
        vec![NativePhaseCurrent::new(0, 1, 1).unwrap()],
    ))
    .unwrap();
    let last = body
        .advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![NativePhaseCurrent::new(-1, 0, 1).unwrap()],
        ))
        .unwrap();
    let two = point(&s, &[2, 0]);
    let imaginary = point(&s, &[0, 1]);
    let before = body.census();
    let section = body.derive_contextual_contrast([1, 2]).unwrap();
    let mut current = section
        .retain_condition_current(
            section.zero_change(),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
    let family = section
        .preimage_absolute(section.second_observed_return().unwrap())
        .unwrap();
    let contact = current.contact(&family).unwrap();
    let recalled = section.read_absolute(current.current()).unwrap();
    let generated = section
        .read_absolute(ResidentConstitutiveCurrent::integers(&two).unwrap())
        .unwrap();
    let mut occurrence = NativeFieldOccurrence::through(last.source, vec![]);
    let next = body
        .advance_current_resident(&mut occurrence, generated.current())
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(body.occurrence_count(), 4);
    assert_eq!(next.lineage.received_from, Some(2));
    assert!(matches!(
        next.lineage.incoming,
        NativeFieldIncoming::Resident { resident_nodes: 1 }
    ));
    assert_eq!(
        body.inspect_incoming(3).unwrap(),
        vec![NativePhaseCurrent::new(-2, -1, 1).unwrap()]
    );
    assert_eq!(
        value(&generated),
        vec![
            Rat::from_integer((-2).into()),
            Rat::from_integer((-1).into())
        ]
    );
    assert_eq!(
        value(&recalled),
        vec![Rat::from_integer((-1).into()), Rat::from_integer(0.into())]
    );
    assert_eq!(
        contact.inspect().unwrap().successor,
        vec![Rat::from_integer(1.into()), Rat::from_integer(0.into())]
    );
    let outside = section
        .read_absolute(ResidentConstitutiveCurrent::integers(&imaginary).unwrap())
        .unwrap();
    assert!(matches!(
        outside.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    let before = body.rest(&[Some(&next.source)], &[]).unwrap();
    assert!(body.derive_contextual_contrast([1, 3]).is_err());
    assert_eq!(body.rest(&[Some(&next.source)], &[]).unwrap(), before);
    drop(body);
    assert_eq!(
        value(
            &section
                .read_absolute(ResidentConstitutiveCurrent::integers(&two).unwrap())
                .unwrap()
        ),
        value(&generated)
    );
}
