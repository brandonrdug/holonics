use super::super::contact_tests::{calibrate, current, phase, points, world};
use super::*;
use crate::embedding_fiber::ResidentReadout;

fn relation<'c>(
    s: &'c ResidentSurface<'c>,
    source: usize,
    target: usize,
    observations: &[(&[i64], &[i64])],
) -> ResidentConstitutiveFibre<'c> {
    let mut law = ResidentConstitutiveFibre::found(s, source, target).unwrap();
    for (x, y) in observations {
        law.advance(x, Some(y)).unwrap();
    }
    law
}
fn unique(reading: ConstitutiveReading) -> Vec<Rat> {
    match reading {
        ConstitutiveReading::Unique { current } => current,
        other => panic!("expected unique receiver: {other:?}"),
    }
}

#[test]
#[ignore = "requires CUDA; correlated plural currents compose to a fixed receiver without selecting a source"]
fn plural_source_keeps_its_joint_fibre_and_a_later_receiver_can_be_fixed() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    // Declared linear-relation controls: the first has the whole diagonal as its returned
    // fibre; the next measures its difference. These specify the algebra being tested.
    let mut upstream = relation(&s, 1, 2, &[(&[1], &[1, 1]), (&[1], &[2, 2])]);
    let source = points(&s, &[1]);
    let family = upstream.advance_resident(current(&source), None).unwrap();
    let difference = relation(&s, 2, 1, &[(&[1, 0], &[1]), (&[0, 1], &[-1])]);
    let first_coordinate = relation(&s, 2, 1, &[(&[1, 0], &[1]), (&[0, 1], &[0])]);
    let before = difference.rest().unwrap();
    let reads = s.census().section_read_outs;
    let image = difference.read_image(&family).unwrap();
    let separating = first_coordinate.read_image(&family).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let observed = image.inspect().unwrap();
    assert_eq!(observed.coverage, ConditionCoverage::Complete);
    assert_eq!(unique(observed.output), vec![Rat::from_integer(0.into())]);
    assert!(matches!(observed.joint, ConstitutiveReading::Plural { .. }));
    assert!(matches!(
        separating.inspect().unwrap().output,
        ConstitutiveReading::Plural { .. }
    ));
    // The supported fixed output really enters another operation on device, even though
    // its source remains plural. No arbitrary member of that source is used.
    let mut consumer = relation(&s, 1, 1, &[(&[1], &[2])]);
    assert_eq!(
        unique(
            consumer
                .advance_resident(image.current(), None)
                .unwrap()
                .inspect()
                .unwrap()
                .predecessor_reading
        ),
        vec![Rat::from_integer(0.into())]
    );
    let incompatible_observation = points(&s, &[1]);
    let incompatible = image.receive(current(&incompatible_observation)).unwrap();
    assert!(matches!(
        incompatible.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    assert_eq!(difference.rest().unwrap(), before);
}

#[test]
#[ignore = "requires CUDA; partial coverage, disjoint domains and an unavailable source remain distinct"]
fn family_image_exhibits_domain_loss_before_a_point_is_used() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut upstream = relation(&s, 1, 2, &[(&[1], &[0, 0]), (&[1], &[1, 1])]);
    let query = points(&s, &[1]);
    let diagonal = upstream.advance_resident(current(&query), None).unwrap();
    let axis = relation(&s, 2, 1, &[(&[1, 0], &[2])]);
    let partial = axis.read_image(&diagonal).unwrap();
    assert!(matches!(
        partial.inspect().unwrap().coverage,
        ConditionCoverage::Partial { .. }
    ));
    assert_eq!(
        unique(partial.inspect().unwrap().output),
        vec![Rat::from_integer(0.into())]
    );
    let mut consumer = relation(&s, 1, 1, &[(&[1], &[1])]);
    let unchanged = consumer.rest().unwrap();
    assert!(consumer.advance_resident(partial.current(), None).is_err());
    let observed = points(&s, &[0]);
    assert!(partial.receive(current(&observed)).is_err());
    assert_eq!(consumer.rest().unwrap(), unchanged);
    let mut affine = relation(&s, 1, 2, &[(&[1], &[1, 1]), (&[1], &[2, 1])]);
    let family = affine.advance_resident(current(&query), None).unwrap();
    assert!(matches!(
        axis.read_image(&family)
            .unwrap()
            .inspect()
            .unwrap()
            .coverage,
        ConditionCoverage::NoSupportedCondition { .. }
    ));
    let mut unknown = ResidentConstitutiveFibre::found(&s, 4, 2).unwrap();
    let missing = points(&s, &[1, 0, 0, 0]);
    let empty = unknown.advance_resident(current(&missing), None).unwrap();
    let image = axis.read_image(&empty).unwrap();
    assert_eq!(
        image.inspect().unwrap().coverage,
        ConditionCoverage::EmptyConditionFibre
    );
    assert!(matches!(
        image.source().inspect().unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
}

#[test]
#[ignore = "requires CUDA; independently measured conditional laws compose whole phase families"]
fn learned_phase_sections_transport_a_whole_family_and_rejoin() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut source_world = world(&s);
    let mut learned = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut learned, &mut source_world, None);
    drop(source_world);
    let law = learned.rest().unwrap();
    drop(learned);
    let learned = law.remount(&s).unwrap();
    let p = points(&s, &[3, 4, 5]);
    let pinv = points(&s, &[3, -4, 5]);
    let first = learned
        .contextual_section(ResidentConstitutiveCurrent::rational(&p).unwrap())
        .unwrap();
    let second = learned
        .contextual_section(ResidentConstitutiveCurrent::rational(&pinv).unwrap())
        .unwrap();
    let mut family_source = relation(&s, 1, 2, &[(&[1], &[1, 0]), (&[1], &[1, 1])]);
    let source = points(&s, &[1]);
    let family = family_source
        .advance_resident(current(&source), None)
        .unwrap();
    let before = family.inspect().unwrap().predecessor_reading;
    let reads = s.census().section_read_outs;
    let phase_image = first.read_change_image(&family).unwrap();
    let returned = second.read_change_image(phase_image.output()).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(
        phase_image.inspect().unwrap().coverage,
        ConditionCoverage::Complete
    );
    assert_eq!(
        returned.inspect().unwrap().coverage,
        ConditionCoverage::Complete
    );
    assert_eq!(returned.inspect().unwrap().output, before);
    // A supported point follows the same composition, retaining its rational phase.
    let mut point_source = relation(&s, 1, 2, &[(&[1], &[2, 3])]);
    let point_family = point_source
        .advance_resident(current(&source), None)
        .unwrap();
    let projected = first.read_change_image(&point_family).unwrap();
    let expected = phase(-6, 17, 5).current();
    assert_eq!(
        unique(projected.inspect().unwrap().output),
        vec![expected.real, expected.imaginary]
    );
}

#[test]
#[ignore = "requires CUDA; actual downstream observation refines the same joint family and its unresolved directions still conduct"]
fn actual_return_refines_source_family_without_selecting_its_free_coordinate() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    // F={(a,a,b)}. Measuring the first coordinate fixes a; b remains unresolved.
    let mut source = relation(
        &s,
        1,
        3,
        &[(&[1], &[1, 1, 0]), (&[1], &[2, 2, 0]), (&[1], &[1, 1, 1])],
    );
    let excitation = points(&s, &[1]);
    let family = source.advance_resident(current(&excitation), None).unwrap();
    let receiver = relation(
        &s,
        3,
        1,
        &[(&[1, 0, 0], &[1]), (&[0, 1, 0], &[0]), (&[0, 0, 1], &[0])],
    );
    let difference = relation(
        &s,
        3,
        1,
        &[(&[1, 0, 0], &[1]), (&[0, 1, 0], &[-1]), (&[0, 0, 1], &[0])],
    );
    let free_coordinate = relation(
        &s,
        3,
        1,
        &[(&[1, 0, 0], &[0]), (&[0, 1, 0], &[0]), (&[0, 0, 1], &[1])],
    );
    let observed = points(&s, &[3]);
    let source_before = family.inspect().unwrap();
    let law_before = receiver.rest().unwrap();
    let reads = s.census().section_read_outs;
    let image = receiver.read_image(&family).unwrap();
    let refined = image.receive(current(&observed)).unwrap();
    let agreed = difference.read_image(refined.family()).unwrap();
    let open = free_coordinate.read_image(refined.family()).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    match refined.inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => {
            assert_eq!(
                &particular[..2],
                &[Rat::from_integer(3.into()), Rat::from_integer(3.into())]
            );
            assert!(directions.iter().all(
                |d| d[0] == Rat::from_integer(0.into()) && d[1] == Rat::from_integer(0.into())
            ));
            assert!(
                directions
                    .iter()
                    .any(|d| d[2] != Rat::from_integer(0.into()))
            );
        }
        other => panic!("expected a retained free source direction: {other:?}"),
    }
    assert_eq!(
        unique(agreed.inspect().unwrap().output),
        vec![Rat::from_integer(0.into())]
    );
    assert!(matches!(
        open.inspect().unwrap().output,
        ConstitutiveReading::Plural { .. }
    ));
    assert_eq!(family.inspect().unwrap(), source_before);
    assert_eq!(receiver.rest().unwrap(), law_before);
}

#[test]
#[ignore = "requires CUDA; source-qualified refinement changes retained condition and later conduct without selecting the free coordinate"]
fn refined_condition_updates_actual_standing_and_changes_the_next_current() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut source_world = world(&s);
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut law, &mut source_world, None);
    drop(source_world);
    let saved = law.rest().unwrap();
    drop(law);
    let law = saved.remount(&s).unwrap();
    let zero = points(&s, &[0, 0]);
    let prior = points(&s, &[0, 4, 5]);
    let actual_input = points(&s, &[2, 3]);
    let observed = points(&s, &[3, 5]);
    let receiver = relation(&s, 2, 1, &[(&[1, 0], &[1]), (&[0, 1], &[0])]);
    let mut standing = law
        .retain_condition_current(
            ResidentConstitutiveCurrent::rational(&prior).unwrap(),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
    let section = law.contextual_section(current(&actual_input)).unwrap();
    let old_current = section.read_change(standing.current()).unwrap();
    let family = law
        .read_condition_preimage(current(&zero), current(&zero))
        .unwrap();
    let same_valued_other = law
        .read_condition_preimage(current(&zero), current(&zero))
        .unwrap();
    let reads = s.census().section_read_outs;
    let image = receiver.read_image(family.family()).unwrap();
    let wrong = image
        .receive(ResidentConstitutiveCurrent::rational(&observed).unwrap())
        .unwrap();
    assert!(same_valued_other.refined_by(wrong).is_err());
    let restriction = image
        .receive(ResidentConstitutiveCurrent::rational(&observed).unwrap())
        .unwrap();
    let restricted = family.refined_by(restriction).unwrap();
    let contact = standing.contact(&restricted).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let contact_reading = contact.inspect().unwrap();
    drop(contact);
    drop(image);
    drop(family);
    drop(same_valued_other);
    // Only the compact new condition evidence and actual standing remain. The next current
    // does not need the prior image, observation family or contact receipt to stay alive.
    let reads = s.census().section_read_outs;
    let next_current = section.read_change(standing.current()).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let expected = phase(3, 4, 5).current();
    assert_eq!(
        contact_reading.successor,
        vec![expected.real, expected.imaginary]
    );
    assert!(
        matches!(restricted.inspect().unwrap(),ConditionPreimageReading::Compatible{directions,..} if !directions.is_empty())
    );
    assert_ne!(
        old_current.inspect().unwrap().predecessor_reading,
        next_current.inspect().unwrap().predecessor_reading
    );
    let expected = phase(-6, 17, 5).current();
    assert_eq!(
        unique(next_current.inspect().unwrap().predecessor_reading),
        vec![expected.real, expected.imaginary]
    );
    assert_eq!(standing.contacts(), 1);
}
