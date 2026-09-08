use super::super::contact_tests::{calibrate, current, observe, phase, points, value, world};
use super::*;
use crate::{dimensional_wave::ExactComplexWaveCurrent, embedding_fiber::ResidentReadout};
use num_traits::Zero;
const METRIC: ConditionContactMetric = ConditionContactMetric::UnitAdmittanceRealification;
fn rational<'a, 'c>(s: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::rational(s).unwrap()
}

#[test]
#[ignore = "requires CUDA; the fixed-source mixed section infers an unprovided phase change and its successor drives later native conduct"]
fn contextual_return_changes_the_actual_condition_and_subsequent_native_current() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut world = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut world, None);
    let fixed = phase(2, 1, 3);
    let hidden = phase(3, 4, 5);
    let initial = phase(1, 0, 1);
    let before_return = observe(&mut world, fixed, initial);
    let after_return = observe(&mut world, fixed, hidden);
    let delta = NativePhaseCurrent::from_current(&after_return.subtract(&before_return)).unwrap();
    let source = points(&s, &fixed.words());
    let about = points(&s, &initial.words());
    let returned = points(&s, &delta.words());
    let next_source = points(&s, &[7, -2]);
    let before = body.census();
    let cut = body.occurrences();
    let section = body.contextual_section(rational(&source)).unwrap();
    let family = section
        .preimage_change(rational(&about), rational(&returned))
        .unwrap();
    let mut retained = section
        .retain_condition_current(rational(&about), METRIC)
        .unwrap();
    let contact = retained.contact(&family).unwrap();
    let prediction = body
        .advance_bilinear_contact(current(&next_source), retained.current(), None)
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(section.relation_cut(), cut);
    assert_eq!(family.relation_cut(), cut);
    let actual_later = observe(&mut world, phase(7, -2, 1), hidden);
    assert_eq!(value(&prediction), actual_later);
    assert_eq!(
        contact.inspect().unwrap().successor,
        vec![Rat::new(3.into(), 5.into()), Rat::new(4.into(), 5.into())]
    );
    let dc = points(&s, &[-2, 4, 5]);
    assert_eq!(
        value(&section.read_change(rational(&dc)).unwrap()),
        after_return.subtract(&before_return)
    );
    // The same returned current can form a relation through the existing native owner.
    let mut receiver = ResidentConstitutiveFibre::found(&s, 2, 2).unwrap();
    let before = body.census();
    let new_relation = receiver
        .advance_resident(current(&next_source), Some(prediction.current()))
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert!(new_relation.inspect().unwrap().formed_pivot.is_some());
    assert_eq!(
        value(
            &receiver
                .advance_resident(current(&next_source), None)
                .unwrap()
        ),
        actual_later
    );
}

#[test]
#[ignore = "requires CUDA; partial and vertical contextual relations retain their full domain and original producing cut"]
fn partial_and_vertical_sections_are_not_selected_maps() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let zero = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let i = points(&s, &[0, 1]);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    body.advance_bilinear_contact(current(&one), current(&zero), Some(current(&zero)))
        .unwrap();
    let partial = body.contextual_section(current(&one)).unwrap();
    assert!(matches!(
        partial
            .read_change(current(&one))
            .unwrap()
            .inspect()
            .unwrap()
            .predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    calibrate(&s, &mut body, &mut world(&s), None);
    let fixed = body.contextual_section(current(&i)).unwrap();
    let previous = fixed.inspect_relation().unwrap();
    body.advance_bilinear_contact(current(&zero), current(&zero), Some(current(&one)))
        .unwrap();
    let vertical = body.contextual_section(current(&i)).unwrap();
    let read = vertical.read_change(current(&one)).unwrap();
    assert!(
        matches!(read.inspect().unwrap().predecessor_reading,ConstitutiveReading::Plural{directions,..} if directions.len()==1)
    );
    let about = points(&s, &[3, 4]);
    let dy = points(&s, &[7, 2]);
    let h = points(&s, &[10, -6]);
    let family = vertical
        .preimage_change(current(&about), current(&dy))
        .unwrap();
    let mut actual = vertical
        .retain_condition_current(current(&h), METRIC)
        .unwrap();
    let c = actual.contact(&family).unwrap();
    assert_eq!(
        c.inspect().unwrap().successor,
        vec![Rat::from_integer(5.into()), Rat::from_integer((-6).into())]
    );
    assert!(
        matches!(family.inspect().unwrap(),ConditionPreimageReading::Compatible{directions,..} if directions.len()==1)
    );
    assert_eq!(fixed.inspect_relation().unwrap(), previous);
    assert_eq!(
        value(&fixed.read_change(current(&one)).unwrap()),
        phase(0, 1, 1).current()
    );
    assert!(matches!(
        partial
            .read_change(current(&one))
            .unwrap()
            .inspect()
            .unwrap()
            .predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    drop(body);
    assert_eq!(
        value(&fixed.read_change(current(&one)).unwrap()),
        phase(0, 1, 1).current()
    );
}

#[test]
#[ignore = "requires CUDA; zero-source change law has free condition fibre while incompatible evidence preserves actual standing"]
fn free_and_empty_change_evidence_preserve_actual_current() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut world(&s), None);
    let z = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let about = points(&s, &[9, 2]);
    let h = points(&s, &[3, 4, 5]);
    let section = body.contextual_section(current(&z)).unwrap();
    let free = section
        .preimage_change(current(&about), current(&z))
        .unwrap();
    let empty = section
        .preimage_change(current(&about), current(&one))
        .unwrap();
    let mut actual = section
        .retain_condition_current(rational(&h), METRIC)
        .unwrap();
    let before = body.census();
    let a = actual.contact(&free).unwrap();
    let b = actual.contact(&empty).unwrap();
    let y = section.read_change(actual.current()).unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(value(&y), ExactComplexWaveCurrent::zero());
    for receipt in [&a, &b] {
        assert!(
            receipt
                .inspect()
                .unwrap()
                .difference
                .iter()
                .all(Zero::is_zero)
        );
    }
    assert!(
        matches!(free.inspect().unwrap(),ConditionPreimageReading::Compatible{directions,..} if directions.len()==2)
    );
    assert!(matches!(
        empty.inspect().unwrap(),
        ConditionPreimageReading::OutsideRepresentedRelation { .. }
    ));
}
