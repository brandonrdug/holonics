use super::super::contact_tests::{calibrate, current, observe, phase, points, value, world};
use super::*;
use crate::embedding_fiber::ResidentReadout;
const METRIC: ConditionContactMetric = ConditionContactMetric::UnitAdmittanceRealification;
fn rational<'a, 'c>(s: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::rational(s).unwrap()
}

/// Host/device parity (context-section kernel): the device infers the exact hidden condition
/// change and its read change equals the exact difference of the two exterior returns.
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
