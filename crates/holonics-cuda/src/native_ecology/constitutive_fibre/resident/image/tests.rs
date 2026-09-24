use super::super::contact_tests::{current, points};
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

/// Host/device parity (fibre-image kernel): the difference map sends the whole diagonal fibre to
/// exactly zero while the joint source stays plural, as the declared linear algebra requires.
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
