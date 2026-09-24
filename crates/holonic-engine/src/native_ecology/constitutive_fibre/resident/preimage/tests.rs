use super::super::contact_tests::{calibrate, current, observe, phase, points, value, world};
use super::*;
use crate::embedding_fiber::ResidentReadout;

fn compatible(p: &ResidentConditionPreimage<'_>) -> (Vec<Rat>, Vec<Vec<Rat>>) {
    match p.inspect().unwrap() {
        ConditionPreimageReading::Compatible {
            particular,
            directions,
        } => (particular, directions),
        other => panic!("expected compatible conditions: {other:?}"),
    }
}

/// Host/device parity (condition-preimage kernel): the device preimage is exactly the hidden
/// condition 3/5 + 4i/5 and the carried prediction equals the later exterior return.
#[test]
#[ignore = "requires CUDA; an unprovided native phase is inferred from an actual later return"]
fn a_condition_preimage_from_native_observation_drives_a_new_current() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let hidden = phase(3, 4, 5);
    let actual = observe(&mut w, phase(2, 3, 1), hidden);
    let x = points(&s, &[2, 3]);
    let y = points(
        &s,
        &NativePhaseCurrent::from_current(&actual).unwrap().words(),
    );
    let before = body.census();
    let cut = body.occurrences();
    let preimage = body
        .read_condition_preimage(
            current(&x),
            ResidentConstitutiveCurrent::rational(&y).unwrap(),
        )
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(body.census().ingress_octets, before.ingress_octets);
    assert_eq!(body.occurrences(), cut);
    let next = points(&s, &[7, -2]);
    let before = body.census();
    let predicted = body
        .advance_bilinear_contact(current(&next), preimage.current(), None)
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    // The hidden condition was never supplied to the learner. This second observation follows
    // prediction; its current is not developmental material for the preceding inference.
    let later = observe(&mut w, phase(7, -2, 1), hidden);
    assert_eq!(value(&predicted), later);
    let (condition, directions) = compatible(&preimage);
    assert!(directions.is_empty());
    assert_eq!(
        condition,
        vec![Rat::new(3.into(), 5.into()), Rat::new(4.into(), 5.into())]
    );
    assert_eq!(preimage.relation_cut(), cut);
}
