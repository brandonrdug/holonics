use super::*;

fn rest(status: i64) -> ResidentConditionCurrentRest {
    let c = 2;
    let mut words = vec![(0, 0); 5 * c + 2];
    words[0] = (14, 14);
    words[1] = (8, 8);
    words[2] = (5, 5);
    words[3] = (-1, -1);
    words[4] = (2, 2);
    words[5] = (2, 2);
    words[6] = (11, 11);
    words[7] = (11, 11);
    words[8] = (-9, -9);
    words[9] = (-9, -9);
    words[10] = (2, 2);
    words[11] = (status, status);
    ResidentConditionCurrentRest {
        header: Header {
            source_complex: 1,
            condition_complex: 1,
            width: c,
            metric: ConditionContactMetric::UnitAdmittanceRealification,
            contacts: 1,
        },
        section: ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words).unwrap(),
    }
}

#[test]
fn canonical_roundtrip_preserves_contact_current() {
    let original = rest(0);
    let mut bytes = Vec::new();
    original.write(&mut bytes).unwrap();
    let decoded =
        ResidentConditionCurrentRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(decoded, original);
    assert_eq!(decoded.source_chart(), original.source_chart());
    assert_eq!(decoded.contacts(), 1);
}

#[test]
fn malformed_contact_equations_are_rejected() {
    let mut malformed = rest(0);
    malformed.section.intervals[1] = (99, 99);
    assert!(malformed.validate().is_err());

    let mut malformed = rest(1);
    malformed.section.intervals[4] = (1, 1);
    assert!(malformed.validate().is_err());
}

#[test]
fn malformed_chart_denominator_and_disposition_are_rejected() {
    let mut malformed = rest(0);
    malformed.header.source_complex = usize::MAX;
    assert!(malformed.validate().is_err());

    let mut malformed = rest(0);
    malformed.section.intervals[10] = (0, 0);
    assert!(malformed.validate().is_err());

    let mut malformed = rest(0);
    malformed.section.intervals[11] = (2, 2);
    assert!(malformed.validate().is_err());

    let mut malformed = rest(1);
    malformed.header.contacts = 0;
    for j in 0..2 {
        malformed.section.intervals[2 + j] = malformed.section.intervals[j];
    }
    malformed.section.intervals[4..10].fill((0, 0));
    assert!(malformed.validate().is_err());
}

#[test]
fn malformed_wire_is_rejected() {
    let original = rest(0);
    let mut bytes = Vec::new();
    original.write(&mut bytes).unwrap();
    bytes.pop();
    assert!(ResidentConditionCurrentRest::read(&mut bytes.as_slice(), bytes.len() as u64).is_err());
}

#[test]
#[ignore = "requires CUDA; remounted condition current continues the same contact owner"]
fn remount_preserves_earlier_receipt_and_continues_contact() {
    use crate::embedding_fiber::ResidentReadout;
    use crate::native_ecology::constitutive_fibre::{
        ConditionContactMetric, ResidentConstitutiveFibre,
    };

    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&surface, 1, 1, 1).unwrap();
    let mount = |value: i64| {
        surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    3,
                    ResidentGrain(0),
                    64,
                    vec![(value, value), (0, 0), (1, 1)],
                )
                .unwrap(),
            )
            .unwrap()
    };
    let source_section = mount(1);
    let condition_section = mount(2);
    let observed_section = mount(3);
    let source = ResidentConstitutiveCurrent::rational(&source_section).unwrap();
    let condition = ResidentConstitutiveCurrent::rational(&condition_section).unwrap();
    let observed = ResidentConstitutiveCurrent::rational(&observed_section).unwrap();
    body.advance_bilinear_contact(source, condition, Some(observed))
        .unwrap();
    let preimage_source_section = mount(1);
    let family = body
        .read_condition_preimage(
            ResidentConstitutiveCurrent::rational(&preimage_source_section).unwrap(),
            ResidentConstitutiveCurrent::rational(&observed_section).unwrap(),
        )
        .unwrap();
    let retained_condition_section = mount(2);
    let mut held = body
        .retain_condition_current(
            ResidentConstitutiveCurrent::rational(&retained_condition_section).unwrap(),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
    let earlier = held.contact(&family).unwrap();
    let earlier_reading = earlier.inspect().unwrap();
    let cold = held.rest().unwrap();
    drop(held);
    let mut resumed = ResidentConditionCurrent::remount(&surface, cold).unwrap();
    let later = resumed.contact(&family).unwrap();
    assert_eq!(earlier.inspect().unwrap(), earlier_reading);
    assert_eq!(later.inspect().unwrap().contact, 2);
    assert_eq!(resumed.contacts(), 2);
}
