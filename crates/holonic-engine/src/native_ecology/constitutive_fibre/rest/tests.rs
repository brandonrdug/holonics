use super::*;
use crate::embedding_fiber::ResidentReadout;

fn empty(
    chart: ConstitutiveSourceChart,
    source: usize,
    target: usize,
) -> ResidentConstitutiveFibreRest {
    let width = source + target;
    ResidentConstitutiveFibreRest {
        header: Header {
            source_chart: chart,
            source_width: source,
            target_width: target,
            occurrences: 0,
        },
        basis: ResidentSectionRest::found(
            width,
            width,
            ResidentGrain(0),
            64,
            vec![(0, 0); width * width],
        )
        .unwrap(),
    }
}

#[test]
fn cold_wire_retains_the_bound_bilinear_chart_and_rejects_corruption() {
    let mut rest = empty(
        ConstitutiveSourceChart::BilinearContact {
            source_complex: 1,
            condition_complex: 2,
        },
        10,
        6,
    );
    rest.header.occurrences = 3;
    rest.basis.intervals[0] = (2, 2);
    rest.basis.intervals[12] = (-3, -3);
    let mut bytes = vec![];
    rest.write(&mut bytes).unwrap();
    assert_eq!(
        ResidentConstitutiveFibreRest::read(&mut &bytes[..], bytes.len() as u64).unwrap(),
        rest
    );
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(
        ResidentConstitutiveFibreRest::read(&mut &trailing[..], trailing.len() as u64).is_err()
    );
    for len in [0, MAGIC.len(), bytes.len() - 1] {
        assert!(ResidentConstitutiveFibreRest::read(&mut &bytes[..len], len as u64).is_err());
    }
    rest.header.source_chart = ConstitutiveSourceChart::BilinearContact {
        source_complex: 2,
        condition_complex: 2,
    };
    assert!(rest.validate().is_err());
}

#[test]
fn cold_validation_preserves_echelon_fibre_and_occurrence_invariants() {
    let mut rest = empty(ConstitutiveSourceChart::Linear, 1, 1);
    rest.basis.intervals[1] = (1, 1); // absent pivot with nonzero row
    assert!(rest.validate().is_err());
    rest.basis.intervals[0] = (1, 1);
    assert!(rest.validate().is_err()); // rank cannot precede the first occurrence
    rest.header.occurrences = 1;
    rest.validate().unwrap();
    rest.basis.intervals[2] = (1, 1); // below the diagonal
    assert!(rest.validate().is_err());
    rest.basis.intervals[2] = (0, 0);
    rest.basis.grain = ResidentGrain(1);
    assert!(rest.validate().is_err());
    rest.basis.grain = ResidentGrain(0);
    rest.basis.intervals[1] = (0, 1);
    assert!(rest.validate().is_err());
}

#[test]
#[ignore = "requires native GPU; restart retains a plural fibre and continues without replay"]
fn rest_remount_preserves_plural_and_outside_readings_and_later_development() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&s, 2, 1).unwrap();
    body.advance(&[1, 0], Some(&[2])).unwrap();
    body.advance(&[1, 0], Some(&[5])).unwrap();
    let plural = body.advance(&[1, 0], None).unwrap();
    let outside = body.advance(&[0, 1], None).unwrap();
    let rest = body.rest().unwrap();
    let mut bytes = vec![];
    rest.write(&mut bytes).unwrap();
    drop(body);
    let before = s.census();
    let mut resumed = ResidentConstitutiveFibre::remount(
        &s,
        ResidentConstitutiveFibreRest::read(&mut &bytes[..], bytes.len() as u64).unwrap(),
    )
    .unwrap();
    assert_eq!(resumed.occurrences(), 4);
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(s.census().deed_launches, before.deed_launches);
    assert_eq!(
        resumed.advance(&[1, 0], None).unwrap().predecessor_reading,
        plural.predecessor_reading
    );
    assert_eq!(
        resumed.advance(&[0, 1], None).unwrap().predecessor_reading,
        outside.predecessor_reading
    );
    resumed.advance(&[0, 1], Some(&[7])).unwrap();
    assert!(matches!(
        resumed.advance(&[0, 1], None).unwrap().predecessor_reading,
        ConstitutiveReading::Plural { .. }
    ));
    assert_eq!(resumed.occurrences(), 8);
}

#[test]
#[ignore = "requires native GPU; bilinear mixed action survives restart and remains a bound source law"]
fn bilinear_relation_continues_from_exact_rest() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let point = |v: &[i64]| {
        s.mount_section_rest(
            &ResidentSectionRest::found(
                1,
                v.len(),
                ResidentGrain(0),
                64,
                v.iter().map(|&x| (x, x)).collect(),
            )
            .unwrap(),
        )
        .unwrap()
    };
    let x = point(&[2, 3]);
    let c = point(&[5, 7]);
    let y = point(&[-11, 29]);
    fn current<'a, 'c>(p: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
        ResidentConstitutiveCurrent::integers(p).unwrap()
    }
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    body.advance_bilinear_contact(current(&x), current(&c), Some(current(&y)))
        .unwrap();
    let original = body
        .advance_bilinear_contact(current(&x), current(&c), None)
        .unwrap();
    let rest = body.rest().unwrap();
    drop(body);
    let mut body = ResidentConstitutiveFibre::remount(&s, rest).unwrap();
    let before = s.census();
    let resumed = body
        .advance_bilinear_contact(current(&x), current(&c), None)
        .unwrap();
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(
        resumed.inspect().unwrap().predecessor_reading,
        original.inspect().unwrap().predecessor_reading
    );
    assert_eq!(resumed.occurrence(), original.occurrence() + 1);
    assert!(body.advance(&[0; 6], None).is_err());
}
