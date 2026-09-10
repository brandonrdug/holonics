use super::*;

fn law() -> ConstitutiveFibreRest {
    ConstitutiveFibreRest {
        chart: LawChart {
            source_width: 1,
            target_width: 1,
            source_chart: ConstitutiveSourceChart::Linear,
            occurrences: 1,
        },
        basis: ResidentSectionRest::found(
            2,
            2,
            ResidentGrain(0),
            64,
            vec![(1, 1), (2, 2), (0, 0), (0, 0)],
        )
        .unwrap(),
    }
}

#[test]
fn local_law_wire_keeps_relation_and_refuses_malformed_chart() {
    let original = law();
    let mut wire = Vec::new();
    original.write(&mut wire).unwrap();
    let restored = ConstitutiveFibreRest::read(&mut wire.as_slice(), wire.len() as u64).unwrap();
    assert_eq!(restored, original);
    wire.push(0);
    assert!(ConstitutiveFibreRest::read(&mut wire.as_slice(), wire.len() as u64).is_err());
    let mut wrong = law();
    wrong.chart.occurrences = 0;
    assert!(wrong.validate().is_err());
    wrong = law();
    wrong.basis.intervals[0] = (-1, -1);
    assert!(wrong.validate().is_err());
    wrong = law();
    wrong.chart.source_chart = ConstitutiveSourceChart::BilinearContact {
        source_complex: 1,
        condition_complex: 1,
    };
    assert!(wrong.validate().is_err());
}
