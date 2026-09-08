use super::*;
use crate::{embedding_fiber::ResidentReadout, resident_section::ResidentSectionRest};

fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn mount<'c>(s: &'c ResidentSurface<'c>, words: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            words.len(),
            ResidentGrain(0),
            64,
            words.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn view<'a, 'c>(
    section: &'a ResidentSection<'c>,
    raw: usize,
    origin_samples: i64,
    lineage: u64,
) -> ResidentPhaseCurrentView<'a, 'c> {
    ResidentPhaseCurrentView::new(
        ResidentConstitutiveCurrent::rational(section).unwrap(),
        PhaseCurrentReceiverId(9),
        PhaseCurrentLineageId(lineage),
        q(origin_samples, 48000),
        q(1, 48000),
        4,
        raw,
    )
    .unwrap()
}
fn values(s: &ResidentSurface<'_>, section: &ResidentSection<'_>) -> Vec<Rat> {
    let pairs = s.read_out(section).unwrap();
    assert!(pairs.iter().all(|(a, b)| a == b));
    let den = pairs.last().unwrap().0;
    pairs[..pairs.len() - 1]
        .iter()
        .map(|v| q(v.0, den))
        .collect()
}

#[test]
#[ignore = "requires native GPU; oriented rational return and complete operand lineage"]
fn exact_oriented_difference_stays_resident() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let p = mount(&s, &[2, -3, 4, 5, 3]);
    let o = mount(&s, &[7, 1, -2, 3, 7]);
    let before = s.census();
    let d = compare_resident(
        &s,
        view(&p, 2, 0, 1),
        view(&o, 2, 0, 2),
        PhaseCurrentLineageId(3),
    )
    .unwrap();
    let after = s.census();
    assert_eq!(after.section_read_outs, before.section_read_outs);
    assert_eq!(after.ingress_octets, before.ingress_octets);
    assert_eq!(after.deed_launches - before.deed_launches, 1);
    assert_eq!(d.predicted().lineage(), PhaseCurrentLineageId(1));
    assert_eq!(d.observed().lineage(), PhaseCurrentLineageId(2));
    assert_eq!(d.view().unwrap().lineage(), PhaseCurrentLineageId(3));
    assert_eq!(d.support().begin, q(0, 1));
    assert_eq!(d.support().end, q(2, 48000));
    assert_eq!(
        values(&s, d.section()),
        vec![q(1, 3), q(8, 7), q(-34, 21), q(-26, 21)]
    );
    assert!(d.support().unobserved_prediction.is_empty());
}

#[test]
#[ignore = "requires native GPU; unmatched support stays unobserved instead of becoming zero"]
fn shifted_support_preserves_both_excluded_populations() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let p = mount(&s, &[1, 0, 2, 0, 3, 0, 4, 0, 1]);
    let o = mount(&s, &[10, 0, 20, 0, 30, 0, 40, 0, 50, 0, 1]);
    let d = compare_resident(
        &s,
        view(&p, 4, 0, 1),
        view(&o, 5, 2, 2),
        PhaseCurrentLineageId(3),
    )
    .unwrap();
    assert_eq!(d.support().predicted, 2..4);
    assert_eq!(d.support().observed, 0..2);
    assert_eq!(d.support().unobserved_prediction, vec![0..2]);
    assert_eq!(d.support().unpredicted_observation, vec![2..5]);
    assert_eq!(d.view().unwrap().origin(), &q(2, 48000));
    assert_eq!(
        values(&s, d.section()),
        vec![q(7, 1), q(0, 1), q(16, 1), q(0, 1)]
    );
    let d = compare_resident(
        &s,
        view(&o, 5, 2, 2),
        view(&p, 4, 0, 1),
        PhaseCurrentLineageId(4),
    )
    .unwrap();
    assert_eq!(d.support().unobserved_prediction, vec![2..5]);
    assert_eq!(d.support().unpredicted_observation, vec![0..2]);
    assert_eq!(
        values(&s, d.section()),
        vec![q(-7, 1), q(0, 1), q(-16, 1), q(0, 1)]
    );
}

#[test]
#[ignore = "requires native GPU; clocks and receiver identity are checked before native work"]
fn mismatched_or_disjoint_charts_refuse_before_launch() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let p = mount(&s, &[1, 2, 1]);
    let before = s.census();
    assert!(matches!(
        compare_resident(
            &s,
            view(&p, 1, 0, 1),
            view(&p, 1, 1, 2),
            PhaseCurrentLineageId(3)
        ),
        Err(ResidentPhaseCurrentError::NonOverlappingSupport)
    ));
    for case in 0..4 {
        let mut o = view(&p, 1, 0, 2);
        match case {
            0 => o.origin = q(1, 96000),
            1 => o.sample_step = q(1, 16000),
            2 => o.receiver = PhaseCurrentReceiverId(10),
            _ => o.phase_extent = 8,
        }
        assert!(compare_resident(&s, view(&p, 1, 0, 1), o, PhaseCurrentLineageId(3)).is_err());
    }
    assert_eq!(s.census().deed_launches, before.deed_launches);
    assert_eq!(s.census().allocations, before.allocations);
}

#[test]
#[ignore = "requires native GPU; complete source validity and late refusal leave operands usable"]
fn malformed_and_overflowing_differences_do_not_publish() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let p = mount(&s, &[-i64::MAX, 0, 1]);
    let o = mount(&s, &[i64::MAX, 0, 1]);
    assert!(compare_resident(
        &s,
        view(&p, 1, 0, 1),
        view(&o, 1, 0, 2),
        PhaseCurrentLineageId(3)
    )
    .is_err());
    let z = mount(&s, &[0, 0, 1]);
    for words in [&[1, 0, 7, 0, 1][..], &[1, 0, 0][..]] {
        let bad = mount(&s, words);
        assert!(compare_resident(
            &s,
            view(&z, 1, 0, 1),
            view(&bad, 1, 0, 2),
            PhaseCurrentLineageId(3)
        )
        .is_err());
    }
    let bad = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, 3, ResidentGrain(0), 64, vec![(0, 1), (0, 0), (1, 1)])
                .unwrap(),
        )
        .unwrap();
    assert!(compare_resident(
        &s,
        view(&z, 1, 0, 1),
        view(&bad, 1, 0, 2),
        PhaseCurrentLineageId(3)
    )
    .is_err());
    let d = compare_resident(
        &s,
        view(&p, 1, 0, 1),
        view(&z, 1, 0, 2),
        PhaseCurrentLineageId(3),
    )
    .unwrap();
    assert_eq!(values(&s, d.section()), vec![q(i64::MAX, 1), q(0, 1)]);
    let a = mount(&s, &[i64::MAX, 0, 3]);
    let b = mount(&s, &[i64::MAX, 0, 6]);
    let d = compare_resident(
        &s,
        view(&a, 1, 0, 1),
        view(&b, 1, 0, 2),
        PhaseCurrentLineageId(3),
    )
    .unwrap();
    assert_eq!(values(&s, d.section()), vec![q(-i64::MAX, 6), q(0, 1)]);
}

#[test]
#[ignore = "requires native GPU; all coordinates of a whole parallel section agree with exact algebra"]
fn complete_parallel_section_matches_independent_rationals() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let extent = 4099;
    let mut a: Vec<i64> = (0..2 * extent)
        .map(|i| (i * 71 % 2999) as i64 - 1500)
        .collect();
    let mut b: Vec<i64> = (0..2 * extent)
        .map(|i| (i * 97 % 1999) as i64 - 1000)
        .collect();
    let expected: Vec<_> = a.iter().zip(&b).map(|(a, b)| q(*b, 7) - q(*a, 3)).collect();
    a.push(3);
    b.push(7);
    let p = mount(&s, &a);
    let o = mount(&s, &b);
    let before = s.census();
    let d = compare_resident(
        &s,
        view(&p, extent, 0, 1),
        view(&o, extent, 0, 2),
        PhaseCurrentLineageId(3),
    )
    .unwrap();
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(values(&s, d.section()), expected);
}
