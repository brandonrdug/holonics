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
    origin: i64,
    receiver: u64,
    lineage: u64,
) -> ResidentPhaseCurrentView<'a, 'c> {
    ResidentPhaseCurrentView::new(
        ResidentConstitutiveCurrent::rational(section).unwrap(),
        PhaseCurrentReceiverId(receiver),
        PhaseCurrentLineageId(lineage),
        q(origin, 48000),
        q(1, 48000),
        4,
        raw,
    )
    .unwrap()
}
fn values(s: &ResidentSurface<'_>, section: &ResidentSection<'_>) -> Vec<Rat> {
    let pairs = s.read_out(section).unwrap();
    assert!(pairs.iter().all(|(a, b)| a == b));
    let denominator = pairs.last().unwrap().0;
    pairs[..pairs.len() - 1]
        .iter()
        .map(|v| q(v.0, denominator))
        .collect()
}

#[test]
#[ignore = "requires native GPU; complex response adjoint uses only actual observed support"]
fn partial_complex_return_preserves_clock_morphology_and_duality() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let x = mount(&s, &[2, 1, -1, 3, 4, -2, 0, 0, 3]);
    let h = mount(&s, &[1, -2, 3, 1, 5]);
    let y = mount(&s, &[7, 2, 3, -4, 7]);
    let prediction = convolve_resident(
        &s,
        view(&x, 3, 5, 1, 11),
        view(&h, 2, 2, 2, 12),
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(13),
    )
    .unwrap();
    let difference = compare_resident(
        &s,
        prediction.view().unwrap(),
        view(&y, 2, 8, 3, 14),
        PhaseCurrentLineageId(15),
    )
    .unwrap();
    let before = s.census();
    let returned =
        return_response_resident(&s, &prediction, &difference, PhaseCurrentLineageId(16)).unwrap();
    let after = s.census();
    assert_eq!(after.deed_launches - before.deed_launches, 1);
    assert_eq!(after.section_read_outs, before.section_read_outs);
    assert_eq!(after.ingress_octets, before.ingress_octets);
    assert_eq!(
        values(&s, returned.section()),
        vec![q(19, 21), q(-5, 21), q(-13, 21), q(-22, 21)]
    );
    assert_eq!(returned.view().unwrap().origin(), &q(2, 48000));
    assert_eq!(returned.view().unwrap().sample_step(), &q(1, 48000));
    assert_eq!(
        returned.view().unwrap().receiver(),
        PhaseCurrentReceiverId(2)
    );
    assert_eq!(returned.view().unwrap().raw_extent(), 2);
    assert_eq!(returned.difference().support().predicted, 1..3);
    assert_eq!(
        returned.difference().support().unobserved_prediction,
        vec![0..1, 3..4]
    );
    assert!(std::ptr::eq(returned.forward(), &prediction));
    assert!(std::ptr::eq(returned.difference(), &difference));

    // Independent receiver identity <R_S X delta_h,e> = <delta_h,X* R_S* e>.
    let delta = mount(&s, &[1, 3, -2, 4, 11]);
    let action = convolve_resident(
        &s,
        view(&x, 3, 5, 1, 11),
        view(&delta, 2, 2, 2, 17),
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(18),
    )
    .unwrap();
    let action = values(&s, action.section());
    let e = values(&s, difference.section());
    let dh = values(&s, &delta);
    let adjoint = values(&s, returned.section());
    let left: Rat = action[2..6].iter().zip(&e).map(|(a, b)| a * b).sum();
    let right: Rat = dh.iter().zip(&adjoint).map(|(a, b)| a * b).sum();
    assert_eq!(left, right);
}

#[test]
#[ignore = "requires native GPU; equal values cannot replace the producing forward carrier"]
fn equal_prediction_from_another_operation_is_refused_without_a_launch() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let x = mount(&s, &[1, 2, 1]);
    let h = mount(&s, &[3, 4, 1]);
    let y = mount(&s, &[5, 6, 1]);
    let make = || {
        convolve_resident(
            &s,
            view(&x, 1, 0, 1, 11),
            view(&h, 1, 0, 2, 12),
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(13),
        )
        .unwrap()
    };
    let original = make();
    let equal = make();
    assert_eq!(values(&s, original.section()), values(&s, equal.section()));
    let difference = compare_resident(
        &s,
        original.view().unwrap(),
        view(&y, 1, 0, 3, 14),
        PhaseCurrentLineageId(15),
    )
    .unwrap();
    let before = s.census();
    assert!(matches!(
        return_response_resident(&s, &equal, &difference, PhaseCurrentLineageId(16)),
        Err(ResidentPhaseCurrentError::PredictionMismatch)
    ));
    assert_eq!(s.census().deed_launches, before.deed_launches);
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    let first =
        return_response_resident(&s, &original, &difference, PhaseCurrentLineageId(16)).unwrap();
    let old = values(&s, first.section());
    let _later = make();
    assert_eq!(values(&s, first.section()), old);
}

#[test]
#[ignore = "requires native GPU; a receiver cut preserves inactive response directions and complete extent"]
fn a_short_receiver_return_keeps_all_response_directions() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let extent = s.declaration().max_sectiond_bytes as usize / 20 + 1;
    let x = mount(&s, &[2, -1, 1]);
    let mut zero = vec![0; 2 * extent + 1];
    *zero.last_mut().unwrap() = 1;
    let h = mount(&s, &zero);
    let y = mount(&s, &[3, 4, 1]);
    let p = convolve_resident(
        &s,
        view(&x, 1, 0, 1, 11),
        view(&h, extent, 0, 2, 12),
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(13),
    )
    .unwrap();
    let d = compare_resident(
        &s,
        p.view().unwrap(),
        view(&y, 1, 2, 3, 14),
        PhaseCurrentLineageId(15),
    )
    .unwrap();
    let before = s.census();
    let a = return_response_resident(&s, &p, &d, PhaseCurrentLineageId(16)).unwrap();
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    let actual = values(&s, a.section());
    let mut expected = vec![q(0, 1); 2 * extent];
    expected[4] = q(2, 1);
    expected[5] = q(11, 1);
    assert_eq!(actual, expected);
    assert_eq!(a.view().unwrap().raw_extent(), extent);
}

#[test]
#[ignore = "requires native GPU; wide adjoint overflow refuses without changing the forward receipt"]
fn overflowing_return_preserves_prediction_and_observation() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let x = mount(&s, &[i64::MAX, 0, 1]);
    let h = mount(&s, &[0, 0, 1]);
    let y = mount(&s, &[i64::MAX, i64::MAX, 1]);
    let p = convolve_resident(
        &s,
        view(&x, 1, 0, 1, 11),
        view(&h, 1, 0, 2, 12),
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(13),
    )
    .unwrap();
    let d = compare_resident(
        &s,
        p.view().unwrap(),
        view(&y, 1, 0, 3, 14),
        PhaseCurrentLineageId(15),
    )
    .unwrap();
    let before_p = values(&s, p.section());
    let before_d = values(&s, d.section());
    let before = s.census();
    assert!(return_response_resident(&s, &p, &d, PhaseCurrentLineageId(16)).is_err());
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(values(&s, p.section()), before_p);
    assert_eq!(values(&s, d.section()), before_d);
}
