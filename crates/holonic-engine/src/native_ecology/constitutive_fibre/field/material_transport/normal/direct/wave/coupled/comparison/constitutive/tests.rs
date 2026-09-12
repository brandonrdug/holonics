use super::super::super::super::comparison_tests::{current, point};
use super::super::super::super::family::tests::{body, law};
use super::super::joint::tests::source_parameters_at;
use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::native_ecology::constitutive_fibre::{ConditionContactMetric, ConstitutiveReading};

fn r(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn free_law<'c>(s: &'c ResidentSurface<'c>) -> ResidentConstitutiveFibre<'c> {
    let mut local = law(s, false);
    let zero = point(s, &[0; 6]);
    let h = point(s, &[1, 0]);
    let vertical = point(s, &[1, 0]);
    local
        .advance_bilinear_contact(current(&zero), current(&h), Some(current(&vertical)))
        .unwrap();
    local
}
fn neighborhood<'c>(
    s: &'c ResidentSurface<'c>,
    local: ResidentConstitutiveFibre<'c>,
) -> ResidentGeneratorNeighborhood<'c> {
    let h = point(s, &[1, 0]);
    ResidentGeneratorNeighborhood::with_shared_condition(
        vec![local],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap()
}

#[test]
#[ignore = "requires CUDA; a real source family has dependent condition/material consequences, not independent rows"]
fn dependent_constitutive_return_preserves_source_condition_correlation() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = body(&s)
        .with_neighborhood(neighborhood(&s, free_law(&s)))
        .unwrap();
    let first = wave.admit_contact(0).unwrap();
    wave.advance_contact(&first).unwrap();
    let next = wave.admit_contact(0).unwrap();
    let prediction = wave.predict_contact(&next).unwrap();
    let observed = point(&s, &[7, 4]);
    let cmp = wave
        .compare_coupled_prediction(&prediction.handle, current(&observed))
        .unwrap();
    let anchor = [1, 0, 2, 1];
    let assignments = [
        source_parameters_at(&cmp, &anchor, &[2, 1, 3, 2]),
        source_parameters_at(&cmp, &anchor, &[2, 1, 4, 2]),
    ];
    let outside = source_parameters_at(&cmp, &[9, 0, 2, 1], &[2, 1, 3, 2]);
    let before = wave.rest().unwrap();
    {
        let mut dependent = wave.read_coupled_constitutive_family(&cmp).unwrap();
        for (i, theta) in assignments.iter().enumerate() {
            let packet = s.mount_exact_rational_packet(theta).unwrap();
            let reads = s.census().section_read_outs;
            let alt = dependent.evaluate(&packet).unwrap();
            assert_eq!(s.census().section_read_outs, reads);
            assert!(std::ptr::eq(alt.parameters(), &packet));
            assert!(std::ptr::eq(alt.comparison(), &cmp));
            assert_eq!(alt.inspect_anchor_difference().unwrap(), vec![r(0, 1); 4]);
            let contact = alt.inspect_condition().unwrap();
            let expected = if i == 0 {
                vec![r(3, 2), r(1, 2)]
            } else {
                vec![r(6, 5), r(2, 5)]
            };
            assert_eq!(contact.successor, expected);
            assert_eq!(contact.predecessor, vec![r(1, 1), r(0, 1)]);
            assert!(matches!(
                alt.prediction().inspect().unwrap().predecessor_reading,
                ConstitutiveReading::Plural { .. }
            ));
            assert_eq!(alt.inspect_formation().unwrap().formed_pivot, None);
            // Point specialization is exactly the old law, with explicit supplied operands.
            // This comparison does not install the alternative into the continuing wave.
            let mut reference = neighborhood(&s, free_law(&s));
            let x = if i == 0 {
                [1, 1, 3, 2, 2, 1]
            } else {
                [2, 1, 4, 2, 2, 1]
            };
            let eta = if i == 0 { [4, 2] } else { [3, 2] };
            let x = point(&s, &x);
            let eta = point(&s, &eta);
            let point_return = reference
                .advance(0, current(&x), Some(current(&eta)))
                .unwrap();
            assert_eq!(
                point_return.contact.as_ref().unwrap().inspect().unwrap(),
                contact
            );
            assert_eq!(
                point_return.formation.as_ref().unwrap().inspect().unwrap(),
                alt.inspect_formation().unwrap()
            );
            eprintln!(
                "dependent theta_index={i} condition={:?} residual={:?} formation={:?}",
                contact.successor,
                contact.difference,
                alt.inspect_formation().unwrap()
            );
        }
        let packet = s.mount_exact_rational_packet(&outside).unwrap();
        assert!(dependent.evaluate(&packet).is_err());
    }
    assert_eq!(wave.rest().unwrap(), before);
    assert_eq!(wave.pending_coupled_predictions(), 1);
    wave.release_coupled_prediction(&prediction.handle).unwrap();
    assert!(wave.read_coupled_constitutive_family(&cmp).is_err());
}

#[test]
#[ignore = "requires CUDA; outside old relation returns staged formation without publishing a selected alternative"]
fn dependent_constitutive_return_retains_condition_obstruction_and_material_extension() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = body(&s)
        .with_neighborhood(neighborhood(&s, law(&s, true)))
        .unwrap();
    let contact = wave.admit_contact(0).unwrap();
    let prediction = wave.predict_contact(&contact).unwrap();
    let observed = point(&s, &[9, 7]);
    let cmp = wave
        .compare_coupled_prediction(&prediction.handle, current(&observed))
        .unwrap();
    let values = source_parameters_at(&cmp, &[1, 0, 2, 1], &[1, 0, 2, 1]);
    let packet = s.mount_exact_rational_packet(&values).unwrap();
    let before = wave.rest().unwrap();
    {
        let mut family = wave.read_coupled_constitutive_family(&cmp).unwrap();
        let reads = s.census().section_read_outs;
        let alt = family.evaluate(&packet).unwrap();
        assert_eq!(s.census().section_read_outs, reads);
        let contact = alt.inspect_condition().unwrap();
        assert_eq!(contact.status,crate::native_ecology::constitutive_fibre::ConditionContactStatus::OutsideRepresentedRelation);
        assert_eq!(contact.successor, contact.predecessor);
        assert!(alt.inspect_formation().unwrap().formed_pivot.is_some());
        eprintln!(
            "dependent outside_relation={contact:?} formation={:?}",
            alt.inspect_formation().unwrap()
        );
    }
    assert_eq!(wave.rest().unwrap(), before);
}
