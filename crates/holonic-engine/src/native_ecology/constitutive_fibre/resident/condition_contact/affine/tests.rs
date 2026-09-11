use super::super::super::contact_tests::{current, points};
use super::*;
use crate::embedding_fiber::ResidentReadout;
const METRIC: ConditionContactMetric = ConditionContactMetric::UnitAdmittanceRealification;
fn r(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn family<'c>(s: &'c ResidentSurface<'c>, shifted: bool) -> ResidentConstitutiveReturn<'c> {
    let mut law = ResidentConstitutiveFibre::found(s, 2, 4).unwrap();
    let x = points(s, &[1, 0]);
    for y in if shifted {
        [[2, 0, -1, 0], [-1, 0, 2, 0]]
    } else {
        [[1, 0, 0, 0], [0, 0, 1, 0]]
    } {
        let y = points(s, &y);
        law.advance_resident(current(&x), Some(current(&y)))
            .unwrap();
    }
    law.read_resident(current(&x)).unwrap()
}
#[test]
#[ignore = "requires CUDA; affine source reaction keeps actual tangential current and its plural fibre"]
fn actual_affine_reaction_is_not_a_particular_solution_cast() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let f = family(&s, false);
    let g = family(&s, true);
    let h = points(&s, &[3, 4, 1, -2]);
    let reads = s.census().section_read_outs;
    let reaction = f.read_contact(current(&h), METRIC).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert!(std::ptr::eq(reaction.family(), &f));
    let seen = reaction.inspect().unwrap();
    assert_eq!(seen.successor, vec![r(3, 2), r(0, 1), r(-1, 2), r(0, 1)]);
    assert_eq!(seen.successor[0].clone() - &seen.successor[2], r(2, 1));
    let norm = |v: &[Rat]| -> Rat { v.iter().map(|v| v * v).sum() };
    assert_eq!(
        norm(&seen.predecessor) + norm(&seen.incoming_normal),
        norm(&seen.successor) + norm(&seen.returned_normal)
    );
    assert_eq!(
        g.read_contact(current(&h), METRIC)
            .unwrap()
            .inspect()
            .unwrap()
            .successor,
        seen.successor
    );
    assert!(matches!(
        reaction.family().inspect().unwrap().predecessor_reading,
        ConstitutiveReading::Plural { .. }
    ));
    // An ordinary point consumer accepts the actual reaction, while still refusing the raw fibre.
    let mut receiver = ResidentConstitutiveFibre::found(&s, 4, 2).unwrap();
    let y = points(&s, &[2, 0]);
    receiver
        .advance_resident(reaction.successor(), Some(current(&y)))
        .unwrap();
    assert!(receiver.read_resident(f.current()).is_err());
    assert!(receiver.read_resident(reaction.successor()).is_ok());
}
#[test]
#[ignore = "requires CUDA; absent incoming family cannot be consumed as an actual source reaction"]
fn empty_affine_contact_retains_actual_prior_but_guards_its_successor() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let law = ResidentConstitutiveFibre::found(&s, 2, 4).unwrap();
    let x = points(&s, &[1, 0]);
    let h = points(&s, &[3, 4, 1, -2]);
    let f = law.read_resident(current(&x)).unwrap();
    let reaction = f.read_contact(current(&h), METRIC).unwrap();
    let seen = reaction.inspect().unwrap();
    assert_eq!(
        seen.status,
        ConditionContactStatus::OutsideRepresentedRelation
    );
    assert_eq!(seen.predecessor, seen.successor);
    let receiver = ResidentConstitutiveFibre::found(&s, 4, 2).unwrap();
    assert!(receiver.read_resident(reaction.successor()).is_err());
    assert!(receiver.read_resident(reaction.predecessor()).is_ok());
    assert!(receiver.read_resident(reaction.actual_successor()).is_ok());
}
