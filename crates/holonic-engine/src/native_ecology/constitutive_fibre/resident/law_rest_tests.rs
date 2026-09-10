use super::contact_tests::{calibrate, current, phase, points, value, world};
use super::*;
use crate::embedding_fiber::ResidentReadout;

fn remount<'c>(
    surface: &'c ResidentSurface<'c>,
    body: ResidentConstitutiveFibre<'c>,
) -> ResidentConstitutiveFibre<'c> {
    let rest = body.rest().unwrap();
    let mut wire = Vec::new();
    rest.write(&mut wire).unwrap();
    drop(body);
    let saved = ConstitutiveFibreRest::read(&mut wire.as_slice(), wire.len() as u64).unwrap();
    assert_eq!(saved, rest);
    saved.remount(surface).unwrap()
}

#[test]
#[ignore = "requires CUDA; restored conditional law composes resident currents with fixed learned material"]
fn restored_law_carries_repeated_phase_and_new_superposition_without_history() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut teacher = world(&s);
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut law, &mut teacher, None);
    drop(teacher);
    let before = law.rest().unwrap();
    let mut law = remount(&s, law);
    let start = points(&s, &[2, 3]);
    let phase_quarter = points(&s, &[0, 1]);
    let rational_phase = points(&s, &[3, 4, 5]);
    let numerical_reads = law.census().section_read_outs;
    let first = law
        .advance_bilinear_contact(
            current(&start),
            ResidentConstitutiveCurrent::rational(&rational_phase).unwrap(),
            None,
        )
        .unwrap();
    let mut current_return = first;
    let resident = law.census().resident_octets_now;
    // A declared work extent, independent of any codec or learned rank. Each complete turn
    // returns to the same current; its causal occurrence and relation chronology are distinct.
    let turns = 64usize;
    for _ in 0..turns * 4 {
        current_return = law
            .advance_bilinear_contact(current_return.current(), current(&phase_quarter), None)
            .unwrap();
        assert_eq!(law.census().resident_octets_now, resident);
    }
    assert_eq!(law.census().section_read_outs, numerical_reads);
    assert_eq!(value(&current_return), phase(-6, 17, 5).current());
    let after = law.rest().unwrap();
    assert_eq!(after.rank(), before.rank());
    assert_eq!(after.relation(), before.relation());
    assert_eq!(
        after.occurrences() - before.occurrences(),
        1 + (turns * 4) as u64
    );
    let mut wire = Vec::new();
    after.write(&mut wire).unwrap();
    eprintln!("learned law: rank={}, basis_words={}, wire_octets={}, composed_steps={}, fixed_resident_octets={}",after.rank(),
        after.relation().intervals.len(),wire.len(),1+turns*4,resident);
    // Development continues through the same law; another observation of a carried relation
    // changes chronology without adding an independent generator coordinate.
    let old_rank = after.rank();
    law.advance_bilinear_contact(
        current(&start),
        ResidentConstitutiveCurrent::rational(&rational_phase).unwrap(),
        Some(current_return.current()),
    )
    .unwrap();
    assert_eq!(law.rest().unwrap().rank(), old_rank);
}

#[test]
#[ignore = "requires CUDA; compact law rest preserves partial domain and a plural receiver fibre"]
fn law_rest_keeps_open_domain_and_full_plural_return() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&s, 2, 2).unwrap();
    body.advance(&[1, 0], Some(&[1, 0])).unwrap();
    let mut body = remount(&s, body);
    assert!(matches!(
        body.advance(&[0, 1], None).unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    body.advance(&[1, 0], Some(&[1, 1])).unwrap();
    let before = body.advance(&[1, 0], None).unwrap().predecessor_reading;
    assert!(matches!(before, ConstitutiveReading::Plural { .. }));
    let mut body = remount(&s, body);
    assert_eq!(
        body.advance(&[1, 0], None).unwrap().predecessor_reading,
        before
    );
    assert!(matches!(
        body.advance(&[0, 1], None).unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
}
