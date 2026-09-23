use super::*;
use crate::embedding_fiber::ResidentReadout;
fn point<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            v.len(),
            ResidentGrain(0),
            64,
            v.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn current<'a, 'c>(v: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::integers(v).unwrap()
}
#[test]
#[ignore = "requires CUDA; one target-vertical graph serves new arrivals and reopens after a changed law"]
fn source_geometry_reuse_preserves_full_contact_and_rejects_changed_directions() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(&s, 3, 1, 1).unwrap();
    let a = point(&s, &[0, 0, 1, 0, 1, 0]);
    let h = point(&s, &[1, 0]);
    for y in [[2, 0], [2, 1]] {
        let y = point(&s, &y);
        law.advance_bilinear_contact(current(&a), current(&h), Some(current(&y)))
            .unwrap();
    }
    let relation = law.read_wave_relation(current(&h), 1).unwrap();
    assert!(relation.source_geometry.get().is_none());
    for source in [[0, 0, 1, 0, 1, 0], [0, 0, 2, 0, 2, 0], [0, 0, 1, 0, 1, 0]] {
        let source = point(&s, &source);
        let reads = s.census().section_read_outs;
        let cached = relation
            .read_source_passage(&law, current(&source))
            .unwrap();
        let (plain, plain_arrival) = prepare_source_contact(
            &s,
            1,
            WaveSourceReceiver::Direct,
            current(&source),
            &law.read_bilinear(current(&source), current(&h)).unwrap(),
            None,
        )
        .unwrap();
        assert_eq!(s.census().section_read_outs, reads);
        assert_eq!(
            cached.arrival.rest().unwrap(),
            plain_arrival.rest().unwrap()
        );
        let cached = cached.relation.source_contact().unwrap();
        assert_eq!(
            s.detach_section(cached.reaction.section(), 64).unwrap(),
            s.detach_section(plain.reaction.section(), 64).unwrap()
        );
        assert!(relation.source_geometry.get().is_some());
    }
    let y = point(&s, &[3, 0]);
    law.advance_bilinear_contact(current(&a), current(&h), Some(current(&y)))
        .unwrap();
    let material = law.rest().unwrap();
    assert!(relation.read_source_contact(&law, current(&a)).is_err());
    assert_eq!(law.rest().unwrap(), material);
    let new_relation = law.read_wave_relation(current(&h), 1).unwrap();
    let new_passage = new_relation.read_source_passage(&law, current(&a)).unwrap();
    let contact = new_passage.relation.source_contact().unwrap();
    assert!(new_passage
        .arrival
        .read_contact_with_geometry(
            contact.offered_joint(),
            ConditionContactMetric::UnitAdmittanceRealification,
            relation.source_geometry.get().unwrap()
        )
        .is_err());
    let (plain, _) = prepare_source_contact(
        &s,
        1,
        WaveSourceReceiver::Direct,
        current(&a),
        &law.read_bilinear(current(&a), current(&h)).unwrap(),
        None,
    )
    .unwrap();
    assert_eq!(
        s.detach_section(contact.reaction.section(), 64).unwrap(),
        s.detach_section(plain.reaction.section(), 64).unwrap()
    );
}
