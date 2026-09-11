use super::super::contact_tests::{calibrate, current, observe, phase, points, world};
use super::*;
use crate::embedding_fiber::ResidentReadout;

fn learned_pair<'c>(s: &'c ResidentSurface<'c>) -> Vec<ResidentConstitutiveFibre<'c>> {
    let mut sources = [world(s), world(s)];
    let mut laws = (0..2)
        .map(|_| ResidentConstitutiveFibre::found_bilinear_contact(s, 1, 2, 1).unwrap())
        .collect::<Vec<_>>();
    let phases = [[1, 0], [0, 1], [-1, 0], [0, -1]];
    for x in [[0, 0], [1, 0], [0, 1]] {
        for a in phases {
            for b in phases {
                let source = points(s, &x);
                let conditions = points(s, &[a[0], a[1], b[0], b[1]]);
                for (member, c) in [a, b].into_iter().enumerate() {
                    let measured = observe(
                        &mut sources[member],
                        phase(x[0], x[1], 1),
                        phase(c[0], c[1], 1),
                    );
                    let words = NativePhaseCurrent::from_current(&measured).unwrap().words();
                    let observed = points(s, &words);
                    laws[member]
                        .advance_bilinear_contact(
                            current(&source),
                            current(&conditions),
                            Some(ResidentConstitutiveCurrent::rational(&observed).unwrap()),
                        )
                        .unwrap();
                }
            }
        }
    }
    laws
}
fn value(result: &ResidentConstitutiveReturn<'_>) -> Vec<Rat> {
    match result.inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Unique { current } => current,
        other => panic!("expected exact current: {other:?}"),
    }
}

#[test]
#[ignore = "requires CUDA; generator dependence selects the changed directions of a shared condition field and the whole neighborhood resumes"]
fn shared_condition_changes_only_receivers_that_depend_on_the_return() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let laws = learned_pair(&s);
    let initial = points(&s, &[0, 4, 3, 0, 5]);
    let mut body = ResidentGeneratorNeighborhood::with_shared_condition(
        laws,
        ResidentConstitutiveCurrent::rational(&initial).unwrap(),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let source = points(&s, &[1, 0]);
    let next_source = points(&s, &[2, 3]);
    let observed = points(&s, &[3, 4, 5]);
    let before = body.rest().unwrap();
    let independent_before = body.read(1, current(&next_source)).unwrap();
    let dependent_before = body.read(0, current(&next_source)).unwrap();
    let reads = s.census().section_read_outs;
    let step = body
        .advance(
            0,
            current(&source),
            Some(ResidentConstitutiveCurrent::rational(&observed).unwrap()),
        )
        .unwrap();
    let independent_after = body.read(1, current(&next_source)).unwrap();
    let dependent_after = body.read(0, current(&next_source)).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert!(step.belongs_to(&body));
    assert_eq!(value(&independent_before), value(&independent_after));
    assert_ne!(value(&dependent_before), value(&dependent_after));
    let expected = phase(-6, 17, 5).current();
    assert_eq!(
        value(&dependent_after),
        vec![expected.real, expected.imaginary]
    );
    let after = body.rest().unwrap();
    assert_eq!(after.epoch(), 1);
    assert_eq!(after.condition().contacts(), 1);
    assert_eq!(after.condition().current_words(), &[3, 4, 3, 0, 5]);
    for (a, b) in before.laws().iter().zip(after.laws()) {
        assert_eq!(a.relation(), b.relation());
    }
    let mut wire = Vec::new();
    after.write(&mut wire).unwrap();
    drop(body);
    let saved = GeneratorNeighborhoodRest::read(&mut wire.as_slice(), wire.len() as u64).unwrap();
    assert_eq!(saved, after);
    let restored = saved.remount(&s).unwrap();
    assert!(!step.belongs_to(&restored));
    assert_eq!(restored.rest().unwrap(), after);
    assert_eq!(
        restored
            .last_received_evidence()
            .unwrap()
            .family
            .inspect()
            .unwrap(),
        step.contact.as_ref().unwrap().family().inspect().unwrap()
    );
    assert_eq!(
        value(&restored.read(0, current(&next_source)).unwrap()),
        value(&dependent_after)
    );
    assert_eq!(
        value(&restored.read(1, current(&next_source)).unwrap()),
        value(&independent_after)
    );
    eprintln!(
        "two-generator rest: {} bytes, ranks {:?}, epoch {}",
        wire.len(),
        after
            .laws()
            .iter()
            .map(ConstitutiveFibreRest::rank)
            .collect::<Vec<_>>(),
        after.epoch()
    );
}

#[test]
#[ignore = "requires CUDA; a late source-lift refusal cannot publish either neighborhood law or current"]
fn failed_material_return_preserves_the_complete_neighborhood() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut source_world = world(&s);
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut law, &mut source_world, None);
    drop(source_world);
    let initial = points(&s, &[1, 0]);
    let mut body = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law],
        current(&initial),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    // The square of this power of two exceeds a signed source word. The inferred condition
    // and its actual current fit, but lifting them together into the learned source does not.
    let large = 1_i64 << (i64::BITS / 2);
    let source = points(&s, &[large, 0]);
    let received = points(&s, &[1, 0]);
    let family = body
        .generator(0)
        .unwrap()
        .read_condition_preimage(current(&source), current(&received))
        .unwrap();
    let prepared = body.condition.prepare_contact(&family).unwrap();
    assert_eq!(
        prepared.inspect().unwrap().successor,
        vec![
            Rat::new(1.into(), large.into()),
            Rat::from_integer(0.into())
        ]
    );
    drop(prepared);
    let before = body.rest().unwrap();
    assert!(
        body.advance(0, current(&source), Some(current(&received)))
            .is_err()
    );
    assert_eq!(body.rest().unwrap(), before);
    body.advance(0, current(&received), Some(current(&received)))
        .unwrap();
    assert_eq!(body.epoch(), 1);
}

#[test]
#[ignore = "requires CUDA; an unrepresented observation forms local material while preserving a recoverable condition state"]
fn neighborhood_development_forms_an_independent_local_relation() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let law = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    let initial = points(&s, &[1, 0]);
    let source = points(&s, &[2, 0]);
    let mut world = world(&s);
    let observed = observe(&mut world, phase(2, 0, 1), phase(1, 0, 1));
    let observed = points(
        &s,
        &NativePhaseCurrent::from_current(&observed).unwrap().words(),
    );
    drop(world);
    let mut body = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law],
        current(&initial),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let step = body
        .advance(
            0,
            current(&source),
            Some(ResidentConstitutiveCurrent::rational(&observed).unwrap()),
        )
        .unwrap();
    assert!(matches!(
        step.prediction.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    assert!(
        step.formation
            .as_ref()
            .unwrap()
            .inspect()
            .unwrap()
            .formed_pivot
            .is_some()
    );
    assert_eq!(
        value(&body.read(0, current(&source)).unwrap()),
        vec![Rat::from_integer(2.into()), Rat::from_integer(0.into())]
    );
    let saved = body.rest().unwrap();
    let family = body
        .last_received_evidence()
        .unwrap()
        .family
        .inspect()
        .unwrap();
    drop(body);
    let restored = saved.remount(&s).unwrap();
    assert_eq!(
        restored
            .last_received_evidence()
            .unwrap()
            .family
            .inspect()
            .unwrap(),
        family
    );
}

#[test]
#[ignore = "requires CUDA; a prepared current can commit only to its actual unchanged predecessor"]
fn prepared_contact_rejects_other_and_stale_standing() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut source_world = world(&s);
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut law, &mut source_world, None);
    drop(source_world);
    let initial = points(&s, &[1, 0]);
    let family = law
        .read_condition_preimage(current(&initial), current(&initial))
        .unwrap();
    let mut left = law
        .retain_condition_current(
            current(&initial),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
    let mut right = law
        .retain_condition_current(
            current(&initial),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
    let before = left.rest().unwrap();
    let prepared = left.prepare_contact(&family).unwrap();
    assert!(right.commit_contact(prepared).is_err());
    assert_eq!(left.rest().unwrap(), before);
    assert_eq!(right.rest().unwrap(), before);
    let stale = left.prepare_contact(&family).unwrap();
    left.contact(&family).unwrap();
    let after = left.rest().unwrap();
    assert!(left.commit_contact(stale).is_err());
    assert_eq!(left.rest().unwrap(), after);
    let decoded = family.rest().unwrap().remount(&s).unwrap();
    assert_eq!(decoded.inspect().unwrap(), family.inspect().unwrap());
}

#[test]
#[ignore = "requires CUDA; discarding a complete prepared member/condition successor preserves conduct and rest"]
fn staged_neighborhood_discard_and_stale_publication_keep_the_predecessor() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let laws = learned_pair(&s);
    let h = points(&s, &[0, 1, 1, 0]);
    let mut body = ResidentGeneratorNeighborhood::with_shared_condition(
        laws,
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let x = points(&s, &[1, 0]);
    let y = points(&s, &[1, 0]);
    let before = body.rest().unwrap();
    let prior = value(&body.read(0, current(&x)).unwrap());
    let reads = s.census().section_read_outs;
    let prepared = body
        .prepare_advance(0, current(&x), Some(current(&y)))
        .unwrap();
    assert!(body.can_commit_advance(&prepared));
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(body.rest().unwrap(), before);
    assert_eq!(value(&body.read(0, current(&x)).unwrap()), prior);
    drop(prepared);
    assert_eq!(body.rest().unwrap(), before);
    let stale = body
        .prepare_advance(0, current(&x), Some(current(&y)))
        .unwrap();
    let committed = body
        .prepare_advance(0, current(&x), Some(current(&y)))
        .unwrap();
    body.publish_advance(committed);
    assert!(!body.can_commit_advance(&stale));
    let after = body.rest().unwrap();
    assert_ne!(after, before);
    drop(stale);
    assert_eq!(body.rest().unwrap(), after);
}

#[test]
#[ignore = "requires CUDA; preparation identity survives absent observations and independent equal-shaped bodies"]
fn staged_neighborhood_read_only_proposal_is_owner_qualified() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let h = points(&s, &[0, 0]);
    let x = points(&s, &[0, 0]);
    let make = || {
        ResidentGeneratorNeighborhood::with_shared_condition(
            vec![ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap()],
            current(&h),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap()
    };
    let mut a = make();
    let b = make();
    let pending = a.prepare_advance(0, current(&x), None).unwrap();
    assert!(a.can_commit_advance(&pending));
    assert!(!b.can_commit_advance(&pending));
    a.advance(0, current(&x), None).unwrap();
    assert!(!a.can_commit_advance(&pending));
}
