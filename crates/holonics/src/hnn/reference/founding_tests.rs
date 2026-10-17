//! R4b publication: one atomic field/constitution/current/moment continuation.
use super::*;
use crate::hnn::field::FoundedRing;

fn fixture(budget: u64) -> (Reference, Resident, MomentId) {
    fixture_with_family(budget, false)
}

fn fixture_with_family(budget: u64, contact_family: bool) -> (Reference, Resident, MomentId) {
    let mut declaration = crate::hnn::tests::learning::chain_declaration(4096);
    declaration.founding = true;
    // One class-independent source clock; the later declared rings take carry only.
    for ring in &mut declaration.rings {
        ring.lock.clear();
    }
    declaration.rings[0].lock = (0..4).collect();
    let mut field = Field::declare(declaration).unwrap();
    if contact_family {
        let family = crate::hnn::receiving::FeatureFamily::new(vec![
            crate::hnn::receiving::Feature::contact(&field, 0),
        ])
        .unwrap();
        field = field.with_letter_family(family).unwrap();
    }
    let budget = if budget == 1 {
        Constitution::initial(&field, 1 << 40).unwrap().exact_bits()
    } else {
        budget
    };
    let reference = Reference::new(4, budget);
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    resident.open_founding().unwrap();
    let prefix = (0..128).map(|k| [0, 0, 1, 0, 2][k % 5]).collect::<Vec<_>>();
    let mut at = 0;
    let mut moment = None;
    while at < prefix.len() {
        let encoded = crate::hnn::tests::support::encoded(&field, &prefix[at..]);
        let (id, returned) = reference
            .ingest(&mut resident, moment.as_ref(), &encoded)
            .unwrap();
        let ingested = returned.forward.present().unwrap();
        at += ingested.cells;
        moment = Some(id);
        if ingested.carry_out {
            let phases = resident.admitted.clone();
            reference.close_aeon(&mut resident, &phases).unwrap();
        }
    }
    assert_eq!(resident.founding.as_ref().unwrap().cells(), 128);
    assert_eq!(resident.read_founding().unwrap().founded, Some(5));
    assert_eq!(resident.staged_founding, Some(5));
    assert_eq!(resident.read_founding().unwrap().founded, None);
    (reference, resident, moment.unwrap())
}

#[test]
fn r4b_14_publication_refusals_keep_the_complete_resident_and_staging() {
    let (reference, mut pending, moment) = fixture(1 << 40);
    let phases = pending.admitted[0].clone();
    let (id, _) = reference.refine(&mut pending, &moment, &phases).unwrap();
    let before = format!("{pending:?}");
    assert!(pending.publish_founding().is_err());
    assert_eq!(format!("{pending:?}"), before);
    assert_eq!(pending.staged_founding, Some(5));
    let targets = crate::hnn::tests::support::encoded(&pending.field, &vec![0; phases.aperture()]);
    reference.compare(&mut pending, id, &targets).unwrap();
    let before = format!("{pending:?}");
    assert!(pending.publish_founding().is_err());
    assert_eq!(format!("{pending:?}"), before);
    assert_eq!(pending.staged_founding, Some(5));
    let (_, mut small, _) = fixture(1);
    let before = format!("{small:?}");
    assert!(matches!(
        small.publish_founding(),
        Err(HnnError::ConstitutionBudget { .. })
    ));
    assert_eq!(format!("{small:?}"), before);
    assert_eq!(small.staged_founding, Some(5));
}

#[test]
fn r4b_15_next_cell_reaches_the_phase_the_founding_evidence_binned() {
    let (reference, mut resident, moment) = fixture(1 << 40);
    let n = resident.founding.as_ref().unwrap().cells();
    let founded = resident.publish_founding().unwrap().unwrap();
    assert_eq!(
        founded,
        FoundedRing {
            period: 5,
            key: (n - 1) % 5
        }
    );
    assert_eq!(resident.staged_founding, None);
    assert_eq!(resident.founding.as_ref().unwrap().cells(), 0);
    resident.admit_exact_current().unwrap();
    let cell = crate::hnn::tests::support::encoded(&resident.field, &[3]);
    reference
        .ingest(&mut resident, Some(&moment), &cell)
        .unwrap();
    let source = resident.moments.get(&moment).unwrap();
    for phase in 0..5 {
        assert_eq!(
            source.phase_counts(3, phase).unwrap().iter().sum::<u64>(),
            u64::from(phase as u64 == n % 5)
        );
    }
    assert_eq!(source.phase_counts(3, (n % 5) as usize).unwrap()[3], 1);
}

#[test]
fn r4b_16_save_and_continue_keeps_every_reading_and_rejects_the_old_field() {
    let (reference, mut direct, moment) = fixture(1 << 40);
    let old_field = direct.field.clone();
    direct.publish_founding().unwrap().unwrap();
    let state = direct.continuing_state(0).unwrap();
    let text = state.to_text();
    let parsed = ContinuingState::from_text(&text).unwrap();
    assert_eq!(state, parsed);
    let field = direct.field.clone();
    let opening = Constitution::initial(&field, 1 << 40).unwrap();
    let mut mounted = reference
        .mount_continued(&field, &Current::at_rest(&field), opening, &parsed)
        .unwrap();
    assert_eq!(mounted.continuing_state(0).unwrap().to_text(), text);
    assert!(
        reference
            .mount_continued(
                &old_field,
                &Current::at_rest(&old_field),
                Constitution::initial(&old_field, 1 << 40).unwrap(),
                &parsed
            )
            .is_err()
    );
    for k in 0..256 {
        let cell = crate::hnn::tests::support::encoded(&field, &[[0, 0, 1, 0, 2][(128 + k) % 5]]);
        let a = reference.ingest(&mut direct, Some(&moment), &cell).unwrap();
        let b = reference
            .ingest(&mut mounted, Some(&moment), &cell)
            .unwrap();
        assert_eq!(a, b);
        if direct.aeon.awaiting {
            let phases = direct.admitted.clone();
            assert_eq!(
                reference.close_aeon(&mut direct, &phases).unwrap(),
                reference.close_aeon(&mut mounted, &phases).unwrap()
            );
        }
        assert_eq!(direct.current, mounted.current);
        assert_eq!(direct.constitution, mounted.constitution);
        assert_eq!(direct.founding, mounted.founding);
        assert_eq!(
            direct.read_founding().unwrap(),
            mounted.read_founding().unwrap()
        );
        assert_eq!(
            direct.continuing_state(0).unwrap().to_text(),
            mounted.continuing_state(0).unwrap().to_text()
        );
    }
}

#[test]
fn r4b_17_publication_keeps_all_old_motion_and_never_coarsens_the_word() {
    let (reference, mut resident, moment) = fixture(1 << 40);
    let phases = resident.admitted[0].clone();
    let (id, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    reference
        .discard(&mut resident, Handle::Pending(id))
        .unwrap();
    let before = resident
        .carried
        .clone()
        .expect("the actual refine carries its end");
    let old_word = *resident.field.word_lattice().unwrap();
    let tally = resident.tally.clone();
    let old_field = resident.field.clone();
    let old_current = resident.current.clone();
    resident.publish_founding().unwrap().unwrap();
    let after = resident.carried.as_ref().unwrap();
    assert_eq!(after.ticks, before.ticks);
    assert_eq!(&after.change.storage[..3], before.change.storage);
    assert_eq!(&after.change.arrivals[..2], before.change.arrivals);
    assert_eq!(&after.change.states[..2], before.change.states);
    assert_eq!(&after.change.resonators[..3], before.change.resonators);
    assert_eq!(
        &after.change.resonator_phases[..3],
        before.change.resonator_phases
    );
    assert_eq!(&after.conductances[..2], before.conductances);
    assert_eq!(&after.momenta[..2], before.momenta);
    assert_eq!(&after.resonator_momenta[..3], before.resonator_momenta);
    let expected_phase = resident
        .constitution
        .ring_resonator(3)
        .unwrap()
        .pump()
        .unwrap()
        .phase_at(before.ticks.saturating_sub(1));
    assert!(after.change.storage[3].iter().all(Zero::is_zero));
    assert_eq!(after.change.resonator_phases[3], Some(expected_phase));
    assert!(
        after.change.resonators[3]
            .as_ref()
            .unwrap()
            .iter()
            .flatten()
            .all(Zero::is_zero)
    );
    assert_eq!(&resident.current.lift()[..3], old_current.lift());
    assert_eq!(resident.tally, tally);
    let word = resident.field.word_lattice().unwrap();
    assert!(word.chart_exponent() >= old_word.chart_exponent());
    assert!(word.target_exponent() >= old_word.target_exponent());
    assert!(word.transient_exponent() >= old_word.transient_exponent());
    assert_eq!(&resident.field.rings()[..3], old_field.rings());
}

#[test]
fn r4b_ingest_refusal_does_not_receive_a_founding_cell() {
    let (reference, mut resident, _) = fixture(1 << 40);
    let law = resident.founding.clone();
    let cell = crate::hnn::tests::support::encoded(&resident.field, &[0]);
    assert!(
        reference
            .ingest(&mut resident, Some(&MomentId(u64::MAX)), &cell)
            .is_err()
    );
    assert_eq!(resident.founding, law);
    assert!(resident.open_founding().is_err());
}

#[test]
fn r4b_contact_family_and_arrived_restore_on_the_founded_field_only() {
    let (reference, mut resident, moment) = fixture_with_family(1 << 40, true);
    let old_field = resident.field.clone();
    // Keep the first-law operand so the saved arrived address crosses the same field change.
    let phases = resident.admitted[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let targets = crate::hnn::tests::support::encoded(&resident.field, &vec![0; phases.aperture()]);
    let (staged, _) = reference.compare(&mut resident, pending, &targets).unwrap();
    reference
        .discard(&mut resident, Handle::Staged(staged))
        .unwrap();
    let letters = resident.address.letters().to_vec();
    let founded = resident.publish_founding().unwrap().unwrap();
    assert_eq!(resident.address.letters(), letters);
    assert!(resident.address.reader().agrees(
        &resident.field,
        &resident.current,
        &resident.aeon.opening
    ));
    assert_eq!(
        resident.current.phase(&resident.field, 3).unwrap(),
        founded.key
    );
    let state = resident.continuing_state(0).unwrap();
    let text = state.to_text();
    let parsed = ContinuingState::from_text(&text).unwrap();
    let opening = Constitution::initial(&resident.field, 1 << 40).unwrap();
    let restored = reference
        .mount_continued(
            &resident.field,
            &Current::at_rest(&resident.field),
            opening,
            &parsed,
        )
        .unwrap();
    assert_eq!(restored.continuing_state(0).unwrap().to_text(), text);
    assert_eq!(restored.address, resident.address);
    let restored_arrived = restored.arrived.as_ref().unwrap();
    let arrived = resident.arrived.as_ref().unwrap();
    // The producing receiver's phases are carried inside the ratio (`PendingRatio`), so the
    // ratio's equality covers them.
    assert_eq!(restored_arrived.ratio, arrived.ratio);
    assert_eq!(restored_arrived.opening, arrived.opening);
    assert_eq!(restored_arrived.targets, arrived.targets);
    assert!(
        reference
            .mount_continued(
                &old_field,
                &Current::at_rest(&old_field),
                Constitution::initial(&old_field, 1 << 40).unwrap(),
                &parsed
            )
            .is_err()
    );
}

fn arrived_features(resident: &Resident) -> Vec<Vec<Rat>> {
    let arrived = resident.arrived.as_ref().unwrap();
    let (word, _) = arrived
        .ratio
        .read_successor_against_on(
            &resident.field,
            &resident.constitution,
            &mut resident.charts.clone(),
            &arrived.targets,
            &arrived.opening,
        )
        .unwrap();
    word.receiving_anchors(arrived.ratio.phases()).unwrap()
}

#[test]
fn r4b_arrived_crosses_the_founding_then_precision_and_collapse() {
    let (reference, mut resident, moment) = fixture(1 << 40);
    for _ in 0..2 {
        let phases = resident.admitted[0].clone();
        let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
        let targets =
            crate::hnn::tests::support::encoded(&resident.field, &vec![0; phases.aperture()]);
        let (staged, _) = reference.compare(&mut resident, pending, &targets).unwrap();
        reference
            .discard(&mut resident, Handle::Staged(staged))
            .unwrap();
    }
    assert!(matches!(
        resident.arrived.as_ref().unwrap().opening,
        WordOpening::Received { .. }
    ));
    let before = resident.ledger.balance().clone();
    resident.publish_founding().unwrap().unwrap();
    let arrived = resident.arrived.as_ref().unwrap();
    let reread = arrived
        .code_length(
            &resident.field,
            &resident.constitution,
            &mut resident.charts.clone(),
        )
        .unwrap()
        .0;
    let after = resident.ledger.balance();
    assert_eq!(after.closing.as_ref(), Some(&reread));
    assert_eq!(after.exchanges, before.exchanges + 1);
    assert_eq!(
        (after.arrivals, after.cells),
        (before.arrivals, before.cells)
    );
    let old = before.closing.as_ref().unwrap();
    let step = ExactInterval {
        lower: &reread.lower - &old.upper,
        upper: &reread.upper - &old.lower,
    };
    assert_eq!(after.exchange.lower, &before.exchange.lower + &step.lower);
    assert_eq!(after.exchange.upper, &before.exchange.upper + &step.upper);
    println!(
        "r4b_founding_exchange lower={} upper={} arrivals={} cells={} exchanges={}",
        step.lower, step.upper, after.arrivals, after.cells, after.exchanges
    );
    assert_eq!(after.total().lower, after.change().lower - &after.widening);
    assert_eq!(after.total().upper, after.change().upper + &after.widening);

    // As in R2's fixed carried-state control, seed a legal retained remainder in a zero map.
    // This witnesses transport/accounting, not production of the remainder by learning.
    let receiver = resident.field.receivers()[0].ring;
    let features = arrived_features(&resident);
    let column = features[0]
        .iter()
        .position(|x| !x.is_zero())
        .expect("the receiving word must reach a nonzero feature");
    let unit = resident
        .constitution
        .lattice(Locus::ReceivingMap(receiver))
        .unwrap()
        .unit();
    let retained = if features[0][column] > Rat::zero() {
        -&unit / crate::ratio::integer(4)
    } else {
        &unit / crate::ratio::integer(4)
    };
    let mut text = resident.constitution.continuing_state(0).unwrap().to_text();
    let start = text
        .find(&format!(
            "receiving {} {}\n",
            2 * resident.field.alphabet(),
            resident.field.ring(receiver).width()
        ))
        .unwrap();
    let at = start + text[start..].find("map-carry 0\n").unwrap();
    text.replace_range(
        at..at + "map-carry 0\n".len(),
        &format!("map-carry 1\n{column} {retained}\n"),
    );
    let opening = Constitution::initial(&resident.field, 1 << 40).unwrap();
    let text = ContinuingState::stamped(&text, &opening).unwrap();
    resident.constitution = opening
        .continued(&ContinuingState::from_text(&text).unwrap())
        .unwrap();
    let event = resident
        .constitution
        .receiving_precision_event(
            receiver,
            &arrived_features(&resident),
            &resident.field.receivers()[0].tolerance,
        )
        .unwrap()
        .expect("the retained component must need precision");
    resident.publish_receiving_precision(&event).unwrap();
    assert_eq!(
        resident.ledger.balance().publications,
        before.publications + 1
    );
    let now = resident
        .arrived
        .as_ref()
        .unwrap()
        .code_length(
            &resident.field,
            &resident.constitution,
            &mut resident.charts.clone(),
        )
        .unwrap()
        .0;
    assert_eq!(resident.ledger.balance().closing.as_ref(), Some(&now));
    let cells = crate::hnn::tests::support::encoded(&resident.field, &[0; 16]);
    assert!(
        reference
            .ingest(&mut resident, Some(&moment), &cells)
            .unwrap()
            .1
            .forward
            .present()
            .unwrap()
            .carry_out
    );
    let phases = resident.admitted.clone();
    reference.close_aeon(&mut resident, &phases).unwrap();
    resident
        .arrived
        .as_ref()
        .unwrap()
        .code_length(
            &resident.field,
            &resident.constitution,
            &mut resident.charts.clone(),
        )
        .unwrap();
}
