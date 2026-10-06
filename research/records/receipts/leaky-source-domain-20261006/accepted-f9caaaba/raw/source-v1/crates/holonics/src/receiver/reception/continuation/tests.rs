use super::*;
use crate::holon::restriction::PreimageFibre;
use crate::ratio::linear::vector::{integer_matrix, ints};
use crate::ratio::{integer, rat};

fn law(storage: i64, coupling: i64) -> JointLaw {
    JointLaw::new(
        ReferenceHolon::new(
            Holon::new(
                PortHolon::medium(
                    &integer_matrix(&[&[0, -coupling], &[coupling, 0]]).unwrap(),
                    &ExactRatMatrix::zero(2, 2).unwrap(),
                    SymmetricForm::from_diagonal(ints(&[storage, 1])),
                    &integer_matrix(&[&[1], &[0]]).unwrap(),
                    false,
                )
                .unwrap(),
            )
            .unwrap(),
            integer(1),
            Scheme::Midpoint,
        )
        .unwrap(),
        1,
    )
    .unwrap()
}

fn receipt() -> ReceiptLaw {
    ReceiptLaw::new(2, vec![], vec![]).unwrap()
}
fn face() -> ReceiverFace {
    ReceiverFace::receiver_state(1, 1).unwrap()
}

#[test]
fn equal_values_do_not_replace_source_clock_or_producer_and_clock_carries() {
    let source = Arc::new(ints(&[1, 0]));
    let mut reading = Clock::ring(integer(1), 2).unwrap();
    reading.advance(&BigUint::from(1u8));
    let clock = Arc::new(reading);
    let producer = JointProducer::declared(law(1, 1), source.clone(), clock.clone()).unwrap();
    let opened = producer
        .open(HolonState::at((*source).clone(), 1), &source, &clock)
        .unwrap();
    let returned = producer
        .interact(&opened, &source, &clock, &ints(&[0]), &face(), &receipt())
        .unwrap();
    let reached = returned.forward.present().unwrap().reached();
    assert_eq!(reached.state().commit, 2);
    assert_eq!(reached.clock().ticks(), BigUint::from(2u8));
    assert_eq!(reached.clock().phase(), &[BigUint::from(0u8)]);
    assert_eq!(reached.clock().winding(), &BigUint::from(1u8));
    let independent_source = Arc::new((*source).clone());
    let independent_clock = Arc::new((*clock).clone());
    assert!(matches!(
        producer.interact(
            reached,
            &independent_source,
            &clock,
            &ints(&[0]),
            &face(),
            &receipt()
        ),
        Err(HolonError::ConformanceFailed {
            what: "the continuation belongs to this source"
        })
    ));
    assert!(matches!(
        producer.interact(
            reached,
            &source,
            &independent_clock,
            &ints(&[0]),
            &face(),
            &receipt()
        ),
        Err(HolonError::ConformanceFailed {
            what: "the continuation belongs to this clock"
        })
    ));
    let other_producer = JointProducer::declared(law(1, 1), source.clone(), clock.clone()).unwrap();
    assert!(matches!(
        other_producer.interact(reached, &source, &clock, &ints(&[0]), &face(), &receipt()),
        Err(HolonError::ConformanceFailed {
            what: "the reached state belongs to this producer"
        })
    ));
    assert!(
        producer
            .clone()
            .interact(reached, &source, &clock, &ints(&[0]), &face(), &receipt())
            .is_ok()
    );
    assert!(
        producer
            .open(HolonState::at((*source).clone(), 2), &source, &clock)
            .is_err()
    );
    assert!(
        JointProducer::declared(
            law(1, 1),
            source,
            Arc::new(Clock::unwound(rat(1, 2)).unwrap())
        )
        .is_err()
    );
}

#[test]
fn material_work_at_reached_point_and_successor_delegation_agree() {
    let source = Arc::new(ints(&[1, 0]));
    let clock = Arc::new(Clock::unwound(integer(1)).unwrap());
    let producer = JointProducer::declared(law(1, 1), source.clone(), clock.clone()).unwrap();
    let origin = producer
        .open(HolonState::new((*source).clone()), &source, &clock)
        .unwrap();
    let produced = producer
        .interact(&origin, &source, &clock, &ints(&[0]), &face(), &receipt())
        .unwrap();
    let step = produced.forward.present().unwrap();
    let successor = law(2, 1);
    let (next_producer, returned) = producer
        .return_storage(
            step.reached(),
            &source,
            &clock,
            successor.clone(),
            integer(1),
            &receipt(),
        )
        .unwrap();
    let next = returned.forward.present().unwrap();
    let work = returned.deposit.present().unwrap();
    assert_eq!(next.state(), step.reached().state());
    assert_eq!(next.clock(), step.reached().clock());
    assert_eq!(work.work, rat(9, 50));
    assert_eq!(&work.after - &work.before, work.work);
    assert!(!returned.pullback.is_present());
    // Independent existing owner: the original passage followed by this same storage return.
    let committed = producer
        .law()
        .law()
        .commit(
            origin.state(),
            &ints(&[0]),
            producer.law().law().holon().port_holon().storage(),
            producer.law().law().holon().active().relation(),
            successor.law().holon().port_holon().storage(),
        )
        .unwrap();
    assert_eq!(&committed.state, next.state());
    assert!(committed.balance.is_exact());
    assert_eq!(committed.balance.deposition_work, work.work);
    assert_eq!(
        committed.balance.stored_change,
        step.step().balance().stored_change.clone() + &work.work
    );
    // Withheld input: no reopening or replay of the source, and no second commit of the deposit.
    let delegated = next_producer
        .interact(next, &source, &clock, &ints(&[3]), &face(), &receipt())
        .unwrap();
    let direct = successor
        .interact(step.reached().state(), &ints(&[3]), &face(), &receipt())
        .unwrap();
    assert_eq!(
        delegated.forward.present().unwrap().step(),
        direct.step().unwrap()
    );
    assert_eq!(
        delegated.forward.present().unwrap().reached().state().commit,
        2
    );
    assert!(
        producer
            .interact(next, &source, &clock, &ints(&[3]), &face(), &receipt())
            .is_err()
    );
}

#[test]
fn zero_configuration_fibre_separates_after_reopening_and_selected_law_delegates() {
    // Declared laws of the same kind, not an authored table of predicted answers. This control
    // checks a finite separating receiver; it is not a claim of continuous key inference.
    let source = Arc::new(vec![law(1, 1), law(2, 1)]);
    let clock = Arc::new(Clock::unwound(integer(1)).unwrap());
    let observed = source[1]
        .interact(
            &HolonState::new(ints(&[0, 0])),
            &ints(&[0]),
            &face(),
            &receipt(),
        )
        .unwrap();
    let candidates: Vec<_> = (0..source.len())
        .filter(|&i| {
            source[i]
                .interact(
                    &HolonState::new(ints(&[0, 0])),
                    &ints(&[0]),
                    &face(),
                    &receipt(),
                )
                .unwrap()
                .step()
                .unwrap()
                .face()
                == observed.step().unwrap().face()
        })
        .collect();
    let fibre = PreimageFibre::new(observed.step().unwrap().face().to_vec(), candidates);
    assert_eq!(fibre.members, vec![0, 1]);
    let producer =
        JointProducer::declared(source[0].clone(), source.clone(), clock.clone()).unwrap();
    let nonexciting = producer
        .open(HolonState::new(ints(&[0, 0])), &source, &clock)
        .unwrap();
    let quiet = producer
        .interact(
            &nonexciting,
            &source,
            &clock,
            &ints(&[0]),
            &face(),
            &receipt(),
        )
        .unwrap();
    assert!(!quiet.deposit.is_present());
    assert!(!quiet.pullback.is_present());
    // This reopens the supplied probe configuration; it does not continue the quiet reached state.
    // Its actual response separates these two declared material candidates.
    let probe = HolonState::new(ints(&[1, 0]));
    let observed_probe = source[1]
        .interact(&probe, &ints(&[0]), &face(), &receipt())
        .unwrap();
    let selected: Vec<_> = fibre
        .members
        .into_iter()
        .filter(|&i| {
            source[i]
                .interact(&probe, &ints(&[0]), &face(), &receipt())
                .unwrap()
                .step()
                .unwrap()
                .face()
                == observed_probe.step().unwrap().face()
        })
        .collect();
    assert_eq!(selected.len(), 1);
    let opened = producer.open(probe, &source, &clock).unwrap();
    let reached = producer
        .interact(&opened, &source, &clock, &ints(&[0]), &face(), &receipt())
        .unwrap();
    let (located, applied) = producer
        .return_storage(
            reached.forward.present().unwrap().reached(),
            &source,
            &clock,
            source[selected[0]].clone(),
            integer(1),
            &receipt(),
        )
        .unwrap();
    let applied_state = applied.forward.present().unwrap();
    let future = located
        .interact(
            applied_state,
            &source,
            &clock,
            &ints(&[-2]),
            &face(),
            &receipt(),
        )
        .unwrap();
    let direct_successor = source[1]
        .interact(applied_state.state(), &ints(&[-2]), &face(), &receipt())
        .unwrap();
    assert_eq!(
        future.forward.present().unwrap().step(),
        direct_successor.step().unwrap()
    );
    let unlocated = producer
        .interact(
            reached.forward.present().unwrap().reached(),
            &source,
            &clock,
            &ints(&[-2]),
            &face(),
            &receipt(),
        )
        .unwrap();
    assert_ne!(
        unlocated.forward.present().unwrap().step().face(),
        direct_successor.step().unwrap().face()
    );
}

#[test]
fn unresolved_receiver_motion_is_carried_for_a_later_separating_face() {
    let source = Arc::new(ints(&[1, 0]));
    let clock = Arc::new(Clock::unwound(integer(1)).unwrap());
    let producer = JointProducer::declared(law(1, 1), source.clone(), clock.clone()).unwrap();
    let origin = producer
        .open(HolonState::new((*source).clone()), &source, &clock)
        .unwrap();
    let blind = ReceiverFace::new(
        ExactRatMatrix::zero(1, 1).unwrap(),
        ExactRatMatrix::zero(1, 1).unwrap(),
        ints(&[0]),
        ints(&[0]),
    )
    .unwrap();
    let returned = producer
        .interact(&origin, &source, &clock, &ints(&[0]), &blind, &receipt())
        .unwrap();
    let produced = returned.forward.present().unwrap();
    assert_eq!(produced.step().face(), &ints(&[0]));
    assert_eq!(produced.step().unresolved().directions, vec![ints(&[1])]);
    assert_eq!(produced.step().next_receiver(), &[rat(4, 5)]);
    // Changing only the reading neither replaces the hidden state by the face nor advances it.
    assert_eq!(
        face()
            .read(
                produced.step().next_source(),
                produced.step().next_receiver()
            )
            .unwrap(),
        vec![rat(4, 5)]
    );
    let continued = producer
        .interact(
            produced.reached(),
            &source,
            &clock,
            &ints(&[0]),
            &face(),
            &receipt(),
        )
        .unwrap();
    let direct = law(1, 1)
        .interact(
            &produced.step().next_state(),
            &ints(&[0]),
            &face(),
            &receipt(),
        )
        .unwrap();
    assert_eq!(
        continued.forward.present().unwrap().step(),
        direct.step().unwrap()
    );
}

#[test]
fn material_return_refuses_other_changes_bad_bound_and_wrong_boundary() {
    let source = Arc::new(ints(&[1, 0]));
    let clock = Arc::new(Clock::unwound(integer(1)).unwrap());
    let producer = JointProducer::declared(law(1, 1), source.clone(), clock.clone()).unwrap();
    let origin = producer
        .open(HolonState::new((*source).clone()), &source, &clock)
        .unwrap();
    let produced = producer
        .interact(&origin, &source, &clock, &ints(&[0]), &face(), &receipt())
        .unwrap();
    let reached = produced.forward.present().unwrap().reached();
    assert!(matches!(
        producer.return_storage(reached, &source, &clock, law(2, 2), integer(1), &receipt()),
        Err(HolonError::Unsupported { .. })
    ));
    assert!(matches!(
        producer.return_storage(reached, &source, &clock, law(2, 1), rat(1, 2), &receipt()),
        Err(HolonError::DepositExceedsBound { .. })
    ));
    assert!(matches!(
        producer.return_storage(reached, &source, &clock, law(-1, 1), integer(1), &receipt()),
        Err(HolonError::ConformanceFailed {
            what: "both storage forms are nonnegative"
        })
    ));
    assert!(
        producer
            .return_storage(
                reached,
                &Arc::new((*source).clone()),
                &clock,
                law(2, 1),
                integer(1),
                &receipt()
            )
            .is_err()
    );
    assert!(
        producer
            .return_storage(
                reached,
                &source,
                &Arc::new((*clock).clone()),
                law(2, 1),
                integer(1),
                &receipt()
            )
            .is_err()
    );
    assert_eq!(reached.state().commit, 1);
    assert_eq!(
        reached.state(),
        &produced.forward.present().unwrap().step().next_state()
    );
    let pump_clock = Clock::ring(integer(1), 2).unwrap();
    let pumped = law(1, 1)
        .law()
        .holon()
        .clone()
        .with_pump(Pump {
            schedule: PumpSchedule::new(vec![SymmetricForm::from_diagonal(ints(&[1, 1]))]).unwrap(),
            clock: pump_clock,
        })
        .unwrap();
    let pumped = JointLaw::new(
        ReferenceHolon::new(pumped, integer(1), Scheme::Midpoint).unwrap(),
        1,
    )
    .unwrap();
    assert!(matches!(
        JointProducer::declared(pumped, source, clock),
        Err(HolonError::Unsupported {
            what: "a joint continuation binding",
            reason: "a pumped law needs its own phase and section binding"
        })
    ));
}
