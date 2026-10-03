//! The existing wave Holon consumes the bound return in charge/flux coordinates (Refs #73 #62).
//! This uses its midpoint joint law. The staggered propagate balance is a different integrator
//! and is not claimed to be interchangeable with this continuation.
use super::*;
use std::sync::Arc;
use num_traits::{One, Zero};
use crate::holon::HolonState;
use crate::holon::law::{ReferenceHolon, Scheme};
use crate::navigator::Clock;
use crate::ratio::linear::vector::matrix;
use crate::ratio::{integer, rat};
use crate::receiver::receipt::{ReceiptLaw, RegionChart};
use crate::receiver::reception::{JointLaw, ReceiverFace};

fn reader() -> crate::ratio::linear::ExactRatMatrix {
    matrix(1, 5, |_, column| {
        if column == 0 || column == 3 { Rat::one() } else { Rat::zero() }
    }).unwrap()
}

fn admitted(chain: &WaveChain) -> JointLaw {
    let native = ReferenceHolon::new(chain.holon().unwrap(), chain.tick().clone(), Scheme::Midpoint)
        .unwrap();
    JointLaw::reading(&native, &reader()).unwrap()
}

#[test]
fn repeated_wave_material_returns_preserve_charge_flux_and_continue_the_native_joint_law() {
    let incidence = Incidence::open_chain(3).unwrap();
    let predecessor = Arc::new(WaveChain::new(
        incidence.clone(),
        WaveMaterial::uniform(&incidence, &integer(2), &rat(1, 4), &integer(3)).unwrap(),
        rat(1, 4),
    ).unwrap());
    let successor = WaveChain::new(
        incidence.clone(),
        WaveMaterial::uniform(&incidence, &integer(3), &rat(1, 4), &integer(2)).unwrap(),
        predecessor.tick().clone(),
    ).unwrap();
    let wave = WaveState::new(vec![integer(1), integer(-1), integer(2)], vec![integer(1), integer(-2)]);
    let mut point = predecessor.configuration(&wave).unwrap();
    point.push(Rat::zero());
    let clock = Arc::new(Clock::unwound(predecessor.tick().clone()).unwrap());
    let producer = WaveChain::bind_receiver(&predecessor, &clock, &reader()).unwrap();
    assert_eq!(producer.current(), predecessor.as_ref());
    assert_eq!(producer.law(), &admitted(&predecessor));
    let origin = producer.open(HolonState::new(point), &predecessor, &clock).unwrap();
    let receipt = ReceiptLaw::new(6, vec![], vec![]).unwrap();
    let face = ReceiverFace::receiver_state(5, 1).unwrap();
    let input = vec![Rat::zero(); 3];
    let produced = producer.interact(&origin, &predecessor, &clock, &input, &face, &receipt).unwrap();
    let reached = produced.forward.present().unwrap().reached();
    let native_point = &reached.state().configuration[..5];
    let old_reading = predecessor.decode_configuration(native_point).unwrap();
    let new_reading = successor.decode_configuration(native_point).unwrap();
    assert_eq!(predecessor.configuration(&old_reading).unwrap(), native_point);
    assert_eq!(successor.configuration(&new_reading).unwrap(), native_point);
    assert_ne!(old_reading, new_reading);
    assert_ne!(successor.configuration(&old_reading).unwrap(), native_point);
    let next_law = admitted(&successor);
    let (next_producer, returned, native_reading) = predecessor.return_material(
        &predecessor, &producer, reached, &clock, &successor, &reader(), rat(1, 2), &receipt,
    ).unwrap();
    assert_eq!(native_reading, new_reading);
    assert_eq!(next_producer.current(), &successor);
    assert_eq!(next_producer.law(), &next_law);
    let wrong_reader = matrix(1, 5, |_, col| if col == 1 { Rat::one() } else { Rat::zero() }).unwrap();
    assert!(predecessor.return_material(&predecessor, &producer, reached, &clock,
        &successor, &wrong_reader, rat(1, 2), &receipt).is_err());
    assert!(successor.return_material(&predecessor, &producer, reached, &clock,
        &successor, &reader(), rat(1, 2), &receipt).is_err());
    let returned_state = returned.forward.present().unwrap();
    assert_eq!(returned_state.state(), reached.state());
    assert_eq!(returned_state.clock(), reached.clock());
    let work = returned.deposit.present().unwrap();
    // Native independent coordinate expression of the work at fixed charges and fluxes.
    let expected = native_point[..3].iter().map(|q| q*q*(rat(1, 3)-rat(1, 2))).sum::<Rat>() / integer(2)
        + native_point[3..].iter().map(|phi| phi*phi*(rat(1, 2)-rat(1, 3))).sum::<Rat>() / integer(2);
    assert_eq!(work.work, expected);
    assert_eq!(&work.after - &work.before, work.work);
    assert!(!work.work.is_zero());
    let next = next_producer.interact(returned_state, &predecessor, &clock, &input, &face, &receipt).unwrap();
    let direct = next_law.interact(reached.state(), &input, &face, &receipt).unwrap();
    let old_next = producer.interact(reached, &predecessor, &clock, &input, &face, &receipt).unwrap();
    let continued = next.forward.present().unwrap();
    assert_eq!(continued.step(), direct.step().unwrap());
    assert_ne!(continued.reached().state().configuration,
        old_next.forward.present().unwrap().reached().state().configuration);
    assert_eq!(continued.reached().state().commit, reached.state().commit + 1);
    let after = &continued.reached().state().configuration[..5];
    assert_eq!(successor.configuration(&successor.decode_configuration(after).unwrap()).unwrap(), after);
    assert!(continued.step().balance().is_exact());
    assert_eq!(continued.reached().clock().ticks(), reached.clock().ticks() + 1u8);

    // Return from the material that actually produced this passage. The original source
    // and clock handles remain unchanged; they do not become the current constitution.
    let second_reached = continued.reached();
    let second_point = &second_reached.state().configuration[..5];
    let prior_material = next_producer.current().clone();
    let prior_law = next_producer.law().clone();
    let prior_state = second_reached.state().clone();
    let prior_clock = second_reached.clock().clone();
    let before_failure = next_producer.interact(
        second_reached, &predecessor, &clock, &input, &face, &receipt,
    ).unwrap();
    // Returning C=3 to C=2 requires compliance growth 3/2, beyond 1+1/4.
    assert!(matches!(successor.return_material(
        &predecessor, &next_producer, second_reached, &clock, &predecessor,
        &reader(), rat(1, 4), &receipt,
    ), Err(WaveError::Holon(crate::holon::HolonError::DepositExceedsBound { .. }))));
    assert_eq!(next_producer.current(), &prior_material);
    assert_eq!(next_producer.law(), &prior_law);
    assert_eq!(second_reached.state(), &prior_state);
    assert_eq!(second_reached.clock(), &prior_clock);
    let after_growth_failure = next_producer.interact(
        second_reached, &predecessor, &clock, &input, &face, &receipt,
    ).unwrap();
    assert_eq!(after_growth_failure.forward.present().unwrap().step(),
        before_failure.forward.present().unwrap().step());
    // Receipt formation fails after the candidate law/work have been derived. No receiver
    // or reached state has been replaced, and the same predecessor remains usable.
    let wrong_receipt = ReceiptLaw::new(5, vec![], vec![]).unwrap();
    assert!(matches!(successor.return_material(
        &predecessor, &next_producer, second_reached, &clock, &predecessor,
        &reader(), rat(1, 2), &wrong_receipt,
    ), Err(WaveError::Holon(crate::holon::HolonError::Shape {
        what: "received state", expected: 5, found: 6,
    }))));
    assert_eq!(next_producer.current(), &prior_material);
    assert_eq!(next_producer.law(), &prior_law);
    assert_eq!(second_reached.state(), &prior_state);
    assert_eq!(second_reached.clock(), &prior_clock);
    let after_receipt_failure = next_producer.interact(
        second_reached, &predecessor, &clock, &input, &face, &receipt,
    ).unwrap();
    assert_eq!(after_receipt_failure.forward.present().unwrap().step(),
        before_failure.forward.present().unwrap().step());
    let (second_producer, second_returned, second_reading) = successor.return_material(
        &predecessor, &next_producer, second_reached, &clock, &predecessor,
        &reader(), rat(1, 2), &receipt,
    ).unwrap();
    assert_eq!(second_producer.current(), predecessor.as_ref());
    assert_eq!(second_producer.law(), producer.law());
    assert_eq!(predecessor.configuration(&second_reading).unwrap(), second_point);
    assert_ne!(second_reading, successor.decode_configuration(second_point).unwrap());
    let second_state = second_returned.forward.present().unwrap();
    assert_eq!(second_state.state(), second_reached.state());
    assert_eq!(second_state.clock(), second_reached.clock());
    let second_work = second_returned.deposit.present().unwrap();
    let second_expected = second_point[..3].iter()
        .map(|q| q*q*(rat(1, 2)-rat(1, 3))).sum::<Rat>() / integer(2)
        + second_point[3..].iter()
            .map(|phi| phi*phi*(rat(1, 3)-rat(1, 2))).sum::<Rat>() / integer(2);
    assert_eq!(second_work.work, second_expected);
    assert_eq!(&second_work.after - &second_work.before, second_work.work);
    assert!(!second_work.work.is_zero());
    // Equal-valued material after the return does not identify the original binding.
    assert!(producer.interact(second_state, &predecessor, &clock, &input, &face, &receipt).is_err());
    assert!(predecessor.return_material(&predecessor, &next_producer, second_reached,
        &clock, &successor, &reader(), rat(1, 2), &receipt).is_err());
    assert!(successor.return_material(&predecessor, &next_producer, second_reached,
        &clock, &predecessor, &wrong_reader, rat(1, 2), &receipt).is_err());
    let wrong_source = Arc::new((*predecessor).clone());
    let wrong_clock = Arc::new((*clock).clone());
    assert!(successor.return_material(&wrong_source, &next_producer, second_reached,
        &clock, &predecessor, &reader(), rat(1, 2), &receipt).is_err());
    assert!(successor.return_material(&predecessor, &next_producer, second_reached,
        &wrong_clock, &predecessor, &reader(), rat(1, 2), &receipt).is_err());
    let second_next = second_producer.interact(
        second_state, &predecessor, &clock, &input, &face, &receipt,
    ).unwrap();
    let second_direct = admitted(&predecessor)
        .interact(second_reached.state(), &input, &face, &receipt).unwrap();
    let held_next = next_producer.interact(
        second_reached, &predecessor, &clock, &input, &face, &receipt,
    ).unwrap();
    let second_continued = second_next.forward.present().unwrap();
    assert_eq!(second_continued.step(), second_direct.step().unwrap());
    assert_ne!(second_continued.reached().state().configuration,
        held_next.forward.present().unwrap().reached().state().configuration);
    assert_eq!(second_continued.reached().state().commit, second_reached.state().commit + 1);
    assert_eq!(second_continued.reached().clock().ticks(), second_reached.clock().ticks() + 1u8);
    assert!(second_continued.step().balance().is_exact());
    let second_after = &second_continued.reached().state().configuration[..5];
    assert_eq!(predecessor.configuration(&predecessor.decode_configuration(second_after).unwrap()).unwrap(), second_after);

    // The face can read no state direction while the reached point still carries the
    // complete wave and the unresolved receiver fibre. A populated receipt reads q[0].
    let blind = ReceiverFace::new(
        matrix(1, 5, |_, _| Rat::zero()).unwrap(),
        matrix(1, 1, |_, _| Rat::zero()).unwrap(),
        vec![Rat::zero()], vec![Rat::zero()],
    ).unwrap();
    let regional_receipt = ReceiptLaw::new(
        6, vec![vec![Rat::one(), Rat::zero(), Rat::zero(), Rat::zero(), Rat::zero(), Rat::zero()]],
        vec![RegionChart::new(Rat::one(), clock.step().clone(), 0).unwrap()],
    ).unwrap();
    let blind_next = next_producer.interact(
        returned_state, &predecessor, &clock, &input, &blind, &regional_receipt,
    ).unwrap();
    let blind_continued = blind_next.forward.present().unwrap();
    assert_eq!(blind_continued.reached().state(), second_reached.state());
    assert_eq!(blind_continued.reached().clock(), second_reached.clock());
    assert_eq!(blind_continued.step().face(), &[Rat::zero()]);
    assert_eq!(blind_continued.step().unresolved().directions, vec![vec![Rat::one()]]);
    assert_eq!(blind_next.receipt.readings(), &[second_point[0].clone()]);
    let (blind_producer, blind_returned, blind_reading) = successor.return_material(
        &predecessor, &next_producer, blind_continued.reached(), &clock, &predecessor,
        &reader(), rat(1, 2), &regional_receipt,
    ).unwrap();
    let blind_state = blind_returned.forward.present().unwrap();
    assert_eq!(blind_state.state(), second_state.state());
    assert_eq!(blind_state.clock(), second_state.clock());
    assert_eq!(predecessor.configuration(&blind_reading).unwrap(), second_point);
    assert_eq!(blind_returned.deposit.present().unwrap(), second_work);
    assert_eq!(blind_returned.receipt.readings(), &[second_point[0].clone()]);
    let blind_following = blind_producer.interact(
        blind_state, &predecessor, &clock, &input, &blind, &regional_receipt,
    ).unwrap();
    let blind_following_step = blind_following.forward.present().unwrap();
    assert_eq!(blind_following_step.reached().state(), second_continued.reached().state());
    assert_eq!(blind_following_step.reached().clock(), second_continued.reached().clock());
    assert_eq!(blind_following_step.step().face(), &[Rat::zero()]);
    assert_eq!(blind_following_step.step().unresolved().directions, vec![vec![Rat::one()]]);
    assert!(blind_following_step.step().balance().is_exact());
    eprintln!("WAVE_RETURN reached_charge_flux={:?}", native_point);
    eprintln!("WAVE_RETURN old_voltage_current={:?}", old_reading);
    eprintln!("WAVE_RETURN successor_voltage_current={:?}", new_reading);
    eprintln!("WAVE_RETURN storage_work={} next_charge_flux={:?} next_cumulative_reading={}",
        work.work, after, continued.reached().state().configuration[5]);
    eprintln!("WAVE_RETURN next_balance_residual={}", continued.step().balance().residual);
    eprintln!("WAVE_RETURN second_reached_charge_flux={:?} second_voltage_current={:?}",
        second_point, second_reading);
    eprintln!("WAVE_RETURN second_storage_work={} second_next_charge_flux={:?} second_next_cumulative_reading={}",
        second_work.work, second_after, second_continued.reached().state().configuration[5]);
    eprintln!("WAVE_RETURN second_next_balance_residual={}", second_continued.step().balance().residual);
    assert!(next_producer.interact(returned_state, &wrong_source, &clock, &input, &face, &receipt).is_err());
    assert!(next_producer.interact(returned_state, &predecessor, &wrong_clock, &input, &face, &receipt).is_err());
    assert!(second_producer.interact(second_state, &wrong_source, &clock, &input, &face, &receipt).is_err());
    assert!(second_producer.interact(second_state, &predecessor, &wrong_clock, &input, &face, &receipt).is_err());
    assert!(successor.decode_configuration(&native_point[..4]).is_err());
}
