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
use crate::receiver::receipt::ReceiptLaw;
use crate::receiver::reception::{JointLaw, ReceiverFace};
use crate::receiver::reception::continuation::JointProducer;

fn admitted(chain: &WaveChain) -> JointLaw {
    let native = ReferenceHolon::new(chain.holon().unwrap(), chain.tick().clone(), Scheme::Midpoint)
        .unwrap();
    // Read V_0 plus I_0. This fixed receiver map, incidence and leakage transport with Q.
    let reader = matrix(1, 5, |_, column| {
        if column == 0 || column == 3 { Rat::one() } else { Rat::zero() }
    }).unwrap();
    JointLaw::reading(&native, &reader).unwrap()
}

#[test]
fn wave_material_return_preserves_charge_flux_and_continues_its_native_joint_law() {
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
    let producer = JointProducer::declared(admitted(&predecessor), predecessor.clone(), clock.clone()).unwrap();
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
    let (next_producer, returned) = producer.return_storage(
        reached, &predecessor, &clock, next_law.clone(), rat(1, 2), &receipt,
    ).unwrap();
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
    eprintln!("WAVE_RETURN reached_charge_flux={:?}", native_point);
    eprintln!("WAVE_RETURN old_voltage_current={:?}", old_reading);
    eprintln!("WAVE_RETURN successor_voltage_current={:?}", new_reading);
    eprintln!("WAVE_RETURN storage_work={} next_charge_flux={:?} next_receiver={}",
        work.work, after, continued.reached().state().configuration[5]);
    eprintln!("WAVE_RETURN next_balance_residual={}", continued.step().balance().residual);
    let wrong_source = Arc::new((*predecessor).clone());
    assert!(next_producer.interact(returned_state, &wrong_source, &clock, &input, &face, &receipt).is_err());
    let wrong_clock = Arc::new((*clock).clone());
    assert!(next_producer.interact(returned_state, &predecessor, &wrong_clock, &input, &face, &receipt).is_err());
    assert!(successor.decode_configuration(&native_point[..4]).is_err());
}
