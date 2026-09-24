use super::*;
use crate::embedding_fiber::ResidentReadout;

fn phase(real: i64, imaginary: i64, denominator: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(real, imaginary, denominator).unwrap()
}

/// Host/device parity (two-port circulation kernel): the device current equals the exact
/// constitutive law and conserves the admittance-weighted energy face.
#[test]
#[ignore = "requires CUDA; actual two-port phase current and complete held successor"]
fn native_junction_current_matches_the_constitutive_law_and_conserves_its_weighted_face() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let seed = NativeJunctionSeed {
        incoming_admittance: 2,
        held_admittance: 5,
        incoming_transport: phase(3, 4, 5),
        initial_held: phase(1, 2, 3),
    };
    let mut body = NativeConstitutiveEcology::found(&surface, vec![seed.clone()]).unwrap();
    let incoming = phase(2, -1, 7);
    let native = body
        .advance(&mut NativeCurrentOccurrence::entering(incoming))
        .unwrap();
    let local = seed
        .incoming_transport
        .current()
        .multiply(&incoming.current());
    let held = seed.initial_held.current();
    let a = Rat::from_integer(seed.incoming_admittance.into());
    let b = Rat::from_integer(seed.held_admittance.into());
    let velocity = local
        .scaled(&a)
        .add(&held.scaled(&b))
        .scaled(&(Rat::from_integer(2.into()) / (&a + &b)));
    assert_eq!(native.source_currents, vec![velocity.subtract(&local)]);
    let rest = body.inspect_held().unwrap();
    let next = phase(
        rest.intervals[0].0,
        rest.intervals[1].0,
        rest.intervals[2].0,
    )
    .current();
    assert_eq!(next, velocity.subtract(&held));
    assert_eq!(
        &a * local.norm_square() + &b * held.norm_square(),
        &a * native.source_currents[0].norm_square() + &b * next.norm_square()
    );
    let again = body
        .advance(&mut NativeCurrentOccurrence::entering(incoming))
        .unwrap();
    assert_ne!(
        native.source_currents, again.source_currents,
        "equal incoming coordinates do not erase the held-phase condition"
    );
    assert_eq!(again.lineage.predecessor_state, Some(0));
    assert_eq!(
        again.successor_rank, 0,
        "free incidence does not invent paired evidence"
    );
}
