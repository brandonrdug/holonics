use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::{ToPrimitive, Zero};

pub(super) fn phase(real: i64, imaginary: i64, denominator: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(real, imaginary, denominator).unwrap()
}

pub(super) fn material() -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 2,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        },
        NativeJunctionSeed {
            incoming_admittance: 2,
            held_admittance: 1,
            incoming_transport: phase(0, 1, 1),
            initial_held: NativePhaseCurrent::zero(),
        },
    ]
}

fn from_current(current: &ExactComplexWaveCurrent) -> NativePhaseCurrent {
    let mut a = current.real.denom().clone();
    let mut b = current.imaginary.denom().clone();
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    let denominator = current.real.denom() / a * current.imaginary.denom();
    phase(
        (current.real.numer() * (&denominator / current.real.denom()))
            .to_i64()
            .unwrap(),
        (current.imaginary.numer() * (&denominator / current.imaginary.denom()))
            .to_i64()
            .unwrap(),
        denominator.to_i64().unwrap(),
    )
}

/// An independently declared exterior linear current law. It knows only actual emitted port
/// currents; it cannot inspect or write native state, relation rows, rank or expected answers.
pub(super) fn exterior(currents: &[ExactComplexWaveCurrent]) -> NativePhaseCurrent {
    let left = phase(1, 1, 2).current();
    let right = phase(2, -1, 3).current();
    from_current(
        &left
            .multiply(&currents[0])
            .add(&right.multiply(&currents[1])),
    )
}

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

#[test]
#[ignore = "requires CUDA; actual source crossing need not be the latest occurrence"]
fn a_receiving_edge_uses_its_retained_emission_not_the_latest_message() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let first = body
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let actual = exterior(&first.source_currents);
    body.advance(&mut NativeCurrentOccurrence::entering(phase(0, 1, 1)))
        .unwrap();
    let response = body
        .advance(&mut NativeCurrentOccurrence::through(first.source, actual))
        .unwrap();
    assert_eq!(response.lineage.predecessor_state, Some(1));
    assert_eq!(response.lineage.received_from, Some(0));
    assert_eq!(response.successor_rank, 1);
    let difference = response.received_difference.unwrap();
    assert_eq!(difference.source_occurrence, 0);
    assert_eq!(difference.arrived, actual.current());
    assert!(matches!(
        difference.former_receiver_fibre,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    // The formed row must represent the original emitted section paired with the arrived current.
    let mut expected = first
        .source_currents
        .into_iter()
        .flat_map(|c| [c.real, c.imaginary])
        .collect::<Vec<_>>();
    expected.extend([actual.current().real, actual.current().imaginary]);
    let rest = body.inspect_relation().unwrap();
    let pivot = response.formed_pivot.unwrap();
    let row = &rest.intervals[pivot * 6..(pivot + 1) * 6];
    let scale = Rat::from_integer(row[pivot].0.into()) / &expected[pivot];
    for (coefficient, expected) in row.iter().zip(expected) {
        assert_eq!(Rat::from_integer(coefficient.0.into()), expected * &scale);
    }
}

#[test]
#[ignore = "requires CUDA; foreign and duplicate receiving edges refuse before effects"]
fn ownership_and_receiving_lineage_are_not_equal_coordinate_values() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut left = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut right = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let first = left
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    // A private adversarial duplicate exercises the check beneath the public non-Clone handle.
    let duplicate = NativeEmissionHandle {
        owner: Rc::clone(&first.source.owner),
        occurrence: first.source.occurrence,
    };
    let mut occurrence = NativeCurrentOccurrence::through(first.source, phase(2, 1, 3));
    let before = right.census();
    assert!(matches!(
        right.advance(&mut occurrence),
        Err(ConstitutiveFibreError::ForeignOccurrence)
    ));
    assert_eq!(right.census(), before);
    left.advance(&mut occurrence).unwrap();
    let before = left.census();
    assert!(matches!(
        left.advance(&mut NativeCurrentOccurrence::through(
            duplicate,
            phase(2, 1, 3)
        )),
        Err(ConstitutiveFibreError::ForeignOccurrence)
    ));
    assert_eq!(left.census(), before);
}

#[test]
#[ignore = "requires CUDA; coupled native development predicts new exterior currents"]
fn formed_relation_changes_the_native_receiver_on_new_currents() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut unlinked = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut step = body
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    unlinked
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let mut previous_sources = Vec::new();
    let mut inferred_new = 0;
    for _ in 0..7 {
        let arrived = exterior(&step.source_currents);
        previous_sources.push(step.source_currents);
        step = body
            .advance(&mut NativeCurrentOccurrence::through(step.source, arrived))
            .unwrap();
        let control = unlinked
            .advance(&mut NativeCurrentOccurrence::entering(arrived))
            .unwrap();
        assert_eq!(
            step.source_currents, control.source_currents,
            "both bodies receive identical actual currents and have the same constitutive seed"
        );
        assert!(matches!(
            control.receiver,
            ConstitutiveReading::OutsideDomain { .. }
        ));
        if let ConstitutiveReading::Unique { current } = &step.receiver {
            let actual = exterior(&step.source_currents).current();
            assert_eq!(current, &vec![actual.real, actual.imaginary]);
            assert!(!previous_sources.contains(&step.source_currents));
            inferred_new += 1;
        }
    }
    assert!(
        inferred_new >= 2,
        "the native relation must conduct beyond literal stored source fields"
    );
    assert_eq!(step.successor_rank, 4);
    assert_eq!(body.lineage().count(), 8);
}

#[test]
#[ignore = "requires CUDA; whole current/formation operation refuses without partial mutation"]
fn refused_current_preserves_phase_relation_and_source_ownership() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut seed = material();
    seed[0].incoming_transport = phase(3, 4, 5);
    let mut body = NativeConstitutiveEcology::found(&surface, seed).unwrap();
    let first = body
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let before_phase = body.inspect_held().unwrap();
    let before_relation = body.inspect_relation().unwrap();
    let mut occurrence =
        NativeCurrentOccurrence::through(first.source, phase(i64::MAX, i64::MAX, 1));
    assert!(matches!(
        body.advance(&mut occurrence),
        Err(ConstitutiveFibreError::Arithmetic(_))
    ));
    assert_eq!(body.inspect_held().unwrap(), before_phase);
    assert_eq!(body.inspect_relation().unwrap(), before_relation);
    assert!(occurrence.source.is_some());
    assert_eq!(body.lineage().count(), 1);
    occurrence.current = phase(1, 0, 1);
    body.advance(&mut occurrence).unwrap();
    assert!(occurrence.source.is_none());
}

#[test]
#[ignore = "requires CUDA; one resident coupled operation has one terminal read"]
fn current_comparison_formation_and_successor_share_one_resident_deed() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let first = body
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let arrived = exterior(&first.source_currents);
    let before = body.census();
    body.advance(&mut NativeCurrentOccurrence::through(first.source, arrived))
        .unwrap();
    let after = body.census();
    assert_eq!(after.deed_launches - before.deed_launches, 1);
    assert_eq!(after.section_read_outs - before.section_read_outs, 1);
    assert_eq!(after.ingress_octets - before.ingress_octets, 48);
    assert_eq!(
        after.egress_section_octets - before.egress_section_octets,
        25 * 16
    );
    assert_eq!(after.control_launches - before.control_launches, 0);
}

#[test]
#[ignore = "requires CUDA; incompatible actual returns retain both receiver and state consequences"]
fn an_incompatible_return_opens_the_fibre_without_overwriting_its_condition() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let seed = NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: phase(1, 0, 1),
    };
    let mut body = NativeConstitutiveEcology::found(&surface, vec![seed]).unwrap();
    let first = body
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    let second = body
        .advance(&mut NativeCurrentOccurrence::entering(phase(1, 0, 1)))
        .unwrap();
    assert_eq!(first.source_currents, second.source_currents);
    body.advance(&mut NativeCurrentOccurrence::through(
        first.source,
        phase(3, 0, 1),
    ))
    .unwrap();
    let returned = body
        .advance(&mut NativeCurrentOccurrence::through(
            second.source,
            phase(4, 0, 1),
        ))
        .unwrap();
    match returned.received_difference.unwrap().former_receiver_fibre {
        ConstitutiveReading::Unique { current } => {
            assert_eq!(current, vec![Rat::from_integer(3.into()), Rat::zero()])
        }
        other => panic!("the prior receiver was not retained: {other:?}"),
    }
    match returned.receiver {
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => {
            assert_eq!(particular, vec![Rat::from_integer(9.into()), Rat::zero()]);
            assert_eq!(
                directions,
                vec![vec![Rat::from_integer(1.into()), Rat::zero()]]
            );
        }
        other => panic!("the incompatible relation was flattened: {other:?}"),
    }
    let held = body.inspect_held().unwrap();
    assert_eq!(held.intervals, vec![(4, 4), (0, 0), (1, 1)]);
}

#[test]
#[ignore = "requires CUDA; actual incidence boundary maps retain the held-state pullback population"]
fn held_state_composition_retains_the_full_joined_occurrences() {
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    let mut other = NativeConstitutiveEcology::found(&surface, material()).unwrap();
    for current in [phase(1, 0, 1), phase(0, 1, 1)] {
        body.advance(&mut NativeCurrentOccurrence::entering(current))
            .unwrap();
        other
            .advance(&mut NativeCurrentOccurrence::entering(current))
            .unwrap();
    }
    let first = body.incidence(0).unwrap();
    let second = body.incidence(1).unwrap();
    assert_eq!(first.len(), 8);
    let joined = body.joined_incidence(0, 1).unwrap();
    assert_eq!(joined.len(), 8);
    for crossing in &joined {
        let left = &crossing.first;
        let right = &crossing.second;
        assert_eq!(
            crossing.middle_transport,
            NativePhaseCurrent::unit().current()
        );
        assert_eq!(left.target, right.source);
        assert_eq!(left.node, right.node);
        assert_eq!(left.occurrence, 0);
        assert_eq!(right.occurrence, 1);
    }
    assert!(first.iter().all(|left| {
        other
            .incidence(1)
            .unwrap()
            .iter()
            .all(|right| left.target != right.source)
    }));
    assert!(body.joined_incidence(1, 0).unwrap().is_empty());
    // Decode the actual incidence contributions and compare their sums with the stored native
    // emission and with the corresponding held successor, not just a population count.
    let words = surface.read_out(&body.history[0].section).unwrap();
    for node in 0..body.material.len() {
        let mut emitted = ExactComplexWaveCurrent::zero();
        let mut held = ExactComplexWaveCurrent::zero();
        for edge in first.iter().filter(|edge| edge.node == node) {
            let source = match edge.source.position {
                NativeCurrentCarrier::Incoming { .. } => phase(1, 0, 1).current(),
                NativeCurrentCarrier::Held { after: None, node } => {
                    body.material[node].initial_held.current()
                }
                _ => panic!("the first current has no other source"),
            };
            let contribution = edge.transport.multiply(&source);
            match edge.target.position {
                NativeCurrentCarrier::Emitted { .. } => emitted = emitted.add(&contribution),
                NativeCurrentCarrier::Held { after: Some(0), .. } => held = held.add(&contribution),
                _ => panic!("the first current has no other target"),
            }
        }
        let native = ExactComplexWaveCurrent::new(
            Rat::new(words[2 * node].0.into(), words[4].0.into()),
            Rat::new(words[2 * node + 1].0.into(), words[4].0.into()),
        );
        assert_eq!(emitted, native);
        let incoming = body.material[node]
            .incoming_transport
            .current()
            .multiply(&phase(1, 0, 1).current());
        assert_eq!(
            held,
            native
                .add(&incoming)
                .subtract(&body.material[node].initial_held.current())
        );
    }
    assert!(second.iter().any(|edge| matches!(
        edge.source.position,
        NativeCurrentCarrier::Held { after: Some(0), .. }
    )));
}
