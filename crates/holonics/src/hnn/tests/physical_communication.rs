//! Bounded law controls of the production complex communication boundary, not task accuracy.

use super::support::{contact, encoded, ring};
use crate::compression::landmark::context::{BaseMeasure, StopPrior};
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
use crate::hnn::field::{
    CribDeclaration, Current, Field, FieldDeclaration, FieldMaterial, ReceiverDeclaration,
};
use crate::hnn::physical::{PhysicalLearning, PhysicalObservation, PhysicalResident};
use crate::hnn::prediction::{DamagedSection, RepairedCell, Unresolved, repair_by_field};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::WordOpening;
use crate::ratio::{integer, rat};
use num_traits::Zero;

fn receiver() -> ReceiverDeclaration {
    ReceiverDeclaration {
        ring: 0,
        aperture: 3,
        tolerance: rat(1, 16),
        depth: 1,
        prior: StopPrior::half(),
        mass: 1,
        base: BaseMeasure::Even,
        receiving_prior: 0,
    }
}

fn field() -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(4, (0..4).collect()), ring(3, Vec::new())],
            contacts: vec![contact(0, 1, 3, 0)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver()],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

fn material(field: &Field) -> Constitution {
    let theta = Constitution::initial(field, CAMPAIGN_ONE_BUDGET).unwrap();
    // The existing non-dyadic source fixture, declared independently of the later observation.
    let source = theta.source_port(0).unwrap().scaled(&rat(1, 3));
    theta.with_ports(0, None, Some(source), None).unwrap()
}

#[test]
fn communication_deposits_after_the_whole_boundary_and_reuses_material_source_and_carry() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident =
        PhysicalResident::new(&field, initial.clone(), current.clone(), WordOpening::Rest);
    let taught = resident
        .communicate(&source, &receiver(), |boundary| {
            println!("whole blind communication boundary: {boundary:?}");
            assert_eq!(boundary.chart(), &source.part(0..0).unwrap());
            assert_eq!(boundary.first_station(), 2);
            assert_eq!(boundary.readings().len(), 1);
            assert_eq!(boundary.readings()[0].station, 2);
            assert_eq!(boundary.readings()[0].read.cells.len(), field.alphabet());
            assert_eq!(boundary.readings()[0].read.phases.len(), field.alphabet());
            assert_eq!(
                boundary.decisions(),
                &[RepairedCell::Held {
                    fibre: (0..field.alphabet()).collect(),
                    unresolved: Unresolved::UncertifiedDomain,
                }]
            );
            assert_eq!(boundary.domains(), &[None]);
            assert!(boundary.faces().is_ok());
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(taught.closes());
    assert!(!taught.declaring_face_reused);
    assert_eq!(taught.carry.ticks, 2);
    assert!(taught.comparison.unwrap().unwrap().publication.stepped > 0);
    assert_ne!(
        resident.constitution().receiving_map(0),
        initial.receiving_map(0)
    );
    assert_eq!(
        resident.constitution().source_port(0),
        initial.source_port(0)
    );
    let theta = resident.constitution().clone();
    let entered = resident.opening().clone();
    let commit = theta.commit();

    // Same actual entering carry and source, with the earlier material: isolate learned R.
    let mut unlearned = PhysicalResident::new(&field, initial, current.clone(), entered.clone());
    let prior = unlearned
        .communicate(&source, &receiver(), |_| None)
        .unwrap();
    let next = resident
        .communicate(&source, &receiver(), |_| None)
        .unwrap();
    assert!(prior.closes() && next.closes());
    assert!(!prior.declaring_face_reused);
    assert!(next.declaring_face_reused, "R changed; the actual rank producer is independent of R");
    assert_ne!(
        next.boundary.readings()[0].read.logits,
        prior.boundary.readings()[0].read.logits
    );
    assert_eq!(next.carry.ticks, taught.carry.ticks + 2);
    assert_eq!(
        resident.constitution().commit(),
        commit,
        "unobserved communication does not deposit"
    );
    let WordOpening::Received { carry, .. } = resident.opening() else {
        panic!("actual carried end")
    };
    assert_eq!(carry, &next.carry);

    // Same learned material, clock and entering carry, changing only an admitted source class.
    // This is a source-sensitivity falsifier, not a favourable answer selected by a grader.
    let mut changed_source = PhysicalResident::new(&field, theta, current, entered);
    let changed = changed_source
        .communicate(&encoded(&field, &[2, 1]), &receiver(), |_| None)
        .unwrap();
    assert!(changed.closes());
    assert!(!changed.declaring_face_reused);
    assert_ne!(
        next.boundary.readings()[0].read.logits,
        changed.boundary.readings()[0].read.logits
    );
    println!(
        "whole unobserved carried communication boundary: {:?}",
        next.boundary
    );
    println!(
        "unit communication material/source/carry elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn communication_observations_cannot_change_the_earlier_boundary() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let mut left =
        PhysicalResident::new(&field, initial.clone(), current.clone(), WordOpening::Rest);
    let mut right = PhysicalResident::new(&field, initial, current, WordOpening::Rest);
    let a = left
        .communicate(&source, &receiver(), |_| {
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    let b = right
        .communicate(&source, &receiver(), |_| {
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 2]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(a.closes() && b.closes());
    assert_eq!(a.boundary, b.boundary);
    assert_eq!(a.carry, b.carry);
    assert_eq!(a.opening, b.opening);
    assert!(a.comparison.unwrap().unwrap().publication.stepped > 0);
    assert!(b.comparison.unwrap().unwrap().publication.stepped > 0);
    assert_ne!(
        left.constitution().receiving_map(0),
        right.constitution().receiving_map(0)
    );
    let a_next = left.communicate(&source, &receiver(), |_| None).unwrap();
    let b_next = right.communicate(&source, &receiver(), |_| None).unwrap();
    assert!(a_next.closes() && b_next.closes());
    assert_ne!(
        a_next.boundary.readings()[0].read.logits,
        b_next.boundary.readings()[0].read.logits
    );
    println!(
        "unit communication post-blind independence elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn communication_refuses_changed_source_or_partition_without_deposition_and_keeps_the_blind_end() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident = PhysicalResident::new(
        &field,
        initial.clone(),
        Current::at_rest(&field),
        WordOpening::Rest,
    );
    for (cells, compared) in [
        ([1, 1, 3], vec![false, false, true]),
        ([0, 1, 3], vec![true, false, true]),
    ] {
        let entered = match resident.opening() {
            WordOpening::Rest => 0,
            WordOpening::Received { carry, .. } => carry.ticks,
        };
        let receipt = resident
            .communicate(&source, &receiver(), |_| {
                Some(PhysicalObservation {
                    observed: encoded(&field, &cells),
                    compared,
                    learning: PhysicalLearning::Receiving,
                })
            })
            .unwrap();
        assert!(receipt.comparison.is_err());
        assert!(receipt.closes());
        assert_eq!(receipt.carry.ticks, entered + 2);
        assert_eq!(resident.constitution(), &initial);
        let WordOpening::Received { carry, .. } = resident.opening() else {
            panic!("blind carried end")
        };
        assert_eq!(carry, &receipt.carry);
    }
    let before = resident.opening().clone();
    assert!(
        resident
            .communicate(&encoded(&field, &[0, 1, 2]), &receiver(), |_| {
                panic!("no future section must refuse before reception")
            })
            .is_err()
    );
    assert_eq!(resident.opening(), &before);
    assert_eq!(resident.constitution(), &initial);
    let mut over_period = receiver();
    over_period.aperture = 5; // the producing source phase period is four
    assert!(
        resident
            .communicate(&source, &over_period, |_| {
                panic!("a unit-source phase wrap must refuse before opening a Word")
            })
            .is_err()
    );
    assert_eq!(resident.opening(), &before);
    assert_eq!(resident.constitution(), &initial);
    println!(
        "unit communication source/partition refusal elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn communication_returns_actual_multistation_held_receipts_without_a_joint_certificate() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let mut resident = PhysicalResident::new(
        &field,
        initial.clone(),
        Current::at_rest(&field),
        WordOpening::Rest,
    );
    let output = resident
        .communicate(&encoded(&field, &[0]), &receiver(), |boundary| {
            assert_eq!(boundary.first_station(), 1);
            assert_eq!(boundary.readings().len(), 2);
            assert_eq!(boundary.readings()[0].station, 1);
            assert_eq!(boundary.readings()[1].station, 2);
            assert_eq!(boundary.readings()[0].tick, 1);
            assert_eq!(boundary.readings()[1].tick, 2);
            assert_eq!(boundary.decisions().len(), 2);
            for decision in boundary.decisions() {
                assert_eq!(
                    decision,
                    &RepairedCell::Held {
                        fibre: (0..field.alphabet()).collect(),
                        unresolved: Unresolved::UncertifiedDomain,
                    }
                );
            }
            assert_eq!(
                boundary.domains(),
                &[None, None],
                "sparse forward supplies no completion certificate; a point face is insufficient"
            );
            println!("whole multi-station blind communication receipt: {boundary:?}");
            None
        })
        .unwrap();
    assert!(output.closes());
    assert!(output.comparison.unwrap().is_none());
    assert_eq!(output.carry.ticks, 2);
    assert_eq!(resident.constitution(), &initial);
    println!(
        "unit communication actual held/domain receipts elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn one_future_communication_carries_one_actual_source_label_through_the_whole_receiving_image() {
    let started = std::time::Instant::now();
    let field = field();
    let initial = material(&field);
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident =
        PhysicalResident::new(&field, initial.clone(), current.clone(), WordOpening::Rest);
    let taught = resident
        .communicate_one_future(&source, &receiver(), |boundary| {
            println!("whole one-future boundary before observation: {boundary:?}");
            let domain = boundary.domains()[0].as_ref().unwrap();
            let response = domain.completion.as_ref().unwrap();
            assert_eq!(boundary.completion_consistency(), Some(response));
            assert_eq!(response.station, 2);
            assert_eq!(response.label_logits.len(), 4);
            assert_eq!(domain.classes, vec![0, 1, 2, 3]); // initial R is zero
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(taught.closes());
    assert!(taught.comparison.unwrap().unwrap().publication.stepped > 0);
    assert_ne!(
        resident.constitution().receiving_map(0),
        initial.receiving_map(0)
    );
    let producing = resident.constitution().clone();
    let entered = resident.opening().clone();
    let next = resident
        .communicate_one_future(&source, &receiver(), |_| None)
        .unwrap();
    assert!(next.closes());
    assert_eq!(next.carry.ticks, 4);
    assert!(next.comparison.unwrap().is_none());
    assert_eq!(resident.constitution(), &producing);
    let domain = next.boundary.domains()[0].as_ref().unwrap();
    let response = domain.completion.as_ref().unwrap();
    assert_eq!(next.boundary.completion_consistency(), Some(response));
    let mut communicated = domain.classes.clone();
    communicated.extend(next.boundary.readings()[0].leaders());
    communicated.sort_unstable();
    communicated.dedup();
    match &next.boundary.decisions()[0] {
        RepairedCell::Released(class) => assert_eq!(communicated, vec![*class]),
        RepairedCell::Held { fibre, .. } => assert_eq!(fibre, &communicated),
        RepairedCell::Intact(_) => panic!("a requested future class was never imposed"),
    }
    assert_eq!(response.station, 2);
    assert_eq!(response.fixed_logits.len(), 8);
    assert_eq!(response.label_logits.len(), 4);
    let phases = ReceivingPhases::declare(&field, &producing, &current, &receiver()).unwrap();
    // Exterior falsifiers only: every complete label runs an independent native Word at the
    // same producing material/source frame/entering carry. Production carries signed columns,
    // not these completed Words or a table of answers.
    for class in 0..4 {
        let complete = encoded(&field, &[0, 1, class]);
        let section = DamagedSection::of_runs(3, &complete, vec![(0, complete.clone())]).unwrap();
        let actual =
            repair_by_field(&field, &producing, &current, &section, &entered, &phases).unwrap();
        let image = response
            .fixed_logits
            .iter()
            .zip(&response.label_logits[class])
            .map(|(fixed, label)| fixed + label)
            .collect::<Vec<_>>();
        assert_eq!(image, actual.reads[2].read.logits);
        assert!(actual.opening.closes() && actual.word.closes());
        assert!(actual.balances.iter().all(|balance| balance.closes()));
        for (value, interval) in image.iter().zip(&domain.logits) {
            assert!(interval.lower <= *value && *value <= interval.upper);
        }
    }
    println!("whole carried one-future boundary: {:?}", next.boundary);
    println!(
        "unit one-future common-label image elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn one_future_source_publication_reaches_the_next_contemporary_communication_opening() {
    let started = std::time::Instant::now();
    let field = field();
    let current = Current::at_rest(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident =
        PhysicalResident::new(&field, material(&field), current.clone(), WordOpening::Rest);
    let received = resident
        .communicate_one_future(&source, &receiver(), |_| {
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(received.closes());
    assert!(!received.declaring_face_reused);
    assert!(received.comparison.unwrap().unwrap().publication.stepped > 0);
    let producing = resident.constitution().clone();
    let mut emitted = None;
    let taught = resident
        .communicate_one_future(&source, &receiver(), |boundary| {
            emitted = Some(boundary.clone());
            Some(PhysicalObservation {
                observed: encoded(&field, &[0, 1, 2]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::SourcePorts,
            })
        })
        .unwrap();
    assert!(taught.closes());
    assert!(taught.declaring_face_reused);
    assert_eq!(taught.boundary, emitted.unwrap());
    let publication = taught.comparison.unwrap().unwrap();
    assert!(publication.publication.stepped > 0);
    let paired = publication.source_pairing.as_ref().unwrap();
    assert_eq!(paired.producing_commit, producing.commit());
    assert!(paired.source_move_squared > integer(0));
    assert!(!paired.receiving.is_zero());
    assert_eq!(paired.receiving, paired.opening);
    assert_eq!(paired.opening, paired.deposition);
    assert!(paired.defect.is_zero() && paired.composition_defect.is_zero());
    assert_eq!(
        resident.constitution().receiving_map(0),
        producing.receiving_map(0)
    );
    assert_ne!(
        resident.constitution().source_port(0),
        producing.source_port(0)
    );
    let entered = resident.opening().clone();
    let WordOpening::Received { carry, .. } = &entered else {
        panic!("actual blind end")
    };
    assert_eq!(carry, &taught.carry);
    let mut prior = PhysicalResident::new(&field, producing, current, entered);
    // A separately fixed prefix; no later observation is supplied to either native read.
    let later_source = encoded(&field, &[2, 1]);
    let before = prior
        .communicate_one_future(&later_source, &receiver(), |_| None)
        .unwrap();
    let commit = resident.constitution().commit();
    let after = resident
        .communicate_one_future(&later_source, &receiver(), |_| None)
        .unwrap();
    assert!(before.closes() && after.closes());
    assert!(!before.declaring_face_reused);
    assert!(after.declaring_face_reused, "new E and a different source still execute under the same declaring medium");
    assert_eq!(after.carry.ticks, taught.carry.ticks + 2);
    assert_ne!(
        before.boundary.readings()[0].read.logits,
        after.boundary.readings()[0].read.logits
    );
    assert_eq!(resident.constitution().commit(), commit);
    // A changed imposition need not change its scalar energy. Each actual work receipt must
    // close; differing energy is not a condition for learning a physical source relation.
    println!(
        "later source openings before={:?} after={:?}",
        before.opening, after.opening
    );
    println!("actual one-future source return: {paired:?}");
    println!(
        "whole later source-conditioned boundary: {:?}",
        after.boundary
    );
    println!(
        "unit one-future source publication elapsed_ns={}",
        started.elapsed().as_nanos()
    );
}

#[test]
fn one_future_communication_keeps_refusal_and_multi_future_admission_honest() {
    let field = field();
    let initial = material(&field);
    let source = encoded(&field, &[0, 1]);
    let mut resident = PhysicalResident::new(
        &field,
        initial.clone(),
        Current::at_rest(&field),
        WordOpening::Rest,
    );
    let refused = resident
        .communicate_one_future(&source, &receiver(), |_| {
            Some(PhysicalObservation {
                observed: encoded(&field, &[1, 1, 3]),
                compared: vec![false, false, true],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(refused.closes());
    assert!(refused.comparison.is_err());
    assert_eq!(resident.constitution(), &initial);
    let entered = resident.opening().clone();
    assert!(
        resident
            .communicate_one_future(&encoded(&field, &[0]), &receiver(), |_| {
                panic!("two future stations need their joint certificate before Word")
            })
            .is_err()
    );
    let mut wrapped = receiver();
    wrapped.aperture = 5;
    assert!(
        resident
            .communicate_one_future(&encoded(&field, &[0, 1, 2, 3]), &wrapped, |_| {
                panic!("unit source period admission precedes Word")
            })
            .is_err()
    );
    assert_eq!(resident.opening(), &entered);
    assert_eq!(resident.constitution(), &initial);
    let WordOpening::Received { carry, .. } = &entered else {
        panic!("blind end retained")
    };
    assert_eq!(carry, &refused.carry);
}
