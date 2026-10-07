//! The continuing consumer is tested through actual native words and reached deposits.

use super::support::{contact, encoded, ring};
use crate::compression::landmark::context::{BaseMeasure, StopPrior};
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
use crate::hnn::field::{
    ConstitutionRead, CribDeclaration, Current, Field, FieldDeclaration, ReceiverDeclaration,
};
use crate::hnn::physical::{PhysicalLearning, PhysicalObservation, PhysicalResident};
use crate::hnn::prediction::{DamagedSection, RepairedCell, repair_by_field};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::WordOpening;
use crate::ratio::{integer, rat};
use num_traits::Zero;

fn receiver(aperture: usize) -> ReceiverDeclaration {
    ReceiverDeclaration {
        ring: 0,
        aperture,
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
            rings: vec![ring(8, (0..8).collect()), ring(3, Vec::new())],
            contacts: vec![contact(0, 1, 3, 0)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: vec![1],
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver(1)],
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

/// Exact notebook period-four geometry, not support::ring's unrelated radius-squared 65 chart.
fn four_station_field() -> Field {
    let quarter_ring = |lock| {
        let mut declared = ring(4, lock);
        declared.placements = (0..4).map(|j| FieldDeclaration::quarter_turn(j, 4)).collect();
        declared
    };
    Field::declare(FieldDeclaration {
        rings: vec![quarter_ring((0..4).collect()), quarter_ring(Vec::new()), quarter_ring(Vec::new())],
        contacts: vec![contact(0, 1, 4, 0), contact(1, 2, 4, 0)],
        loops: Vec::new(), sources: vec![0], offsets: vec![1, 2, 3], alphabet: 4,
        step: integer(1), exponent_grain: 1, receivers: vec![receiver(3)],
        crib: CribDeclaration { window: 16, offset: 1 }, population: 1 << 16,
        lattice: Default::default(),
    }.by_lattice_rule()).unwrap()
}

#[test]
fn four_station_pair_coordinate_retains_carry_and_has_a_matched_source_dependent_consequence() {
    use crate::hnn::encoding::Encoded;
    use crate::hnn::prediction::predict_sparse_by_field;
    use crate::holarchy::terrain::{CyclicLaw, KnownTruth};
    use crate::ratio::Rat;
    let field = four_station_field();
    let current = Current::at_rest(&field);
    let receiving = receiver(4);
    let material = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    let mut resident = PhysicalResident::new(&field, material, current.clone(), WordOpening::Rest);
    let teaching = KnownTruth::cyclic_class_orbit(CyclicLaw::OrderTwo { opening: 2 }, 4, 20261006001, 4).unwrap();
    let mut last = None;
    for observed in Encoded::identity(&teaching, &field).unwrap() {
        let damaged = DamagedSection::damage(&observed, &[2]).unwrap();
        let received = resident.receive_sparse(&damaged, &receiving, |blind, _| {
            assert!(blind.word.closes() && blind.opening.closes());
            Some(PhysicalObservation { observed: observed.clone(), compared: vec![false, false, true, false], learning: PhysicalLearning::Receiving })
        }).unwrap();
        assert!(received.comparison.unwrap().unwrap().publication.stepped > 0);
        last = Some(observed);
    }
    let producing = resident.constitution().clone();
    let entered = resident.opening().clone();
    let observed = last.unwrap();
    let damaged = DamagedSection::damage(&observed, &[2]).unwrap();
    let mut phases = None;
    let started = std::time::Instant::now();
    let received = resident.receive_sparse(&damaged, &receiving, |blind, declared| {
        phases = Some(declared.clone());
        println!("four-station pair blind before repeated teacher: {blind:?}");
        Some(PhysicalObservation { observed: observed.clone(), compared: vec![false, false, true, false], learning: PhysicalLearning::PairOutputs })
    }).unwrap();
    println!("four-station current pair coordinate whole_role_ns={}", started.elapsed().as_nanos());
    let publication = received.comparison.unwrap().unwrap();
    let pairing = publication.source_pairing.unwrap();
    assert!(pairing.receiving < Rat::zero(), "own realized first-order descent");
    assert!(pairing.source_move_squared > Rat::zero());
    assert!(pairing.defect.is_zero() && pairing.composition_defect.is_zero());
    assert_eq!(pairing.receiving, pairing.opening);
    assert_eq!(pairing.opening, pairing.deposition);
    assert_eq!(pairing.return_remainders.entries, 0);
    let phases = phases.unwrap();
    let control = predict_sparse_by_field(&field, &producing, &current, &damaged, &entered, &phases).unwrap().finish();
    assert_eq!(control, received.prediction, "teacher cannot alter prior blind receipt or carry");
    assert_eq!(producing.source_port(0), resident.constitution().source_port(0));
    assert_eq!(producing.receiving_map(0), resident.constitution().receiving_map(0));
    assert!(field.offsets().iter().any(|&d| producing.pair_port(0,d).unwrap().outputs() != resident.constitution().pair_port(0,d).unwrap().outputs()));
    let common = resident.opening().clone();
    let learned = resident.constitution().clone();
    let probes = KnownTruth::cyclic_class_orbit(CyclicLaw::OrderTwo { opening: 2 }, 4, 20261006011, 4).unwrap();
    let mut effects = Vec::new();
    for (index, observed) in Encoded::identity(&probes, &field).unwrap().into_iter().enumerate() {
        let damaged = DamagedSection::damage(&observed, &[2]).unwrap();
        let started = std::time::Instant::now();
        let received = resident.receive_sparse(&damaged, &receiving, |_, _| None).unwrap();
        println!("four-station current continuing probe {index} whole_role_ns={}", started.elapsed().as_nanos());
        assert!(matches!(received.comparison, Ok(None)));
        assert!(received.prediction.balances.iter().all(|b| b.closes()));
        let before = predict_sparse_by_field(&field, &producing, &current, &damaged, &common, &phases).unwrap().finish();
        let after = predict_sparse_by_field(&field, &learned, &current, &damaged, &common, &phases).unwrap().finish();
        if index == 0 { assert_eq!(received.prediction, after); }
        effects.push(after.reads[2].read.logits.iter().zip(&before.reads[2].read.logits).map(|(a,b)| a-b).collect::<Vec<_>>());
        assert_eq!(resident.constitution(), &learned, "probes do not deposit");
    }
    // Existing source translations are a mechanical perturbation control, not independent data.
    assert!(effects.iter().flatten().any(|v| !v.is_zero()), "later receiving consequence");
    assert!(effects[1..].iter().any(|e| e != &effects[0]), "source-dependent consequence");
    println!("four-station exact matched pair effects={effects:?}; no useful-margin or generalization acceptance asserted");
}

/// Current consumer's sparse PairOutputs contract at a nonzero source frame and carried tick.
/// The historical pumped 8/3 completion-domain control remains a distinct, incomplete obligation.
#[test]
fn four_station_sparse_pair_return_at_nonzero_source_phase_matches_its_applied_direction() {
    use crate::hnn::encoding::Encoded;
    use crate::hnn::prediction::predict_sparse_by_field;
    use crate::holarchy::terrain::{CyclicLaw, KnownTruth};
    use crate::ratio::Rat;
    use crate::ratio::linear::vector::{dot, sub};
    let whole = std::time::Instant::now();
    let work = crate::hnn::word::work::read();
    let field = four_station_field();
    let mut current = Current::at_rest(&field);
    current.rekey(&field, 0, 2).unwrap();
    let receiving = receiver(4);
    let initial = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    let mut resident = PhysicalResident::new(&field, initial, current.clone(), WordOpening::Rest);
    let teaching = KnownTruth::cyclic_class_orbit(CyclicLaw::OrderTwo { opening: 2 }, 4, 20261006001, 4).unwrap();
    let mut last = None;
    println!("nonzero-phase current consumer setup_ns={}; source_frame={current:?}", whole.elapsed().as_nanos());
    for (index, observed) in Encoded::identity(&teaching, &field).unwrap().into_iter().enumerate() {
        let started = std::time::Instant::now();
        let damaged = DamagedSection::damage(&observed, &[2]).unwrap();
        let received = resident.receive_sparse(&damaged, &receiving, |blind, _| {
            assert!(blind.word.closes() && blind.opening.closes());
            Some(PhysicalObservation { observed: observed.clone(), compared: vec![false, false, true, false], learning: PhysicalLearning::Receiving })
        }).unwrap();
        assert!(received.comparison.unwrap().unwrap().publication.stepped > 0);
        println!("nonzero-phase current consumer R{index} role_ns={}; carry_tick={}", started.elapsed().as_nanos(), received.prediction.carry.ticks);
        last = Some(observed);
    }
    let producing = resident.constitution().clone();
    let entered = resident.opening().clone();
    let WordOpening::Received { carry, .. } = &entered else { panic!("actual entered carry") };
    let entered_tick = carry.ticks;
    assert_eq!(entered_tick, 12);
    assert_eq!(resident.current(), &current);
    let observed = last.unwrap();
    let damaged = DamagedSection::damage(&observed, &[2]).unwrap();
    let mut phases = None;
    let started = std::time::Instant::now();
    let received = resident.receive_sparse(&damaged, &receiving, |blind, declared| {
        phases = Some(declared.clone());
        println!("nonzero-phase current pair blind before repeated teacher: {blind:?}");
        Some(PhysicalObservation { observed: observed.clone(), compared: vec![false, false, true, false], learning: PhysicalLearning::PairOutputs })
    }).unwrap();
    println!("nonzero-phase current consumer pair role_ns={}", started.elapsed().as_nanos());
    let publication = received.comparison.unwrap().unwrap();
    let paired = publication.source_pairing.as_ref().unwrap();
    assert_eq!(paired.producing_commit, producing.commit());
    assert_eq!(paired.source_lift.as_slice(), current.lift());
    assert_eq!(paired.opened_at, entered_tick);
    assert_eq!(paired.junction_steps, 4);
    assert_eq!(paired.response_ticks, 2);
    assert_eq!(paired.crossings.len(), 1);
    assert_eq!(paired.crossings[0].tick, entered_tick + 2);
    assert!(paired.receiving < Rat::zero() && paired.source_move_squared > Rat::zero());
    assert_eq!(paired.receiving, paired.opening);
    assert_eq!(paired.opening, paired.deposition);
    assert!(paired.defect.is_zero() && paired.composition_defect.is_zero());
    assert_eq!(paired.return_remainders.entries, 0);
    assert_eq!(paired.receiving, -&publication.source_certificate.as_ref().unwrap().joint.decrease);
    let phases = phases.unwrap();
    let started = std::time::Instant::now();
    let no_deposit = predict_sparse_by_field(&field, &producing, &current, &damaged, &entered, &phases).unwrap().finish();
    assert_eq!(no_deposit, received.prediction);
    println!("nonzero-phase current consumer no-deposit role_ns={}", started.elapsed().as_nanos());
    let learned = resident.constitution().clone();
    assert_eq!(producing.source_port(0), learned.source_port(0));
    assert_eq!(producing.receiving_map(0), learned.receiving_map(0));
    let started = std::time::Instant::now();
    // Fresh hypothetical material consequence at the original producing opening, discarded.
    let applied = predict_sparse_by_field(&field, &learned, &current, &damaged, &entered, &phases).unwrap().finish();
    let delta = sub(&applied.reads[2].read.logits, &received.prediction.reads[2].read.logits);
    let covector = publication.ratio.covector().unwrap();
    assert_eq!(paired.receiving, dot(&covector.logits()[2], &delta));
    assert_eq!(paired.crossings[0].logit_move_squared, dot(&delta, &delta));
    // Already reached quantities only: this does not construct a response operator or new Word.
    let receiving_map_squared: Rat = producing.receiving_map(0).unwrap().entries().iter().map(|q| q*q).sum();
    println!("nonzero-phase current consumer receiving_map_squared={receiving_map_squared}; actual_compared_covector={:?}; reached_feature_energy={:?}; actual_source_certificate={:?}; scale_does_not_by_itself_identify_the_weak_channel", covector.logits()[2], publication.feature_energy, publication.source_certificate);
    println!("nonzero-phase current consumer applied-direction control role_ns={}", started.elapsed().as_nanos());
    let actual_opening = resident.opening().clone();
    let WordOpening::Received { carry: actual_carry, .. } = &actual_opening else { panic!("retained actual carry") };
    assert_eq!(actual_carry, &received.prediction.carry);
    let probes = KnownTruth::cyclic_class_orbit(CyclicLaw::OrderTwo { opening: 2 }, 4, 20261006011, 4).unwrap();
    let later = Encoded::identity(&probes, &field).unwrap().remove(0);
    let later = DamagedSection::damage(&later, &[2]).unwrap();
    let started = std::time::Instant::now();
    let expected = predict_sparse_by_field(&field, &learned, &current, &later, &actual_opening, &phases).unwrap().finish();
    println!("nonzero-phase current consumer later matched Word role_ns={}", started.elapsed().as_nanos());
    let started = std::time::Instant::now();
    let next = resident.receive_sparse(&later, &receiving, |_, _| None).unwrap();
    assert!(matches!(next.comparison, Ok(None)));
    assert_eq!(next.prediction, expected);
    assert_eq!(next.prediction.carry.ticks, received.prediction.carry.ticks + 3);
    assert_eq!(resident.constitution(), &learned);
    assert_eq!(resident.current(), &current);
    assert!(next.prediction.balances.iter().all(|b| b.closes()));
    println!("nonzero-phase current consumer actual later Word role_ns={}", started.elapsed().as_nanos());
    // Exact state receipts are exterior test evidence, not retained event archives in the HNN.
    println!("nonzero-phase current consumer producing={producing:?}; entered={entered:?}; learned={learned:?}; pair={paired:?}; actual_next={:?}; no completion-domain or useful1/16acceptance", next.prediction);
    println!("nonzero-phase current consumer whole_control_ns={}; owner_work={:?}; includes_final_exact_state_receipt", whole.elapsed().as_nanos(), crate::hnn::word::work::read().since(work));
}

#[test]
fn the_resident_retains_the_learned_pair_and_reads_the_correlated_family_on_its_carried_state() {
    let field = field();
    let initial = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    let current = Current::at_rest(&field);
    let mut resident =
        PhysicalResident::new(&field, initial.clone(), current.clone(), WordOpening::Rest);
    // These three declared comparisons match the accepted bounded pair consumer. Each callback
    // sees the whole blind receipt before returning its observation; no output is installed.
    for cells in [[0, 2], [1, 1]] {
        let observed = encoded(&field, &cells);
        let damaged = DamagedSection::damage(&observed, &[1]).unwrap();
        let received = resident
            .receive(&damaged, &receiver(2), |blind| {
                println!("resident blind receiving observation: {blind:?}");
                assert!(blind.opening.closes() && blind.word.closes());
                Some(PhysicalObservation {
                    observed,
                    compared: vec![false, true],
                    learning: PhysicalLearning::Receiving,
                })
            })
            .unwrap();
        assert!(received.comparison.unwrap().unwrap().publication.stepped > 0);
        assert!(
            resident
                .constitution()
                .pair_port(0, 1)
                .unwrap()
                .outputs()
                .iter()
                .flatten()
                .all(Zero::is_zero)
        );
    }
    assert_ne!(
        resident.constitution().receiving_map(0),
        initial.receiving_map(0)
    );
    let observed = encoded(&field, &[0, 1, 2]);
    let damaged = DamagedSection::damage(&observed, &[2]).unwrap();
    let received = resident
        .receive(&damaged, &receiver(3), |blind| {
            println!("resident blind pair observation: {blind:?}");
            Some(PhysicalObservation {
                observed,
                compared: vec![false, false, true],
                learning: PhysicalLearning::PairOutputs,
            })
        })
        .unwrap();
    assert!(received.comparison.unwrap().unwrap().publication.stepped > 0);
    assert_ne!(
        resident.constitution().pair_port(0, 1),
        initial.pair_port(0, 1)
    );
    let commit = resident.constitution().commit();
    let entering = resident.opening().clone();
    let entered_tick = match &entering {
        WordOpening::Received { carry, .. } => carry.ticks,
        WordOpening::Rest => panic!("the resident must retain its actual physical end"),
    };
    let mut cells = vec![2; 9];
    cells[0] = 0;
    cells[8] = 1;
    let chart = encoded(&field, &[]);
    let sparse = DamagedSection::of_runs(
        9,
        &chart,
        vec![
            (0, encoded(&field, &cells[..1])),
            (2, encoded(&field, &cells[2..])),
        ],
    )
    .unwrap();
    let blind = resident.read(&sparse, &receiver(2)).unwrap();
    assert_eq!(
        resident.constitution().commit(),
        commit,
        "an unobserved query does not deposit"
    );
    assert_eq!(blind.carry.ticks, entered_tick + 1);
    assert_eq!(
        resident.current(),
        &current,
        "the declared source frame is retained separately"
    );
    let domain = blind.domains[1].as_ref().unwrap();
    let response = domain.completion.as_ref().unwrap();
    let phases =
        ReceivingPhases::declare(&field, resident.constitution(), &current, &receiver(2)).unwrap();
    let mut union = std::collections::BTreeSet::new();
    for missing in 0..field.alphabet() {
        cells[1] = missing;
        let complete = DamagedSection::damage(&encoded(&field, &cells), &[]).unwrap();
        let witness = repair_by_field(
            &field,
            resident.constitution(),
            &current,
            &complete,
            &entering,
            &phases,
        )
        .unwrap();
        assert_eq!(
            crate::ratio::linear::vector::add(
                &response.fixed_logits,
                &response.label_logits[missing]
            ),
            witness.reads[1].read.logits
        );
        union.extend(witness.reads[1].leaders());
    }
    assert_eq!(domain.classes, union.into_iter().collect::<Vec<_>>());
    assert_eq!(blind.cells[1], RepairedCell::Released(2));
    assert!(blind.opening.closes() && blind.word.closes());
    assert!(blind.balances.iter().all(|balance| balance.closes()));
    println!("retained resident target-free whole output: {blind:?}");
}

#[test]
fn a_refused_resident_observation_keeps_material_and_carries_into_the_next_native_read() {
    let field = field();
    let initial = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    let current = Current::at_rest(&field);
    let mut resident = PhysicalResident::new(&field, initial.clone(), current, WordOpening::Rest);
    let observed = encoded(&field, &[0, 2]);
    let damaged = DamagedSection::damage(&observed, &[1]).unwrap();
    let first = resident
        .receive(&damaged, &receiver(2), |_| {
            Some(PhysicalObservation {
                observed,
                compared: vec![false, false],
                learning: PhysicalLearning::Receiving,
            })
        })
        .unwrap();
    assert!(first.comparison.is_err());
    assert_eq!(resident.constitution(), &initial);
    let carry = first.prediction.carry;
    let next = resident.read(&damaged, &receiver(2)).unwrap();
    assert_eq!(next.carry.ticks, carry.ticks + 1);
    assert_eq!(resident.constitution(), &initial);
    assert!(next.opening.closes() && next.word.closes());
    let opening = resident.opening().clone();
    let foreign = super::support::encoded_classes(3, &[0, 1]);
    let foreign = DamagedSection::damage(&foreign, &[1]).unwrap();
    assert!(resident.read(&foreign, &receiver(2)).is_err());
    assert_eq!(
        resident.opening(),
        &opening,
        "forward refusal executes no new reception"
    );
    assert_eq!(resident.constitution(), &initial);
}

/// A bounded native law control: two post-blind R observations, one selected source observation,
/// a matched independent forward and a different unobserved continuation. The targets are not a
/// validation dataset; neither the contract nor the next query asks for a desired output class.
#[test]
fn the_resident_certifies_the_applied_source_return_at_its_carried_clock_and_nonzero_phase() {
    use crate::ratio::linear::vector::{dot, sub};
    use crate::ratio::Rat;
    for learning in [PhysicalLearning::SourcePorts, PhysicalLearning::PairOutputs] {
        let field = field();
        let initial = super::prediction::pumped_at(
            &field, Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap(), 0,
        );
        let mut current = Current::at_rest(&field);
        current.rekey(&field, 0, 3).unwrap();
        let mut resident = PhysicalResident::new(
            &field, initial, current.clone(), WordOpening::Rest,
        );
        for cells in [[0, 2], [1, 1]] {
            let observed = encoded(&field, &cells);
            let damaged = DamagedSection::damage(&observed, &[1]).unwrap();
            let received = resident.receive(&damaged, &receiver(2), |_| Some(PhysicalObservation {
                observed, compared: vec![false, true], learning: PhysicalLearning::Receiving,
            })).unwrap();
            let publication = received.comparison.unwrap().unwrap();
            assert!(publication.source_pairing.is_none());
        }
        let producing = resident.constitution().clone();
        let entered = resident.opening().clone();
        let WordOpening::Received { carry, .. } = &entered else { panic!("physical carry") };
        let entered_tick = carry.ticks;
        assert!(entered_tick > 0);
        let observed = encoded(&field, &[0, 1, 2]);
        let damaged = DamagedSection::damage(&observed, &[2]).unwrap();
        let mut captured = None;
        let received = resident.receive(&damaged, &receiver(3), |blind| {
            captured = Some(blind.clone());
            Some(PhysicalObservation {
                observed, compared: vec![false, false, true], learning,
            })
        }).unwrap();
        assert_eq!(received.prediction, captured.unwrap());
        let publication = received.comparison.unwrap().unwrap();
        let paired = publication.source_pairing.as_ref().unwrap();
        assert_eq!(paired.producing_commit, producing.commit());
        assert_eq!(paired.source_lift.as_slice(), current.lift());
        assert_eq!(paired.receiver, 0);
        assert_eq!(paired.opened_at, entered_tick);
        assert_eq!(paired.junction_steps, 3);
        assert_eq!(paired.response_ticks, 2);
        assert!(paired.source_move_squared > Rat::zero());
        assert!(!paired.receiving.is_zero(), "a nonzero observable pairing is required");
        assert_eq!(paired.receiving, paired.opening);
        assert_eq!(paired.opening, paired.deposition);
        assert!(paired.defect.is_zero() && paired.composition_defect.is_zero());
        assert_eq!(paired.return_remainders.entries, 0);
        assert_eq!(paired.crossings.len(), 1);
        assert_eq!(paired.crossings[0].station, 2);
        assert_eq!(paired.crossings[0].crossing, 2);
        assert_eq!(paired.crossings[0].tick, entered_tick + 2);
        assert_eq!(paired.receiving, -&publication.source_certificate.as_ref().unwrap().joint.decrease);
        assert_eq!(producing.receiving_map(0), resident.constitution().receiving_map(0));
        assert_eq!(producing.ring_resonator(0), resident.constitution().ring_resonator(0));
        let phases = ReceivingPhases::declare(
            &field, &producing, &current, &receiver(3),
        ).unwrap();
        // This extra Word is an exterior unit control, not how production obtains its certificate.
        let matched = repair_by_field(
            &field, resident.constitution(), &current, &damaged, &entered, &phases,
        ).unwrap();
        let delta = sub(&matched.reads[2].read.logits, &received.prediction.reads[2].read.logits);
        let covector = publication.ratio.covector().unwrap();
        assert_eq!(paired.receiving, dot(&covector.logits()[2], &delta));
        assert_eq!(paired.crossings[0].logit_move_squared, dot(&delta, &delta));
        assert!(matched.opening.closes() && matched.word.closes());
        assert!(matched.balances.iter().all(|balance| balance.closes()));
        // The publication did not install the hypothetical source-perturbed state: the next
        // section enters on the original blind physical end and contemporary learned material.
        let next_entered = resident.opening().clone();
        let WordOpening::Received { carry: next_carry, .. } = &next_entered else { panic!("carry") };
        assert_eq!(next_carry, &received.prediction.carry);
        let chart = encoded(&field, &[]);
        let later = DamagedSection::of_runs(4, &chart, vec![
            (0, encoded(&field, &[1, 0])), (3, encoded(&field, &[3])),
        ]).unwrap();
        let expected_phases = ReceivingPhases::declare(
            &field, resident.constitution(), &current, &receiver(3),
        ).unwrap();
        let actual_same_law = repair_by_field(
            &field, resident.constitution(), &current, &later, &next_entered, &expected_phases,
        ).unwrap();
        let commit = resident.constitution().commit();
        let next = resident.read(&later, &receiver(3)).unwrap();
        assert_eq!(next, actual_same_law);
        assert_eq!(next.carry.ticks, received.prediction.carry.ticks + 2);
        assert_eq!(resident.constitution().commit(), commit);
        assert_eq!(resident.current(), &current);
        println!("resident source-return contract {learning:?}: {paired:?}; blind {:?}; next {:?}",
            received.prediction, next);
    }
}
