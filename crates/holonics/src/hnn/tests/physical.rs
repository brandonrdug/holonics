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
