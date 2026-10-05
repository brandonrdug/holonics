//! Public native source entrance and its actual continuing field consumer.
//! Fixed physical law fixtures only: no training, private data or scientific repair claim.

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use holonics::hnn::word::PowerForm;
use holonics::hnn::{
    Absorption, Constitution, Current, Field, FieldDeclaration, RingDeclaration, SourceMoment,
    Word, WordOpening,
};
use holonics::holon::parametron::Carrier;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{Rat, integer, rat};
use num_traits::{One, Zero};
use std::sync::Arc;

fn ring(period: u64, lock: Vec<u64>) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|p| ((period - p) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial: 0,
    }
}

fn receiver(ring: usize, aperture: usize) -> ReceiverDeclaration {
    ReceiverDeclaration {
        ring,
        aperture,
        tolerance: rat(1, 16),
        depth: 2,
        prior: StopPrior::half(),
        mass: 1,
        base: BaseMeasure::Even,
        receiving_prior: 0,
    }
}

fn chain() -> Field {
    let contact = |from, to, exponent| ContactDeclaration {
        from,
        to,
        channel: vec![(0, 0), (1, 1)],
        admittance: integer(2),
        exponent: integer(exponent),
    };
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(2, vec![0]), ring(3, vec![0]), ring(2, vec![])],
            contacts: vec![contact(0, 1, 2), contact(1, 2, 0)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: vec![1],
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver(2, 2)],
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

fn pair_field(alphabet: usize) -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(16, (0..16).collect())],
            contacts: Vec::new(),
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver(0, 1)],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 24,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

fn material(field: &Field, ring: usize) -> ResonatorMaterial {
    let width = field.ring(ring).width();
    ResonatorMaterial::new(
        ExactRatMatrix::identity(width).unwrap(),
        ExactRatMatrix::identity(width).unwrap().scaled(&rat(1, 8)),
        ExactRatMatrix::identity(width).unwrap().scaled(&rat(1, 16)),
        Some(PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap()),
    )
    .unwrap()
}

// The following are proposed unit tests of an entrance and its actual physical consumer.
// The synthetic passage in the last test supplies lawful unit-test truth; it is not a
// scientific validation set, training curriculum or evidence of text repair.

#[test]
fn sparse_source_moments_enter_the_actual_loaded_port_with_exact_work() {
    let field = chain();
    let current = Current::at_rest(&field);
    let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ring_resonator(
            &field,
            0,
            material(&field, 0)
                .with_symmetric_saturation(Rat::one())
                .unwrap(),
        )
        .unwrap();
    // Only station zero is clamped: missing stations contribute no class and no offset pair.
    let source = SourceMoment::open(&field, &current)
        .continued(&field, &current, 0, &[Some(0), None, None])
        .unwrap();
    let expected = source.open_storage(&field, &theta, &current).unwrap();
    let (mut word, receipt) = Word::open_source_exact_received(
        &field,
        &theta,
        &current,
        Arc::new(source.clone()),
        &WordOpening::Rest,
    )
    .unwrap();
    assert!(receipt.closes());
    assert_eq!(receipt.before, Rat::zero());
    assert_eq!(receipt.absorbed, Rat::zero());
    assert!(receipt.imposed > Rat::zero());
    assert_eq!(word.change().unwrap().storage, expected);
    word.tick().unwrap();
    assert!(word.field_balances().last().unwrap().closes());
    let change = word.change().unwrap();
    let [u, w] = change.resonators[0].as_ref().unwrap();
    assert!(u.iter().chain(w).any(|x| !x.is_zero()));
}

#[test]
fn exact_source_reentry_preserves_the_entered_interior_and_counts_source_once() {
    let field = chain();
    let current = Current::at_rest(&field);
    let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ring_resonator(
            &field,
            0,
            material(&field, 0)
                .with_symmetric_saturation(Rat::one())
                .unwrap(),
        )
        .unwrap();
    let source = SourceMoment::open(&field, &current)
        .continued(&field, &current, 0, &[Some(0)])
        .unwrap();
    let (mut first, _) = Word::open_source_exact_received(
        &field,
        &theta,
        &current,
        Arc::new(source.clone()),
        &WordOpening::Rest,
    )
    .unwrap();
    first.run(2).unwrap();
    let carry = first.reception_end().unwrap();
    let opening = WordOpening::Received {
        carry: carry.clone(),
        absorption: Absorption::Nothing,
    };
    let (mut next, receipt) =
        Word::open_exact_received(&field, &theta, &current, &source, &opening).unwrap();
    assert!(receipt.closes());
    assert_eq!(next.opened_at(), carry.ticks);
    let change = next.change().unwrap();
    assert_eq!(change.arrivals, carry.change.arrivals);
    assert_eq!(change.states, carry.change.states);
    assert_eq!(change.resonators, carry.change.resonators);
    assert_eq!(change.resonator_phases, carry.change.resonator_phases);
    let injection = source.open_storage(&field, &theta, &current).unwrap();
    for ring in 0..field.rings().len() {
        assert_eq!(
            change.storage[ring],
            if field.is_source(ring) {
                injection[ring].clone()
            } else {
                carry.change.storage[ring].clone()
            },
        );
    }
    let form = PowerForm::read(&field, &theta, &current).unwrap();
    assert_eq!(
        receipt.before,
        form.power(&carry.change).unwrap() + form.resonator_power(&carry.change).unwrap()
    );
    next.tick().unwrap();
    assert!(next.field_balances().last().unwrap().closes());
}

#[test]
fn an_observed_pair_deposit_changes_the_later_continuing_loaded_response() {
    use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    use holonics::hnn::executed::pair_deposit;
    use holonics::hnn::field::ConstitutionRead;
    use holonics::hnn::keys::{PairLocation, station_pairs};
    let field = pair_field(4);
    // The locator is given observations, not the desired LocatedPair or its distance.
    let mut location = PairLocation::open(&field, 0);
    for a in 0..4 {
        for b in 0..4 {
            let mut passage = vec![a, b];
            for _ in 0..6 {
                passage.push((passage[passage.len() - 2] + 1) % 4);
            }
            for observation in station_pairs(&field, 0, &passage, 2).unwrap() {
                location.observe(&observation);
            }
        }
    }
    let located = location
        .survivors()
        .located()
        .expect("the fixture's pair is located");
    let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ring_resonator(
            &field,
            0,
            material(&field, 0)
                .with_symmetric_saturation(Rat::one())
                .unwrap(),
        )
        .unwrap();
    let prior = theta.source_port(0).unwrap().clone();
    let (learned, deposit) = pair_deposit(&field, &theta, &prior, 0, &located).unwrap();
    assert!(deposit.certificate.holds());
    assert!(deposit.slip_after < deposit.slip_before);
    let current = Current::at_rest(&field);
    let source = SourceMoment::open(&field, &current)
        .continued(&field, &current, 0, &[Some(1)])
        .unwrap();
    let (mut prior_word, _) = Word::open_source_exact_received(
        &field,
        &theta,
        &current,
        Arc::new(source.clone()),
        &WordOpening::Rest,
    )
    .unwrap();
    prior_word.run(2).unwrap();
    let carry = prior_word.reception_end().unwrap();
    let opening = WordOpening::Received {
        carry,
        absorption: Absorption::Nothing,
    };
    let (mut before, before_work) =
        Word::open_exact_received(&field, &theta, &current, &source, &opening).unwrap();
    let (mut after, after_work) =
        Word::open_exact_received(&field, &learned, &current, &source, &opening).unwrap();
    assert!(before_work.closes() && after_work.closes());
    assert_eq!(
        before.change().unwrap().resonators,
        after.change().unwrap().resonators
    );
    before.tick().unwrap();
    after.tick().unwrap();
    assert!(before.field_balances().last().unwrap().closes());
    assert!(after.field_balances().last().unwrap().closes());
    assert_ne!(
        before.change().unwrap().resonators,
        after.change().unwrap().resonators
    );
    // This gate is an arrived-material-to-actual-motion gate. Symbol decoding and the
    // field's compatible-domain coverage remain the consumer's independent acceptance.
}
