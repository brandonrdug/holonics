//! Public native source entrance and its actual continuing field consumer.
//! Fixed physical law fixtures only: no training, private data or scientific repair claim.

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use holonics::hnn::word::PowerForm;
use holonics::hnn::{
    Absorption, Constitution, Current, Encoded, Field, FieldDeclaration, RingDeclaration,
    SourceMoment, Word, WordOpening,
};
use holonics::holarchy::terrain::{CyclicLaw, KnownTruth};
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
    pair_field_with_offsets(alphabet, Vec::new())
}

fn pair_field_with_offsets(alphabet: usize, offsets: Vec<usize>) -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(16, (0..16).collect())],
            contacts: Vec::new(),
            loops: Vec::new(),
            sources: vec![0],
            offsets,
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

/// A source-placement counterexample, not a training family. At unit transport, the continued
/// section keeps phase counts and omits its offset pairs. Swapping two unlike intact classes a
/// source period apart therefore leaves the entire moment equal. No later choice of element,
/// contact or receiving coefficients can distinguish those identical native inputs.
fn source_alias_field() -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(8, (0..8).collect()), ring(3, Vec::new())],
            contacts: vec![ContactDeclaration {
                from: 0,
                to: 1,
                channel: vec![(0, 0), (1, 1), (2, 2)],
                admittance: integer(2),
                exponent: integer(0),
            }],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver(0, 1)],
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
fn same_phase_intact_swap_has_one_native_source_moment_and_one_physical_motion() {
    let field = source_alias_field();
    let current = Current::at_rest(&field);
    let period = usize::try_from(field.ring(0).period()).unwrap();
    let mut left = vec![None; period + 1];
    left[0] = Some(0);
    left[period] = Some(1);
    let mut right = left.clone();
    right.swap(0, period);
    assert_ne!(left, right);
    assert_ne!(left[0], right[0]);
    let open = SourceMoment::open(&field, &current);
    let left_moment = open.continued(&field, &current, 0, &left).unwrap();
    let right_moment = open.continued(&field, &current, 0, &right).unwrap();
    assert_eq!(left_moment, right_moment);

    // Execute the existing nonlinear loaded port as well: it cannot recover a placement that
    // the source moment merged. The only supplied arrays are intact inputs, never a target.
    let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ring_resonator(
            &field,
            0,
            material(&field, 0)
                .with_symmetric_saturation(rat(1, 16))
                .unwrap(),
        )
        .unwrap();
    assert_eq!(
        holonics::hnn::field::FieldMaterial::transport(&theta, 0),
        integer(1)
    );
    assert_eq!(
        left_moment.open_storage(&field, &theta, &current).unwrap(),
        right_moment.open_storage(&field, &theta, &current).unwrap()
    );
    let (mut left_word, left_receipt) =
        Word::open_exact_received(&field, &theta, &current, &left_moment, &WordOpening::Rest)
            .unwrap();
    let (mut right_word, right_receipt) =
        Word::open_exact_received(&field, &theta, &current, &right_moment, &WordOpening::Rest)
            .unwrap();
    assert!(left_receipt.closes() && right_receipt.closes());
    assert_eq!(left_word.change().unwrap(), right_word.change().unwrap());
    for _ in 0..3 {
        left_word.tick().unwrap();
        right_word.tick().unwrap();
        assert_eq!(left_word.change().unwrap(), right_word.change().unwrap());
        assert!(left_word.field_balances().last().unwrap().closes());
        assert!(right_word.field_balances().last().unwrap().closes());
    }
    assert_eq!(
        left_word.reception_end().unwrap(),
        right_word.reception_end().unwrap()
    );
}

// These unit tests exercise the entrance and its actual physical consumer.
// The synthetic passage supplies lawful unit-test truth; it is not a
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
    println!(
        "source entrance: before={} after={} absorbed={} imposed={}",
        receipt.before, receipt.after, receipt.absorbed, receipt.imposed
    );
    assert_eq!(word.change().unwrap().storage, expected);
    word.tick().unwrap();
    assert!(word.field_balances().last().unwrap().closes());
    let first_crossing = word.change().unwrap();
    let [u, w] = first_crossing.resonators[0].as_ref().unwrap();
    // At this cut Y_source = G_contact: the first scattering transmits the pulse
    // into the contact and leaves zero at the source storage/loaded port.
    assert!(u.iter().chain(w).all(Zero::is_zero));
    assert!(
        first_crossing
            .arrivals
            .iter()
            .flatten()
            .flatten()
            .any(|x| !x.is_zero())
    );
    // The next crossing reads that actual contact return, without resetting the Word.
    word.tick().unwrap();
    assert!(word.field_balances().last().unwrap().closes());
    let change = word.change().unwrap();
    let [u, w] = change.resonators[0].as_ref().unwrap();
    assert!(u.iter().chain(w).any(|x| !x.is_zero()));
    println!(
        "source passage: first loaded point at rest, second loaded point reached through contact return"
    );
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
    println!(
        "source re-entry: carried_crossing={} opened_at={} source_absorbed={} source_imposed={}",
        carry.ticks,
        next.opened_at(),
        receipt.absorbed,
        receipt.imposed
    );
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
fn nonzero_offset_moments_drive_the_actual_loaded_port_without_marginal_source() {
    use holonics::hnn::field::ConstitutionRead;
    use holonics::hnn::moment::PairPort;
    let field = pair_field_with_offsets(4, vec![1]);
    let mut current = Current::at_rest(&field);
    let mut source = SourceMoment::open(&field, &current);
    // The word [0, 1] as a known truth (THE_MACHINE guard 9): the line terrain on ℤ/4 whose drawn
    // start and step are 0 and 1, through its declared identity.
    let truth = KnownTruth::cyclic(CyclicLaw::Line, 4, 2_026_100_982, 1, 2).unwrap();
    assert_eq!(truth.passages(), &[vec![0, 1]]);
    let cells = Encoded::identity(&truth, &field).unwrap().remove(0);
    let ingested = source.ingest(&field, &mut current, &cells).unwrap();
    assert_eq!(ingested.cells, 2);
    let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ring_resonator(
            &field,
            0,
            material(&field, 0)
                .with_symmetric_saturation(Rat::one())
                .unwrap(),
        )
        .unwrap()
        // A declared probe isolates the factored offset port with marginal E zero.
        .with_ports(
            0,
            None,
            Some(ExactRatMatrix::zero(field.ring(0).width(), field.alphabet()).unwrap()),
            None,
        )
        .unwrap();
    // Initial E^(1) has zero outputs. Declare one unit output along its existing
    // factored read axes so the probe exercises a nonzero pair material, without
    // pretending that this fixture material was located or learned.
    let pair = theta.pair_port(0, 1).unwrap();
    let mut outputs = pair.outputs().to_vec();
    outputs[0][0] = Rat::one();
    let pair = PairPort::new(
        outputs,
        pair.current_reads().to_vec(),
        pair.earlier_reads().to_vec(),
    )
    .unwrap();
    let theta = theta.with_pair(0, 1, pair).unwrap();
    let table = source.offset_table(&field, 0, 1).unwrap().unwrap();
    assert_eq!(table.population, 1);
    let (marginal, pairs) = source.open_parts(&field, &theta, &current, 0).unwrap();
    assert!(
        marginal
            .iter()
            .flat_map(|(_, values)| values)
            .all(Zero::is_zero)
    );
    assert!(pairs.iter().any(|x| !x.is_zero()));
    assert_eq!(
        source.open_storage(&field, &theta, &current).unwrap()[0],
        pairs
    );
    let (mut word, receipt) = Word::open_source_exact_received(
        &field,
        &theta,
        &current,
        Arc::new(source),
        &WordOpening::Rest,
    )
    .unwrap();
    assert!(receipt.closes());
    assert!(receipt.imposed > Rat::zero());
    word.tick().unwrap();
    assert!(word.field_balances().last().unwrap().closes());
    let change = word.change().unwrap();
    let [u, w] = change.resonators[0].as_ref().unwrap();
    assert!(u.iter().chain(w).any(|x| !x.is_zero()));
    println!(
        "offset-only source entrance: pair_population={} pair_weight={} source_imposed={}",
        table.population, table.weight, receipt.imposed
    );
}

#[test]
fn an_observed_pair_deposit_changes_the_later_continuing_loaded_response() {
    use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    use holonics::hnn::executed::pair_deposit;
    use holonics::hnn::field::ConstitutionRead;
    use holonics::hnn::keys::{PairLocation, station_pairs};
    let field = pair_field(4);
    // The locator is given observations, not the desired LocatedPair or its distance: the order-2
    // terrain's passages (a drawn opening of two cells, then x_t = x_(t−2) + 1 on ℤ/4), entering
    // through the terrain's declared identity (THE_MACHINE guard 9).
    let truth =
        KnownTruth::cyclic(CyclicLaw::OrderTwo { opening: 2 }, 4, 2_026_100_984, 32, 8).unwrap();
    let mut location = PairLocation::open(&field, 0);
    for passage in Encoded::identity(&truth, &field).unwrap() {
        for observation in station_pairs(&field, 0, &passage, 2).unwrap() {
            location.observe(&observation);
        }
    }
    let located = location
        .survivors()
        .located()
        .expect("the fixture's pair is located");
    assert_eq!(
        (located.offset, located.map.clone()),
        (2, vec![(0, 1), (1, 2), (2, 3), (3, 0)])
    );
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
    let before_change = before.change().unwrap();
    let after_change = after.change().unwrap();
    let before_state = before_change.resonators[0].as_ref().unwrap();
    let after_state = after_change.resonators[0].as_ref().unwrap();
    println!(
        "reached source relation: slip_before={} slip_after={} next_ring0_delta_u0={} next_ring0_delta_w0={}",
        deposit.slip_before,
        deposit.slip_after,
        &after_state[0][0] - &before_state[0][0],
        &after_state[1][0] - &before_state[1][0]
    );
    assert_ne!(
        before.change().unwrap().resonators,
        after.change().unwrap().resonators
    );
    // This gate is an arrived-material-to-actual-motion gate. Symbol decoding and the
    // field's compatible-domain coverage remain the consumer's independent acceptance.
}
