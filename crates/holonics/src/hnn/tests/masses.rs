//! The receiving parametron's region class masses (Decision 27): the context-free fixture and its
//! Krichevsky–Trofimov fixed point at every prefix, before and after the grain reader; the masses'
//! forgetting of the past's order; the order-1 face at the preceding-cell region, through the
//! compare's composition and the constitution's deposit; the grain exponent's integer comparison;
//! the refusals; the bits; and the field's declaration of the partition.

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use super::learning::{OPEN_BUDGET, chain, chain_declaration, chain_of};
use super::support::{contact, small_field};
use crate::hnn::HnnError;
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution, Locus, Steps};
use crate::hnn::field::{ConstitutionRead, Current, Field, FieldDeclaration};
use crate::hnn::masses::{ClassMasses, CountFace, MassStep, Regions, grain_exponent};
use crate::hnn::moment::SourceMoment;
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::Deposit;
use crate::hnn::ratio::{HolonRatio, interval_difference, log2_enclosure, target_phases};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::reference::{compose, kt_probability};
use crate::ratio::{Rat, integer, rat};

fn unit(ring: usize, region: usize, class: usize) -> MassStep {
    MassStep {
        ring,
        region,
        class,
        weight: integer(1),
    }
}

/// `2^k ≤ p^L < 2^(k+1)`, checked over ℚ.
fn brackets(p: &Rat, grain: u64, k: &BigInt) -> bool {
    let power = |x: &Rat| {
        let mut out = Rat::one();
        for _ in 0..grain {
            out *= x;
        }
        out
    };
    let two = |k: &BigInt| {
        let magnitude = usize::try_from(k.magnitude().clone()).unwrap();
        let value = Rat::from_integer(BigInt::one() << magnitude);
        if k.sign() == num_bigint::Sign::Minus {
            value.recip()
        } else {
            value
        }
    };
    let read = power(p);
    two(k) <= read && read < two(&(k + 1))
}

/// **The grain read of a probability**: its exponent by the same integer comparison.
fn grain_of(p: &Rat, grain: u64) -> BigInt {
    grain_exponent(
        &p.numer().to_biguint().unwrap(),
        &p.denom().to_biguint().unwrap(),
        grain,
    )
    .unwrap()
}

/// Decision 27's context-free fixture (Lean `HNN/RegionCounts.{kt_fixture, grain_fixture,
/// count_face_eq_kt}`): one region, two classes `a, b`, `α = (1/2, 1/2)`, unit weights, `L_R = 16`.
/// After `a, a, b` the masses are `C = (5/2, 3/2)` (half-units `(5, 3)`), `N = 4`, `p = (5/8, 3/8)`,
/// the grain exponents `(−11, −23)`, the carry and phase classes `(−1, 5)` and `(−2, 9)`. At every
/// prefix the count face is the online order-0 Krichevsky–Trofimov probability exactly (the
/// reference's baseline, `kt_probability`), and so is its grain read: the same exponent from the
/// same integer comparison. The scored face of the grain logits codes each class within one grain
/// of KT's code length (`grain_code_residual`).
#[test]
fn the_context_free_fixture_is_the_order_zero_krichevsky_trofimov_face() {
    let (a, b, grain) = (0usize, 1usize, 16u64);
    let mut masses = ClassMasses::prior(Regions::Whole, 2);
    let mut counts = [0u64; 2];
    let within = rat(1, 16);
    for (seen, class) in [a, a, b].into_iter().enumerate() {
        // The face read before the deposit: the online order-0 KT probability of the prefix.
        let count = CountFace::read(&masses, 0, grain).unwrap();
        for c in [a, b] {
            let kt = kt_probability(counts[c], seen as u64, 2);
            assert_eq!(masses.probability(0, c).unwrap(), kt, "prefix {seen}");
            assert_eq!(count.exponents()[c], grain_of(&kt, grain), "prefix {seen}");
            assert!(brackets(&kt, grain, &count.exponents()[c]));
            let gap = interval_difference(
                &count.code_length(c).unwrap(),
                &log2_enclosure(&kt.recip()).unwrap(),
            )
            .unwrap();
            assert!(
                gap.lower > -within.clone() && gap.upper < within,
                "prefix {seen}"
            );
        }
        masses.deposit(&unit(2, 0, class)).unwrap();
        counts[class] += 1;
    }
    assert_eq!(masses.half_units(0, a).unwrap(), 5);
    assert_eq!(masses.half_units(0, b).unwrap(), 3);
    assert_eq!(masses.mass(0, a).unwrap(), rat(5, 2));
    assert_eq!(masses.mass(0, b).unwrap(), rat(3, 2));
    assert_eq!(masses.total(0).unwrap(), integer(4));
    assert_eq!(masses.probability(0, a).unwrap(), rat(5, 8));
    assert_eq!(masses.probability(0, b).unwrap(), rat(3, 8));
    assert_eq!(masses.probability(0, a).unwrap(), kt_probability(2, 3, 2));
    assert_eq!(masses.probability(0, b).unwrap(), kt_probability(1, 3, 2));
    let count = CountFace::read(&masses, 0, grain).unwrap();
    assert_eq!(count.exponents(), &[BigInt::from(-11), BigInt::from(-23)]);
    assert_eq!(
        count.cells(),
        vec![(BigInt::from(-1), 5u64), (BigInt::from(-2), 9u64)]
    );
    assert_eq!(
        count.logits(),
        vec![rat(-11, 16), Rat::zero(), rat(-23, 16), Rat::zero()]
    );
    assert_eq!(masses.deposited_mass(), integer(3));
    // The prior decays exactly (`count_prior_decay`): p = A/(A+S)·α/A + S/(A+S)·q̄ with A = 1, S = 3.
    let (prior, reached) = (integer(1), integer(3));
    let qbar = [rat(2, 3), rat(1, 3)];
    for c in [a, b] {
        assert_eq!(
            masses.probability(0, c).unwrap(),
            &prior / (&prior + &reached) * rat(1, 2) + &reached / (&prior + &reached) * &qbar[c]
        );
    }
}

/// The masses forget the order of the past (Lean `HNN/RegionCounts.{regionRun_perm,
/// past_permutation_fixture, count_future_sufficient}`): `a, a, b` and `a, b, a` leave equal masses,
/// so every future word of reached comparisons leaves equal masses and equal faces.
#[test]
fn permuting_the_past_gives_the_same_future_face() {
    let run = |word: &[usize]| {
        let mut masses = ClassMasses::prior(Regions::Whole, 2);
        for &class in word {
            masses.deposit(&unit(2, 0, class)).unwrap();
        }
        masses
    };
    let (mut left, mut right) = (run(&[0, 0, 1]), run(&[0, 1, 0]));
    assert_eq!(left, right);
    for class in [1usize, 1, 0, 1] {
        left.deposit(&unit(2, 0, class)).unwrap();
        right.deposit(&unit(2, 0, class)).unwrap();
        assert_eq!(
            CountFace::read(&left, 0, 16).unwrap(),
            CountFace::read(&right, 0, 16).unwrap()
        );
    }
    assert_ne!(run(&[0, 0, 1]), run(&[0, 1, 1]));
}

/// **At the preceding-cell region the count face is order-1's** (Decision 27): on a field of
/// aperture 1, each window's pending ratio reads its count face at the region of its moment's
/// retained window (`window[0]`, the cell before the target; the empty-window region at the cut's
/// start); the compare's composition stages one unit mass at that region and the target's class
/// (`reference::compose`), and the constitution deposits it. At every window the count face read
/// through the pending ratio is the online order-1 Krichevsky–Trofimov probability of the next cell
/// given its preceding cell exactly, the stream's first cell in its own empty-window context, and
/// its grain read is order-1's by the same comparison.
#[test]
fn at_the_preceding_cell_region_the_count_face_is_order_one() {
    let field = small_field(&[2, 3], vec![contact(0, 1, 1, 0)], 1);
    let alphabet = field.alphabet();
    let mut theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let stream = [1usize, 1, 0, 1, 1, 0, 0, 1, 1, 1];
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    let mut order_one: BTreeMap<(Option<usize>, usize), u64> = BTreeMap::new();
    let mut totals: BTreeMap<Option<usize>, u64> = BTreeMap::new();
    let mut previous = None;
    for &target in &stream {
        let phases =
            ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
        let pending = PendingRatio::produce(&current, &moment, &phases, theta.commit());
        let count = phases.count_face(&theta, &moment).unwrap();
        let region = previous.map_or(0, |cell: usize| 1 + cell);
        assert_eq!(count.region(), region);
        let masses = theta.class_masses(1).unwrap();
        for class in 0..alphabet {
            let kt = kt_probability(
                order_one.get(&(previous, class)).copied().unwrap_or(0),
                totals.get(&previous).copied().unwrap_or(0),
                alphabet,
            );
            assert_eq!(masses.probability(region, class).unwrap(), kt);
            assert_eq!(count.exponents()[class], grain_of(&kt, phases.grain()));
        }
        // The compare's composition and the deposit.
        let (word, faces) = pending.read(&field, &theta).unwrap();
        let anchors = target_phases(&field, pending.anchor(), 1, &[target]).unwrap();
        let ratio = HolonRatio::compare(faces, &[target], &anchors).unwrap();
        let back = word
            .pull_back(
                &ratio.covector().unwrap(),
                theta.receiving_map(1).unwrap(),
                &pending.anchor()[1],
                &phases,
            )
            .unwrap();
        let (_, deposit) = compose(&field, &theta, &pending, &back, &[target]).unwrap();
        assert_eq!(deposit.masses(), &[unit(1, region, target)]);
        let (next, reading) = theta.deposited(&deposit).unwrap();
        assert_eq!(reading.masses, integer(1));
        assert_eq!(
            next.class_masses(1)
                .unwrap()
                .half_units(region, target)
                .unwrap(),
            theta
                .class_masses(1)
                .unwrap()
                .half_units(region, target)
                .unwrap()
                + 2
        );
        theta = next;
        *order_one.entry((previous, target)).or_insert(0) += 1;
        *totals.entry(previous).or_insert(0) += 1;
        previous = Some(target);
        // One cell is consumed whether or not its step carries the joint clock out.
        let ingested = moment.ingest(&field, &mut current, &[target]).unwrap();
        assert_eq!(ingested.cells, 1);
    }
    assert_eq!(
        theta.class_masses(1).unwrap().deposited_mass(),
        integer(stream.len() as i64)
    );
}

/// The deposit of the class masses through the constitution (Lean `count_step_mass`): each step
/// adds its weight at its region and class and to its region's total, and nothing else; the reading
/// reports the mass added; the receiving locus's clock does not move for masses alone, which carry
/// no remainder; the successor's bits count the masses. On the chain's exposure field (no window,
/// the whole region) the deposits `a, a, b` give the order-0 KT face.
#[test]
fn the_constitution_deposits_the_masses_of_its_reached_comparisons() {
    let field = chain_of(18);
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let masses = theta.class_masses(2).unwrap();
    assert_eq!(masses.regions(), Regions::Whole);
    assert_eq!(masses.region_count(), 1);
    let mut next = theta.clone();
    let mut counts = [0u64; 4];
    for (seen, class) in [0usize, 0, 1].into_iter().enumerate() {
        let deposit = Deposit::new(next.commit(), Vec::new(), Vec::new(), Vec::new())
            .with_masses(vec![unit(2, 0, class)]);
        let (successor, reading) = next.deposited(&deposit).unwrap();
        assert_eq!(reading.masses, integer(1));
        assert_eq!(successor.clock(Locus::ReceivingMap(2)), 0);
        assert!(reading.released.is_empty());
        next = successor;
        counts[class] += 1;
        for (c, &count) in counts.iter().enumerate() {
            assert_eq!(
                next.class_masses(2).unwrap().probability(0, c).unwrap(),
                kt_probability(count, seen as u64 + 1, field.alphabet())
            );
        }
    }
    // `N = |A|/2 + 3 = 5` over the chain's four classes.
    assert_eq!(next.class_masses(2).unwrap().total(0).unwrap(), integer(5));
    // The prior's bits are counted with the receiving locus's: each mass `1/2` takes 1 + 2 bits.
    let prior_bits = 3 * field.alphabet() as u64;
    assert_eq!(
        ClassMasses::prior(Regions::Whole, field.alphabet()).bits(),
        prior_bits
    );
    // After `a, a, b`: 5/2, 3/2, 1/2, 1/2 take 3 + 2, 2 + 2, 1 + 2 and 1 + 2 bits.
    assert_eq!(next.class_masses(2).unwrap().bits(), 5 + 4 + 3 + 3);
    assert_eq!(
        next.exact_bits() - theta.exact_bits(),
        next.class_masses(2).unwrap().bits() - prior_bits
    );
}

/// The masses refuse what they cannot hold exactly (Decision 27: integers of half-units): a weight
/// off `½ℤ` or below zero, a region or class outside the storage; a refused deposit moves nothing,
/// a zero weight moves nothing, and a half weight moves one half-unit. The constitution refuses a
/// step on a ring that carries no masses.
#[test]
fn the_masses_refuse_what_they_cannot_hold_exactly() {
    let mut masses = ClassMasses::prior(Regions::PrecedingCell, 4);
    let before = masses.clone();
    for weight in [rat(1, 3), integer(-1), rat(-1, 2)] {
        assert!(matches!(
            masses.deposit(&MassStep {
                weight,
                ..unit(2, 1, 1)
            }),
            Err(HnnError::MassWeight { .. })
        ));
    }
    assert!(masses.deposit(&unit(2, 5, 0)).is_err());
    assert!(matches!(
        masses.deposit(&unit(2, 0, 4)),
        Err(HnnError::CellOutside { .. })
    ));
    assert_eq!(masses, before);
    masses
        .deposit(&MassStep {
            weight: Rat::zero(),
            ..unit(2, 1, 1)
        })
        .unwrap();
    assert_eq!(masses, before);
    masses
        .deposit(&MassStep {
            weight: rat(1, 2),
            ..unit(2, 1, 1)
        })
        .unwrap();
    assert_eq!(masses.half_units(1, 1).unwrap(), 2);
    assert_eq!(masses.total_half_units(1).unwrap(), 5);
    assert_eq!(masses.mass(1, 1).unwrap(), integer(1));
    let field = chain();
    let theta = Constitution::initial(&field, Steps::campaign_one(), CAMPAIGN_ONE_BUDGET).unwrap();
    let deposit =
        Deposit::new(0, Vec::new(), Vec::new(), Vec::new()).with_masses(vec![unit(1, 0, 0)]);
    assert!(theta.deposited(&deposit).is_err());
}

/// Lean `HNN/RegionCounts.{grainExponent_spec, grain_log_iff_pow_bounds, grain_face_residual}`: the
/// grain exponent is the unique `k` with `2^k ≤ (a/b)^L < 2^(k+1)`, from integer comparisons, and
/// `k/L ≤ log₂(a/b) < (k+1)/L`; at `L = 1` it is `⌊log₂(a/b)⌋`; an exact power of two reads its own
/// exponent; a zero is refused.
#[test]
fn the_grain_exponent_is_the_integer_comparison() {
    for p in [
        rat(5, 8),
        rat(3, 8),
        rat(1, 1),
        rat(1, 256),
        rat(3, 7),
        rat(255, 256),
        rat(1, 3),
        rat(9, 2),
        rat(1023, 1025),
    ] {
        for grain in [1u64, 2, 7, 16] {
            let k = grain_of(&p, grain);
            assert!(brackets(&p, grain, &k), "{p} at {grain}");
            let log = log2_enclosure(&p).unwrap();
            let grain_rat = Rat::from_integer(BigInt::from(grain));
            assert!(Rat::from_integer(k.clone()) / &grain_rat <= log.upper);
            assert!(log.lower < Rat::from_integer(&k + 1) / &grain_rat);
        }
    }
    assert_eq!(grain_of(&rat(1, 256), 16), BigInt::from(-128));
    assert_eq!(grain_of(&rat(9, 2), 1), BigInt::from(2));
    assert!(grain_exponent(&BigUint::zero(), &BigUint::one(), 16).is_err());
}

/// The partition is declared on the receiver and coded in the description (guard 13): the
/// preceding-cell region is refused on a field that retains no window (no declared offset), and a
/// change of partition changes the field's code. Campaign 1 declares the preceding cell: `|A| + 1 =
/// 257` regions over 256 classes, all at the prior.
#[test]
fn the_field_declares_the_partition_and_codes_it() {
    let mut declared = chain_declaration(1 << 20);
    declared.offsets = Vec::new();
    assert!(matches!(
        Field::declare(declared.clone()),
        Err(HnnError::RegionWindow { ring: 2 })
    ));
    declared.receivers[0].regions = Regions::Whole;
    assert!(Field::declare(declared).is_ok());
    let preceding = chain();
    let mut whole = chain_declaration(1 << 20);
    whole.receivers[0].regions = Regions::Whole;
    let whole = Field::declare(whole).unwrap();
    let steps = Steps::campaign_one();
    assert_ne!(
        preceding.describe(&steps, OPEN_BUDGET, 64),
        whole.describe(&steps, OPEN_BUDGET, 64)
    );
    let campaign = Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap();
    assert_eq!(campaign.receivers()[0].regions, Regions::PrecedingCell);
    let theta = Constitution::initial(&campaign, steps, CAMPAIGN_ONE_BUDGET).unwrap();
    let masses = theta.class_masses(2).unwrap();
    assert_eq!(masses.region_count(), 257);
    assert_eq!(masses.classes(), 256);
    assert!(theta.class_masses(0).is_none());
    // The window's region: empty, then the preceding cell's.
    assert_eq!(Regions::PrecedingCell.region(&[None], 256).unwrap(), 0);
    assert_eq!(Regions::PrecedingCell.region(&[Some(7)], 256).unwrap(), 8);
    assert_eq!(Regions::Whole.region(&[Some(7)], 256).unwrap(), 0);
    assert!(Regions::PrecedingCell.region(&[Some(256)], 256).is_err());
}
