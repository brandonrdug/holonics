//! Each terrain's truth receipt checked exactly on small fixtures: the draw's step and exact
//! uniformity, a hand-computed moiré's period, least period, determining depth, lock and key
//! description, a drawn moiré's periodicity and cycle, a two-leaf tree source's stationary law,
//! rate, passage code and weighting bound, the shift closure of Lean's unclosed tree, a drawn tree
//! source's closure and depth, the recovered tree, and the switch epochs and the dormant grating.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use super::*;
use crate::aeon::Cycle;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, Landmarks, LetterFamily, StopPrior, address,
};
use crate::hnn::contact::ContactLock;
use crate::navigator::address::LockAddress;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::surprisal::SymbolicSurprisal;
use crate::ratio::{Rat, rat};

/// The step is `⌊2^64/φ⌋`: `γ² + γ·2^64 ≤ 2^128 < (γ + 1)² + (γ + 1)·2^64` (`φ⁻¹` is the root of
/// `x² + x − 1`), and odd, so the rotation's orbit is all of `ℤ/2^64`. A draw below a power of two
/// rejects nothing, so it is the word's residue; every draw lies below its bound, and the accepted
/// words are whole turns of `ℤ/b`.
#[test]
fn the_draw_is_the_golden_rotation_and_draws_below_a_bound_exactly() {
    let gamma = BigUint::from(Draw::STEP);
    let unit = BigUint::one() << 64usize;
    let square = &unit * &unit;
    assert!(&gamma * &gamma + &gamma * &unit <= square);
    let next = &gamma + BigUint::one();
    assert!(&next * &next + &next * &unit > square);
    assert_eq!(Draw::STEP % 2, 1);
    let (mut words, mut draws) = (Draw::new(11), Draw::new(11));
    for _ in 0..64 {
        assert_eq!(draws.below(16) as u64, words.next() % 16);
    }
    let mut draw = Draw::new(5);
    for bound in 1..40usize {
        assert!(draw.below(bound) < bound);
        let b = bound as u64;
        let rejected = BigUint::from(b.wrapping_neg() % b);
        assert!(((&unit - rejected) % BigUint::from(b)).is_zero());
    }
}

fn hand_moire(class: MoireClass) -> Moire {
    Moire::new(
        vec![
            Grating::new(1, 4, 0).unwrap(),
            Grating::new(1, 3, 1).unwrap(),
        ],
        class,
    )
    .unwrap()
}

/// Two gratings, `1/4` at phase `0` and `1/3` at phase `1/3`: the sheets `0011…` and `010…`, the
/// parity color `0 1 1 1 1 0 1 0 0 0 0 1` and the sheet tuple `0 2 1 1 2 0 1 3 0 0 3 1`, each of
/// least period 12 (the joint period `lcm(4, 3)`), determined by 4 and 2 preceding cells. The pair's
/// rate ratio `3/4` is its lock at the Farey address of `3/4`, closing after 4 turns of the second
/// ring; over one joint period the rings wind `(3, 4)` times, and the contact law reads the fibre
/// `(3/5, 1)`'s least-denominator rate `2/3`, not the exact lock. The family `Q = 4` holds
/// `N_4 = 2·1 + 3·2 + 4·2 = 16` gratings, so two draw `16² = 2^8` keys: 8 bits.
#[test]
fn a_hand_computed_moire_has_its_period_locks_and_key_description() {
    let parity = hand_moire(MoireClass::Parity);
    assert_eq!(parity.emit(12), vec![0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1]);
    let sheets = hand_moire(MoireClass::Sheets);
    assert_eq!(sheets.emit(12), vec![0, 2, 1, 1, 2, 0, 1, 3, 0, 0, 3, 1]);
    assert_eq!(sheets.alphabet(), 4);
    let family = MoireFamily {
        rings: 2,
        denominator: 4,
    };
    assert_eq!(family.gratings(), 16);
    let truth = parity.truth(&family).unwrap();
    assert_eq!(truth.joint_period, BigUint::from(12u32));
    assert_eq!(truth.least_period, 12);
    assert_eq!(truth.depth, 4);
    assert_eq!(truth.rate, ExactInterval::point(Rat::zero()));
    assert_eq!(truth.key_space, BigUint::from(256u32));
    assert_eq!(truth.key_bits, 8);
    let lock = &truth.locks[0];
    assert_eq!(lock.rings, (0, 1));
    assert_eq!(lock.ratio, rat(3, 4));
    assert_eq!(
        lock.address,
        LockAddress::from_ratio(&BigInt::from(3), &BigInt::from(4)).unwrap()
    );
    assert_eq!(lock.period, BigInt::from(4));
    assert_eq!(lock.windings, (BigInt::from(3), BigInt::from(4)));
    assert_eq!(
        lock.reading,
        ContactLock::Locked {
            numerator: BigUint::from(2u32),
            denominator: BigUint::from(3u32),
        }
    );
    assert_eq!(sheets.truth(&family).unwrap().depth, 2);
    // A grating outside the family is refused.
    assert!(
        parity
            .truth(&MoireFamily {
                rings: 2,
                denominator: 3,
            })
            .is_err()
    );
    // The joint period is the torus's cycle: its forward aeon closes, a proper divisor's does not.
    let lift = parity.parametric();
    let closes = |ticks: i64| {
        let end: Vec<BigInt> = parity
            .gratings()
            .iter()
            .map(|g| BigInt::from(ticks * g.numerator() as i64))
            .collect();
        let aeon = lift.forward(vec![BigInt::zero(); 2], &end).unwrap();
        Cycle::close(&lift, aeon).is_ok()
    };
    assert!(closes(12));
    assert!(!closes(6));
    assert!(!closes(4));
}

/// A drawn moiré of three gratings, denominators up to `2^4`: its emission repeats at its joint
/// period, its least period divides it, its determining depth is at most its least period, and the
/// family's key description is `⌈log₂ 862³⌉ = 30` bits (`N_16 = 862 = 2·431`). Invalid gratings are
/// refused.
#[test]
fn a_drawn_moire_repeats_at_its_joint_period() {
    let family = MoireFamily {
        rings: 3,
        denominator: 16,
    };
    assert_eq!(family.gratings(), 862);
    let moire = Moire::draw(&family, MoireClass::Parity, &mut Draw::new(3)).unwrap();
    let truth = moire.truth(&family).unwrap();
    assert_eq!(truth.key_bits, 30);
    let period = usize::try_from(&truth.joint_period).unwrap();
    let cells = moire.emit(2 * period);
    assert_eq!(cells[..period], cells[period..]);
    assert_eq!(period % truth.least_period, 0);
    assert!(truth.depth <= truth.least_period);
    assert_eq!(truth.locks.len(), 3);
    for grating in moire.gratings() {
        assert!(grating.denominator() <= 16);
    }
    assert!(Grating::new(2, 4, 0).is_err());
    assert!(Grating::new(0, 4, 0).is_err());
    assert!(Grating::new(1, 4, 4).is_err());
}

fn two_leaf_source() -> TreeSource {
    let tree = ContextTree::new(2, vec![vec![0], vec![1]]).unwrap();
    TreeSource::new(tree, 4, vec![vec![1, 3], vec![2, 2]], vec![0]).unwrap()
}

/// The two-leaf source, `θ_[0] = (1/4, 3/4)` and `θ_[1] = (1/2, 1/2)`: its leaf chain's stationary
/// law is `(2/5, 3/5)`, its rate `2/5 (2 − ¾ log₂ 3) + 3/5 = 7/5 − (3/10) log₂ 3` exactly, enclosed
/// in `[1849/2000, 92453/100000]` (from `2^15849 < 3^10000 < 2^15850`). The passage `1 1 0` from the
/// past `0` costs `−log₂(3/4) − 2 log₂(1/2) = 4 − log₂ 3`. At a receiver of depth 3 the first cell
/// meets the boundary, the next two reach the leaf `[1]`, and the bound is
/// `Γ(S′) = 4` (the root's split, its boundary leaf and the two leaves above depth 3) plus
/// `½ log₂ 2 + 1` plus one boundary bit: `13/2`.
#[test]
fn the_two_leaf_source_has_its_exact_stationary_law_rate_and_bound() {
    let source = two_leaf_source();
    let truth = source.truth().unwrap();
    assert_eq!(truth.stationary, vec![rat(2, 5), rat(3, 5)]);
    let rate = SymbolicSurprisal::term(2, rat(7, 5))
        .unwrap()
        .plus(&SymbolicSurprisal::term(3, rat(-3, 10)).unwrap());
    assert_eq!(truth.rate, rate);
    assert!(truth.rate_bits.lower >= rat(1849, 2000));
    assert!(truth.rate_bits.upper <= rat(92453, 100000));
    let passage = source.passage(&[1, 1, 0]).unwrap();
    assert_eq!(passage.counts, vec![vec![0, 1], vec![1, 1]]);
    let code = SymbolicSurprisal::term(2, rat(4, 1))
        .unwrap()
        .plus(&SymbolicSurprisal::term(3, rat(-1, 1)).unwrap());
    assert_eq!(passage.code, code);
    let bound = source.weighting_bound(&[1, 1, 0], 3).unwrap();
    assert_eq!(bound.model, 4);
    assert_eq!(bound.visits, vec![0, 2]);
    assert_eq!(bound.boundary, 1);
    assert_eq!(bound.parameters, ExactInterval::point(rat(3, 2)));
    assert_eq!(bound.total, ExactInterval::point(rat(13, 2)));
    assert_eq!(source.tree().cost(1).unwrap(), 1);
    assert!(source.tree().cost(0).is_err());
}

/// Lean `Compression/Landmark/Context/Standing.unclosed_leaf_is_not_a_standing`: the depth-three
/// tree that stops at `[1]` and `[0, 0]` and splits `[0, 1]` is not closed under the shift (the
/// addresses `1 1 0` and `1 0 0` reach `[1]`, their shifts by `0` two leaves), so no source is
/// declared over it; its closure splits `[1]`, and the closed tree's leaf chain is stochastic.
#[test]
fn the_unclosed_tree_is_refused_and_its_closure_splits_the_short_leaf() {
    let leaves = vec![vec![1], vec![0, 0], vec![0, 1, 0], vec![0, 1, 1]];
    let mut tree = ContextTree::new(2, leaves).unwrap();
    assert!(!tree.is_shift_closed());
    assert!(TreeSource::new(tree.clone(), 2, vec![vec![1, 1]; 4], vec![0, 0, 0]).is_err());
    tree.close();
    assert!(tree.is_shift_closed());
    assert_eq!(
        tree.leaves(),
        vec![vec![0, 0], vec![0, 1, 0], vec![0, 1, 1], vec![1, 0], vec![1, 1]]
    );
    let source = TreeSource::new(tree, 2, vec![vec![1, 1]; 5], vec![0, 0, 0]).unwrap();
    let stationary = source.truth().unwrap().stationary;
    assert_eq!(stationary.iter().sum::<Rat>(), Rat::one());
    // A declaration whose leaves miss an address, or nest, is refused.
    assert!(ContextTree::new(2, vec![vec![0]]).is_err());
    assert!(ContextTree::new(2, vec![vec![0], vec![1], vec![0, 1]]).is_err());
}

/// A drawn tree source of depth 4 over bits: shift-closed, reaching depth 4, with a positive
/// stationary law of total mass one and a rate between 0 and 1 bit; its emission is the seeded
/// draw's, and its passage counts every cell once.
#[test]
fn a_drawn_tree_source_is_closed_full_depth_and_its_truth_is_a_law() {
    let family = TreeSourceFamily {
        alphabet: 2,
        depth: 4,
        grid: 16,
    };
    let source = TreeSource::draw(&family, &mut Draw::new(17)).unwrap();
    assert!(source.tree().is_shift_closed());
    assert_eq!(source.tree().depth(), 4);
    let truth = source.truth().unwrap();
    assert_eq!(truth.stationary.iter().sum::<Rat>(), Rat::one());
    assert!(truth.stationary.iter().all(|weight| *weight > Rat::zero()));
    assert!(truth.rate_bits.lower >= Rat::zero() && truth.rate_bits.upper <= Rat::one());
    let cells = source.emit(1 << 10, &mut Draw::new(19));
    assert_eq!(cells, source.emit(1 << 10, &mut Draw::new(19)));
    let passage = source.passage(&cells).unwrap();
    assert_eq!(passage.counts.iter().flatten().sum::<u64>(), 1 << 10);
}

/// A `½` tree of depth 3 with a passage deposited.
fn standing_of(cells: &[usize]) -> Landmarks {
    let declaration = LandmarkDeclaration {
        alphabet: 2,
        depth: 3,
        forced: 0,
        population: cells.len() as u64,
        grain: 16,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
        mass: 1,
        base: crate::compression::landmark::context::BaseMeasure::Even,
    };
    let mut standing = Landmarks::new(declaration).unwrap();
    for (position, &cell) in cells.iter().enumerate() {
        standing
            .deposit(&address(cells, position, 3), cell)
            .unwrap();
    }
    standing
}

/// The two-leaf source's passage of `2^11` cells, deposited in a `½` tree of depth 3: the
/// standing's posterior stop weight splits the root and stops at `[0]` and `[1]`, the drawn tree.
/// A passage of the source whose two leaves share one face (a memoryless source) is recovered as
/// the root alone, so the reading is the standing's, not the drawn tree's: the root is that
/// source's minimal tree, recovered exactly.
#[test]
fn the_two_leaf_source_is_recovered_from_its_passage() {
    let source = two_leaf_source();
    let recovery = source
        .recovery(&standing_of(&source.emit(1 << 11, &mut Draw::new(23))))
        .unwrap();
    assert_eq!(recovery.addresses, 8);
    assert_eq!(recovery.unvisited, 0);
    assert_eq!(recovery.recovered, vec![vec![0], vec![1]]);
    assert_eq!(recovery.agree, 8);
    assert!(recovery.exact);
    let tree = ContextTree::new(2, vec![vec![0], vec![1]]).unwrap();
    let memoryless = TreeSource::new(tree, 4, vec![vec![1, 3], vec![1, 3]], vec![0]).unwrap();
    let recovery = source
        .recovery(&standing_of(&memoryless.emit(1 << 11, &mut Draw::new(23))))
        .unwrap();
    assert_eq!(recovery.recovered, vec![Vec::<usize>::new()]);
    assert_eq!(recovery.agree, 0);
    assert!(!recovery.exact);
    // Its minimal tree is the root, which the standing recovers exactly.
    assert_eq!(memoryless.minimal(), vec![Vec::<usize>::new()]);
    assert_eq!(source.minimal(), vec![vec![0], vec![1]]);
    let recovery = memoryless
        .recovery(&standing_of(&memoryless.emit(1 << 11, &mut Draw::new(23))))
        .unwrap();
    assert_eq!(recovery.agree_minimal, 8);
    assert!(recovery.exact_minimal && !recovery.exact);
}

/// The switch epochs are the aeon owner's: lengths `3, 2, 4` over nine cells switch at cells 3
/// and 5, so the cells' epochs are `0 0 0 1 1 2 2 2 2`, the sources alternate on their parity and
/// the flux is the two switches. A dormant grating is silent exactly in the odd aeons and returns
/// at its continued phase.
#[test]
fn the_switch_epochs_are_the_aeon_owners_and_a_dormant_grating_returns_at_its_phase() {
    let first: Vec<usize> = (0..9).collect();
    let second: Vec<usize> = (100..109).collect();
    let switching = Switching::new([&first, &second], vec![3, 2, 4, 5]).unwrap();
    assert_eq!(switching.cells, vec![0, 1, 2, 103, 104, 5, 6, 7, 8]);
    assert_eq!(switching.truth.switches, vec![3, 5]);
    assert_eq!(switching.truth.lengths, vec![3, 2, 4]);
    let epochs: Vec<usize> = (0..9)
        .map(|t| switching.truth.epochs.epoch_of(t).unwrap())
        .collect();
    assert_eq!(epochs, vec![0, 0, 0, 1, 1, 2, 2, 2, 2]);
    assert_eq!(switching.truth.epochs.flux(), BigInt::from(2));
    assert!(Switching::new([&first, &second], vec![3, 2]).is_err());

    let moire = hand_moire(MoireClass::Parity);
    let family = AeonFamily {
        shortest: 3,
        longest: 5,
    };
    let dormant = Switching::dormant(&moire, 1, 48, &family, &mut Draw::new(29)).unwrap();
    assert_eq!(dormant.truth.dormant, Some(1));
    let every = moire.emit(48);
    let alone = moire.emit_active(48, &[true, false]);
    assert!(dormant.truth.switches.len() >= 9);
    for (t, cell) in dormant.cells.iter().enumerate() {
        match dormant.truth.source(t).unwrap() {
            0 => assert_eq!(*cell, every[t]),
            _ => assert_eq!(*cell, alone[t]),
        }
    }
    assert!(
        dormant
            .truth
            .lengths
            .iter()
            .all(|length| (3..=5).contains(length))
    );
}
