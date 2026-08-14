//! Whether the three-site turning equation's solution **closes**, decided by
//! integer alternation on a circle.
//!
//! # The object
//!
//! A second-order transport law on the plane, well behaved everywhere except at
//! **three sites** — `0`, `1`, and infinity. Three is the smallest interesting
//! number of sites, because two can always be rescaled to one configuration.
//! The classical name is the *hypergeometric equation*; it carries three dials
//! `a`, `b`, `c`.
//!
//! At each site, a solution carried once around in a small loop comes back
//! **turned**. That amount is the site's **local turn number** (classically the
//! *exponent difference*), and the three are read straight off the dials:
//!
//! ```text
//! λ = 1 − c        at 0
//! μ = c − a − b    at 1
//! ν = a − b        at infinity
//! ```
//!
//! # The question: does the solution close?
//!
//! Carry a solution around a site and back and you do not recover it — you
//! recover a **combination** of the two independent solutions. Each loop is
//! therefore a transformation, and composing loops generates the **return
//! group** (classically the *monodromy group*).
//!
//! **If the return group is finite the solution takes finitely many values and
//! closes — it is algebraic. If the group is infinite it never closes**, and no
//! finite expression in roots carries it. This is the same shape as every other
//! entry in this atlas: the group decides what is enumerable, a finite group
//! gives a table, and an infinite one gives no table.
//!
//! # What decides it: the alternation test
//!
//! Put the dials on a circle. Each rational `p/h` is a mark at that fraction of
//! the way round. Two families of marks appear:
//!
//! - the **numerator family** — the marks for `a` and `b`
//! - the **denominator family** — the marks for `c` and for `1`, which sits at
//!   position zero
//!
//! **The return group is finite exactly when the two families take turns around
//! the circle** — numerator, denominator, numerator, denominator — with no two
//! of one kind adjacent. That is the alternation test (classically the
//! *Beukers–Heckman interlacing criterion*, Invent. Math. 95, 1989).
//!
//! And one further requirement, which is the interesting half: the marks must
//! alternate under **every restretching of the circle** — multiply every mark's
//! position by any whole number sharing no factor with the common denominator,
//! and look again. Survive every restretching and the group is finite; fail one
//! and it is infinite. (Those restretchings are the Galois conjugates, indexed
//! by the units mod `h`; the mechanism is entirely "spin the marks by a coprime
//! multiple and check again.")
//!
//! # Why nothing is extracted
//!
//! Over a common denominator `h` every mark is an **integer in `[0, h)`**.
//! Alternation is then sorting integers and checking labels take turns;
//! restretching is multiplication mod `h`. **No root is extracted, no angle is
//! taken, no matrix is built, and no float appears.**
//!
//! # The third outcome, which is not a failure of the test
//!
//! If a numerator mark **lands on** a denominator mark, the equation splits into
//! simpler pieces and the criterion does not apply to it at all. That is neither
//! "closes" nor "does not close" — it is outside the test's aperture, and it is
//! returned by name rather than folded into either verdict.
//!
//! # The declared aperture
//!
//! Rational dials only, which the exact carrier enforces by construction, and
//! second order only — two numerator marks against two denominator marks. The
//! alternation machinery below is written for `n` against `n` so the order can
//! rise later, but nothing here drives it above two.
//!
//! **The classical fifteen-row table of closing turn numbers (Schwarz's list) is
//! a CONTROL in this module and never a decider.** A table consulted to classify
//! its own rows returns the preimage of an authored field and carries no
//! evidence. The alternation test computes; the rows check it.

use std::collections::BTreeMap;

use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use num_bigint::BigInt;

/// The three dials of the three-site turning equation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ThreeSiteDials {
    pub a: Rat,
    pub b: Rat,
    pub c: Rat,
}

/// How much a solution turns per loop at each of the three sites.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalTurns {
    pub at_zero: Rat,
    pub at_one: Rat,
    pub at_infinity: Rat,
}

impl ThreeSiteDials {
    pub fn new(a: Rat, b: Rat, c: Rat) -> Self {
        Self { a, b, c }
    }

    /// `λ = 1 − c`, `μ = c − a − b`, `ν = a − b`.
    pub fn local_turns(&self) -> LocalTurns {
        LocalTurns {
            at_zero: Rat::one() - &self.c,
            at_one: &self.c - &self.a - &self.b,
            at_infinity: &self.a - &self.b,
        }
    }
}

impl LocalTurns {
    pub fn new(at_zero: Rat, at_one: Rat, at_infinity: Rat) -> Self {
        Self {
            at_zero,
            at_one,
            at_infinity,
        }
    }

    /// Invert the reading above: `c = 1 − λ`, `a + b = 1 − λ − μ`, `a − b = ν`.
    /// The three forks, read off the signs the magnitude face deletes.
    pub fn branch_word(&self) -> BranchWord {
        let hand = |turn: &Rat| {
            if turn.is_zero() {
                BranchHand::Unforked
            } else if turn.is_negative() {
                BranchHand::Reversed
            } else {
                BranchHand::Forward
            }
        };
        BranchWord {
            at_zero: hand(&self.at_zero),
            at_one: hand(&self.at_one),
            at_infinity: hand(&self.at_infinity),
        }
    }

    pub fn dials(&self) -> ThreeSiteDials {
        let c = Rat::one() - &self.at_zero;
        let sum = Rat::one() - &self.at_zero - &self.at_one;
        let two = Rat::from_integer(BigInt::from(2));
        let a = (&sum + &self.at_infinity) / &two;
        let b = (&sum - &self.at_infinity) / &two;
        ThreeSiteDials { a, b, c }
    }

    /// `1/p + 1/q + 1/r` against `1`, read off the turn numbers as the sum
    /// itself rather than through reciprocals, so no inversion is needed and a
    /// zero turn is not a division by zero.
    ///
    /// The three-way split is the classical one: a sum **above** one is the
    /// sphere and the only place a finite return group can live; equal to one is
    /// the flat plane; below one is the saddle. **Both of the latter are
    /// infinite.** The icosahedral row `(1/2, 1/3, 1/5)` sums to `31/30`, which
    /// is the whole margin the sphere has.
    ///
    /// **This is the MAGNITUDE FACE, and the orientation it quotients by is
    /// returned beside it rather than deleted.** See `branch_word`.
    ///
    /// The sum is taken on absolute turn numbers. That is not a correctness
    /// repair and calling it one was the assistant's error, corrected by
    /// Brandon 2026-08-14: *the asymmetry is time parity, the arrow of causal
    /// trajectory in which discrete events branch.* At each site the solution
    /// branches into TWO continuations, and the turn number is the difference of
    /// their two exponents — so its sign records **which continuation was taken
    /// first**. Three sites, three forks, `2³` orientation words.
    ///
    /// Taking the absolute value is therefore a **quotient by that fork group**,
    /// exactly the deletion `|·|` always performs. It is lawful as a face; it is
    /// not lawful as a repair, and the fiber must be exhibited.
    pub fn curvature_sign(&self) -> CurvatureSign {
        let total = self.at_zero.abs() + self.at_one.abs() + self.at_infinity.abs();
        match total.cmp(&Rat::one()) {
            std::cmp::Ordering::Greater => CurvatureSign::Spherical,
            std::cmp::Ordering::Equal => CurvatureSign::Flat,
            std::cmp::Ordering::Less => CurvatureSign::Saddle,
        }
    }
}

/// Which continuation was taken first at a site: the site's fork, retained.
///
/// A turn number is the difference of the site's two exponents, so its sign is
/// not noise to normalise away — it is **which of the two branches the reading
/// walked first**, the arrow of causal trajectory at that fork.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum BranchHand {
    Forward,
    Reversed,
    /// The two exponents coincide, so the site has no fork to orient.
    Unforked,
}

/// The three forks as one word — the phase the magnitude face quotients away.
///
/// **Exchanging the two symmetric dials flips exactly one letter**, the one at
/// infinity, because that site's two exponents ARE those two dials. So the
/// exchange is not a relabelling to be normalised out: it is a choice of branch
/// order at one fork, and it is invisible to the magnitude face and visible
/// here. That is the phase-object theorem on this material — a change with zero
/// remainder to one receiver and a real movement to another.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BranchWord {
    pub at_zero: BranchHand,
    pub at_one: BranchHand,
    pub at_infinity: BranchHand,
}

/// Which of the three geometries the turn numbers sit in.
///
/// Stated on the turn numbers directly: `λ + μ + ν > 1` is the sphere. Written
/// with reciprocal orders `1/p + 1/q + 1/r > 1` it is the same condition, and
/// the flat row is **exactly** the set of rotation orders a lattice admits,
/// which `winding_inertia::lattice_admits_order` already derives on rational
/// grounds. `(2,3,5)` is spherical and not lattice-admissible, which is the
/// whole reason five separates the two cuts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CurvatureSign {
    Spherical,
    Flat,
    Saddle,
}

/// Two marks of the same family sitting next to each other on the circle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AdjacentPair {
    pub family: MarkFamily,
    pub first: u64,
    pub second: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum MarkFamily {
    Numerator,
    Denominator,
}

/// What the alternation test returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ClosureReading {
    /// Every restretching alternated: the return group is finite and the
    /// solution closes.
    Closes {
        circle: u64,
        restretchings_checked: usize,
    },
    /// A restretching put two marks of one family next to each other. The
    /// group is infinite and the solution never closes.
    DoesNotClose {
        circle: u64,
        /// The multiplier whose spin broke the alternation. `1` means the marks
        /// failed as drawn, without needing any restretching at all.
        failing_restretching: u64,
        /// The two marks that ended up adjacent — the exhibited obstruction,
        /// not a verdict.
        adjacency: AdjacentPair,
        restretchings_checked: usize,
    },
    /// A numerator mark landed on a denominator mark, so the equation splits
    /// and the criterion does not apply. Outside the aperture, by name.
    Splits { coincident_mark: u64, circle: u64 },
}

impl ClosureReading {
    pub fn closes(&self) -> bool {
        matches!(self, Self::Closes { .. })
    }

    pub fn circle(&self) -> u64 {
        match self {
            Self::Closes { circle, .. }
            | Self::DoesNotClose { circle, .. }
            | Self::Splits { circle, .. } => *circle,
        }
    }
}

/// The full reading, with the turn numbers and the geometry beside the verdict.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReturnGroupReading {
    pub schema: String,
    pub dials: ThreeSiteDials,
    pub turns: LocalTurns,
    pub curvature: CurvatureSign,
    /// The fork orientation the curvature face quotients by, retained.
    pub branch_word: BranchWord,
    /// Marks in `[0, circle)`, as drawn before any restretching.
    pub numerator_marks: Vec<u64>,
    pub denominator_marks: Vec<u64>,
    pub closure: ClosureReading,
}

/// Decide whether the solution closes, by alternation under every restretching.
pub fn read_return_group(dials: &ThreeSiteDials) -> Result<ReturnGroupReading, ClosureError> {
    // The denominator family is `{1, c}`; `1` sits at position zero on the
    // circle because a whole turn is no turn.
    let numerator = [dials.a.clone(), dials.b.clone()];
    let denominator = [Rat::zero(), dials.c.clone()];

    let circle = common_circle(numerator.iter().chain(denominator.iter()))?;
    let numerator_marks = marks_on(&numerator, circle)?;
    let denominator_marks = marks_on(&denominator, circle)?;

    let turns = dials.local_turns();
    let curvature = turns.curvature_sign();
    let branch_word = turns.branch_word();

    let closure = decide_closure(&numerator_marks, &denominator_marks, circle)?;

    Ok(ReturnGroupReading {
        schema: SCHEMA.to_owned(),
        dials: dials.clone(),
        turns,
        curvature,
        branch_word,
        numerator_marks,
        denominator_marks,
        closure,
    })
}

/// The same reading, entered by the three local turn numbers.
pub fn read_from_turns(turns: &LocalTurns) -> Result<ReturnGroupReading, ClosureError> {
    read_return_group(&turns.dials())
}

fn decide_closure(
    numerator: &[u64],
    denominator: &[u64],
    circle: u64,
) -> Result<ClosureReading, ClosureError> {
    // A shared mark means the equation splits; the criterion does not apply.
    for mark in numerator {
        if denominator.contains(mark) {
            return Ok(ClosureReading::Splits {
                coincident_mark: *mark,
                circle,
            });
        }
    }

    let mut checked = 0_usize;
    for multiplier in 1..circle.max(2) {
        if gcd(multiplier, circle) != 1 {
            continue;
        }
        checked += 1;
        let spun_numerator: Vec<u64> = numerator
            .iter()
            .map(|mark| (mark * multiplier) % circle)
            .collect();
        let spun_denominator: Vec<u64> = denominator
            .iter()
            .map(|mark| (mark * multiplier) % circle)
            .collect();
        if let Some(adjacency) = same_family_adjacency(&spun_numerator, &spun_denominator) {
            return Ok(ClosureReading::DoesNotClose {
                circle,
                failing_restretching: multiplier,
                adjacency,
                restretchings_checked: checked,
            });
        }
    }
    if checked == 0 {
        return Err(ClosureError::EmptyRestretchingFamily { circle });
    }
    Ok(ClosureReading::Closes {
        circle,
        restretchings_checked: checked,
    })
}

/// Walk the circle once and return the first two marks of one family that sit
/// next to each other, or `None` when the families take turns the whole way.
///
/// The walk is cyclic: the last mark's neighbour is the first. A repeat within
/// one family lands as an adjacency, which is the correct reading — two marks
/// at one position are certainly not separated by a mark of the other family.
fn same_family_adjacency(numerator: &[u64], denominator: &[u64]) -> Option<AdjacentPair> {
    let mut circle_walk: Vec<(u64, MarkFamily)> = numerator
        .iter()
        .map(|mark| (*mark, MarkFamily::Numerator))
        .chain(
            denominator
                .iter()
                .map(|mark| (*mark, MarkFamily::Denominator)),
        )
        .collect();
    // Sort by position; on a tie the family ordering is irrelevant because a
    // tie between families was already refused as a split, and a tie within one
    // family is the adjacency being looked for either way.
    circle_walk.sort_by_key(|(mark, family)| (*mark, *family));
    let extent = circle_walk.len();
    for index in 0..extent {
        let (first, family) = circle_walk[index];
        let (second, next_family) = circle_walk[(index + 1) % extent];
        if family == next_family {
            return Some(AdjacentPair {
                family,
                first,
                second,
            });
        }
    }
    None
}

/// The smallest circle every mark lands on exactly: the least common multiple
/// of the denominators, taken after reducing each dial modulo one whole turn.
fn common_circle<'a>(values: impl Iterator<Item = &'a Rat>) -> Result<u64, ClosureError> {
    let mut circle = 1_u64;
    for value in values {
        let reduced = fractional_turn(value);
        let denominator = u64::try_from(reduced.denom().clone())
            .map_err(|_| ClosureError::CircleTooLarge)?;
        circle = lcm(circle, denominator)?;
    }
    Ok(circle)
}

fn marks_on(values: &[Rat], circle: u64) -> Result<Vec<u64>, ClosureError> {
    values
        .iter()
        .map(|value| {
            let reduced = fractional_turn(value);
            let numerator =
                u64::try_from(reduced.numer().clone()).map_err(|_| ClosureError::CircleTooLarge)?;
            let denominator = u64::try_from(reduced.denom().clone())
                .map_err(|_| ClosureError::CircleTooLarge)?;
            Ok(numerator * (circle / denominator))
        })
        .collect()
}

/// A dial modulo one whole turn, landed in `[0, 1)`. A whole turn is no turn,
/// which is why the denominator family's `1` sits at position zero.
fn fractional_turn(value: &Rat) -> Rat {
    let mut reduced = value.clone();
    let one = Rat::one();
    while reduced.is_negative() {
        reduced += &one;
    }
    while reduced >= one {
        reduced -= &one;
    }
    reduced
}

fn gcd(mut left: u64, mut right: u64) -> u64 {
    while right != 0 {
        let carried = left % right;
        left = right;
        right = carried;
    }
    left
}

fn lcm(left: u64, right: u64) -> Result<u64, ClosureError> {
    let divisor = gcd(left, right);
    if divisor == 0 {
        return Ok(0);
    }
    (left / divisor)
        .checked_mul(right)
        .ok_or(ClosureError::CircleTooLarge)
}

/// The classical closing turn numbers, as a CONTROL on the computed test.
///
/// Fifteen rows (classically *Schwarz's list*, 1873), one per finite rotation
/// group of the sphere: the two-sided family, then the tetrahedron, octahedron,
/// and icosahedron. Keyed by row number so each is addressable, and **carrying
/// the solid it belongs to**, because that is the mechanism the row is an
/// instance of rather than a label on it.
///
/// **Nothing in this module consults this table to decide anything.** It exists
/// so the computed alternation test can be checked against fifteen independently
/// known answers. A table used as the decider would return the preimage of its
/// own declaration.
pub fn closing_turn_table() -> BTreeMap<u32, (LocalTurns, Solid)> {
    let row = |p: i64, q: i64, r: i64, s: i64, t: i64, u: i64| {
        LocalTurns::new(rational(p, q), rational(r, s), rational(t, u))
    };
    BTreeMap::from([
        // Row one is a family rather than a point: the third turn is free.
        (1, (row(1, 2, 1, 2, 1, 3), Solid::TwoSided)),
        (2, (row(1, 2, 1, 3, 1, 3), Solid::Tetrahedron)),
        (3, (row(2, 3, 1, 3, 1, 3), Solid::Tetrahedron)),
        (4, (row(1, 2, 1, 3, 1, 4), Solid::Octahedron)),
        (5, (row(2, 3, 1, 4, 1, 4), Solid::Octahedron)),
        (6, (row(1, 2, 1, 3, 1, 5), Solid::Icosahedron)),
        (7, (row(2, 5, 1, 3, 1, 3), Solid::Icosahedron)),
        (8, (row(2, 3, 1, 5, 1, 5), Solid::Icosahedron)),
        (9, (row(1, 2, 2, 5, 1, 5), Solid::Icosahedron)),
        (10, (row(3, 5, 1, 3, 1, 5), Solid::Icosahedron)),
        (11, (row(2, 5, 2, 5, 2, 5), Solid::Icosahedron)),
        (12, (row(2, 3, 1, 3, 1, 5), Solid::Icosahedron)),
        (13, (row(4, 5, 1, 5, 1, 5), Solid::Icosahedron)),
        (14, (row(1, 2, 2, 5, 1, 3), Solid::Icosahedron)),
        (15, (row(3, 5, 2, 5, 1, 3), Solid::Icosahedron)),
    ])
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Solid {
    TwoSided,
    Tetrahedron,
    Octahedron,
    Icosahedron,
}

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

const SCHEMA: &str = "holonic-engine.hypergeometric-closure.v1";

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ClosureError {
    #[error("a dial's denominator exceeds the circle this carrier can address")]
    CircleTooLarge,
    #[error(
        "a circle of {circle} admits no restretching to check, so alternation was never put \
         under a second frame"
    )]
    EmptyRestretchingFamily { circle: u64 },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn turns(p: i64, q: i64, r: i64, s: i64, t: i64, u: i64) -> LocalTurns {
        LocalTurns::new(rational(p, q), rational(r, s), rational(t, u))
    }

    #[test]
    fn the_dials_and_the_turn_numbers_are_the_same_reading_from_two_sides() {
        let dials = ThreeSiteDials::new(rational(11, 60), rational(-1, 60), rational(1, 2));
        let recovered = dials.local_turns().dials();
        assert_eq!(recovered, dials);
    }

    /// Every classically known closing row must compute as closing, by the
    /// alternation test alone. The table is not consulted by the test.
    #[test]
    fn every_row_of_the_classical_table_computes_as_closing() {
        for (row, (turns, solid)) in closing_turn_table() {
            let reading = read_from_turns(&turns).expect("the row is inside the aperture");
            assert!(
                reading.closure.closes(),
                "row {row} ({solid:?}) is classically finite and the alternation test refused it: \
                 {:?}",
                reading.closure
            );
            assert_eq!(
                reading.curvature,
                CurvatureSign::Spherical,
                "row {row} is finite so its turn numbers must sum above one"
            );
        }
    }

    /// The elliptic case, whose value a mean iteration computes and which is
    /// famously not algebraic. Its turn numbers are all zero.
    #[test]
    fn the_elliptic_case_does_not_close_and_it_is_the_negative_control() {
        let reading = read_from_turns(&turns(0, 1, 0, 1, 0, 1)).expect("inside the aperture");
        assert_eq!(reading.dials.a, rational(1, 2));
        assert_eq!(reading.dials.b, rational(1, 2));
        assert_eq!(reading.dials.c, rational(1, 1));
        assert!(!reading.closure.closes());
        assert_eq!(reading.curvature, CurvatureSign::Saddle);
    }

    /// The flat row: turn numbers summing to exactly one. Infinite, and it is
    /// the row that coincides with the rotation orders a lattice admits.
    /// **The phase-object theorem, on this material.** Exchanging the two
    /// symmetric dials is a choice of branch order at the site at infinity. It
    /// is INVISIBLE to the magnitude face — same geometry, same closure — and
    /// VISIBLE in the fork word, where exactly one letter flips.
    ///
    /// A reading that only checked the face would call the exchange a nothing.
    /// A reading that only checked the word would call it a total change. Both
    /// are true of their own receiver, and the module returns both.
    #[test]
    fn exchanging_the_two_symmetric_dials_is_invisible_to_the_face_and_visible_in_the_word() {
        let forward = ThreeSiteDials::new(rational(11, 60), rational(-1, 60), rational(1, 2));
        let exchanged = ThreeSiteDials::new(rational(-1, 60), rational(11, 60), rational(1, 2));
        let first = read_return_group(&forward).expect("inside the aperture");
        let second = read_return_group(&exchanged).expect("inside the aperture");

        // The face does not move.
        assert_eq!(first.curvature, second.curvature);
        assert_eq!(first.closure.closes(), second.closure.closes());

        // The phase does, and at exactly one of the three forks.
        assert_ne!(first.branch_word, second.branch_word);
        assert_eq!(first.branch_word.at_zero, second.branch_word.at_zero);
        assert_eq!(first.branch_word.at_one, second.branch_word.at_one);
        assert_ne!(
            first.branch_word.at_infinity, second.branch_word.at_infinity,
            "the exchange must flip the fork at infinity, because that site's two exponents ARE \
             the two dials being exchanged"
        );
    }

    /// The fork word is not constant across the material, or it would be a
    /// field carrying nothing.
    #[test]
    fn the_fork_word_takes_several_values_on_the_declared_material() {
        let mut words = std::collections::BTreeSet::new();
        for (_, (turn_numbers, _)) in closing_turn_table() {
            words.insert(turn_numbers.branch_word());
        }
        for triple in [
            turns(0, 1, 0, 1, 0, 1),
            turns(1, 4, 1, 4, 1, 4),
            turns(1, 2, -1, 3, 1, 5),
            turns(1, 2, 1, 3, -1, 5),
        ] {
            words.insert(triple.branch_word());
        }
        assert!(
            words.len() >= 3,
            "the fork word took only {} values, so it is not distinguishing anything",
            words.len()
        );
    }

    /// **The flat locus IS the splitting locus, and this was found by a driver
    /// refuting.** `λ + μ + ν = 1 − 2b` identically, so a flat sum forces `b`
    /// (or `a`, when the turn at infinity runs the other way) to zero — and a
    /// dial at zero lands on the denominator family's mark at zero, which is
    /// exactly the coincidence that splits the equation.
    ///
    /// So a flat triple is never merely "infinite": it is outside the
    /// criterion altogether, and reporting it as a refusal would be reporting
    /// the wrong species.
    #[test]
    fn every_flat_triple_splits_rather_than_merely_failing_to_close() {
        let flat = [
            turns(1, 3, 1, 3, 1, 3),
            turns(1, 2, 1, 3, 1, 6),
            turns(1, 2, 1, 4, 1, 4),
            turns(1, 4, 1, 4, 1, 2),
            turns(1, 6, 1, 3, 1, 2),
        ];
        for triple in flat {
            let reading = read_from_turns(&triple).expect("inside the aperture");
            assert_eq!(
                reading.curvature,
                CurvatureSign::Flat,
                "fixture {triple:?} is not flat"
            );
            assert!(
                matches!(reading.closure, ClosureReading::Splits { .. }),
                "a flat triple returned {:?} rather than splitting",
                reading.closure
            );
        }
    }

    /// The identity behind it: the signed turn sum is `1 − 2b`, exactly.
    #[test]
    fn the_signed_turn_sum_is_one_minus_twice_the_second_dial() {
        for (numerator, denominator) in [(11, 60), (3, 8), (-1, 12), (7, 5)] {
            let dials = ThreeSiteDials::new(
                rational(1, 3),
                rational(numerator, denominator),
                rational(1, 2),
            );
            let turns = dials.local_turns();
            let sum = &turns.at_zero + &turns.at_one + &turns.at_infinity;
            let expected =
                Rat::one() - Rat::from_integer(BigInt::from(2)) * rational(numerator, denominator);
            assert_eq!(sum, expected);
        }
    }

    /// A saddle triple. Infinite, and the obstruction is exhibited rather than
    /// asserted: two numerator marks land next to each other.
    #[test]
    fn a_saddle_triple_does_not_close_and_names_the_adjacent_pair() {
        let reading = read_from_turns(&turns(1, 4, 1, 4, 1, 4)).expect("inside the aperture");
        assert_eq!(reading.curvature, CurvatureSign::Saddle);
        let ClosureReading::DoesNotClose {
            circle,
            failing_restretching,
            adjacency,
            ..
        } = &reading.closure
        else {
            panic!("the saddle triple must not close");
        };
        assert_eq!(*circle, 8);
        assert_eq!(*failing_restretching, 1, "it fails as drawn, unspun");
        assert_eq!(adjacency.family, MarkFamily::Numerator);
        assert_eq!((adjacency.first, adjacency.second), (1, 3));
    }

    /// The half of the criterion that is easy to lose: a triple whose marks
    /// alternate AS DRAWN and stop alternating once the circle is restretched.
    ///
    /// Without such material the restretching loop could be deleted and every
    /// test would still pass, which would make the second frame decorative.
    #[test]
    fn some_material_alternates_as_drawn_and_fails_only_under_a_restretching() {
        let mut found = None;
        // Sweep a bounded family of dials and look for one that survives the
        // drawn check and dies under a spin. The sweep is the search; the
        // assertion is that such material EXISTS in this family at all.
        for numerator in 1..30_i64 {
            for denominator in 1..30_i64 {
                let dials = ThreeSiteDials::new(
                    rational(numerator, 30),
                    rational(denominator, 30),
                    rational(1, 2),
                );
                let Ok(reading) = read_return_group(&dials) else {
                    continue;
                };
                if let ClosureReading::DoesNotClose {
                    failing_restretching,
                    ..
                } = &reading.closure
                {
                    if *failing_restretching > 1 {
                        found = Some((dials, *failing_restretching));
                        break;
                    }
                }
            }
            if found.is_some() {
                break;
            }
        }
        let (dials, multiplier) = found.expect(
            "no material in this family alternated as drawn and failed under a restretching, so \
             the restretching loop is not being exercised and its agreement proves nothing",
        );
        // And confirm directly that the drawn arrangement really did alternate.
        let reading = read_return_group(&dials).expect("inside the aperture");
        assert!(
            same_family_adjacency(&reading.numerator_marks, &reading.denominator_marks).is_none(),
            "the fixture did not alternate as drawn, so it does not exhibit what this test claims"
        );
        assert!(multiplier > 1);
    }

    #[test]
    fn a_shared_mark_splits_the_equation_and_is_refused_by_name() {
        // b = 0 lands on the denominator family's mark at zero.
        let dials = ThreeSiteDials::new(rational(1, 3), rational(0, 1), rational(2, 3));
        let reading = read_return_group(&dials).expect("inside the aperture");
        assert!(matches!(
            reading.closure,
            ClosureReading::Splits {
                coincident_mark: 0,
                ..
            }
        ));
        assert!(!reading.closure.closes());
    }

    /// The verdicts must be reachable in all three species on real material, or
    /// the reading is a two-valued test wearing a third arm.
    #[test]
    fn all_three_verdicts_occur_on_the_declared_material() {
        let mut closes = 0;
        let mut refuses = 0;
        let mut splits = 0;
        for (_, (turns, _)) in closing_turn_table() {
            if read_from_turns(&turns).expect("inside").closure.closes() {
                closes += 1;
            }
        }
        for triple in [
            turns(0, 1, 0, 1, 0, 1),
            turns(1, 4, 1, 4, 1, 4),
            turns(1, 7, 1, 7, 1, 7),
        ] {
            if matches!(
                read_from_turns(&triple).expect("inside").closure,
                ClosureReading::DoesNotClose { .. }
            ) {
                refuses += 1;
            }
        }
        let split = read_return_group(&turns(1, 3, 1, 3, 1, 3).dials()).expect("inside");
        if matches!(split.closure, ClosureReading::Splits { .. }) {
            splits += 1;
        }
        assert_eq!(closes, 15);
        assert_eq!(refuses, 3);
        assert_eq!(splits, 1);
    }

    /// The spherical/flat/saddle split is read off the turn numbers, and the
    /// flat row is the one that meets standing terrain.
    #[test]
    fn only_spherical_turn_numbers_can_close() {
        for triple in [
            turns(1, 4, 1, 4, 1, 4),
            turns(0, 1, 0, 1, 0, 1),
            turns(1, 7, 1, 7, 1, 7),
            turns(1, 8, 1, 8, 1, 8),
        ] {
            let reading = read_from_turns(&triple).expect("inside the aperture");
            assert_ne!(reading.curvature, CurvatureSign::Spherical);
            assert!(
                !reading.closure.closes(),
                "a non-spherical triple closed, which would refute the geometry split"
            );
        }
    }
}
