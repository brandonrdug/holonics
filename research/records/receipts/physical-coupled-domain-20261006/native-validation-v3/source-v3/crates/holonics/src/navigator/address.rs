//! **Address words and lock addresses: the Stern–Brocot word of a rate ratio.**
//!
//! A navigator's source word is its address ([objects §3](../../../../docs/ELEMENTARY_OBJECTS.md#3-navigator)).
//! For a pair of commensurate clocks the address of their lock is the Stern–Brocot path of the
//! rate ratio `p/q`, stored run-length, which is its continued fraction; the word is a product of
//! unimodular generators in `SL₂(ℤ)`. Two locks are neighbours exactly when their matrix is
//! unimodular, and the mediant is the cheapest lock between neighbours.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Geometry/PairResonance.mediant_neighbours_both`, `neighbours_iff_unimodular` | [`mediant`], [`are_neighbours`] |
//! | `Geometry/PairResonance.between_neighbours_costs_at_least_the_mediant` | [`simplest_between`], [`LockAddress::period`] |
//! | `Geometry/PairResonance.unimodular_rechart_is_invertible` | [`IntMat2::unimodular_inverse`] |
//! | `Geometry/Farey.sbL`, `sbR`, `theProductCarriesTheConvergents` | [`LockAddress`] |

use crate::ratio::Rat;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use thiserror::Error;

/// Every refusal of an address. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum AddressError {
    #[error("a lock address needs a positive rate ratio; received {numerator}/{denominator}")]
    NotAPositiveRate {
        numerator: BigInt,
        denominator: BigInt,
    },
    #[error("the word is not unimodular; its determinant is {determinant}")]
    NonUnimodular { determinant: BigInt },
    #[error("the open interval ({lower}, {upper}) holds no rational")]
    EmptyInterval { lower: Rat, upper: Rat },
}

/// [definition] An exact two-by-two integer matrix: the modular word's carrier.
/// Lean: `Farey.cfProd`, `PairResonance.neighbours_iff_unimodular`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntMat2 {
    rows: [[BigInt; 2]; 2],
}

impl IntMat2 {
    pub fn new(rows: [[BigInt; 2]; 2]) -> Self {
        Self { rows }
    }

    pub fn from_i64(rows: [[i64; 2]; 2]) -> Self {
        Self::new(rows.map(|row| row.map(BigInt::from)))
    }

    pub fn identity() -> Self {
        Self::from_i64([[1, 0], [0, 1]])
    }

    /// `L = !![1,0;1,1]`, the left Stern–Brocot generator. Lean: `Farey.sbL`.
    pub(crate) fn left_turn(length: &BigUint) -> Self {
        Self::new([
            [BigInt::one(), BigInt::zero()],
            [BigInt::from(length.clone()), BigInt::one()],
        ])
    }

    /// `R = !![1,1;0,1]`, the right Stern–Brocot generator. Lean: `Farey.sbR`, `sbRPower_eq`.
    pub(crate) fn right_turn(length: &BigUint) -> Self {
        Self::new([
            [BigInt::one(), BigInt::from(length.clone())],
            [BigInt::zero(), BigInt::one()],
        ])
    }

    pub fn rows(&self) -> &[[BigInt; 2]; 2] {
        &self.rows
    }

    pub fn multiply(&self, other: &Self) -> Self {
        let entry = |row: usize, column: usize| {
            &self.rows[row][0] * &other.rows[0][column]
                + &self.rows[row][1] * &other.rows[1][column]
        };
        Self::new([[entry(0, 0), entry(0, 1)], [entry(1, 0), entry(1, 1)]])
    }

    pub fn trace(&self) -> BigInt {
        &self.rows[0][0] + &self.rows[1][1]
    }

    pub fn determinant(&self) -> BigInt {
        &self.rows[0][0] * &self.rows[1][1] - &self.rows[0][1] * &self.rows[1][0]
    }

    /// [proved-derived; implemented-exact] A unimodular word is invertible *over the integers*: a
    /// rechart of the pair's winding lattice, not a loss of resolution.
    /// Lean: `PairResonance.unimodular_rechart_is_invertible`.
    pub fn unimodular_inverse(&self) -> Result<Self, AddressError> {
        let determinant = self.determinant();
        let adjugate = Self::new([
            [self.rows[1][1].clone(), -self.rows[0][1].clone()],
            [-self.rows[1][0].clone(), self.rows[0][0].clone()],
        ]);
        if determinant.is_one() {
            Ok(adjugate)
        } else if determinant == -BigInt::one() {
            Ok(Self::new(adjugate.rows.map(|row| row.map(|value| -value))))
        } else {
            Err(AddressError::NonUnimodular { determinant })
        }
    }
}

/// [definition] One Stern–Brocot turn.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Turn {
    /// Towards the smaller neighbour.
    L,
    /// Towards the larger neighbour.
    R,
}

/// [definition] A run of equal turns: one partial quotient of the continued fraction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockRun {
    pub turn: Turn,
    pub length: BigUint,
}

/// [definition] The modular address of a resonance lock: the Stern–Brocot path of the rate ratio
/// `p/q`, stored run-length — which is exactly its continued fraction.
///
/// The empty word addresses the root `1/1`. Lean: `Farey` (the word is a matrix product in
/// `SL₂(ℤ)`) and `PairResonance` (neighbouring locks are the unimodular pairs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockAddress {
    runs: Vec<LockRun>,
}

impl LockAddress {
    /// The address of a positive rate ratio, reduced first so the address is a function of the
    /// ratio and not of its spelling.
    ///
    /// Cost: one Euclidean descent — logarithmic in `min(p, q)`, so linear in the operands'
    /// digit length. The word is never expanded turn by turn.
    pub fn from_ratio(numerator: &BigInt, denominator: &BigInt) -> Result<Self, AddressError> {
        let refuse = || AddressError::NotAPositiveRate {
            numerator: numerator.clone(),
            denominator: denominator.clone(),
        };
        if denominator.is_zero() {
            return Err(refuse());
        }
        let reduced = Rat::new(numerator.clone(), denominator.clone());
        if !reduced.is_positive() {
            return Err(refuse());
        }
        let mut upper = reduced.numer().clone();
        let mut lower = reduced.denom().clone();
        let mut quotients: Vec<BigUint> = Vec::new();
        while !lower.is_zero() {
            let quotient = (&upper / &lower).to_biguint().ok_or_else(refuse)?;
            let remainder = &upper % &lower;
            quotients.push(quotient);
            upper = lower;
            lower = remainder;
        }
        // The Euclidean descent's last partial quotient is the step onto the node itself, so the
        // Stern-Brocot word is one turn shorter than the quotient sum.
        if let Some(last) = quotients.last_mut() {
            *last -= BigUint::one();
        }
        let runs = quotients
            .into_iter()
            .enumerate()
            .filter(|(_, length)| !length.is_zero())
            .map(|(index, length)| LockRun {
                turn: if index % 2 == 0 { Turn::R } else { Turn::L },
                length,
            })
            .collect();
        Ok(Self { runs })
    }

    /// The runs, outermost first.
    pub fn runs(&self) -> &[LockRun] {
        &self.runs
    }

    /// The partial quotients `[a₀; a₁, …, a_N]` of the addressed ratio, recovered from the runs:
    /// a leading `L` run means `a₀ = 0`, and the last quotient is one longer than its run (the
    /// Euclidean descent's final step lands on the node itself). The root `1/1` is `[1]`.
    /// `crate::aeon::TwoClocks::convergents` reads the near-return grains from them.
    pub fn partial_quotients(&self) -> Vec<BigUint> {
        let mut quotients: Vec<BigUint> = Vec::with_capacity(self.runs.len() + 1);
        if self.runs.first().is_some_and(|run| run.turn == Turn::L) {
            quotients.push(BigUint::zero());
        }
        quotients.extend(self.runs.iter().map(|run| run.length.clone()));
        match quotients.last_mut() {
            Some(last) => *last += BigUint::one(),
            None => quotients.push(BigUint::one()),
        }
        quotients
    }

    /// The total number of turns: the Stern–Brocot depth.
    pub fn depth(&self) -> BigUint {
        self.runs
            .iter()
            .fold(BigUint::zero(), |total, run| total + &run.length)
    }

    /// The word's unimodular matrix, `∏ L^a / R^a`. Lean: `Farey.theProductCarriesTheConvergents`;
    /// the determinant check is `Farey.theGeneratorsAreUnimodular` along the word.
    ///
    /// Cost: one two-by-two multiplication per *run*, not per turn.
    pub fn matrix(&self) -> Result<IntMat2, AddressError> {
        let mut product = IntMat2::identity();
        for run in &self.runs {
            let step = match run.turn {
                Turn::L => IntMat2::left_turn(&run.length),
                Turn::R => IntMat2::right_turn(&run.length),
            };
            product = product.multiply(&step);
        }
        let determinant = product.determinant();
        if !determinant.is_one() {
            return Err(AddressError::NonUnimodular { determinant });
        }
        Ok(product)
    }

    /// The addressed ratio: the mediant of the two columns the word carries.
    pub(crate) fn to_ratio(&self) -> Result<Rat, AddressError> {
        let matrix = self.matrix()?;
        let rows = matrix.rows();
        let numerator = &rows[0][0] + &rows[0][1];
        let denominator = &rows[1][0] + &rows[1][1];
        if denominator.is_zero() {
            return Err(AddressError::NonUnimodular {
                determinant: matrix.determinant(),
            });
        }
        Ok(Rat::new(numerator, denominator))
    }

    /// The closure cost of the lock: `q` for `p/q` in lowest terms — the number of turns of the
    /// first object before the pair returns to its initial joint phase.
    /// Lean: `PairResonance.between_neighbours_costs_at_least_the_mediant` prices this.
    pub fn period(&self) -> Result<BigInt, AddressError> {
        Ok(self.to_ratio()?.denom().clone())
    }
}

/// [definition] The mediant of two rationals, taken on their reduced representatives.
/// Lean: `PairResonance.mediant_neighbours_both`, `mediant_lies_between`.
pub fn mediant(left: &Rat, right: &Rat) -> Rat {
    Rat::new(left.numer() + right.numer(), left.denom() + right.denom())
}

/// [definition] Two locks are neighbours exactly when their matrix is unimodular: `p'q − pq' = 1`.
/// Lean: `PairResonance.neighbours_iff_unimodular`, `Farey.theMediantConditionIsUnimodularity`.
pub fn are_neighbours(left: &Rat, right: &Rat) -> bool {
    (right.numer() * left.denom() - left.numer() * right.denom()).is_one()
}

/// [definition] The cheapest lock strictly inside an open rational interval: the lowest-denominator
/// rational there, which is placement up to a declared tolerance rather than to a rounded value.
///
/// [agent-inferred] When several rationals share the minimal denominator (an interval spanning
/// more than one integer), the Stern–Brocot ancestor — the one the descent reaches first — is
/// returned; the minimal denominator itself is unique and is what the tests pin.
///
/// Cost: a continued-fraction descent, logarithmic in the endpoints' denominators. It never walks
/// the Stern–Brocot tree one turn at a time.
pub fn simplest_between(lower: &Rat, upper: &Rat) -> Result<Rat, AddressError> {
    if lower >= upper {
        return Err(AddressError::EmptyInterval {
            lower: lower.clone(),
            upper: upper.clone(),
        });
    }
    let zero = Rat::zero();
    if *lower < zero && zero < *upper {
        return Ok(zero);
    }
    if *lower >= zero {
        Ok(simplest_nonnegative(lower, upper))
    } else {
        Ok(-simplest_nonnegative(&-upper.clone(), &-lower.clone()))
    }
}

/// The nonnegative branch of [`simplest_between`], with `0 <= lower < upper`.
fn simplest_nonnegative(lower: &Rat, upper: &Rat) -> Rat {
    let base = lower.floor();
    let next = &base + Rat::one();
    if next < *upper {
        return next;
    }
    let low_fraction = lower - &base;
    let high_fraction = upper - &base;
    if low_fraction.is_zero() {
        // The interval is (0, high_fraction] after the shift: 1/k for the least admissible k.
        let step = (Rat::one() / &high_fraction).floor() + Rat::one();
        return base + Rat::one() / step;
    }
    // x lies in (low, high) exactly when 1/x lies in (1/high, 1/low), and the reciprocal is the
    // Stern-Brocot mirror, so it carries the simplest representative across.
    let inner = simplest_nonnegative(&(Rat::one() / high_fraction), &(Rat::one() / low_fraction));
    base + Rat::one() / inner
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::rat;

    fn nat(value: u32) -> BigUint {
        BigUint::from(value)
    }

    #[test]
    fn the_address_round_trips_with_its_ratio() {
        for p in 1i64..=18 {
            for q in 1i64..=18 {
                let address = LockAddress::from_ratio(&BigInt::from(p), &BigInt::from(q))
                    .expect("a positive rate");
                let reduced = Rat::new(BigInt::from(p), BigInt::from(q));
                assert_eq!(
                    address.to_ratio().expect("a unimodular word"),
                    reduced,
                    "address of {p}/{q} did not reopen"
                );
                assert_eq!(
                    address.period().expect("a unimodular word"),
                    *reduced.denom(),
                    "the closure cost is the reduced denominator"
                );
                // The address is a function of the ratio, not of the spelling.
                let scaled = LockAddress::from_ratio(&BigInt::from(3 * p), &BigInt::from(3 * q))
                    .expect("a positive rate");
                assert_eq!(address, scaled);
            }
        }
        assert!(
            LockAddress::from_ratio(&BigInt::from(1), &BigInt::from(1))
                .expect("the root")
                .runs()
                .is_empty()
        );
        assert_eq!(
            LockAddress::from_ratio(&BigInt::from(3), &BigInt::from(2))
                .expect("a positive rate")
                .runs(),
            &[
                LockRun {
                    turn: Turn::R,
                    length: nat(1)
                },
                LockRun {
                    turn: Turn::L,
                    length: nat(1)
                }
            ]
        );
        assert!(matches!(
            LockAddress::from_ratio(&BigInt::from(-1), &BigInt::from(2)),
            Err(AddressError::NotAPositiveRate { .. })
        ));
        assert!(matches!(
            LockAddress::from_ratio(&BigInt::from(1), &BigInt::zero()),
            Err(AddressError::NotAPositiveRate { .. })
        ));
    }

    #[test]
    fn the_word_is_unimodular_and_integrally_invertible() {
        for p in 1i64..=12 {
            for q in 1i64..=12 {
                let matrix = LockAddress::from_ratio(&BigInt::from(p), &BigInt::from(q))
                    .expect("a positive rate")
                    .matrix()
                    .expect("a unimodular word");
                assert!(matrix.determinant().is_one());
                let inverse = matrix.unimodular_inverse().expect("det one is invertible");
                assert_eq!(matrix.multiply(&inverse), IntMat2::identity());
                assert_eq!(inverse.multiply(&matrix), IntMat2::identity());
            }
        }
        let exchange = IntMat2::from_i64([[0, 1], [1, 0]]);
        assert_eq!(exchange.determinant(), BigInt::from(-1));
        assert_eq!(
            exchange
                .unimodular_inverse()
                .expect("det minus one is invertible")
                .multiply(&exchange),
            IntMat2::identity()
        );
        assert_eq!(
            IntMat2::from_i64([[2, 0], [0, 2]]).unimodular_inverse(),
            Err(AddressError::NonUnimodular {
                determinant: BigInt::from(4)
            })
        );
        assert_eq!(IntMat2::from_i64([[1, 2], [3, 4]]).trace(), BigInt::from(5));
    }

    #[test]
    fn neighbours_have_a_mediant_that_neighbours_both() {
        let left = rat(1, 3);
        let right = rat(1, 2);
        assert!(are_neighbours(&left, &right));
        let middle = mediant(&left, &right);
        assert_eq!(middle, rat(2, 5));
        assert!(are_neighbours(&left, &middle));
        assert!(are_neighbours(&middle, &right));
        assert!(left < middle && middle < right, "the mediant lies between");
        assert!(!are_neighbours(&rat(1, 3), &rat(2, 3)));
    }

    #[test]
    fn every_ratio_between_neighbours_costs_at_least_the_mediant() {
        // Exhaustive over the small Farey neighbours and every a/b strictly between them.
        for q in 1i64..=7 {
            for p in 0i64..=q {
                for q_prime in 1i64..=7 {
                    for p_prime in 0i64..=q_prime {
                        let left = Rat::new(BigInt::from(p), BigInt::from(q));
                        let right = Rat::new(BigInt::from(p_prime), BigInt::from(q_prime));
                        if !are_neighbours(&left, &right) {
                            continue;
                        }
                        // The spelling may be unreduced; the cost is q + q' of the reduced pair.
                        let middle = mediant(&left, &right);
                        let cost = left.denom() + right.denom();
                        assert_eq!(*middle.denom(), cost);
                        for b in 1i64..=14 {
                            if BigInt::from(b) >= cost {
                                break;
                            }
                            for a in 0i64..=b {
                                let candidate = Rat::new(BigInt::from(a), BigInt::from(b));
                                assert!(
                                    !(left < candidate && candidate < right),
                                    "{a}/{b} is cheaper than the mediant of {p}/{q} and \
                                     {p_prime}/{q_prime}"
                                );
                            }
                        }
                        assert_eq!(
                            simplest_between(&left, &right).expect("a nonempty interval"),
                            middle,
                            "the mediant is the cheapest lock in the gap"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn simplest_between_agrees_with_brute_force() {
        let endpoints: Vec<Rat> = (-6i64..=6)
            .flat_map(|numerator| {
                (1i64..=5).map(move |denominator| {
                    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
                })
            })
            .collect();
        for lower in &endpoints {
            for upper in &endpoints {
                if lower >= upper {
                    assert!(matches!(
                        simplest_between(lower, upper),
                        Err(AddressError::EmptyInterval { .. })
                    ));
                    continue;
                }
                let found = simplest_between(lower, upper).expect("a nonempty interval");
                assert!(*lower < found && found < *upper, "must lie strictly inside");
                // Brute force: no rational with a smaller denominator lies strictly inside.
                let bound = found.denom().clone();
                let mut minimal_witnesses: Vec<Rat> = Vec::new();
                let mut denominator = BigInt::one();
                while denominator <= bound {
                    let span = 12i64;
                    for numerator in -span * 6..=span * 6 {
                        let candidate = Rat::new(BigInt::from(numerator), denominator.clone());
                        if *candidate.denom() != denominator {
                            continue;
                        }
                        if *lower < candidate && candidate < *upper {
                            minimal_witnesses.push(candidate);
                        }
                    }
                    if !minimal_witnesses.is_empty() {
                        break;
                    }
                    denominator += BigInt::one();
                }
                assert_eq!(
                    denominator, bound,
                    "brute force found a cheaper denominator in ({lower}, {upper})"
                );
                if minimal_witnesses.len() == 1 {
                    assert_eq!(minimal_witnesses[0], found);
                } else {
                    assert!(minimal_witnesses.contains(&found));
                }
            }
        }
    }
}
