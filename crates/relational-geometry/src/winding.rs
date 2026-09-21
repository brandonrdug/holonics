//! Phase carry, pair resonance, generator trace faces and cell holonomy.
//!
//! The helix is the circle with its carry retained. This module is the exact executable owner of
//! that statement and of the three constructions that ride on it: the modular address of a
//! resonance lock, the trace/determinant faces a phase carriage conserves, and the screw that a
//! triangular cell's transports return. Every value here is an exact integer or an exact rational;
//! no float, no sampled angle and no tolerance enters.
//!
//! It reuses the crate's existing owners rather than restating them: [`Rat`] and [`BigInt`] for
//! scalars, [`AffineMap3`] for transports (its `followed_by`/`inverse` *are* the group operation
//! used by the holonomy), and [`ScrewPair`]/[`crate::SituatedScrew`]/[`crate::ScrewGenerator`] for
//! the pair lock, whose velocities come from `ScrewGenerator::velocity` at the retained initial
//! configuration. `crate::polygon_winding` is a different receiver (a ray-crossing count on a
//! sampled boundary) and is deliberately not involved.
//!
//! | Lean | Rust |
//! |---|---|
//! | `PhaseCarry.phase_add_winding` | [`phase`], [`winding`] |
//! | `PhaseCarry.winding_add`, `carry_le_one`, `carry_cocycle` | [`carry`] |
//! | `PhaseCarry.digits_succ`, `odometer_iterate`, `value_digits` | [`Odometer`] |
//! | `PhaseCarry.closed_loop_has_integer_winding` | [`closed_loop_winding`] |
//! | `PairResonance.lock_iff_zero_power` (zero-power direction) | [`pair_lock`] |
//! | `PairResonance.mediant_neighbours_both`, `neighbours_iff_unimodular` | [`mediant`], [`are_neighbours`] |
//! | `PairResonance.between_neighbours_costs_at_least_the_mediant` | [`simplest_between`], [`LockAddress::period`] |
//! | `PairResonance.unimodular_rechart_is_invertible` | [`IntMat2::unimodular_inverse`] |
//! | `Farey.sbL`, `sbR`, `theProductCarriesTheConvergents` | [`LockAddress`] |
//! | `LocalFactor.companion`, `theLocalFactorIsTheTransferDeterminant` | [`SiteFactor`] |
//! | `TraceSequence.trace`, `LocalFactor.theCompanionPowersCarryTheSequence` | [`SiteFactor::trace_sequence`] |
//! | `GeneratorTraceFaces.machine_factor_of_companions`, `machine_trace_sequence` | [`Machine`] |
//! | `CellHolonomy.triangleHolonomy`, `regauge`, `triangleHolonomy_regauge` | [`triangle_holonomy`], [`regauge`] |

use crate::{AffineMap3, Rat, RatMat3, RatVec3, ScrewPair};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use thiserror::Error;

/// Every refusal this module can return. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum WindingError {
    #[error("a circle of zero steps carries no phase chart")]
    ZeroModulus,
    #[error("odometer level {level} declares radix {radix}; a level needs at least two states")]
    DegenerateRadix { level: usize, radix: BigUint },
    #[error("odometer level {level} holds digit {digit}, which does not lie below radix {radix}")]
    DigitOutOfRange {
        level: usize,
        digit: BigUint,
        radix: BigUint,
    },
    #[error("an odometer declared {radices} radices and {digits} digits")]
    LevelCountMismatch { radices: usize, digits: usize },
    #[error(
        "the lifted loop does not close on the circle of {modulus} steps; remainder {remainder}"
    )]
    LoopDoesNotClose { modulus: BigInt, remainder: BigInt },
    #[error("a lock address needs a positive rate ratio; received {numerator}/{denominator}")]
    NotAPositiveRate {
        numerator: BigInt,
        denominator: BigInt,
    },
    #[error("the word is not unimodular; its determinant is {determinant}")]
    NonUnimodular { determinant: BigInt },
    #[error("the open interval ({lower}, {upper}) holds no rational")]
    EmptyInterval { lower: Rat, upper: Rat },
    #[error("a gauge frame must be invertible")]
    SingularGauge,
    #[error("the holonomy carries curvature, so its translation part is not a Burgers step")]
    CurvedHolonomy,
}

// ---------------------------------------------------------------------------------------------
// 1. Phase, winding and carry
// ---------------------------------------------------------------------------------------------

/// [definition] The phase of `x` on the circle of `n` steps. Lean: `PhaseCarry.phase`.
pub fn phase(n: &BigUint, x: &BigUint) -> Result<BigUint, WindingError> {
    if n.is_zero() {
        return Err(WindingError::ZeroModulus);
    }
    Ok(x % n)
}

/// [definition] The winding of `x`: completed turns of the circle of `n` steps.
/// Lean: `PhaseCarry.winding`, with `phase_add_winding` giving `phase + n*winding = x`.
pub fn winding(n: &BigUint, x: &BigUint) -> Result<BigUint, WindingError> {
    if n.is_zero() {
        return Err(WindingError::ZeroModulus);
    }
    Ok(x / n)
}

/// [definition] The carry of two phases: the turn completed by adding them.
///
/// [proved-derived; implemented-exact] It is the exact defect of the winding's additivity
/// (`PhaseCarry.winding_add`), never exceeds one turn (`carry_le_one`) and is a cocycle
/// (`carry_cocycle`). The tests exercise all three.
pub fn carry(n: &BigUint, a: &BigUint, b: &BigUint) -> Result<BigUint, WindingError> {
    if n.is_zero() {
        return Err(WindingError::ZeroModulus);
    }
    Ok(((a % n) + (b % n)) / n)
}

/// [proved-derived; implemented-exact] A closed loop of lifted integer increments has an integer
/// winding. Lean: `PhaseCarry.closed_loop_has_integer_winding`. A loop that does not close is
/// refused carrying its exact remainder rather than rounded to the nearest turn.
///
/// Cost: one pass over the increments.
pub fn closed_loop_winding(
    modulus: &BigInt,
    increments: &[BigInt],
) -> Result<BigInt, WindingError> {
    if modulus.is_zero() {
        return Err(WindingError::ZeroModulus);
    }
    let total: BigInt = increments.iter().sum();
    let remainder = &total % modulus;
    if !remainder.is_zero() {
        return Err(WindingError::LoopDoesNotClose {
            modulus: modulus.clone(),
            remainder,
        });
    }
    Ok(total / modulus)
}

/// [definition] A mixed-radix odometer: the cascade in which each level advances by the winding of
/// the level below. Lean: `PhaseCarry.odometer`, `digits`, `value`.
///
/// `overflow_winding` is the completed turns of the whole cascade — the material a product of
/// independent circles would have dropped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Odometer {
    radices: Vec<BigUint>,
    digits: Vec<BigUint>,
    overflow_winding: BigUint,
}

impl Odometer {
    /// A validated odometer at rest. Each radix must admit at least two states: a one-state level
    /// holds no phase, so its digit chart would read nothing and every step would be a carry.
    pub fn new(radices: Vec<BigUint>) -> Result<Self, WindingError> {
        let digits = vec![BigUint::zero(); radices.len()];
        Self::with_digits(radices, digits)
    }

    /// A validated odometer at a declared reading: one digit per level, each strictly below its
    /// radix.
    pub fn with_digits(radices: Vec<BigUint>, digits: Vec<BigUint>) -> Result<Self, WindingError> {
        if radices.len() != digits.len() {
            return Err(WindingError::LevelCountMismatch {
                radices: radices.len(),
                digits: digits.len(),
            });
        }
        let two = BigUint::from(2u32);
        for (level, radix) in radices.iter().enumerate() {
            if *radix < two {
                return Err(WindingError::DegenerateRadix {
                    level,
                    radix: radix.clone(),
                });
            }
            if digits[level] >= *radix {
                return Err(WindingError::DigitOutOfRange {
                    level,
                    digit: digits[level].clone(),
                    radix: radix.clone(),
                });
            }
        }
        Ok(Self {
            radices,
            digits,
            overflow_winding: BigUint::zero(),
        })
    }

    /// Read a value into the digit chart. Lean: `PhaseCarry.digits` iterated up the cascade.
    pub fn from_value(radices: Vec<BigUint>, value: &BigUint) -> Result<Self, WindingError> {
        let mut odometer = Self::new(radices)?;
        let mut remaining = value.clone();
        for level in 0..odometer.radices.len() {
            odometer.digits[level] = &remaining % &odometer.radices[level];
            remaining /= &odometer.radices[level];
        }
        odometer.overflow_winding = remaining;
        Ok(odometer)
    }

    pub fn radices(&self) -> &[BigUint] {
        &self.radices
    }

    pub fn digits(&self) -> &[BigUint] {
        &self.digits
    }

    pub fn overflow_winding(&self) -> &BigUint {
        &self.overflow_winding
    }

    pub fn levels(&self) -> usize {
        self.radices.len()
    }

    /// One act-and-advance step. Lean: `PhaseCarry.digits_succ`.
    pub fn step(&mut self) {
        self.advance(&BigUint::one());
    }

    /// Advance by `k` at once. Lean: `PhaseCarry.odometer_iterate` — the level above advances by
    /// the winding of the level below, so `k` is never counted down.
    ///
    /// Cost: at most one big-integer division and remainder per level, independent of `k`'s
    /// magnitude; it is linear in the number of levels and in `k`'s digit length, not in `k`.
    pub fn advance(&mut self, k: &BigUint) {
        let mut incoming = k.clone();
        for level in 0..self.radices.len() {
            if incoming.is_zero() {
                break;
            }
            let total = &self.digits[level] + &incoming;
            self.digits[level] = &total % &self.radices[level];
            incoming = total / &self.radices[level];
        }
        self.overflow_winding += incoming;
    }

    /// The value the digit chart carries. Lean: `PhaseCarry.value_digits` — the chart is faithful.
    ///
    /// Cost: one Horner pass down the levels.
    pub fn value(&self) -> BigUint {
        let mut total = self.overflow_winding.clone();
        for level in (0..self.radices.len()).rev() {
            total = total * &self.radices[level] + &self.digits[level];
        }
        total
    }
}

// ---------------------------------------------------------------------------------------------
// 2. Pair resonance and the modular address
// ---------------------------------------------------------------------------------------------

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
    pub fn left_turn(length: &BigUint) -> Self {
        Self::new([
            [BigInt::one(), BigInt::zero()],
            [BigInt::from(length.clone()), BigInt::one()],
        ])
    }

    /// `R = !![1,1;0,1]`, the right Stern–Brocot generator. Lean: `Farey.sbR`, `sbRPower_eq`.
    pub fn right_turn(length: &BigUint) -> Self {
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
    pub fn unimodular_inverse(&self) -> Result<Self, WindingError> {
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
            Err(WindingError::NonUnimodular { determinant })
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
    pub fn from_ratio(numerator: &BigInt, denominator: &BigInt) -> Result<Self, WindingError> {
        let refuse = || WindingError::NotAPositiveRate {
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
    pub fn matrix(&self) -> Result<IntMat2, WindingError> {
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
            return Err(WindingError::NonUnimodular { determinant });
        }
        Ok(product)
    }

    /// The addressed ratio: the mediant of the two columns the word carries.
    pub fn to_ratio(&self) -> Result<Rat, WindingError> {
        let matrix = self.matrix()?;
        let rows = matrix.rows();
        let numerator = &rows[0][0] + &rows[0][1];
        let denominator = &rows[1][0] + &rows[1][1];
        if denominator.is_zero() {
            return Err(WindingError::NonUnimodular {
                determinant: matrix.determinant(),
            });
        }
        Ok(Rat::new(numerator, denominator))
    }

    /// The closure cost of the lock: `q` for `p/q` in lowest terms — the number of turns of the
    /// first object before the pair returns to its initial joint phase.
    /// Lean: `PairResonance.between_neighbours_costs_at_least_the_mediant` prices this.
    pub fn period(&self) -> Result<BigInt, WindingError> {
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
pub fn simplest_between(lower: &Rat, upper: &Rat) -> Result<Rat, WindingError> {
    if lower >= upper {
        return Err(WindingError::EmptyInterval {
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

/// [proved-derived; implemented-exact] The pair locks at rate ratio `p/q` exactly when
/// `q·V_a(x_a(0)) = p·V_b(x_b(0))` — the zero-power direction of
/// `PairResonance.lock_iff_zero_power`, read from the pair's own generators at their retained
/// initial configurations. The dissipative face's weight and `D` are the consumer's material and
/// are not inferred here.
pub fn pair_lock(pair: &ScrewPair, numerator: &BigInt, denominator: &BigInt) -> bool {
    let first = pair.first();
    let second = pair.second();
    let first_velocity = first.generator().velocity(first.initial());
    let second_velocity = second.generator().velocity(second.initial());
    first_velocity.scale(&Rat::from_integer(denominator.clone()))
        == second_velocity.scale(&Rat::from_integer(numerator.clone()))
}

// ---------------------------------------------------------------------------------------------
// 3. Generator trace faces and the machine's transfer determinant
// ---------------------------------------------------------------------------------------------

/// [definition] The dichotomy of the site's transfer: where its characteristic root sits.
/// Lean: `TraceSequence` — the circle of radius `√q` against the hyperbola.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SiteKind {
    /// `a² < 4q`: the root is off the real line and the sequence circulates.
    Rotation,
    /// `a² = 4q`: the boundary case, a repeated real root.
    Marginal,
    /// `a² > 4q`: two real roots and the sequence goes hyperbolic.
    Dilation,
}

/// [definition] One site of the machine, read through its two conserved faces: the trace `a` and
/// the determinant `q` of its transfer material. Lean: `LocalFactor.companion` and
/// `theCompanionHasTraceAndDeterminant`; both faces are conserved by phase carriage
/// (`GeneratorTraceFaces.carried_material_conserves_determinant`, `..._trace_sequence`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SiteFactor {
    trace: Rat,
    determinant: Rat,
}

impl SiteFactor {
    pub fn new(trace: Rat, determinant: Rat) -> Self {
        Self { trace, determinant }
    }

    pub fn trace(&self) -> &Rat {
        &self.trace
    }

    pub fn determinant(&self) -> &Rat {
        &self.determinant
    }

    /// The Frobenius companion `!![a, −q; 1, 0]`. Lean: `LocalFactor.companion`.
    pub fn companion(&self) -> [[Rat; 2]; 2] {
        [
            [self.trace.clone(), -self.determinant.clone()],
            [Rat::one(), Rat::zero()],
        ]
    }

    /// The trace sequence `t₀ = 2`, `t₁ = a`, `t_{n+2} = a·t_{n+1} − q·t_n`, through index
    /// `degree` inclusive. Lean: `TraceSequence.trace`, and
    /// `LocalFactor.theCompanionPowersCarryTheSequence` identifies it with `tr(Mⁿ)`.
    ///
    /// Cost: `degree` exact multiplications; the companion is never exponentiated.
    pub fn trace_sequence(&self, degree: usize) -> Vec<Rat> {
        let mut sequence = Vec::with_capacity(degree + 1);
        sequence.push(Rat::from_integer(BigInt::from(2)));
        for index in 1..=degree {
            let term = if index == 1 {
                self.trace.clone()
            } else {
                &self.trace * &sequence[index - 1] - &self.determinant * &sequence[index - 2]
            };
            sequence.push(term);
        }
        sequence
    }

    /// The coefficients of `det(1 − T·M) = 1 − aT + qT²`, lowest power first.
    /// Lean: `LocalFactor.theLocalFactorIsTheTransferDeterminant`.
    pub fn transfer_coefficients(&self) -> [Rat; 3] {
        [Rat::one(), -self.trace.clone(), self.determinant.clone()]
    }

    /// The site's dichotomy, decided exactly on `a²` against `4q`.
    pub fn kind(&self) -> SiteKind {
        let discriminant =
            &self.trace * &self.trace - Rat::from_integer(BigInt::from(4)) * &self.determinant;
        if discriminant.is_negative() {
            SiteKind::Rotation
        } else if discriminant.is_zero() {
            SiteKind::Marginal
        } else {
            SiteKind::Dilation
        }
    }
}

/// [definition] A machine of independent sites: the block-diagonal material of
/// `GeneratorTraceFaces`. Its transfer determinant is the product of the site factors and its
/// closed-word count is the sum of the site trace sequences.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Machine {
    sites: Vec<SiteFactor>,
}

impl Machine {
    pub fn new(sites: Vec<SiteFactor>) -> Self {
        Self { sites }
    }

    pub fn sites(&self) -> &[SiteFactor] {
        &self.sites
    }

    /// The exact coefficient vector of `∏_g (1 − a_g T + q_g T²)`, lowest power first, of length
    /// `2·sites + 1`. Lean: `GeneratorTraceFaces.machine_factor_of_companions`.
    ///
    /// Cost: one convolution per site, quadratic in the site count.
    pub fn transfer_determinant(&self) -> Vec<Rat> {
        let mut coefficients = vec![Rat::one()];
        for site in &self.sites {
            let factor = site.transfer_coefficients();
            let mut next = vec![Rat::zero(); coefficients.len() + 2];
            for (left, coefficient) in coefficients.iter().enumerate() {
                for (right, entry) in factor.iter().enumerate() {
                    next[left + right] += coefficient * entry;
                }
            }
            coefficients = next;
        }
        coefficients
    }

    /// The machine's closed-word count through index `degree`: the sum of the site trace
    /// sequences. Lean: `GeneratorTraceFaces.machine_trace_sequence`.
    pub fn trace_sequence(&self, degree: usize) -> Vec<Rat> {
        let mut total = vec![Rat::zero(); degree + 1];
        for site in &self.sites {
            for (index, term) in site.trace_sequence(degree).into_iter().enumerate() {
                total[index] += term;
            }
        }
        total
    }

    /// The common dilation `q` when every site shares it, and `None` otherwise — including for a
    /// machine with no sites, which declares no `q` at all.
    pub fn common_dilation(&self) -> Option<Rat> {
        let first = self.sites.first()?.determinant();
        if self.sites.iter().all(|site| site.determinant() == first) {
            Some(first.clone())
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------------------------
// 4. Cell holonomy: the face around a cell is a screw
// ---------------------------------------------------------------------------------------------

/// [definition] The holonomy of three affine transports around a triangular cell, based at vertex
/// `0`: apply `g01`, then `g12`, then `g20`. Lean: `CellHolonomy.triangleHolonomy`, whose group
/// product `g01 * g12 * g20` is this left-to-right application order.
///
/// Its linear part is the cell's curvature and, when that part is the identity, its translation is
/// the Burgers step ([`burgers_step`]).
pub fn triangle_holonomy(g01: &AffineMap3, g12: &AffineMap3, g20: &AffineMap3) -> AffineMap3 {
    g01.followed_by(g12).followed_by(g20)
}

/// [definition] Regauging an edge transport by the vertex frames `ki`, `kj`:
/// `kᵢ⁻¹ ∘ g ∘ kⱼ` in the same order. Lean: `CellHolonomy.regauge`. A singular frame is refused.
pub fn regauge(
    ki: &AffineMap3,
    kj: &AffineMap3,
    g: &AffineMap3,
) -> Result<AffineMap3, WindingError> {
    let inverse = ki.inverse().ok_or(WindingError::SingularGauge)?;
    Ok(inverse.followed_by(g).followed_by(kj))
}

/// [definition] The trace of an affine map's linear part: a gauge-free face of the holonomy.
/// Lean: `CellHolonomy.holonomy_trace_is_gauge_free`.
pub fn linear_trace(map: &AffineMap3) -> Rat {
    &map.linear.rows[0][0] + &map.linear.rows[1][1] + &map.linear.rows[2][2]
}

/// [definition] The Burgers step of a cell: the translation part of a holonomy whose linear part is
/// the identity. A holonomy that rotates carries curvature, and its translation is then frame
/// dependent, so it is refused rather than reported.
pub fn burgers_step(holonomy: &AffineMap3) -> Result<&RatVec3, WindingError> {
    if holonomy.linear != RatMat3::identity() {
        return Err(WindingError::CurvedHolonomy);
    }
    Ok(&holonomy.translation)
}

#[cfg(test)]
mod tests;
