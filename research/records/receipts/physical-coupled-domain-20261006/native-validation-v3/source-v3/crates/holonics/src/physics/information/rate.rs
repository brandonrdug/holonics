//! The cross-entropy rate with both motions and their clocks, and the two-parameter flow square.

use num_traits::{Signed, Zero};

use crate::aeon::{AxesJoin, ClockAxis, PositiveLaw, weighted_surprisal};
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::surprisal::SymbolicSurprisal;

use super::InformationError;
use super::apply::same_extent;

/// [definition] **A rate carried as ratio forms**: in nats, `ln 2 · log2_part + rational_part`, with
/// no logarithm evaluated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RateForm {
    pub log2_part: SymbolicSurprisal,
    pub rational_part: Rat,
}

impl RateForm {
    pub fn zero() -> Self {
        Self {
            log2_part: SymbolicSurprisal::zero(),
            rational_part: Rat::zero(),
        }
    }

    /// Whether the rate vanishes. Exact: `ln 2 · Σ c_p log₂ p = Σ c_p ln p`, and `{1} ∪ {ln p : p
    /// prime}` is ℚ-linearly independent (Hermite–Lindemann: a nonzero rational combination of the
    /// `ln p` is the logarithm of a rational other than one, hence transcendental, by unique
    /// factorization), so the two parts vanish separately.
    pub fn is_zero(&self) -> bool {
        self.log2_part.is_zero() && self.rational_part.is_zero()
    }

    pub fn plus(&self, other: &Self) -> Self {
        Self {
            log2_part: self.log2_part.plus(&other.log2_part),
            rational_part: &self.rational_part + &other.rational_part,
        }
    }

    /// The rate converted by a clock ratio `dτ/dλ`.
    pub fn scaled(&self, factor: &Rat) -> Self {
        Self {
            log2_part: self.log2_part.scaled(factor),
            rational_part: &self.rational_part * factor,
        }
    }
}

/// Refuse a rate that changes the total mass: the moving aperture keeps its normalization
/// (Lean `CrossEntropyRate.sum_rate_eq_zero`).
fn check_rate(
    what: &'static str,
    law: &PositiveLaw,
    rates: &[Rat],
) -> Result<(), InformationError> {
    same_extent(what, law.masses().len(), rates.len())?;
    if rates
        .iter()
        .fold(Rat::zero(), |sum, rate| sum + rate)
        .is_zero()
    {
        Ok(())
    } else {
        Err(InformationError::MovingSupport { what })
    }
}

/// The two terms of the rate: the population's `−Σ ṗ log q`, the infinitesimal exchange of the
/// first law of learning (`aeon::exchange`), and the reference's `−Σ p q̇/q`, its infinitesimal
/// deposition (`aeon::deposition`).
fn rate_terms(
    population: &PositiveLaw,
    population_rate: &[Rat],
    reference: &PositiveLaw,
    reference_rate: &[Rat],
) -> Result<(RateForm, RateForm), InformationError> {
    same_extent(
        "reference",
        population.masses().len(),
        reference.masses().len(),
    )?;
    check_rate("the population's rate", population, population_rate)?;
    check_rate("the reference's rate", reference, reference_rate)?;
    // −Σ ṗ ln q = ln 2 · Σ ṗ S(q), with S(q) = −log₂ q: the owner's weighted surprisal.
    let population_term = RateForm {
        log2_part: weighted_surprisal(population_rate, reference)?,
        rational_part: Rat::zero(),
    };
    let reference_term = RateForm {
        log2_part: SymbolicSurprisal::zero(),
        rational_part: population
            .masses()
            .iter()
            .zip(reference_rate)
            .zip(reference.masses())
            .fold(Rat::zero(), |sum, ((p, q_dot), q)| sum - p * q_dot / q),
    };
    Ok((population_term, reference_term))
}

/// [proved-derived; implemented-exact] **The cross-entropy rate** `dC/dλ = −Σ ṗ log q − Σ p q̇/q`
/// (Lean `Aeon/Production/FirstLaw.hasDerivAt_crossEntropy`): both motions enter, the dots already on the
/// common parameter. Refused when a rate changes the total mass (a moving support).
pub fn cross_entropy_rate(
    population: &PositiveLaw,
    population_rate: &[Rat],
    reference: &PositiveLaw,
    reference_rate: &[Rat],
) -> Result<RateForm, InformationError> {
    let (population_term, reference_term) =
        rate_terms(population, population_rate, reference, reference_rate)?;
    Ok(population_term.plus(&reference_term))
}

/// [definition] **A population moving on its own clock**: its law, its rate per tick of its own
/// axis, and the axis.
#[derive(Clone, Copy, Debug)]
pub struct Clocked<'a> {
    pub law: &'a PositiveLaw,
    pub rate: &'a [Rat],
    pub axis: ClockAxis,
}

/// [proved-derived; implemented-exact] **The cross-entropy rate on plural clocks** (Lean
/// `hasDerivAt_crossEntropy_clocks`): the population's rate is on its own axis's clock and the
/// reference's on its own; each dot is converted to the common axis by the join's
/// `dτ_axis/dτ_common`. A join with a defect, or an axis the join does not reach, is refused with
/// the join's own refusal: no rate is invented across a cycle that does not close.
pub fn cross_entropy_rate_on_clocks(
    population: Clocked<'_>,
    reference: Clocked<'_>,
    join: &AxesJoin,
    common: ClockAxis,
) -> Result<RateForm, InformationError> {
    let (population_term, reference_term) = rate_terms(
        population.law,
        population.rate,
        reference.law,
        reference.rate,
    )?;
    let population_clock = join.rate(population.axis, common)?;
    let reference_clock = join.rate(reference.axis, common)?;
    Ok(population_term
        .scaled(&population_clock)
        .plus(&reference_term.scaled(&reference_clock)))
}

/// [proved-derived; implemented-exact] **The free energy's rate** at a fixed Gibbs reference, in units
/// of `k_B T ln 2` per unit parameter: `Σ ṗᵢ log₂(pᵢ/qᵢ) = Σ ṗ S(q) − Σ ṗ S(p)` (Lean `hasDerivAt_kl`
/// with `q̇ = 0`), the pairing of the ratio covector with the produced velocity. Refused for a
/// moving support.
pub fn free_energy_rate(
    population: &PositiveLaw,
    population_rate: &[Rat],
    reference: &PositiveLaw,
) -> Result<SymbolicSurprisal, InformationError> {
    same_extent(
        "reference",
        population.masses().len(),
        reference.masses().len(),
    )?;
    check_rate("the population's rate", population, population_rate)?;
    Ok(weighted_surprisal(population_rate, reference)?
        .minus(&weighted_surprisal(population_rate, population)?))
}

/// [definition] **The two-parameter flow square's return**: the two orders agree on this state, or
/// both orders with the commutator on the state and the exact difference of their cross-entropies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlowSquare {
    /// The orders agree on this state; `matrices_commute` says whether `AB = BA` (Lean
    /// `commuting_square_reads_alike`'s hypothesis), which agreement on one state does not imply.
    ClosesOnState {
        population: Vec<Rat>,
        cross_entropy: SymbolicSurprisal,
        matrices_commute: bool,
    },
    Defect {
        first_then_second: Vec<Rat>,
        second_then_first: Vec<Rat>,
        /// `(second·first − first·second) p`.
        commutator_on_state: Vec<Rat>,
        /// `C₂(first then second) − C₂(second then first)`.
        cross_entropy_difference: SymbolicSurprisal,
    },
}

/// Refuse a step that is not column-stochastic: a negative entry, or a column that does not sum to
/// one (the step would not keep a population a population).
fn check_step(what: &'static str, step: &ExactRatMatrix) -> Result<(), InformationError> {
    for column in 0..step.columns() {
        let mut total = Rat::zero();
        for row in 0..step.rows() {
            let entry = step.get(row, column)?;
            if entry.is_negative() {
                return Err(InformationError::NotAStep { what, column });
            }
            total += entry;
        }
        if total != Rat::from_integer(1.into()) {
            return Err(InformationError::NotAStep { what, column });
        }
    }
    Ok(())
}

/// [proved-derived; implemented-exact] **The flow square** of two column-stochastic steps of one
/// population (Lean `ClockJoin.commuting_square_reads_alike`, `square_defect`,
/// `flow_square_orders`, `flow_square_crossEntropy_differs`): when the two orders agree on the state
/// every receiver reads them alike, here the cross-entropy against `reference`; otherwise their
/// difference is the commutator on the state, computed from the matrices, with the two
/// cross-entropies' exact difference. Refused for a step that is not column-stochastic.
pub fn flow_square(
    first: &ExactRatMatrix,
    second: &ExactRatMatrix,
    population: &PositiveLaw,
    reference: &PositiveLaw,
) -> Result<FlowSquare, InformationError> {
    check_step("the first step", first)?;
    check_step("the second step", second)?;
    let masses = population.masses();
    let first_then_second = second.apply(&first.apply(masses)?)?;
    let second_then_first = first.apply(&second.apply(masses)?)?;
    let commutator = second.multiply(first)?.subtract(&first.multiply(second)?)?;
    if first_then_second == second_then_first {
        let cross_entropy = weighted_surprisal(&first_then_second, reference)?;
        let matrices_commute = commutator.entries().iter().all(Zero::is_zero);
        return Ok(FlowSquare::ClosesOnState {
            population: first_then_second,
            cross_entropy,
            matrices_commute,
        });
    }
    let cross_entropy_difference = weighted_surprisal(&first_then_second, reference)?
        .minus(&weighted_surprisal(&second_then_first, reference)?);
    Ok(FlowSquare::Defect {
        commutator_on_state: commutator.apply(masses)?,
        first_then_second,
        second_then_first,
        cross_entropy_difference,
    })
}
