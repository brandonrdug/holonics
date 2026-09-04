//! Exact arithmetic fibers founded by causal multiplication.
//!
//! Integers enter in succession.  A prime is founded only when multiplication
//! by every already-founded prime axis at or below its square root fails to
//! reach the new integer.  Distinct prime support becomes oriented simplicial
//! incidence; repeated prime factors remain exact multiplicity on that
//! support and never masquerade as extra dimensions.
//!
//! Polynomial observations are receiver fibers, not plotted scalar points.
//! The first implemented family is `x^2 - a` over a founded prime receiver,
//! together with exact Hensel and Chinese-remainder transport.  A bounded
//! residue grammar can then be inferred solely from paired root fibers.  The
//! grammar does not contain quadratic reciprocity in advance.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CausalAlgebraicError, CausalCellId, CausalChain, CellularRestriction, ComparativeMultiplicity,
    EventId, EventSuccessor, ExactCellularSheaf, ExactEventLaw, ExactLinearMap,
    GradedCausalComplex, PrimeValuation, SheafDiffusionError,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeAxisProbe {
    pub prime_axis: u64,
    pub quotient: u64,
    pub remainder: u64,
}

/// The two dispositions which remain possible while a candidate's direct
/// multiplication receiver is still open.
///
/// This is not a probability space.  A disposition remains present exactly
/// when the returned prime-axis probes have not yet excluded it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum PrimeRecognitionDisposition {
    Irreducible,
    Composite,
}

/// One exact section of the candidate's still-admissible continuation fiber.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeContinuationFiber {
    pub schema: String,
    /// Number of ordered prime-axis probes whose returns are present here.
    pub after_probe_count: u64,
    pub admissible_dispositions: BTreeSet<PrimeRecognitionDisposition>,
    /// Factor axes in the admitted square-root horizon which have not yet
    /// returned.  They remain topology, not a scalar uncertainty score.
    pub unreturned_factor_axes: Vec<u64>,
}

impl PrimeContinuationFiber {
    pub fn is_open(&self) -> bool {
        self.admissible_dispositions.len() > 1
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeFactorWitness {
    pub prime_axis: u64,
    pub cofactor: u64,
    pub exact_product: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrimeRecognitionClosure {
    Composite {
        witness: PrimeFactorWitness,
    },
    Irreducible {
        /// The complete admitted factor horizon returned nonzero remainders.
        failed_axes: Vec<u64>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeRecognitionStep {
    pub depth: u64,
    pub probe: PrimeAxisProbe,
    pub fiber_after: PrimeContinuationFiber,
}

/// Prefix-minimal obstruction to the irreducible continuation branch.
///
/// A composite candidate can have further factor witnesses, but this front is
/// the first returned axis in the declared ordered receiver which makes the
/// irreducible branch impossible.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeIrreducibilityObstruction {
    pub schema: String,
    pub depth: u64,
    pub witness: PrimeFactorWitness,
}

/// Exact work bounds in the declared ordered prime-axis observation language.
///
/// These are not universal primality-complexity bounds.  Before
/// `distinguishing_probe_lower_bound` probes, the retained fiber still admits
/// both dispositions; the enacted closure at
/// `certificate_probe_upper_bound` supplies a matching constructive bound.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeRecognitionBounds {
    pub factor_horizon_axis_count: u64,
    pub distinguishing_probe_lower_bound: u64,
    pub certificate_probe_upper_bound: u64,
}

/// Complete causal recognition testimony for one admitted integer.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeRecognitionTrace {
    pub schema: String,
    pub candidate: u64,
    pub initial_fiber: PrimeContinuationFiber,
    pub steps: Vec<PrimeRecognitionStep>,
    pub closure: PrimeRecognitionClosure,
    pub bounds: PrimeRecognitionBounds,
    pub irreducibility_obstruction: Option<PrimeIrreducibilityObstruction>,
}

impl PrimeRecognitionTrace {
    pub fn open_fiber_count(&self) -> u64 {
        std::iter::once(&self.initial_fiber)
            .chain(self.steps.iter().map(|step| &step.fiber_after))
            .filter(|fiber| fiber.is_open())
            .count() as u64
    }

    pub fn is_irreducible(&self) -> bool {
        matches!(self.closure, PrimeRecognitionClosure::Irreducible { .. })
    }
}

/// One von-Mangoldt occurrence retained without evaluating a logarithm.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimePowerCurrentEvent {
    pub value: u64,
    pub prime: u64,
    pub exponent: u32,
    /// Coefficient of the formal basis element `log(prime)` after this event.
    pub log_coefficient_after: u32,
    /// `exp(psi(value)) = lcm(1, ..., value)` as an exact integer face.
    pub chebyshev_product_after: BigUint,
}

/// Exact symbolic Chebyshev current
///
/// `psi(x) = sum_p log_coefficients[p] * log(p)`.
///
/// The integer `chebyshev_product` is the equivalent multiplicative face
/// `exp(psi(x)) = lcm(1, ..., x)`.  No floating logarithm enters standing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimePowerCurrent {
    pub schema: String,
    pub through: u64,
    pub log_coefficients: BTreeMap<u64, u32>,
    pub chebyshev_product: BigUint,
}

impl Default for PrimePowerCurrent {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.prime-power-current.v1".to_owned(),
            through: 1,
            log_coefficients: BTreeMap::new(),
            chebyshev_product: BigUint::one(),
        }
    }
}

impl PrimePowerCurrent {
    /// Return the exact formal departure `sum a_p log(p) - through`.
    pub fn formal_departure(&self) -> FormalChebyshevDeparture {
        FormalChebyshevDeparture {
            schema: "holonic-engine.formal-chebyshev-departure.v1".to_owned(),
            through: self.through,
            log_coefficients: self.log_coefficients.clone(),
            smooth_coordinate: BigInt::from(self.through),
        }
    }

    fn advance(
        &mut self,
        occurrence: &ArithmeticOccurrence,
    ) -> Result<Option<PrimePowerCurrentEvent>, ArithmeticFiberError> {
        self.through = occurrence.value;
        if occurrence.valuation.len() != 1 {
            return Ok(None);
        }
        let valuation = &occurrence.valuation[0];
        let coefficient = self.log_coefficients.entry(valuation.prime).or_default();
        *coefficient = coefficient
            .checked_add(1)
            .ok_or(ArithmeticFiberError::CarrierOverflow)?;
        self.chebyshev_product *= BigUint::from(valuation.prime);
        Ok(Some(PrimePowerCurrentEvent {
            value: occurrence.value,
            prime: valuation.prime,
            exponent: valuation.exponent,
            log_coefficient_after: *coefficient,
            chebyshev_product_after: self.chebyshev_product.clone(),
        }))
    }
}

/// The residual `psi(x) - x` retained as an exact formal expression.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FormalChebyshevDeparture {
    pub schema: String,
    pub through: u64,
    pub log_coefficients: BTreeMap<u64, u32>,
    pub smooth_coordinate: BigInt,
}

/// Exact geometric valuation generator under one declared Zeta receiver.
///
/// For integer `sigma > 1`, valuation `k` has receiver mass
/// `zero_valuation_mass * recurrence_ratio^k`.  The mass is a selected
/// receiver quotient, not an ontic random choice.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactZetaValuationFiber {
    pub prime: u64,
    pub sigma: u32,
    pub zero_valuation_mass: Rat,
    pub recurrence_ratio: Rat,
}

impl ExactZetaValuationFiber {
    pub fn mass_at(&self, exponent: u32) -> Rat {
        (0..exponent).fold(self.zero_valuation_mass.clone(), |mass, _| {
            mass * &self.recurrence_ratio
        })
    }
}

/// Exact finite place-set section of the Zeta valuation product.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactZetaReceiverMeasure {
    pub schema: String,
    pub sigma: u32,
    pub selected_primes: Vec<u64>,
    pub valuation_fibers: Vec<ExactZetaValuationFiber>,
    /// Mass of the cell with zero valuation at every selected prime.
    pub coprime_cell_mass: Rat,
    /// Reciprocal Euler return through the same finite place set.
    pub valuation_return_mass: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoundedPrime {
    pub prime: u64,
    pub cell: CausalCellId,
    /// Every extant prime axis capable of being a factor was tested.
    pub failed_axes: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoundedMultiplicativeCell {
    pub squarefree_support: Vec<u64>,
    pub cell: CausalCellId,
    pub grade: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticOccurrence {
    pub event: EventId,
    pub value: u64,
    pub valuation: Vec<PrimeValuation>,
    pub squarefree_support: Vec<u64>,
    pub support_cell: CausalCellId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticFiberStanding {
    pub schema: String,
    pub value: u64,
    incidence: GradedCausalComplex,
    prime_cells: BTreeMap<u64, CausalCellId>,
    squarefree_cells: BTreeMap<Vec<u64>, CausalCellId>,
    occurrences: BTreeMap<u64, ArithmeticOccurrence>,
    recognitions: BTreeMap<u64, PrimeRecognitionTrace>,
    prime_power_current: PrimePowerCurrent,
    used_events: BTreeSet<EventId>,
}

impl Default for ArithmeticFiberStanding {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.arithmetic-fiber-standing.v2".to_owned(),
            value: 1,
            incidence: GradedCausalComplex::default(),
            prime_cells: BTreeMap::new(),
            squarefree_cells: BTreeMap::new(),
            occurrences: BTreeMap::new(),
            recognitions: BTreeMap::new(),
            prime_power_current: PrimePowerCurrent::default(),
            used_events: BTreeSet::new(),
        }
    }
}

impl ArithmeticFiberStanding {
    pub fn incidence(&self) -> &GradedCausalComplex {
        &self.incidence
    }

    /// Extend the shared arithmetic incidence from another production law in
    /// this crate.
    ///
    /// The arithmetic validator deliberately accepts additional caused cells:
    /// multiplication owns its named support cells, but receiver ecologies may
    /// found other cells over the same prime vertices. Keeping this mouth
    /// crate-private prevents an application from injecting those cells.
    pub(crate) fn incidence_mut(&mut self) -> &mut GradedCausalComplex {
        &mut self.incidence
    }

    pub fn prime_cells(&self) -> &BTreeMap<u64, CausalCellId> {
        &self.prime_cells
    }

    pub fn squarefree_cells(&self) -> &BTreeMap<Vec<u64>, CausalCellId> {
        &self.squarefree_cells
    }

    pub fn occurrences(&self) -> &BTreeMap<u64, ArithmeticOccurrence> {
        &self.occurrences
    }

    pub fn recognitions(&self) -> &BTreeMap<u64, PrimeRecognitionTrace> {
        &self.recognitions
    }

    pub fn prime_power_current(&self) -> &PrimePowerCurrent {
        &self.prime_power_current
    }

    /// Form the exact finite-place Zeta valuation measure selected by this
    /// receiver.  Only already-founded prime identities may define axes.
    pub fn zeta_receiver_measure(
        &self,
        sigma: u32,
        selected_primes: &BTreeSet<u64>,
    ) -> Result<ExactZetaReceiverMeasure, ArithmeticFiberError> {
        self.validate()?;
        if sigma <= 1 {
            return Err(ArithmeticFiberError::InvalidZetaSigma(sigma));
        }
        let mut valuation_fibers = Vec::with_capacity(selected_primes.len());
        let mut coprime_cell_mass = Rat::one();
        for prime in selected_primes {
            self.prime_cell(*prime)?;
            let prime_to_sigma = BigInt::from(*prime).pow(sigma);
            let recurrence_ratio = Rat::new(BigInt::one(), prime_to_sigma.clone());
            let zero_valuation_mass = Rat::new(&prime_to_sigma - BigInt::one(), prime_to_sigma);
            coprime_cell_mass *= &zero_valuation_mass;
            valuation_fibers.push(ExactZetaValuationFiber {
                prime: *prime,
                sigma,
                zero_valuation_mass,
                recurrence_ratio,
            });
        }
        let valuation_return_mass = coprime_cell_mass.clone().recip();
        Ok(ExactZetaReceiverMeasure {
            schema: "holonic-engine.exact-zeta-receiver-measure.v1".to_owned(),
            sigma,
            selected_primes: selected_primes.iter().copied().collect(),
            valuation_fibers,
            coprime_cell_mass,
            valuation_return_mass,
        })
    }

    pub fn prime_cell(&self, prime: u64) -> Result<CausalCellId, ArithmeticFiberError> {
        self.prime_cells
            .get(&prime)
            .copied()
            .ok_or(ArithmeticFiberError::UnfoundedPrime(prime))
    }

    pub fn quadratic_fiber(
        &self,
        prime: u64,
        radicand: impl Into<BigInt>,
    ) -> Result<QuadraticPrimeFiber, ArithmeticFiberError> {
        let prime_cell = self.prime_cell(prime)?;
        quadratic_prime_fiber(prime, prime_cell, radicand.into())
    }

    pub fn paired_quadratic_fiber(
        &self,
        left: u64,
        right: u64,
    ) -> Result<PairedQuadraticFiber, ArithmeticFiberError> {
        if left == right {
            return Err(ArithmeticFiberError::RepeatedReciprocityPrime(left));
        }
        if left == 2 || right == 2 {
            return Err(ArithmeticFiberError::EvenReciprocityPrime);
        }
        let (lower, upper) = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        let lower_receives_upper = self.quadratic_fiber(lower, BigInt::from(upper))?;
        let upper_receives_lower = self.quadratic_fiber(upper, BigInt::from(lower))?;
        let observed_hand = lower_receives_upper.character * upper_receives_lower.character;
        if !matches!(observed_hand, -1 | 1) {
            return Err(ArithmeticFiberError::DegenerateReciprocityFiber {
                left: lower,
                right: upper,
            });
        }
        Ok(PairedQuadraticFiber {
            schema: "holonic-engine.paired-quadratic-fiber.v1".to_owned(),
            lower_prime: lower,
            upper_prime: upper,
            lower_receives_upper,
            upper_receives_lower,
            observed_hand,
        })
    }

    pub fn validate(&self) -> Result<(), ArithmeticFiberError> {
        self.incidence.validate()?;
        if self.schema != "holonic-engine.arithmetic-fiber-standing.v2" {
            return Err(ArithmeticFiberError::MalformedArithmeticStanding);
        }
        if self.value == 0 {
            return Err(ArithmeticFiberError::InvalidStandingValue);
        }
        let expected_values = if self.value < 2 {
            BTreeSet::new()
        } else {
            (2..=self.value).collect()
        };
        let supplied_values = self.occurrences.keys().copied().collect::<BTreeSet<_>>();
        if expected_values != supplied_values {
            return Err(ArithmeticFiberError::OccurrenceChronologyMismatch);
        }
        let occurrence_events = self
            .occurrences
            .values()
            .map(|occurrence| occurrence.event)
            .collect::<BTreeSet<_>>();
        if occurrence_events.len() != self.occurrences.len()
            || occurrence_events != self.used_events
        {
            return Err(ArithmeticFiberError::OccurrenceEventMismatch);
        }
        if self.recognitions.keys().copied().collect::<BTreeSet<_>>() != expected_values {
            return Err(ArithmeticFiberError::RecognitionChronologyMismatch);
        }

        for (prime, cell) in &self.prime_cells {
            if *prime < 2 {
                return Err(ArithmeticFiberError::InvalidPrimeIdentity(*prime));
            }
            if self.squarefree_cells.get(&vec![*prime]) != Some(cell) {
                return Err(ArithmeticFiberError::PrimeCellMismatch(*prime));
            }
            let body = self.incidence.cell(*cell)?;
            if body.grade != 0 || !body.boundary.is_zero() {
                return Err(ArithmeticFiberError::PrimeCellMismatch(*prime));
            }
            for earlier in self
                .prime_cells
                .keys()
                .take_while(|earlier| *earlier < prime)
            {
                if earlier <= &(prime / earlier) && prime.is_multiple_of(*earlier) {
                    return Err(ArithmeticFiberError::InvalidPrimeIdentity(*prime));
                }
            }
        }

        for (support, cell) in &self.squarefree_cells {
            if support.is_empty()
                || support.windows(2).any(|pair| pair[0] >= pair[1])
                || support
                    .iter()
                    .any(|prime| !self.prime_cells.contains_key(prime))
            {
                return Err(ArithmeticFiberError::MalformedSquarefreeSupport(
                    support.clone(),
                ));
            }
            let grade = u32::try_from(support.len() - 1)
                .map_err(|_| ArithmeticFiberError::CarrierOverflow)?;
            let body = self.incidence.cell(*cell)?;
            if body.grade != grade {
                return Err(ArithmeticFiberError::SquarefreeGradeMismatch {
                    support: support.clone(),
                    expected: grade,
                    supplied: body.grade,
                });
            }
            let expected_boundary = squarefree_boundary(support, &self.squarefree_cells)?;
            if body.boundary != expected_boundary {
                return Err(ArithmeticFiberError::SquarefreeBoundaryMismatch(
                    support.clone(),
                ));
            }
            let squarefree_product = support.iter().try_fold(1_u64, |product, prime| {
                product
                    .checked_mul(*prime)
                    .ok_or(ArithmeticFiberError::CarrierOverflow)
            })?;
            let founding = self
                .occurrences
                .get(&squarefree_product)
                .ok_or_else(|| ArithmeticFiberError::SquarefreeFoundingMismatch(support.clone()))?;
            if founding.squarefree_support != *support
                || founding.support_cell != *cell
                || body.source_events != BTreeSet::from([founding.event])
            {
                return Err(ArithmeticFiberError::SquarefreeFoundingMismatch(
                    support.clone(),
                ));
            }
        }

        for (value, occurrence) in &self.occurrences {
            if occurrence.value != *value
                || occurrence.value < 2
                || occurrence.valuation.is_empty()
                || occurrence
                    .valuation
                    .iter()
                    .any(|valuation| valuation.exponent == 0)
            {
                return Err(ArithmeticFiberError::MalformedOccurrence(*value));
            }
            let support = occurrence
                .valuation
                .iter()
                .map(|valuation| valuation.prime)
                .collect::<Vec<_>>();
            if support != occurrence.squarefree_support
                || support.windows(2).any(|pair| pair[0] >= pair[1])
                || self.squarefree_cells.get(&support) != Some(&occurrence.support_cell)
            {
                return Err(ArithmeticFiberError::MalformedOccurrence(*value));
            }
            let mut product = 1_u64;
            for valuation in &occurrence.valuation {
                if !self.prime_cells.contains_key(&valuation.prime) {
                    return Err(ArithmeticFiberError::MalformedOccurrence(*value));
                }
                for _ in 0..valuation.exponent {
                    product = product
                        .checked_mul(valuation.prime)
                        .ok_or(ArithmeticFiberError::CarrierOverflow)?;
                }
            }
            if product != *value {
                return Err(ArithmeticFiberError::MalformedOccurrence(*value));
            }
            let probes = prime_horizon_probes(*value, &self.prime_cells);
            let expected_recognition = derive_prime_recognition(*value, &probes)?;
            if self.recognitions.get(value) != Some(&expected_recognition) {
                return Err(ArithmeticFiberError::MalformedPrimeRecognition(*value));
            }
            match &expected_recognition.closure {
                PrimeRecognitionClosure::Composite { witness } => {
                    if witness.exact_product != *value
                        || (occurrence.valuation.len() == 1
                            && occurrence.valuation[0].prime == *value)
                    {
                        return Err(ArithmeticFiberError::MalformedPrimeRecognition(*value));
                    }
                }
                PrimeRecognitionClosure::Irreducible { .. } => {
                    if occurrence.valuation
                        != vec![PrimeValuation {
                            prime: *value,
                            exponent: 1,
                        }]
                    {
                        return Err(ArithmeticFiberError::MalformedPrimeRecognition(*value));
                    }
                }
            }
        }

        let mut expected_current = PrimePowerCurrent::default();
        for occurrence in self.occurrences.values() {
            expected_current.advance(occurrence)?;
        }
        if self.prime_power_current != expected_current {
            return Err(ArithmeticFiberError::MalformedPrimePowerCurrent);
        }
        Ok(())
    }

    fn enact(
        &mut self,
        event: &ArithmeticFiberEvent,
    ) -> Result<ArithmeticFiberRadiation, ArithmeticFiberError> {
        let expected = self
            .value
            .checked_add(1)
            .ok_or(ArithmeticFiberError::CarrierOverflow)?;
        if event.value != expected {
            return Err(ArithmeticFiberError::NonSuccessor {
                expected,
                supplied: event.value,
            });
        }
        if self.used_events.contains(&event.event) {
            return Err(ArithmeticFiberError::RepeatedEvent(event.event));
        }

        let probes = prime_horizon_probes(event.value, &self.prime_cells);
        let recognition = derive_prime_recognition(event.value, &probes)?;
        let (mut valuation, residual) = factor_through_founded_axes(event.value, &self.prime_cells);
        let mut founded_prime = None;
        let mut founded_cells = Vec::new();

        if recognition.is_irreducible() {
            if residual != event.value {
                return Err(ArithmeticFiberError::PrimeFoundingContradiction(
                    event.value,
                ));
            }
            let cell = self.incidence.found_cell(
                format!("prime[{}]", event.value),
                BTreeSet::from([event.event]),
                0,
                CausalChain::default(),
            )?;
            self.prime_cells.insert(event.value, cell);
            self.squarefree_cells.insert(vec![event.value], cell);
            valuation.push(PrimeValuation {
                prime: event.value,
                exponent: 1,
            });
            let failed_axes = match &recognition.closure {
                PrimeRecognitionClosure::Irreducible { failed_axes } => failed_axes.clone(),
                PrimeRecognitionClosure::Composite { .. } => unreachable!(),
            };
            founded_prime = Some(FoundedPrime {
                prime: event.value,
                cell,
                failed_axes,
            });
            founded_cells.push(FoundedMultiplicativeCell {
                squarefree_support: vec![event.value],
                cell,
                grade: 0,
            });
        } else {
            if residual == event.value {
                return Err(ArithmeticFiberError::PrimeFoundingContradiction(
                    event.value,
                ));
            }
            if residual > 1 {
                if !self.prime_cells.contains_key(&residual) {
                    return Err(ArithmeticFiberError::UnfoundedResidualPrime(residual));
                }
                valuation.push(PrimeValuation {
                    prime: residual,
                    exponent: 1,
                });
            }
        }
        valuation.sort_by_key(|factor| factor.prime);
        let support = valuation
            .iter()
            .map(|factor| factor.prime)
            .collect::<Vec<_>>();
        if support.is_empty() {
            return Err(ArithmeticFiberError::MalformedOccurrence(event.value));
        }

        for size in 2..=support.len() {
            for subset in combinations(&support, size) {
                if self.squarefree_cells.contains_key(&subset) {
                    continue;
                }
                let boundary = squarefree_boundary(&subset, &self.squarefree_cells)?;
                let grade =
                    u32::try_from(size - 1).map_err(|_| ArithmeticFiberError::CarrierOverflow)?;
                let name = format!(
                    "multiplicative[{}]",
                    subset
                        .iter()
                        .map(u64::to_string)
                        .collect::<Vec<_>>()
                        .join("*")
                );
                let cell = self.incidence.found_cell(
                    name,
                    BTreeSet::from([event.event]),
                    grade,
                    boundary,
                )?;
                self.squarefree_cells.insert(subset.clone(), cell);
                founded_cells.push(FoundedMultiplicativeCell {
                    squarefree_support: subset,
                    cell,
                    grade,
                });
            }
        }
        let support_cell = self.squarefree_cells[&support];
        let occurrence = ArithmeticOccurrence {
            event: event.event,
            value: event.value,
            valuation,
            squarefree_support: support,
            support_cell,
        };
        self.value = event.value;
        self.used_events.insert(event.event);
        self.occurrences.insert(event.value, occurrence.clone());
        self.recognitions.insert(event.value, recognition.clone());
        let prime_power_event = self.prime_power_current.advance(&occurrence)?;
        self.validate()?;
        Ok(ArithmeticFiberRadiation {
            schema: "holonic-engine.arithmetic-fiber-radiation.v2".to_owned(),
            event: event.event,
            value: event.value,
            probes,
            recognition,
            founded_prime,
            founded_cells,
            occurrence,
            prime_power_event,
            prime_power_current: self.prime_power_current.clone(),
        })
    }
}

fn prime_horizon_probes(
    value: u64,
    prime_cells: &BTreeMap<u64, CausalCellId>,
) -> Vec<PrimeAxisProbe> {
    prime_cells
        .keys()
        .take_while(|prime| **prime <= value / **prime)
        .map(|prime| PrimeAxisProbe {
            prime_axis: *prime,
            quotient: value / *prime,
            remainder: value % *prime,
        })
        .collect()
}

fn recognition_dispositions(
    remains_open: bool,
    irreducible: bool,
) -> BTreeSet<PrimeRecognitionDisposition> {
    match (remains_open, irreducible) {
        (true, _) => BTreeSet::from([
            PrimeRecognitionDisposition::Irreducible,
            PrimeRecognitionDisposition::Composite,
        ]),
        (false, true) => BTreeSet::from([PrimeRecognitionDisposition::Irreducible]),
        (false, false) => BTreeSet::from([PrimeRecognitionDisposition::Composite]),
    }
}

fn continuation_fiber(
    after_probe_count: u64,
    admissible_dispositions: BTreeSet<PrimeRecognitionDisposition>,
    unreturned_factor_axes: Vec<u64>,
) -> PrimeContinuationFiber {
    PrimeContinuationFiber {
        schema: "holonic-engine.prime-continuation-fiber.v1".to_owned(),
        after_probe_count,
        admissible_dispositions,
        unreturned_factor_axes,
    }
}

fn derive_prime_recognition(
    candidate: u64,
    probes: &[PrimeAxisProbe],
) -> Result<PrimeRecognitionTrace, ArithmeticFiberError> {
    let horizon_count =
        u64::try_from(probes.len()).map_err(|_| ArithmeticFiberError::CarrierOverflow)?;
    let initial_fiber = continuation_fiber(
        0,
        recognition_dispositions(!probes.is_empty(), probes.is_empty()),
        probes.iter().map(|probe| probe.prime_axis).collect(),
    );
    let mut steps = Vec::new();
    let mut failed_axes = Vec::new();
    let mut obstruction = None;
    let mut closure = None;

    for (index, probe) in probes.iter().enumerate() {
        let depth = u64::try_from(index + 1).map_err(|_| ArithmeticFiberError::CarrierOverflow)?;
        let unreturned_factor_axes = probes[index + 1..]
            .iter()
            .map(|remaining| remaining.prime_axis)
            .collect::<Vec<_>>();
        if probe.remainder == 0 {
            let exact_product = probe
                .prime_axis
                .checked_mul(probe.quotient)
                .ok_or(ArithmeticFiberError::CarrierOverflow)?;
            if exact_product != candidate {
                return Err(ArithmeticFiberError::MalformedPrimeRecognition(candidate));
            }
            let witness = PrimeFactorWitness {
                prime_axis: probe.prime_axis,
                cofactor: probe.quotient,
                exact_product,
            };
            steps.push(PrimeRecognitionStep {
                depth,
                probe: probe.clone(),
                fiber_after: continuation_fiber(
                    depth,
                    recognition_dispositions(false, false),
                    unreturned_factor_axes,
                ),
            });
            obstruction = Some(PrimeIrreducibilityObstruction {
                schema: "holonic-engine.prime-irreducibility-obstruction.v1".to_owned(),
                depth,
                witness: witness.clone(),
            });
            closure = Some(PrimeRecognitionClosure::Composite { witness });
            break;
        }

        failed_axes.push(probe.prime_axis);
        let remains_open = !unreturned_factor_axes.is_empty();
        steps.push(PrimeRecognitionStep {
            depth,
            probe: probe.clone(),
            fiber_after: continuation_fiber(
                depth,
                recognition_dispositions(remains_open, !remains_open),
                unreturned_factor_axes,
            ),
        });
    }

    let closure = closure.unwrap_or(PrimeRecognitionClosure::Irreducible { failed_axes });
    let enacted_depth =
        u64::try_from(steps.len()).map_err(|_| ArithmeticFiberError::CarrierOverflow)?;
    Ok(PrimeRecognitionTrace {
        schema: "holonic-engine.prime-recognition-trace.v1".to_owned(),
        candidate,
        initial_fiber,
        steps,
        closure,
        bounds: PrimeRecognitionBounds {
            factor_horizon_axis_count: horizon_count,
            distinguishing_probe_lower_bound: enacted_depth,
            certificate_probe_upper_bound: enacted_depth,
        },
        irreducibility_obstruction: obstruction,
    })
}

fn factor_through_founded_axes(
    value: u64,
    prime_cells: &BTreeMap<u64, CausalCellId>,
) -> (Vec<PrimeValuation>, u64) {
    let mut remaining = value;
    let mut factors = Vec::new();
    for prime in prime_cells.keys() {
        if *prime > remaining / *prime {
            break;
        }
        if !remaining.is_multiple_of(*prime) {
            continue;
        }
        let mut exponent = 0;
        while remaining.is_multiple_of(*prime) {
            remaining /= *prime;
            exponent += 1;
        }
        factors.push(PrimeValuation {
            prime: *prime,
            exponent,
        });
    }
    (factors, remaining)
}

fn combinations(population: &[u64], size: usize) -> Vec<Vec<u64>> {
    fn visit(
        population: &[u64],
        remaining: usize,
        next: usize,
        prefix: &mut Vec<u64>,
        result: &mut Vec<Vec<u64>>,
    ) {
        if remaining == 0 {
            result.push(prefix.clone());
            return;
        }
        let final_start = population.len().saturating_sub(remaining);
        for member in next..=final_start {
            prefix.push(population[member]);
            visit(population, remaining - 1, member + 1, prefix, result);
            prefix.pop();
        }
    }

    let mut result = Vec::new();
    visit(
        population,
        size,
        0,
        &mut Vec::with_capacity(size),
        &mut result,
    );
    result
}

fn squarefree_boundary(
    support: &[u64],
    cells: &BTreeMap<Vec<u64>, CausalCellId>,
) -> Result<CausalChain, ArithmeticFiberError> {
    if support.len() == 1 {
        return Ok(CausalChain::default());
    }
    let mut boundary = CausalChain::default();
    for removed in 0..support.len() {
        let mut face = support.to_vec();
        face.remove(removed);
        let cell = cells
            .get(&face)
            .copied()
            .ok_or_else(|| ArithmeticFiberError::MissingSquarefreeFace(face.clone()))?;
        boundary.add_term(
            cell,
            ComparativeMultiplicity::from_hand(if removed % 2 == 0 { 1 } else { -1 }, 1_u8)?,
        );
    }
    Ok(boundary)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticFiberEvent {
    pub event: EventId,
    pub value: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticFiberRadiation {
    pub schema: String,
    pub event: EventId,
    pub value: u64,
    pub probes: Vec<PrimeAxisProbe>,
    pub recognition: PrimeRecognitionTrace,
    pub founded_prime: Option<FoundedPrime>,
    pub founded_cells: Vec<FoundedMultiplicativeCell>,
    pub occurrence: ArithmeticOccurrence,
    pub prime_power_event: Option<PrimePowerCurrentEvent>,
    pub prime_power_current: PrimePowerCurrent,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ArithmeticFiberLaw;

impl ExactEventLaw for ArithmeticFiberLaw {
    type Standing = ArithmeticFiberStanding;
    type Event = ArithmeticFiberEvent;
    type Radiation = ArithmeticFiberRadiation;
    type Error = ArithmeticFiberError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.validate()?;
        let mut standing_after = standing_before.clone();
        let radiation = standing_after.enact(event)?;
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuadraticPrimeFiber {
    pub schema: String,
    pub prime: u64,
    pub prime_cell: CausalCellId,
    pub radicand: BigInt,
    pub residue: u64,
    pub roots: Vec<u64>,
    /// Exactly `number_of_roots - 1` for an odd prime fiber.
    pub character: i8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuadraticFiberIsomorphism {
    pub schema: String,
    pub scale: u64,
    pub inverse_scale: u64,
    pub source: QuadraticPrimeFiber,
    pub target: QuadraticPrimeFiber,
    pub mapped_roots: Vec<u64>,
    pub reverse_mapped_roots: Vec<u64>,
    pub exact_forward_residuals: Vec<u64>,
    pub exact_reverse_residuals: Vec<u64>,
    pub character_preserved: bool,
}

impl QuadraticPrimeFiber {
    pub fn validate(&self) -> Result<(), ArithmeticFiberError> {
        if self.prime < 3 || self.prime.is_multiple_of(2) {
            return Err(ArithmeticFiberError::EvenQuadraticPrime);
        }
        let expected_residue = normalized_mod(&self.radicand, &BigInt::from(self.prime))
            .to_u64()
            .ok_or(ArithmeticFiberError::CarrierOverflow)?;
        if self.residue != expected_residue
            || self.roots.windows(2).any(|roots| roots[0] >= roots[1])
            || self.roots.iter().any(|root| {
                *root >= self.prime || mul_mod(*root, *root, self.prime) != self.residue
            })
        {
            return Err(ArithmeticFiberError::QuadraticRootFailure);
        }
        if i8::try_from(self.roots.len()).map_err(|_| ArithmeticFiberError::CarrierOverflow)? - 1
            != self.character
            || !matches!(self.character, -1..=1)
        {
            return Err(ArithmeticFiberError::QuadraticRootCountFailure);
        }
        Ok(())
    }

    /// Re-present `x^2 = a` as `y^2 = u^2 a` through the receiver-local
    /// coordinate isomorphism `y = u x`, where `u` is a nonzero field unit.
    pub fn unit_scale(
        &self,
        scale: u64,
    ) -> Result<QuadraticFiberIsomorphism, ArithmeticFiberError> {
        self.validate()?;
        let scale = scale % self.prime;
        if scale == 0 {
            return Err(ArithmeticFiberError::NonunitQuadraticScale);
        }
        let inverse_scale = pow_mod(scale, self.prime - 2, self.prime);
        let target_radicand = &self.radicand * BigInt::from(scale) * BigInt::from(scale);
        let target = quadratic_prime_fiber(self.prime, self.prime_cell, target_radicand)?;
        let mut mapped_roots = self
            .roots
            .iter()
            .map(|root| mul_mod(scale, *root, self.prime))
            .collect::<Vec<_>>();
        mapped_roots.sort_unstable();
        mapped_roots.dedup();
        let mut reverse_mapped_roots = target
            .roots
            .iter()
            .map(|root| mul_mod(inverse_scale, *root, self.prime))
            .collect::<Vec<_>>();
        reverse_mapped_roots.sort_unstable();
        reverse_mapped_roots.dedup();
        let exact_forward_residuals = mapped_roots
            .iter()
            .map(|root| {
                modular_difference(
                    mul_mod(*root, *root, self.prime),
                    target.residue,
                    self.prime,
                )
            })
            .collect::<Vec<_>>();
        let exact_reverse_residuals = reverse_mapped_roots
            .iter()
            .map(|root| {
                modular_difference(mul_mod(*root, *root, self.prime), self.residue, self.prime)
            })
            .collect::<Vec<_>>();
        if mapped_roots != target.roots
            || reverse_mapped_roots != self.roots
            || exact_forward_residuals
                .iter()
                .any(|residual| *residual != 0)
            || exact_reverse_residuals
                .iter()
                .any(|residual| *residual != 0)
        {
            return Err(ArithmeticFiberError::QuadraticIsomorphismFailure);
        }
        Ok(QuadraticFiberIsomorphism {
            schema: "holonic-engine.quadratic-fiber-isomorphism.v1".to_owned(),
            scale,
            inverse_scale,
            source: self.clone(),
            character_preserved: self.character == target.character,
            target,
            mapped_roots,
            reverse_mapped_roots,
            exact_forward_residuals,
            exact_reverse_residuals,
        })
    }
}

fn quadratic_prime_fiber(
    prime: u64,
    prime_cell: CausalCellId,
    radicand: BigInt,
) -> Result<QuadraticPrimeFiber, ArithmeticFiberError> {
    if prime == 2 {
        return Err(ArithmeticFiberError::EvenQuadraticPrime);
    }
    let modulus = BigInt::from(prime);
    let residue = normalized_mod(&radicand, &modulus)
        .to_u64()
        .ok_or(ArithmeticFiberError::CarrierOverflow)?;
    let (mut roots, character) = if residue == 0 {
        (vec![0], 0)
    } else {
        let legendre = pow_mod(residue, (prime - 1) / 2, prime);
        if legendre == prime - 1 {
            (Vec::new(), -1)
        } else if legendre == 1 {
            let root = tonelli_shanks(residue, prime)?;
            let other = prime - root;
            let mut roots = vec![root, other];
            roots.sort_unstable();
            roots.dedup();
            (roots, 1)
        } else {
            return Err(ArithmeticFiberError::InvalidQuadraticCharacter {
                prime,
                residue,
                witness: legendre,
            });
        }
    };
    roots.sort_unstable();
    if roots
        .iter()
        .any(|root| mul_mod(*root, *root, prime) != residue)
    {
        return Err(ArithmeticFiberError::QuadraticRootFailure);
    }
    if i8::try_from(roots.len()).map_err(|_| ArithmeticFiberError::CarrierOverflow)? - 1
        != character
    {
        return Err(ArithmeticFiberError::QuadraticRootCountFailure);
    }
    Ok(QuadraticPrimeFiber {
        schema: "holonic-engine.quadratic-prime-fiber.v1".to_owned(),
        prime,
        prime_cell,
        radicand,
        residue,
        roots,
        character,
    })
}

fn mul_mod(left: u64, right: u64, modulus: u64) -> u64 {
    ((u128::from(left) * u128::from(right)) % u128::from(modulus)) as u64
}

fn modular_difference(left: u64, right: u64, modulus: u64) -> u64 {
    if left >= right {
        left - right
    } else {
        modulus - (right - left)
    }
}

fn pow_mod(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut result = 1 % modulus;
    base %= modulus;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = mul_mod(result, base, modulus);
        }
        base = mul_mod(base, base, modulus);
        exponent >>= 1;
    }
    result
}

fn tonelli_shanks(residue: u64, prime: u64) -> Result<u64, ArithmeticFiberError> {
    if prime % 4 == 3 {
        return Ok(pow_mod(residue, (prime + 1) / 4, prime));
    }
    let mut odd = prime - 1;
    let mut power = 0_u32;
    while odd.is_multiple_of(2) {
        odd /= 2;
        power += 1;
    }
    let nonresidue = (2..prime)
        .find(|candidate| pow_mod(*candidate, (prime - 1) / 2, prime) == prime - 1)
        .ok_or(ArithmeticFiberError::MissingQuadraticNonresidue(prime))?;
    let mut coefficient = pow_mod(nonresidue, odd, prime);
    let mut root = pow_mod(residue, odd.div_ceil(2), prime);
    let mut remainder = pow_mod(residue, odd, prime);
    let mut remaining_power = power;
    while remainder != 1 {
        let mut cursor = mul_mod(remainder, remainder, prime);
        let mut index = 1_u32;
        while cursor != 1 && index < remaining_power {
            cursor = mul_mod(cursor, cursor, prime);
            index += 1;
        }
        if index >= remaining_power {
            return Err(ArithmeticFiberError::TonelliFailure { prime, residue });
        }
        let exponent = 1_u64
            .checked_shl(remaining_power - index - 1)
            .ok_or(ArithmeticFiberError::CarrierOverflow)?;
        let adjustment = pow_mod(coefficient, exponent, prime);
        root = mul_mod(root, adjustment, prime);
        let square = mul_mod(adjustment, adjustment, prime);
        remainder = mul_mod(remainder, square, prime);
        coefficient = square;
        remaining_power = index;
    }
    Ok(root)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum QuadraticHenselBranch {
    NoLift,
    Unique {
        digit: u64,
        root: BigInt,
        exact_residual: BigInt,
    },
    FullFiber {
        base_root: BigInt,
        stride: BigInt,
        digit_count: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuadraticHenselStep {
    pub schema: String,
    pub prime: u64,
    pub exponent_before: u32,
    pub modulus_before: BigInt,
    pub modulus_after: BigInt,
    pub radicand: BigInt,
    pub root_before: BigInt,
    pub derivative_mod_prime: u64,
    pub quotient_mod_prime: u64,
    pub branch: QuadraticHenselBranch,
}

fn lift_quadratic_root(
    prime: u64,
    exponent_before: u32,
    radicand: impl Into<BigInt>,
    root: impl Into<BigInt>,
) -> Result<QuadraticHenselStep, ArithmeticFiberError> {
    if prime < 2 || exponent_before == 0 {
        return Err(ArithmeticFiberError::InvalidHenselBase);
    }
    let radicand = radicand.into();
    let modulus_before = BigInt::from(prime).pow(exponent_before);
    let modulus_after = &modulus_before * prime;
    let root_before = normalized_mod(&root.into(), &modulus_before);
    let function = &root_before * &root_before - &radicand;
    if !normalized_mod(&function, &modulus_before).is_zero() {
        return Err(ArithmeticFiberError::NotQuadraticRoot {
            modulus: modulus_before,
        });
    }
    let prime_modulus = BigInt::from(prime);
    let derivative_mod_prime = normalized_mod(&(&root_before * 2), &prime_modulus)
        .to_u64()
        .ok_or(ArithmeticFiberError::CarrierOverflow)?;
    let quotient_mod_prime = normalized_mod(&(function / &modulus_before), &prime_modulus)
        .to_u64()
        .ok_or(ArithmeticFiberError::CarrierOverflow)?;
    let branch = if derivative_mod_prime == 0 {
        if quotient_mod_prime == 0 {
            QuadraticHenselBranch::FullFiber {
                base_root: root_before.clone(),
                stride: modulus_before.clone(),
                digit_count: prime,
            }
        } else {
            QuadraticHenselBranch::NoLift
        }
    } else {
        let inverse = pow_mod(derivative_mod_prime, prime - 2, prime);
        let negative = if quotient_mod_prime == 0 {
            0
        } else {
            prime - quotient_mod_prime
        };
        let digit = mul_mod(negative, inverse, prime);
        let lifted = &root_before + &modulus_before * digit;
        let exact_residual = normalized_mod(&(&lifted * &lifted - &radicand), &modulus_after);
        if !exact_residual.is_zero() {
            return Err(ArithmeticFiberError::HenselResidualFailure);
        }
        QuadraticHenselBranch::Unique {
            digit,
            root: lifted,
            exact_residual,
        }
    };
    Ok(QuadraticHenselStep {
        schema: "holonic-engine.quadratic-hensel-step.v1".to_owned(),
        prime,
        exponent_before,
        modulus_before,
        modulus_after,
        radicand,
        root_before,
        derivative_mod_prime,
        quotient_mod_prime,
        branch,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuadraticHenselPath {
    pub root_mod_prime: u64,
    pub steps: Vec<QuadraticHenselStep>,
    /// False means an exact branching family or no-lift boundary was reached;
    /// it does not mean the preceding receipts were approximate.
    pub reached_target: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuadraticHenselTower {
    pub schema: String,
    pub fiber: QuadraticPrimeFiber,
    pub target_exponent: u32,
    pub paths: Vec<QuadraticHenselPath>,
}

impl QuadraticPrimeFiber {
    pub fn lift_root(
        &self,
        exponent_before: u32,
        root: impl Into<BigInt>,
    ) -> Result<QuadraticHenselStep, ArithmeticFiberError> {
        self.validate()?;
        lift_quadratic_root(
            self.prime,
            exponent_before,
            self.radicand.clone(),
            root.into(),
        )
    }

    pub fn hensel_tower(
        &self,
        target_exponent: u32,
    ) -> Result<QuadraticHenselTower, ArithmeticFiberError> {
        self.validate()?;
        if target_exponent == 0 {
            return Err(ArithmeticFiberError::InvalidHenselBase);
        }
        let mut paths = Vec::new();
        for root in &self.roots {
            let mut steps = Vec::new();
            let mut current = BigInt::from(*root);
            let mut reached_target = true;
            for exponent in 1..target_exponent {
                let step = lift_quadratic_root(
                    self.prime,
                    exponent,
                    self.radicand.clone(),
                    current.clone(),
                )?;
                match &step.branch {
                    QuadraticHenselBranch::Unique { root, .. } => {
                        current = root.clone();
                    }
                    QuadraticHenselBranch::NoLift | QuadraticHenselBranch::FullFiber { .. } => {
                        reached_target = false;
                        steps.push(step);
                        break;
                    }
                }
                steps.push(step);
            }
            paths.push(QuadraticHenselPath {
                root_mod_prime: *root,
                steps,
                reached_target,
            });
        }
        Ok(QuadraticHenselTower {
            schema: "holonic-engine.quadratic-hensel-tower.v1".to_owned(),
            fiber: self.clone(),
            target_exponent,
            paths,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCongruence {
    pub residue: BigInt,
    pub modulus: BigInt,
}

impl ExactCongruence {
    pub fn new(
        residue: impl Into<BigInt>,
        modulus: impl Into<BigInt>,
    ) -> Result<Self, ArithmeticFiberError> {
        let modulus = modulus.into();
        if !modulus.is_positive() {
            return Err(ArithmeticFiberError::NonpositiveModulus);
        }
        Ok(Self {
            residue: normalized_mod(&residue.into(), &modulus),
            modulus,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChineseRemainderReceipt {
    pub schema: String,
    pub left: ExactCongruence,
    pub right: ExactCongruence,
    pub bezout_left: BigInt,
    pub bezout_right: BigInt,
    pub bezout_residual: BigInt,
    pub combined: ExactCongruence,
    pub left_residual: BigInt,
    pub right_residual: BigInt,
}

pub fn chinese_remainder_pair(
    left: ExactCongruence,
    right: ExactCongruence,
) -> Result<ChineseRemainderReceipt, ArithmeticFiberError> {
    let (gcd, bezout_left, bezout_right) =
        extended_gcd(left.modulus.clone(), right.modulus.clone());
    if gcd != BigInt::one() {
        return Err(ArithmeticFiberError::NoncoprimeModuli(gcd));
    }
    let bezout_residual =
        &bezout_left * &left.modulus + &bezout_right * &right.modulus - BigInt::one();
    if !bezout_residual.is_zero() {
        return Err(ArithmeticFiberError::BezoutFailure);
    }
    let correction = normalized_mod(
        &((&right.residue - &left.residue) * &bezout_left),
        &right.modulus,
    );
    let modulus = &left.modulus * &right.modulus;
    let residue = normalized_mod(&(&left.residue + &left.modulus * correction), &modulus);
    let combined = ExactCongruence { residue, modulus };
    let left_residual = normalized_mod(&(&combined.residue - &left.residue), &left.modulus);
    let right_residual = normalized_mod(&(&combined.residue - &right.residue), &right.modulus);
    if !left_residual.is_zero() || !right_residual.is_zero() {
        return Err(ArithmeticFiberError::ChineseRemainderFailure);
    }
    Ok(ChineseRemainderReceipt {
        schema: "holonic-engine.chinese-remainder-receipt.v1".to_owned(),
        left,
        right,
        bezout_left,
        bezout_right,
        bezout_residual,
        combined,
        left_residual,
        right_residual,
    })
}

fn extended_gcd(left: BigInt, right: BigInt) -> (BigInt, BigInt, BigInt) {
    let (mut old_remainder, mut remainder) = (left, right);
    let (mut old_left, mut left_coefficient) = (BigInt::one(), BigInt::zero());
    let (mut old_right, mut right_coefficient) = (BigInt::zero(), BigInt::one());
    while !remainder.is_zero() {
        let quotient = &old_remainder / &remainder;
        (old_remainder, remainder) = (remainder.clone(), old_remainder - &quotient * &remainder);
        (old_left, left_coefficient) = (
            left_coefficient.clone(),
            old_left - &quotient * &left_coefficient,
        );
        (old_right, right_coefficient) = (
            right_coefficient.clone(),
            old_right - quotient * &right_coefficient,
        );
    }
    if old_remainder.is_negative() {
        (-old_remainder, -old_left, -old_right)
    } else {
        (old_remainder, old_left, old_right)
    }
}

fn normalized_mod(value: &BigInt, modulus: &BigInt) -> BigInt {
    let residue = value % modulus;
    if residue.is_negative() {
        residue + modulus
    } else {
        residue
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PairedQuadraticFiber {
    pub schema: String,
    pub lower_prime: u64,
    pub upper_prime: u64,
    pub lower_receives_upper: QuadraticPrimeFiber,
    pub upper_receives_lower: QuadraticPrimeFiber,
    /// The comparison inferred from the two root populations.
    pub observed_hand: i8,
}

impl PairedQuadraticFiber {
    pub fn validate(&self) -> Result<(), ArithmeticFiberError> {
        self.lower_receives_upper.validate()?;
        self.upper_receives_lower.validate()?;
        if self.lower_prime >= self.upper_prime
            || self.lower_prime == 2
            || self.lower_receives_upper.prime != self.lower_prime
            || self.upper_receives_lower.prime != self.upper_prime
            || self.lower_receives_upper.radicand != BigInt::from(self.upper_prime)
            || self.upper_receives_lower.radicand != BigInt::from(self.lower_prime)
            || self.observed_hand
                != self.lower_receives_upper.character * self.upper_receives_lower.character
            || !matches!(self.observed_hand, -1 | 1)
        {
            return Err(ArithmeticFiberError::MalformedPairedFiber {
                left: self.lower_prime,
                right: self.upper_prime,
            });
        }
        Ok(())
    }

    pub fn validate_against(
        &self,
        standing: &ArithmeticFiberStanding,
    ) -> Result<(), ArithmeticFiberError> {
        self.validate()?;
        if standing.prime_cell(self.lower_prime)? != self.lower_receives_upper.prime_cell
            || standing.prime_cell(self.upper_prime)? != self.upper_receives_lower.prime_cell
        {
            return Err(ArithmeticFiberError::PairedFiberSourceMismatch {
                left: self.lower_prime,
                right: self.upper_prime,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ResiduePair {
    pub lower: u64,
    pub upper: u64,
}

impl ResiduePair {
    fn new(left: u64, right: u64) -> Self {
        if left <= right {
            Self {
                lower: left,
                upper: right,
            }
        } else {
            Self {
                lower: right,
                upper: left,
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResidueTransportLaw {
    pub schema: String,
    pub modulus: u64,
    pub grammar_bound: u64,
    pub hands: BTreeMap<ResiduePair, i8>,
    pub evidence_pairs: usize,
}

impl ResidueTransportLaw {
    pub fn validate(&self) -> Result<(), ArithmeticFiberError> {
        let output_hands = self.hands.values().copied().collect::<BTreeSet<_>>();
        if self.modulus < 2
            || self.grammar_bound < self.modulus
            || self.evidence_pairs == 0
            || self
                .hands
                .keys()
                .any(|pair| pair.lower > pair.upper || pair.upper >= self.modulus)
            || output_hands != BTreeSet::from([-1, 1])
        {
            return Err(ArithmeticFiberError::MalformedResidueTransport);
        }
        Ok(())
    }

    pub fn receive(
        &self,
        left: u64,
        right: u64,
    ) -> Result<ResidueTransportRead, ArithmeticFiberError> {
        self.validate()?;
        let residue_pair = ResiduePair::new(left % self.modulus, right % self.modulus);
        Ok(ResidueTransportRead {
            left,
            right,
            residue_pair,
            predicted_hand: self.hands.get(&residue_pair).copied(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResidueTransportRead {
    pub left: u64,
    pub right: u64,
    pub residue_pair: ResiduePair,
    pub predicted_hand: Option<i8>,
}

pub fn discover_residue_transport(
    standing: &ArithmeticFiberStanding,
    evidence: &[PairedQuadraticFiber],
    grammar_bound: u64,
) -> Result<ResidueTransportLaw, ArithmeticFiberError> {
    standing.validate()?;
    if evidence.is_empty() {
        return Err(ArithmeticFiberError::EmptyTransportEvidence);
    }
    if grammar_bound < 2 {
        return Err(ArithmeticFiberError::InvalidGrammarBound(grammar_bound));
    }
    for modulus in 2..=grammar_bound {
        let mut hands = BTreeMap::new();
        let mut valid = true;
        for pair in evidence {
            pair.validate_against(standing)?;
            let bucket = ResiduePair::new(pair.lower_prime % modulus, pair.upper_prime % modulus);
            match hands.get(&bucket) {
                Some(existing) if *existing != pair.observed_hand => {
                    valid = false;
                    break;
                }
                Some(_) => {}
                None => {
                    hands.insert(bucket, pair.observed_hand);
                }
            }
        }
        let output_hands = hands.values().copied().collect::<BTreeSet<_>>();
        if valid && output_hands == BTreeSet::from([-1, 1]) {
            return Ok(ResidueTransportLaw {
                schema: "holonic-engine.residue-transport-law.v1".to_owned(),
                modulus,
                grammar_bound,
                hands,
                evidence_pairs: evidence.len(),
            });
        }
    }
    Err(ArithmeticFiberError::NoResidueTransport { grammar_bound })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResidueTransportGrade {
    pub pair: PairedQuadraticFiber,
    pub read: ResidueTransportRead,
    pub exact_residual: Option<i8>,
}

impl ResidueTransportLaw {
    pub fn grade(
        &self,
        pair: PairedQuadraticFiber,
    ) -> Result<ResidueTransportGrade, ArithmeticFiberError> {
        pair.validate()?;
        let read = self.receive(pair.lower_prime, pair.upper_prime)?;
        let exact_residual = read
            .predicted_hand
            .map(|predicted| predicted - pair.observed_hand);
        Ok(ResidueTransportGrade {
            pair,
            read,
            exact_residual,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReciprocityCalibrationReceipt {
    pub schema: String,
    pub training_prime_ceiling: u64,
    pub heldout_prime_ceiling: u64,
    pub transport: ResidueTransportLaw,
    pub training: Vec<PairedQuadraticFiber>,
    pub heldout: Vec<ResidueTransportGrade>,
    pub all_heldout_buckets_received: bool,
    pub all_heldout_residuals_zero: bool,
}

pub fn calibrate_quadratic_transport(
    standing: &ArithmeticFiberStanding,
    training_prime_ceiling: u64,
    heldout_prime_ceiling: u64,
    grammar_bound: u64,
) -> Result<ReciprocityCalibrationReceipt, ArithmeticFiberError> {
    standing.validate()?;
    if training_prime_ceiling >= heldout_prime_ceiling || heldout_prime_ceiling > standing.value {
        return Err(ArithmeticFiberError::InvalidCalibrationBoundary);
    }
    let primes = standing
        .prime_cells
        .keys()
        .copied()
        .filter(|prime| *prime > 2 && *prime <= heldout_prime_ceiling)
        .collect::<Vec<_>>();
    let mut training = Vec::new();
    let mut heldout_pairs = Vec::new();
    for left in 0..primes.len() {
        for right in left + 1..primes.len() {
            let pair = standing.paired_quadratic_fiber(primes[left], primes[right])?;
            if primes[right] <= training_prime_ceiling {
                training.push(pair);
            } else {
                heldout_pairs.push(pair);
            }
        }
    }
    let transport = discover_residue_transport(standing, &training, grammar_bound)?;
    let heldout = heldout_pairs
        .into_iter()
        .map(|pair| transport.grade(pair))
        .collect::<Result<Vec<_>, _>>()?;
    let all_heldout_buckets_received = heldout
        .iter()
        .all(|grade| grade.read.predicted_hand.is_some());
    let all_heldout_residuals_zero = heldout.iter().all(|grade| grade.exact_residual == Some(0));
    Ok(ReciprocityCalibrationReceipt {
        schema: "holonic-engine.reciprocity-calibration-receipt.v1".to_owned(),
        training_prime_ceiling,
        heldout_prime_ceiling,
        transport,
        training,
        heldout,
        all_heldout_buckets_received,
        all_heldout_residuals_zero,
    })
}

/// Instantiate the inferred pair transport as a rank-one sheaf on selected
/// prime vertices and their multiplicative pair cells.  Every other stalk,
/// including higher products, is retained with dimension zero rather than
/// deleted from the caused arithmetic ecology.
pub fn residue_transport_sheaf(
    standing: &ArithmeticFiberStanding,
    transport: &ResidueTransportLaw,
    selected_primes: &BTreeSet<u64>,
) -> Result<ExactCellularSheaf, ArithmeticFiberError> {
    standing.validate()?;
    transport.validate()?;
    if selected_primes.is_empty() || selected_primes.contains(&2) {
        return Err(ArithmeticFiberError::InvalidSheafPrimeSelection);
    }
    for prime in selected_primes {
        standing.prime_cell(*prime)?;
    }
    for pair in combinations(&selected_primes.iter().copied().collect::<Vec<_>>(), 2) {
        if !standing.squarefree_cells.contains_key(&pair) {
            return Err(ArithmeticFiberError::MissingMultiplicativePair(pair));
        }
        if transport
            .receive(pair[0], pair[1])?
            .predicted_hand
            .is_none()
        {
            return Err(ArithmeticFiberError::OpenResidueTransport {
                left: pair[0],
                right: pair[1],
            });
        }
    }

    let selected_vertices = selected_primes
        .iter()
        .map(|prime| standing.prime_cells[prime])
        .collect::<BTreeSet<_>>();
    let selected_edges = standing
        .squarefree_cells
        .iter()
        .filter_map(|(support, cell)| {
            (support.len() == 2 && support.iter().all(|prime| selected_primes.contains(prime)))
                .then_some(*cell)
        })
        .collect::<BTreeSet<_>>();
    let dimensions = standing
        .incidence
        .cells()
        .iter()
        .map(|(cell, body)| {
            let dimension = usize::from(
                (body.grade == 0 && selected_vertices.contains(cell))
                    || (body.grade == 1 && selected_edges.contains(cell)),
            );
            (*cell, dimension)
        })
        .collect::<BTreeMap<_, _>>();
    let support_by_cell = standing
        .squarefree_cells
        .iter()
        .map(|(support, cell)| (*cell, support.clone()))
        .collect::<BTreeMap<_, _>>();
    let prime_by_cell = standing
        .prime_cells
        .iter()
        .map(|(prime, cell)| (*cell, *prime))
        .collect::<BTreeMap<_, _>>();
    let mut restrictions = Vec::new();
    for (upper, body) in standing.incidence.cells() {
        for lower in body.boundary.support() {
            let rows = dimensions[upper];
            let columns = dimensions[&lower];
            let map = if rows == 1 && columns == 1 {
                let support = &support_by_cell[upper];
                let lower_prime = prime_by_cell[&lower];
                let hand = if lower_prime == support[0] {
                    1
                } else {
                    transport
                        .receive(support[0], support[1])?
                        .predicted_hand
                        .ok_or(ArithmeticFiberError::OpenResidueTransport {
                            left: support[0],
                            right: support[1],
                        })?
                };
                ExactLinearMap::new(1, 1, vec![vec![Rat::from_integer(BigInt::from(hand))]])?
            } else {
                ExactLinearMap::zero(rows, columns)
            };
            restrictions.push(CellularRestriction {
                lower,
                upper: *upper,
                map,
            });
        }
    }
    Ok(ExactCellularSheaf::new(
        standing.incidence.clone(),
        dimensions,
        restrictions,
    )?)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResidueTriangleObstruction {
    pub primes: [u64; 3],
    pub pair_hands: [i8; 3],
    pub cycle_holonomy: i8,
    pub extends_as_nonzero_rank_one_fiber: bool,
}

pub fn residue_triangle_obstructions(
    transport: &ResidueTransportLaw,
    selected_primes: &BTreeSet<u64>,
) -> Result<Vec<ResidueTriangleObstruction>, ArithmeticFiberError> {
    transport.validate()?;
    let primes = selected_primes.iter().copied().collect::<Vec<_>>();
    let mut receipts = Vec::new();
    for triple in combinations(&primes, 3) {
        let pairs = [
            (triple[0], triple[1]),
            (triple[1], triple[2]),
            (triple[0], triple[2]),
        ];
        let mut pair_hands = [0_i8; 3];
        for (ordinal, (left, right)) in pairs.into_iter().enumerate() {
            pair_hands[ordinal] = transport
                .receive(left, right)?
                .predicted_hand
                .ok_or(ArithmeticFiberError::OpenResidueTransport { left, right })?;
        }
        let cycle_holonomy = pair_hands.iter().product();
        receipts.push(ResidueTriangleObstruction {
            primes: [triple[0], triple[1], triple[2]],
            pair_hands,
            cycle_holonomy,
            extends_as_nonzero_rank_one_fiber: cycle_holonomy == 1,
        });
    }
    Ok(receipts)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ArithmeticFiberError {
    #[error("arithmetic succession expected {expected}, but source supplied {supplied}")]
    NonSuccessor { expected: u64, supplied: u64 },
    #[error("source occurrence {0:?} was already used by this arithmetic world")]
    RepeatedEvent(EventId),
    #[error("finite arithmetic exceeded its exact u64 carrier")]
    CarrierOverflow,
    #[error("the arithmetic standing has an unknown or malformed schema")]
    MalformedArithmeticStanding,
    #[error("an arithmetic standing value must be at least one")]
    InvalidStandingValue,
    #[error("arithmetic occurrence chronology does not cover every admitted integer")]
    OccurrenceChronologyMismatch,
    #[error("arithmetic occurrence identities do not match the retained event population")]
    OccurrenceEventMismatch,
    #[error("prime-recognition chronology does not cover every admitted integer")]
    RecognitionChronologyMismatch,
    #[error("integer {0} retained malformed prime-recognition testimony")]
    MalformedPrimeRecognition(u64),
    #[error("the retained symbolic prime-power current does not match arithmetic chronology")]
    MalformedPrimePowerCurrent,
    #[error("a Zeta receiver requires an integer sigma greater than one, received {0}")]
    InvalidZetaSigma(u32),
    #[error("{0} is not a valid founded prime identity")]
    InvalidPrimeIdentity(u64),
    #[error("prime {0} does not coincide with its grade-zero multiplicative cell")]
    PrimeCellMismatch(u64),
    #[error("prime {0} has not been founded by this arithmetic standing")]
    UnfoundedPrime(u64),
    #[error("factorization exposed residual prime {0} before its causal founding")]
    UnfoundedResidualPrime(u64),
    #[error("multiplication probes contradicted the proposed prime founding at {0}")]
    PrimeFoundingContradiction(u64),
    #[error("squarefree support is malformed: {0:?}")]
    MalformedSquarefreeSupport(Vec<u64>),
    #[error("squarefree support is missing immediate face {0:?}")]
    MissingSquarefreeFace(Vec<u64>),
    #[error("squarefree support {support:?} expected grade {expected}, retained grade {supplied}")]
    SquarefreeGradeMismatch {
        support: Vec<u64>,
        expected: u32,
        supplied: u32,
    },
    #[error("squarefree support {0:?} has the wrong oriented boundary")]
    SquarefreeBoundaryMismatch(Vec<u64>),
    #[error("squarefree support {0:?} is not founded by its least product occurrence")]
    SquarefreeFoundingMismatch(Vec<u64>),
    #[error("integer {0} retained a malformed valuation occurrence")]
    MalformedOccurrence(u64),
    #[error("quadratic receiver fibers currently require an odd founded prime")]
    EvenQuadraticPrime,
    #[error("paired quadratic fibers require distinct primes, received {0} twice")]
    RepeatedReciprocityPrime(u64),
    #[error("the paired quadratic calibration is restricted to odd prime receivers")]
    EvenReciprocityPrime,
    #[error("paired fibers over {left} and {right} were degenerate")]
    DegenerateReciprocityFiber { left: u64, right: u64 },
    #[error("paired quadratic fiber ({left}, {right}) is malformed")]
    MalformedPairedFiber { left: u64, right: u64 },
    #[error("paired quadratic fiber ({left}, {right}) does not inhabit its claimed prime cells")]
    PairedFiberSourceMismatch { left: u64, right: u64 },
    #[error("Euler receiver over {prime} returned neither hand for residue {residue}: {witness}")]
    InvalidQuadraticCharacter {
        prime: u64,
        residue: u64,
        witness: u64,
    },
    #[error("no quadratic nonresidue was found in the declared prime receiver {0}")]
    MissingQuadraticNonresidue(u64),
    #[error("Tonelli transport failed over prime {prime} for residue {residue}")]
    TonelliFailure { prime: u64, residue: u64 },
    #[error("a reported quadratic root does not satisfy its exact fiber")]
    QuadraticRootFailure,
    #[error("quadratic character does not equal root population minus one")]
    QuadraticRootCountFailure,
    #[error("a quadratic coordinate scaling must be a nonzero field unit")]
    NonunitQuadraticScale,
    #[error("a quadratic coordinate isomorphism failed its exact root bijection")]
    QuadraticIsomorphismFailure,
    #[error("Hensel transport requires a prime base and positive exponent")]
    InvalidHenselBase,
    #[error("the supplied value is not a quadratic root modulo {modulus}")]
    NotQuadraticRoot { modulus: BigInt },
    #[error("a unique Hensel lift retained a nonzero exact residual")]
    HenselResidualFailure,
    #[error("a congruence modulus must be positive")]
    NonpositiveModulus,
    #[error("Chinese-remainder moduli are not coprime; gcd is {0}")]
    NoncoprimeModuli(BigInt),
    #[error("the extended-gcd receipt failed its exact Bezout identity")]
    BezoutFailure,
    #[error("the Chinese-remainder result failed one of its source congruences")]
    ChineseRemainderFailure,
    #[error("residue transport discovery requires at least one paired fiber")]
    EmptyTransportEvidence,
    #[error("residue grammar bound must be at least two, received {0}")]
    InvalidGrammarBound(u64),
    #[error("paired fiber carried invalid observed hand {0}")]
    InvalidObservedHand(i8),
    #[error("a retained residue transport law is malformed")]
    MalformedResidueTransport,
    #[error("no deterministic residue transport was supported through modulus {grammar_bound}")]
    NoResidueTransport { grammar_bound: u64 },
    #[error("calibration requires training < heldout <= current arithmetic standing")]
    InvalidCalibrationBoundary,
    #[error("a residue-transport sheaf requires a nonempty selection of odd founded primes")]
    InvalidSheafPrimeSelection,
    #[error("multiplicative pair {0:?} has not yet entered the arithmetic ecology")]
    MissingMultiplicativePair(Vec<u64>),
    #[error("residue transport is open for prime pair ({left}, {right})")]
    OpenResidueTransport { left: u64, right: u64 },
    #[error(transparent)]
    Algebraic(#[from] CausalAlgebraicError),
    #[error(transparent)]
    Sheaf(#[from] SheafDiffusionError),
}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use relational_geometry::integer;

    use super::*;
    use crate::{CausalWorld, ExactSheafCochain, ExactSheafDiffusionLaw, SheafDiffusionEvent};

    fn arithmetic_through(limit: u64) -> ArithmeticFiberStanding {
        let mut world = CausalWorld::new(ArithmeticFiberLaw, ArithmeticFiberStanding::default());
        for value in 2..=limit {
            world
                .receive(&ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                })
                .unwrap();
        }
        world.standing().clone()
    }

    #[test]
    fn multiplication_founds_primes_support_and_power_multiplicity() {
        let standing = arithmetic_through(30);
        assert_eq!(
            standing.prime_cells.keys().copied().collect::<Vec<_>>(),
            vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        );
        let thirty = &standing.occurrences[&30];
        assert_eq!(thirty.squarefree_support, vec![2, 3, 5]);
        assert_eq!(
            standing.incidence.cell(thirty.support_cell).unwrap().grade,
            2
        );
        let eight = &standing.occurrences[&8];
        assert_eq!(
            eight.valuation,
            vec![PrimeValuation {
                prime: 2,
                exponent: 3
            }]
        );
        assert_eq!(eight.support_cell, standing.prime_cells[&2]);
        assert_eq!(
            standing.incidence.f_vector(),
            BTreeMap::from([(0, 10), (1, 7), (2, 1)])
        );
        standing.validate().unwrap();
    }

    #[test]
    fn recognition_fibers_close_only_at_the_factor_front_or_complete_horizon() {
        let standing = arithmetic_through(77);

        let forty_seven = &standing.recognitions[&47];
        assert!(matches!(
            forty_seven.closure,
            PrimeRecognitionClosure::Irreducible {
                ref failed_axes
            } if failed_axes == &[2, 3, 5]
        ));
        assert_eq!(forty_seven.open_fiber_count(), 3);
        assert_eq!(
            forty_seven.bounds,
            PrimeRecognitionBounds {
                factor_horizon_axis_count: 3,
                distinguishing_probe_lower_bound: 3,
                certificate_probe_upper_bound: 3,
            }
        );
        assert!(forty_seven.irreducibility_obstruction.is_none());
        assert_eq!(
            forty_seven
                .steps
                .last()
                .unwrap()
                .fiber_after
                .admissible_dispositions,
            BTreeSet::from([PrimeRecognitionDisposition::Irreducible])
        );

        let forty_nine = &standing.recognitions[&49];
        assert_eq!(forty_nine.open_fiber_count(), 4);
        assert!(matches!(
            forty_nine.closure,
            PrimeRecognitionClosure::Composite {
                witness: PrimeFactorWitness {
                    prime_axis: 7,
                    cofactor: 7,
                    exact_product: 49,
                }
            }
        ));
        assert_eq!(
            forty_nine.irreducibility_obstruction,
            Some(PrimeIrreducibilityObstruction {
                schema: "holonic-engine.prime-irreducibility-obstruction.v1".to_owned(),
                depth: 4,
                witness: PrimeFactorWitness {
                    prime_axis: 7,
                    cofactor: 7,
                    exact_product: 49,
                },
            })
        );
        assert_eq!(
            forty_nine
                .steps
                .last()
                .unwrap()
                .fiber_after
                .admissible_dispositions,
            BTreeSet::from([PrimeRecognitionDisposition::Composite])
        );

        let seventy_seven = &standing.recognitions[&77];
        assert!(matches!(
            seventy_seven.closure,
            PrimeRecognitionClosure::Composite {
                witness: PrimeFactorWitness {
                    prime_axis: 7,
                    cofactor: 11,
                    exact_product: 77,
                }
            }
        ));
        assert_eq!(
            seventy_seven.bounds.distinguishing_probe_lower_bound,
            seventy_seven.bounds.certificate_probe_upper_bound
        );
        assert_eq!(
            seventy_seven.open_fiber_count(),
            seventy_seven.bounds.distinguishing_probe_lower_bound
        );
    }

    #[test]
    fn prime_power_current_and_zeta_place_measure_remain_exact_receiver_faces() {
        let standing = arithmetic_through(30);
        assert_eq!(
            standing.prime_power_current.log_coefficients,
            BTreeMap::from([
                (2, 4),
                (3, 3),
                (5, 2),
                (7, 1),
                (11, 1),
                (13, 1),
                (17, 1),
                (19, 1),
                (23, 1),
                (29, 1),
            ])
        );
        assert_eq!(
            standing.prime_power_current.chebyshev_product,
            BigUint::from(2_329_089_562_800_u64)
        );
        assert_eq!(
            standing.prime_power_current.formal_departure(),
            FormalChebyshevDeparture {
                schema: "holonic-engine.formal-chebyshev-departure.v1".to_owned(),
                through: 30,
                log_coefficients: standing.prime_power_current.log_coefficients.clone(),
                smooth_coordinate: BigInt::from(30),
            }
        );

        let measure = standing
            .zeta_receiver_measure(2, &BTreeSet::from([2, 3, 5]))
            .unwrap();
        assert_eq!(
            measure.coprime_cell_mass,
            Rat::new(BigInt::from(16), BigInt::from(25))
        );
        assert_eq!(
            measure.valuation_return_mass,
            Rat::new(BigInt::from(25), BigInt::from(16))
        );
        assert_eq!(
            measure.valuation_fibers[0].mass_at(1),
            Rat::new(BigInt::from(3), BigInt::from(16))
        );
        assert_eq!(
            standing.zeta_receiver_measure(1, &BTreeSet::from([2])),
            Err(ArithmeticFiberError::InvalidZetaSigma(1))
        );
    }

    #[test]
    fn recognition_and_current_tampering_cannot_become_standing() {
        let standing = arithmetic_through(30);
        let mut forged_recognition = standing.clone();
        forged_recognition
            .recognitions
            .get_mut(&25)
            .unwrap()
            .bounds
            .distinguishing_probe_lower_bound = 1;
        assert_eq!(
            forged_recognition.validate(),
            Err(ArithmeticFiberError::MalformedPrimeRecognition(25))
        );

        let mut forged_current = standing;
        forged_current
            .prime_power_current
            .log_coefficients
            .insert(2, 99);
        assert_eq!(
            forged_current.validate(),
            Err(ArithmeticFiberError::MalformedPrimePowerCurrent)
        );
    }

    #[test]
    fn arithmetic_refusal_and_fiber_evidence_cannot_forge_partial_standing_or_a_hand() {
        let mut world = CausalWorld::new(ArithmeticFiberLaw, ArithmeticFiberStanding::default());
        world
            .receive(&ArithmeticFiberEvent {
                event: EventId(1),
                value: 2,
            })
            .unwrap();
        let before = world.standing().clone();
        assert_eq!(
            world.receive(&ArithmeticFiberEvent {
                event: EventId(2),
                value: 4,
            }),
            Err(ArithmeticFiberError::NonSuccessor {
                expected: 3,
                supplied: 4,
            })
        );
        assert_eq!(world.standing(), &before);

        let standing = arithmetic_through(13);
        let mut forged = standing.paired_quadratic_fiber(3, 5).unwrap();
        forged.observed_hand = -forged.observed_hand;
        assert!(matches!(
            discover_residue_transport(&standing, &[forged], 8),
            Err(ArithmeticFiberError::MalformedPairedFiber { left: 3, right: 5 })
        ));
    }

    #[test]
    fn quadratic_fibers_are_exact_and_presentation_translation_is_invariant() {
        let standing = arithmetic_through(50);
        let fiber = standing.quadratic_fiber(7, 2).unwrap();
        assert_eq!(fiber.roots, vec![3, 4]);
        assert_eq!(fiber.character, 1);
        let translated = standing.quadratic_fiber(7, 2 + 9 * 7).unwrap();
        assert_eq!(fiber.residue, translated.residue);
        assert_eq!(fiber.roots, translated.roots);
        let isomorphism = fiber.unit_scale(3).unwrap();
        assert!(isomorphism.character_preserved);
        assert_eq!(isomorphism.mapped_roots, isomorphism.target.roots);
        assert!(
            isomorphism
                .exact_forward_residuals
                .iter()
                .chain(&isomorphism.exact_reverse_residuals)
                .all(Zero::is_zero)
        );
        let nonresidue = standing.quadratic_fiber(7, 3).unwrap();
        assert!(nonresidue.roots.is_empty());
        assert_eq!(nonresidue.character, -1);
    }

    #[test]
    fn hensel_and_chinese_remainder_transport_retain_zero_residuals() {
        let standing = arithmetic_through(10);
        let tower = standing
            .quadratic_fiber(7, 2)
            .unwrap()
            .hensel_tower(2)
            .unwrap();
        let lifted = tower
            .paths
            .iter()
            .map(|path| match &path.steps[0].branch {
                QuadraticHenselBranch::Unique {
                    root,
                    exact_residual,
                    ..
                } => {
                    assert!(exact_residual.is_zero());
                    root.clone()
                }
                other => panic!("unexpected Hensel branch: {other:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(lifted, vec![BigInt::from(10), BigInt::from(39)]);
        let full = standing
            .quadratic_fiber(7, 0)
            .unwrap()
            .lift_root(1, 0)
            .unwrap();
        assert!(matches!(
            full.branch,
            QuadraticHenselBranch::FullFiber { digit_count: 7, .. }
        ));
        let stopped = standing
            .quadratic_fiber(7, 7)
            .unwrap()
            .lift_root(1, 0)
            .unwrap();
        assert_eq!(stopped.branch, QuadraticHenselBranch::NoLift);

        let crt = chinese_remainder_pair(
            ExactCongruence::new(2, 3).unwrap(),
            ExactCongruence::new(3, 5).unwrap(),
        )
        .unwrap();
        assert_eq!(crt.combined, ExactCongruence::new(8, 15).unwrap());
        assert!(crt.bezout_residual.is_zero());
        assert!(crt.left_residual.is_zero());
        assert!(crt.right_residual.is_zero());
    }

    #[test]
    fn bounded_grammar_discovers_mod_four_and_grades_unseen_primes() {
        let standing = arithmetic_through(97);
        let insufficient = calibrate_quadratic_transport(&standing, 11, 97, 12).unwrap();
        assert_eq!(insufficient.transport.modulus, 4);
        assert!(!insufficient.all_heldout_buckets_received);
        assert!(!insufficient.all_heldout_residuals_zero);
        assert!(
            insufficient
                .heldout
                .iter()
                .any(|grade| grade.exact_residual.is_none())
        );
        let minimal_complete = calibrate_quadratic_transport(&standing, 13, 97, 12).unwrap();
        assert!(minimal_complete.all_heldout_buckets_received);
        assert!(minimal_complete.all_heldout_residuals_zero);

        let receipt = calibrate_quadratic_transport(&standing, 43, 97, 12).unwrap();
        assert_eq!(receipt.transport.modulus, 4);
        assert!(receipt.all_heldout_buckets_received);
        assert!(receipt.all_heldout_residuals_zero);
        assert!(!receipt.heldout.is_empty());
        assert!(
            receipt
                .heldout
                .iter()
                .all(|grade| grade.exact_residual == Some(0))
        );
        for grade in &receipt.heldout {
            let swapped = receipt
                .transport
                .receive(grade.pair.upper_prime, grade.pair.lower_prime)
                .unwrap();
            assert_eq!(swapped.predicted_hand, grade.read.predicted_hand);
        }
    }

    #[test]
    fn inferred_transport_becomes_a_sheaf_and_exposes_cycle_obstruction() {
        let standing = arithmetic_through(97);
        let calibration = calibrate_quadratic_transport(&standing, 43, 97, 12).unwrap();
        let selected = BTreeSet::from([3, 5, 7]);
        let obstructions =
            residue_triangle_obstructions(&calibration.transport, &selected).unwrap();
        assert_eq!(obstructions.len(), 1);
        assert_eq!(obstructions[0].cycle_holonomy, -1);
        assert!(!obstructions[0].extends_as_nonzero_rank_one_fiber);

        let sheaf = residue_transport_sheaf(&standing, &calibration.transport, &selected).unwrap();
        let capacities = sheaf
            .complex()
            .cells()
            .iter()
            .filter(|(_, body)| body.grade == 0)
            .map(|(cell, _)| {
                (
                    *cell,
                    if selected
                        .iter()
                        .any(|prime| standing.prime_cells[prime] == *cell)
                    {
                        vec![integer(1)]
                    } else {
                        Vec::new()
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let law = ExactSheafDiffusionLaw::new(sheaf.clone(), 0, capacities).unwrap();
        let mut content = ExactSheafCochain::zero(&sheaf, 0);
        content.values.get_mut(&standing.prime_cells[&3]).unwrap()[0] = integer(1);
        let initial = law.initial_standing(content).unwrap();
        let (_, receipt) = law
            .enact(
                &initial,
                &SheafDiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();
        assert_eq!(receipt.certificate.harmonic_dimension, 0);
        assert!(receipt.energy_departed.is_positive());
        assert!(
            receipt
                .balance_residual
                .values
                .values()
                .flatten()
                .all(Zero::is_zero)
        );

        let balanced = BTreeSet::from([3, 5, 13]);
        let balanced_obstructions =
            residue_triangle_obstructions(&calibration.transport, &balanced).unwrap();
        assert_eq!(balanced_obstructions[0].cycle_holonomy, 1);
        let balanced_sheaf =
            residue_transport_sheaf(&standing, &calibration.transport, &balanced).unwrap();
        let balanced_capacities = balanced_sheaf
            .complex()
            .cells()
            .iter()
            .filter(|(_, body)| body.grade == 0)
            .map(|(cell, _)| {
                (
                    *cell,
                    if balanced
                        .iter()
                        .any(|prime| standing.prime_cells[prime] == *cell)
                    {
                        vec![integer(1)]
                    } else {
                        Vec::new()
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let balanced_law =
            ExactSheafDiffusionLaw::new(balanced_sheaf.clone(), 0, balanced_capacities).unwrap();
        let balanced_initial = balanced_law
            .initial_standing(ExactSheafCochain::zero(&balanced_sheaf, 0))
            .unwrap();
        let (_, balanced_receipt) = balanced_law
            .enact(
                &balanced_initial,
                &SheafDiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();
        assert_eq!(balanced_receipt.certificate.harmonic_dimension, 1);
    }
}
