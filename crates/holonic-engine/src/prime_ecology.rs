//! A topology-forming ecology of prime receivers and polynomial material.
//!
//! The application does not supply prime fibers, phase relations, horns, or
//! higher cells. It may pass an integer occurrence or an inherited polynomial
//! into one atomic [`PrimeEcologyLaw`] event. Multiplication founds the prime;
//! the prime receives every inherited polynomial; exact finite-field
//! factorization derives its local Frobenius phases; and common phase
//! constituents found higher cells in the same caused arithmetic complex.
//!
//! A boundary-complete support with no contemporary common constituent is
//! retained as a potential horn. A horn-resolution event supplies only that
//! support. Every concrete inherited boundary phase emits its missing-receiver
//! continuation stratum; coefficientwise CRT retains the complete result as a
//! finite union of affine integer-polynomial torsors. Realised branches fill
//! the horn while obstructed branches remain empty. No representative
//! polynomial is promoted into standing as the family itself.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ArithmeticFiberError, ArithmeticFiberEvent, ArithmeticFiberLaw, ArithmeticFiberRadiation,
    ArithmeticFiberStanding, CausalAlgebraicError, CausalCellId, CausalChain,
    ComparativeMultiplicity, EventId, EventSuccessor, ExactCongruence, ExactEventLaw,
    chinese_remainder_pair,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PolynomialProbeId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct HornFillerSpaceId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct HornFillerBranchId {
    pub space: HornFillerSpaceId,
    pub ordinal: u32,
}

pub const DEFAULT_HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CausalMaterialKind {
    Inherited,
    Enacted,
    Proposed,
    Induced,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalMaterialLineage {
    pub kind: CausalMaterialKind,
    pub source_events: BTreeSet<EventId>,
}

impl CausalMaterialLineage {
    fn new(kind: CausalMaterialKind, source_events: BTreeSet<EventId>) -> Self {
        Self {
            kind,
            source_events,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum PolynomialProbeFamily {
    General,
    Cyclotomic { order: u32 },
}

/// One inherited polynomial over the integers, stored coefficient-first.
///
/// Probes are monic so reduction at every founded prime retains their degree.
/// This is an inherited decoder, not a precomputed prime response.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegerPolynomialProbe {
    pub schema: String,
    pub id: PolynomialProbeId,
    pub name: String,
    pub family: PolynomialProbeFamily,
    pub coefficients: Vec<BigInt>,
}

impl IntegerPolynomialProbe {
    pub fn new(
        id: PolynomialProbeId,
        name: impl Into<String>,
        coefficients: Vec<BigInt>,
    ) -> Result<Self, PrimeEcologyError> {
        let probe = Self {
            schema: "holonic-engine.integer-polynomial-probe.v1".to_owned(),
            id,
            name: name.into(),
            family: PolynomialProbeFamily::General,
            coefficients: trim_integer_polynomial(coefficients),
        };
        probe.validate()?;
        Ok(probe)
    }

    pub fn cyclotomic(id: PolynomialProbeId, order: u32) -> Result<Self, PrimeEcologyError> {
        if order == 0 {
            return Err(PrimeEcologyError::ZeroCyclotomicOrder);
        }
        let coefficients = cyclotomic_coefficients(order)?;
        let probe = Self {
            schema: "holonic-engine.integer-polynomial-probe.v1".to_owned(),
            id,
            name: format!("cyclotomic[{order}]"),
            family: PolynomialProbeFamily::Cyclotomic { order },
            coefficients,
        };
        probe.validate()?;
        Ok(probe)
    }

    pub fn degree(&self) -> usize {
        self.coefficients.len() - 1
    }

    pub fn validate(&self) -> Result<(), PrimeEcologyError> {
        if self.schema != "holonic-engine.integer-polynomial-probe.v1"
            || self.name.is_empty()
            || self.coefficients.len() < 2
            || self.coefficients.last() != Some(&BigInt::one())
            || self.coefficients.last().is_some_and(Zero::is_zero)
        {
            return Err(PrimeEcologyError::MalformedPolynomialProbe(self.id));
        }
        if let PolynomialProbeFamily::Cyclotomic { order } = self.family
            && (order == 0 || self.coefficients != cyclotomic_coefficients(order)?)
        {
            return Err(PrimeEcologyError::MalformedPolynomialProbe(self.id));
        }
        Ok(())
    }
}

fn trim_integer_polynomial(mut coefficients: Vec<BigInt>) -> Vec<BigInt> {
    while coefficients.len() > 1 && coefficients.last().is_some_and(Zero::is_zero) {
        coefficients.pop();
    }
    coefficients
}

fn cyclotomic_coefficients(order: u32) -> Result<Vec<BigInt>, PrimeEcologyError> {
    fn receive(
        order: u32,
        cache: &mut BTreeMap<u32, Vec<BigInt>>,
    ) -> Result<Vec<BigInt>, PrimeEcologyError> {
        if let Some(received) = cache.get(&order) {
            return Ok(received.clone());
        }
        let degree = usize::try_from(order).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
        let mut polynomial = vec![BigInt::zero(); degree + 1];
        polynomial[0] = -BigInt::one();
        polynomial[degree] = BigInt::one();
        for divisor in 1..order {
            if order.is_multiple_of(divisor) {
                let lower = receive(divisor, cache)?;
                polynomial = exact_integer_polynomial_quotient(polynomial, &lower)?;
            }
        }
        polynomial = trim_integer_polynomial(polynomial);
        cache.insert(order, polynomial.clone());
        Ok(polynomial)
    }

    if order == 0 {
        return Err(PrimeEcologyError::ZeroCyclotomicOrder);
    }
    receive(order, &mut BTreeMap::new())
}

fn exact_integer_polynomial_quotient(
    numerator: Vec<BigInt>,
    denominator: &[BigInt],
) -> Result<Vec<BigInt>, PrimeEcologyError> {
    let denominator = trim_integer_polynomial(denominator.to_vec());
    if denominator.is_empty() || denominator.last() != Some(&BigInt::one()) {
        return Err(PrimeEcologyError::NonexactCyclotomicDivision);
    }
    let mut remainder = trim_integer_polynomial(numerator);
    if remainder.len() < denominator.len() {
        return Err(PrimeEcologyError::NonexactCyclotomicDivision);
    }
    let mut quotient = vec![BigInt::zero(); remainder.len() - denominator.len() + 1];
    while remainder.len() >= denominator.len() && !remainder.iter().all(Zero::is_zero) {
        let shift = remainder.len() - denominator.len();
        let coefficient = remainder
            .last()
            .cloned()
            .ok_or(PrimeEcologyError::NonexactCyclotomicDivision)?;
        quotient[shift] += &coefficient;
        for (index, divisor) in denominator.iter().enumerate() {
            remainder[index + shift] -= &coefficient * divisor;
        }
        remainder = trim_integer_polynomial(remainder);
    }
    if !remainder.iter().all(Zero::is_zero) {
        return Err(PrimeEcologyError::NonexactCyclotomicDivision);
    }
    Ok(trim_integer_polynomial(quotient))
}

/// A canonical polynomial over one prime receiver field.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PrimePolynomial {
    pub prime: u64,
    pub coefficients: Vec<u64>,
}

impl PrimePolynomial {
    fn new(prime: u64, coefficients: Vec<u64>) -> Result<Self, PrimeEcologyError> {
        if prime < 2 {
            return Err(PrimeEcologyError::InvalidPrimeModulus(prime));
        }
        let coefficients = trim_prime_polynomial(
            coefficients
                .into_iter()
                .map(|coefficient| coefficient % prime)
                .collect(),
        );
        Ok(Self {
            prime,
            coefficients,
        })
    }

    fn zero(prime: u64) -> Self {
        Self {
            prime,
            coefficients: vec![0],
        }
    }

    fn one(prime: u64) -> Self {
        Self {
            prime,
            coefficients: vec![1],
        }
    }

    fn x(prime: u64) -> Self {
        Self {
            prime,
            coefficients: vec![0, 1],
        }
    }

    pub fn is_zero(&self) -> bool {
        self.coefficients.len() == 1 && self.coefficients[0] == 0
    }

    pub fn degree(&self) -> Option<usize> {
        (!self.is_zero()).then_some(self.coefficients.len() - 1)
    }

    fn leading(&self) -> u64 {
        *self
            .coefficients
            .last()
            .expect("canonical polynomials are never empty")
    }

    fn validate(&self) -> Result<(), PrimeEcologyError> {
        if self.prime < 2
            || self.coefficients.is_empty()
            || self.coefficients.iter().any(|value| *value >= self.prime)
            || (self.coefficients.len() > 1 && self.leading() == 0)
        {
            return Err(PrimeEcologyError::MalformedPrimePolynomial);
        }
        Ok(())
    }
}

fn trim_prime_polynomial(mut coefficients: Vec<u64>) -> Vec<u64> {
    if coefficients.is_empty() {
        return vec![0];
    }
    while coefficients.len() > 1 && coefficients.last() == Some(&0) {
        coefficients.pop();
    }
    coefficients
}

fn add_mod(left: u64, right: u64, modulus: u64) -> u64 {
    ((u128::from(left) + u128::from(right)) % u128::from(modulus)) as u64
}

fn mul_mod(left: u64, right: u64, modulus: u64) -> u64 {
    ((u128::from(left) * u128::from(right)) % u128::from(modulus)) as u64
}

fn neg_mod(value: u64, modulus: u64) -> u64 {
    if value == 0 { 0 } else { modulus - value }
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

fn poly_add(
    left: &PrimePolynomial,
    right: &PrimePolynomial,
) -> Result<PrimePolynomial, PrimeEcologyError> {
    same_modulus(left, right)?;
    let length = left.coefficients.len().max(right.coefficients.len());
    let mut coefficients = vec![0; length];
    for (index, slot) in coefficients.iter_mut().enumerate() {
        *slot = add_mod(
            left.coefficients.get(index).copied().unwrap_or(0),
            right.coefficients.get(index).copied().unwrap_or(0),
            left.prime,
        );
    }
    PrimePolynomial::new(left.prime, coefficients)
}

fn poly_sub(
    left: &PrimePolynomial,
    right: &PrimePolynomial,
) -> Result<PrimePolynomial, PrimeEcologyError> {
    let negated = PrimePolynomial::new(
        right.prime,
        right
            .coefficients
            .iter()
            .map(|value| neg_mod(*value, right.prime))
            .collect(),
    )?;
    poly_add(left, &negated)
}

fn poly_mul(
    left: &PrimePolynomial,
    right: &PrimePolynomial,
) -> Result<PrimePolynomial, PrimeEcologyError> {
    same_modulus(left, right)?;
    if left.is_zero() || right.is_zero() {
        return Ok(PrimePolynomial::zero(left.prime));
    }
    let mut coefficients = vec![0; left.coefficients.len() + right.coefficients.len() - 1];
    for (left_index, left_value) in left.coefficients.iter().enumerate() {
        for (right_index, right_value) in right.coefficients.iter().enumerate() {
            let product = mul_mod(*left_value, *right_value, left.prime);
            coefficients[left_index + right_index] =
                add_mod(coefficients[left_index + right_index], product, left.prime);
        }
    }
    PrimePolynomial::new(left.prime, coefficients)
}

fn poly_div_rem(
    numerator: &PrimePolynomial,
    denominator: &PrimePolynomial,
) -> Result<(PrimePolynomial, PrimePolynomial), PrimeEcologyError> {
    same_modulus(numerator, denominator)?;
    if denominator.is_zero() {
        return Err(PrimeEcologyError::PolynomialDivisionByZero);
    }
    let mut remainder = numerator.clone();
    let numerator_degree = numerator.degree().unwrap_or(0);
    let denominator_degree = denominator
        .degree()
        .ok_or(PrimeEcologyError::PolynomialDivisionByZero)?;
    if numerator.is_zero() || numerator_degree < denominator_degree {
        return Ok((PrimePolynomial::zero(numerator.prime), remainder));
    }
    let inverse_leading = pow_mod(denominator.leading(), numerator.prime - 2, numerator.prime);
    let mut quotient = vec![0; numerator_degree - denominator_degree + 1];
    while !remainder.is_zero()
        && remainder
            .degree()
            .is_some_and(|degree| degree >= denominator_degree)
    {
        let remainder_degree = remainder
            .degree()
            .ok_or(PrimeEcologyError::MalformedPrimePolynomial)?;
        let shift = remainder_degree - denominator_degree;
        let coefficient = mul_mod(remainder.leading(), inverse_leading, numerator.prime);
        quotient[shift] = add_mod(quotient[shift], coefficient, numerator.prime);
        let mut subtractor = vec![0; shift + denominator.coefficients.len()];
        for (index, value) in denominator.coefficients.iter().enumerate() {
            subtractor[index + shift] = mul_mod(coefficient, *value, numerator.prime);
        }
        remainder = poly_sub(
            &remainder,
            &PrimePolynomial::new(numerator.prime, subtractor)?,
        )?;
    }
    Ok((PrimePolynomial::new(numerator.prime, quotient)?, remainder))
}

fn poly_monic(polynomial: &PrimePolynomial) -> Result<PrimePolynomial, PrimeEcologyError> {
    if polynomial.is_zero() {
        return Ok(polynomial.clone());
    }
    let inverse = pow_mod(polynomial.leading(), polynomial.prime - 2, polynomial.prime);
    PrimePolynomial::new(
        polynomial.prime,
        polynomial
            .coefficients
            .iter()
            .map(|value| mul_mod(*value, inverse, polynomial.prime))
            .collect(),
    )
}

fn poly_derivative(polynomial: &PrimePolynomial) -> Result<PrimePolynomial, PrimeEcologyError> {
    if polynomial.coefficients.len() <= 1 {
        return Ok(PrimePolynomial::zero(polynomial.prime));
    }
    PrimePolynomial::new(
        polynomial.prime,
        polynomial
            .coefficients
            .iter()
            .enumerate()
            .skip(1)
            .map(|(degree, coefficient)| {
                mul_mod(
                    *coefficient,
                    degree as u64 % polynomial.prime,
                    polynomial.prime,
                )
            })
            .collect(),
    )
}

fn poly_gcd(
    left: &PrimePolynomial,
    right: &PrimePolynomial,
    work: &mut PolynomialFactorizationWork,
) -> Result<PrimePolynomial, PrimeEcologyError> {
    same_modulus(left, right)?;
    let (mut older, mut newer) = (left.clone(), right.clone());
    while !newer.is_zero() {
        work.gcd_divisions = work
            .gcd_divisions
            .checked_add(1)
            .ok_or(PrimeEcologyError::CarrierOverflow)?;
        let (_, remainder) = poly_div_rem(&older, &newer)?;
        older = newer;
        newer = remainder;
    }
    poly_monic(&older)
}

fn poly_pow_mod(
    base: &PrimePolynomial,
    mut exponent: u128,
    modulus: &PrimePolynomial,
) -> Result<PrimePolynomial, PrimeEcologyError> {
    same_modulus(base, modulus)?;
    if modulus.is_zero() {
        return Err(PrimeEcologyError::PolynomialDivisionByZero);
    }
    let mut result = PrimePolynomial::one(base.prime);
    let (_, mut power) = poly_div_rem(base, modulus)?;
    while exponent > 0 {
        if exponent & 1 == 1 {
            let product = poly_mul(&result, &power)?;
            (_, result) = poly_div_rem(&product, modulus)?;
        }
        exponent >>= 1;
        if exponent > 0 {
            let square = poly_mul(&power, &power)?;
            (_, power) = poly_div_rem(&square, modulus)?;
        }
    }
    Ok(result)
}

fn same_modulus(left: &PrimePolynomial, right: &PrimePolynomial) -> Result<(), PrimeEcologyError> {
    if left.prime != right.prime {
        Err(PrimeEcologyError::PolynomialModulusMismatch {
            left: left.prime,
            right: right.prime,
        })
    } else {
        Ok(())
    }
}

fn reduce_integer_polynomial(
    prime: u64,
    coefficients: &[BigInt],
) -> Result<PrimePolynomial, PrimeEcologyError> {
    let modulus = BigInt::from(prime);
    let reduced = coefficients
        .iter()
        .map(|coefficient| {
            let mut residue = coefficient % &modulus;
            if residue.is_negative() {
                residue += &modulus;
            }
            residue.to_u64().ok_or(PrimeEcologyError::CarrierOverflow)
        })
        .collect::<Result<Vec<_>, _>>()?;
    PrimePolynomial::new(prime, reduced)
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PolynomialFactorizationWork {
    pub gcd_divisions: u64,
    pub frobenius_columns: u64,
    pub row_eliminations: u64,
    pub berlekamp_shifts: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ExactPrimeMatrix {
    pub prime: u64,
    pub entries: Vec<Vec<u64>>,
}

impl ExactPrimeMatrix {
    fn identity(prime: u64, dimension: usize) -> Self {
        let mut entries = vec![vec![0; dimension]; dimension];
        for (index, row) in entries.iter_mut().enumerate() {
            row[index] = 1 % prime;
        }
        Self { prime, entries }
    }

    fn dimension(&self) -> usize {
        self.entries.len()
    }

    fn validate(&self) -> Result<(), PrimeEcologyError> {
        let dimension = self.dimension();
        if self.prime < 2
            || dimension == 0
            || self
                .entries
                .iter()
                .any(|row| row.len() != dimension || row.iter().any(|entry| *entry >= self.prime))
        {
            return Err(PrimeEcologyError::MalformedPrimeMatrix);
        }
        Ok(())
    }

    fn multiply(&self, right: &Self) -> Result<Self, PrimeEcologyError> {
        self.validate()?;
        right.validate()?;
        if self.prime != right.prime || self.dimension() != right.dimension() {
            return Err(PrimeEcologyError::PrimeMatrixMismatch);
        }
        let dimension = self.dimension();
        let mut entries = vec![vec![0; dimension]; dimension];
        for (row, output) in entries.iter_mut().enumerate() {
            for (column, slot) in output.iter_mut().enumerate() {
                for inner in 0..dimension {
                    *slot = add_mod(
                        *slot,
                        mul_mod(
                            self.entries[row][inner],
                            right.entries[inner][column],
                            self.prime,
                        ),
                        self.prime,
                    );
                }
            }
        }
        Ok(Self {
            prime: self.prime,
            entries,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IrreduciblePrimeFactor {
    pub polynomial: PrimePolynomial,
    pub multiplicity: u32,
    /// Frobenius `a -> a^p` in the quotient basis `1,x,...,x^(d-1)`.
    pub frobenius: ExactPrimeMatrix,
    pub frobenius_order: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PrimeFactorPhaseType {
    pub degree: u32,
    pub frobenius_order: u32,
    pub multiplicity: u32,
    pub population: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PolynomialFiberSignature {
    pub degree: u32,
    pub distinct_root_count: u32,
    pub separable: bool,
    pub factor_phases: Vec<PrimeFactorPhaseType>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PolynomialPrimeFiber {
    pub schema: String,
    pub prime: u64,
    pub prime_cell: CausalCellId,
    pub probe: PolynomialProbeId,
    pub reduced: PrimePolynomial,
    pub derivative_gcd: PrimePolynomial,
    pub factors: Vec<IrreduciblePrimeFactor>,
    pub signature: PolynomialFiberSignature,
    pub work: PolynomialFactorizationWork,
    pub lineage: CausalMaterialLineage,
}

impl PolynomialPrimeFiber {
    pub fn validate(&self) -> Result<(), PrimeEcologyError> {
        if self.schema != "holonic-engine.polynomial-prime-fiber.v1"
            || self.reduced.prime != self.prime
            || self.derivative_gcd.prime != self.prime
            || self.factors.is_empty()
        {
            return Err(PrimeEcologyError::MalformedPolynomialFiber {
                prime: self.prime,
                probe: self.probe,
            });
        }
        self.reduced.validate()?;
        self.derivative_gcd.validate()?;
        if self.lineage.kind != CausalMaterialKind::Enacted || self.lineage.source_events.len() != 2
        {
            return Err(PrimeEcologyError::MalformedPolynomialFiber {
                prime: self.prime,
                probe: self.probe,
            });
        }
        let mut product = PrimePolynomial::one(self.prime);
        let mut previous = None;
        let mut grouped = BTreeMap::<(u32, u32, u32), u32>::new();
        let mut roots = 0_u32;
        for factor in &self.factors {
            factor.polynomial.validate()?;
            factor.frobenius.validate()?;
            if factor.polynomial.prime != self.prime
                || factor.multiplicity == 0
                || factor.frobenius.prime != self.prime
                || factor.frobenius.dimension()
                    != factor
                        .polynomial
                        .degree()
                        .ok_or(PrimeEcologyError::MalformedPrimePolynomial)?
            {
                return Err(PrimeEcologyError::MalformedPolynomialFiber {
                    prime: self.prime,
                    probe: self.probe,
                });
            }
            if previous
                .as_ref()
                .is_some_and(|polynomial: &PrimePolynomial| polynomial >= &factor.polynomial)
            {
                return Err(PrimeEcologyError::MalformedPolynomialFiber {
                    prime: self.prime,
                    probe: self.probe,
                });
            }
            previous = Some(factor.polynomial.clone());
            let degree = u32::try_from(
                factor
                    .polynomial
                    .degree()
                    .ok_or(PrimeEcologyError::MalformedPrimePolynomial)?,
            )
            .map_err(|_| PrimeEcologyError::CarrierOverflow)?;
            let mut irreducibility_work = PolynomialFactorizationWork::default();
            let factor_derivative = poly_derivative(&factor.polynomial)?;
            let factor_gcd = poly_gcd(
                &factor.polynomial,
                &factor_derivative,
                &mut irreducibility_work,
            )?;
            if factor_gcd.degree() != Some(0)
                || (degree > 1
                    && berlekamp_basis(&factor.polynomial, &mut irreducibility_work)?.len() != 1)
            {
                return Err(PrimeEcologyError::ReducibleReportedFactor);
            }
            let (expected_frobenius, expected_order) = frobenius_matrix(&factor.polynomial)?;
            if factor.frobenius != expected_frobenius || factor.frobenius_order != expected_order {
                return Err(PrimeEcologyError::FrobeniusOrderFailure);
            }
            if degree == 1 {
                roots = roots
                    .checked_add(1)
                    .ok_or(PrimeEcologyError::CarrierOverflow)?;
            }
            let computed_order = matrix_order(&factor.frobenius, degree)?;
            if factor.frobenius_order != computed_order {
                return Err(PrimeEcologyError::FrobeniusOrderFailure);
            }
            *grouped
                .entry((degree, factor.frobenius_order, factor.multiplicity))
                .or_default() += 1;
            for _ in 0..factor.multiplicity {
                product = poly_mul(&product, &factor.polynomial)?;
            }
        }
        if product != self.reduced {
            return Err(PrimeEcologyError::PolynomialFactorizationResidual);
        }
        let expected_signature = PolynomialFiberSignature {
            degree: u32::try_from(
                self.reduced
                    .degree()
                    .ok_or(PrimeEcologyError::MalformedPrimePolynomial)?,
            )
            .map_err(|_| PrimeEcologyError::CarrierOverflow)?,
            distinct_root_count: roots,
            separable: self.derivative_gcd.degree() == Some(0),
            factor_phases: grouped
                .into_iter()
                .map(
                    |((degree, frobenius_order, multiplicity), population)| PrimeFactorPhaseType {
                        degree,
                        frobenius_order,
                        multiplicity,
                        population,
                    },
                )
                .collect(),
        };
        if self.signature != expected_signature {
            return Err(PrimeEcologyError::MalformedPolynomialFiber {
                prime: self.prime,
                probe: self.probe,
            });
        }
        Ok(())
    }
}

fn matrix_order(matrix: &ExactPrimeMatrix, maximum: u32) -> Result<u32, PrimeEcologyError> {
    matrix.validate()?;
    let identity = ExactPrimeMatrix::identity(matrix.prime, matrix.dimension());
    let mut power = identity.clone();
    for order in 1..=maximum {
        power = power.multiply(matrix)?;
        if power == identity {
            return Ok(order);
        }
    }
    Err(PrimeEcologyError::FrobeniusOrderFailure)
}

fn frobenius_matrix(
    factor: &PrimePolynomial,
) -> Result<(ExactPrimeMatrix, u32), PrimeEcologyError> {
    let degree = factor
        .degree()
        .ok_or(PrimeEcologyError::MalformedPrimePolynomial)?;
    if degree == 0 {
        return Err(PrimeEcologyError::MalformedPrimePolynomial);
    }
    let x = PrimePolynomial::x(factor.prime);
    let mut entries = vec![vec![0; degree]; degree];
    for (column, basis_power) in (0_u128..).take(degree).enumerate() {
        let exponent = basis_power
            .checked_mul(u128::from(factor.prime))
            .ok_or(PrimeEcologyError::CarrierOverflow)?;
        let image = poly_pow_mod(&x, exponent, factor)?;
        for (row, coefficient) in image.coefficients.iter().enumerate() {
            entries[row][column] = *coefficient;
        }
    }
    let matrix = ExactPrimeMatrix {
        prime: factor.prime,
        entries,
    };
    let order = matrix_order(
        &matrix,
        u32::try_from(degree).map_err(|_| PrimeEcologyError::CarrierOverflow)?,
    )?;
    Ok((matrix, order))
}

fn nullspace_mod_prime(
    mut matrix: Vec<Vec<u64>>,
    prime: u64,
    work: &mut PolynomialFactorizationWork,
) -> Result<Vec<Vec<u64>>, PrimeEcologyError> {
    if matrix.is_empty() {
        return Ok(Vec::new());
    }
    let rows = matrix.len();
    let columns = matrix[0].len();
    if matrix.iter().any(|row| row.len() != columns) {
        return Err(PrimeEcologyError::MalformedPrimeMatrix);
    }
    let mut pivot_columns = Vec::new();
    let mut pivot_row = 0_usize;
    for column in 0..columns {
        let Some(found) = (pivot_row..rows).find(|row| matrix[*row][column] != 0) else {
            continue;
        };
        matrix.swap(pivot_row, found);
        let inverse = pow_mod(matrix[pivot_row][column], prime - 2, prime);
        for entry in &mut matrix[pivot_row] {
            *entry = mul_mod(*entry, inverse, prime);
        }
        for row in 0..rows {
            if row == pivot_row || matrix[row][column] == 0 {
                continue;
            }
            let factor = matrix[row][column];
            let pivot_values = matrix[pivot_row].clone();
            for (entry, pivot_entry) in matrix[row][column..]
                .iter_mut()
                .zip(&pivot_values[column..])
            {
                *entry = add_mod(
                    *entry,
                    neg_mod(mul_mod(factor, *pivot_entry, prime), prime),
                    prime,
                );
            }
            work.row_eliminations = work
                .row_eliminations
                .checked_add(1)
                .ok_or(PrimeEcologyError::CarrierOverflow)?;
        }
        pivot_columns.push(column);
        pivot_row += 1;
        if pivot_row == rows {
            break;
        }
    }
    let free_columns = (0..columns)
        .filter(|column| !pivot_columns.contains(column))
        .collect::<Vec<_>>();
    let mut basis = Vec::new();
    for free in free_columns {
        let mut vector = vec![0; columns];
        vector[free] = 1;
        for (row, pivot) in pivot_columns.iter().copied().enumerate().rev() {
            let mut sum = 0_u64;
            for (column, coefficient) in matrix[row].iter().enumerate().skip(pivot + 1) {
                sum = add_mod(sum, mul_mod(*coefficient, vector[column], prime), prime);
            }
            vector[pivot] = neg_mod(sum, prime);
        }
        basis.push(vector);
    }
    Ok(basis)
}

fn berlekamp_basis(
    polynomial: &PrimePolynomial,
    work: &mut PolynomialFactorizationWork,
) -> Result<Vec<PrimePolynomial>, PrimeEcologyError> {
    let degree = polynomial
        .degree()
        .ok_or(PrimeEcologyError::MalformedPrimePolynomial)?;
    let x = PrimePolynomial::x(polynomial.prime);
    let mut matrix = vec![vec![0; degree]; degree];
    for (column, basis_power) in (0_u128..).take(degree).enumerate() {
        let exponent = basis_power
            .checked_mul(u128::from(polynomial.prime))
            .ok_or(PrimeEcologyError::CarrierOverflow)?;
        let image = poly_pow_mod(&x, exponent, polynomial)?;
        work.frobenius_columns = work
            .frobenius_columns
            .checked_add(1)
            .ok_or(PrimeEcologyError::CarrierOverflow)?;
        for (row, coefficient) in image.coefficients.iter().enumerate() {
            matrix[row][column] = *coefficient;
        }
        matrix[column][column] = add_mod(
            matrix[column][column],
            neg_mod(1, polynomial.prime),
            polynomial.prime,
        );
    }
    nullspace_mod_prime(matrix, polynomial.prime, work)?
        .into_iter()
        .map(|coefficients| PrimePolynomial::new(polynomial.prime, coefficients))
        .collect()
}

fn berlekamp_split(
    polynomial: &PrimePolynomial,
    basis: &[PrimePolynomial],
    work: &mut PolynomialFactorizationWork,
) -> Result<(PrimePolynomial, PrimePolynomial), PrimeEcologyError> {
    for member in basis {
        if member.degree().unwrap_or(0) == 0 {
            continue;
        }
        for shift in 0..polynomial.prime {
            work.berlekamp_shifts = work
                .berlekamp_shifts
                .checked_add(1)
                .ok_or(PrimeEcologyError::CarrierOverflow)?;
            let shifted = poly_sub(
                member,
                &PrimePolynomial::new(polynomial.prime, vec![shift])?,
            )?;
            let divisor = poly_gcd(polynomial, &shifted, work)?;
            let divisor_degree = divisor.degree().unwrap_or(0);
            let polynomial_degree = polynomial.degree().unwrap_or(0);
            if divisor_degree == 0 || divisor_degree == polynomial_degree {
                continue;
            }
            let (quotient, remainder) = poly_div_rem(polynomial, &divisor)?;
            if !remainder.is_zero() {
                return Err(PrimeEcologyError::PolynomialFactorizationResidual);
            }
            return Ok((poly_monic(&divisor)?, poly_monic(&quotient)?));
        }
    }
    Err(PrimeEcologyError::BerlekampSplitFailure)
}

fn factor_monic(
    polynomial: &PrimePolynomial,
    population: &mut BTreeMap<PrimePolynomial, u32>,
    work: &mut PolynomialFactorizationWork,
) -> Result<(), PrimeEcologyError> {
    let polynomial = poly_monic(polynomial)?;
    let degree = polynomial
        .degree()
        .ok_or(PrimeEcologyError::MalformedPrimePolynomial)?;
    if degree == 0 {
        return Ok(());
    }
    if degree == 1 {
        *population.entry(polynomial).or_default() += 1;
        return Ok(());
    }

    let derivative = poly_derivative(&polynomial)?;
    if derivative.is_zero() {
        let prime_stride =
            usize::try_from(polynomial.prime).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
        if polynomial
            .coefficients
            .iter()
            .enumerate()
            .any(|(degree, coefficient)| degree % prime_stride != 0 && *coefficient != 0)
        {
            return Err(PrimeEcologyError::PerfectPowerExtractionFailure);
        }
        let root = PrimePolynomial::new(
            polynomial.prime,
            polynomial
                .coefficients
                .iter()
                .step_by(prime_stride)
                .copied()
                .collect(),
        )?;
        let mut root_population = BTreeMap::new();
        factor_monic(&root, &mut root_population, work)?;
        let prime_multiplicity =
            u32::try_from(polynomial.prime).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
        for (factor, multiplicity) in root_population {
            let total = multiplicity
                .checked_mul(prime_multiplicity)
                .ok_or(PrimeEcologyError::CarrierOverflow)?;
            *population.entry(factor).or_default() += total;
        }
        return Ok(());
    }

    let repeated = poly_gcd(&polynomial, &derivative, work)?;
    let repeated_degree = repeated.degree().unwrap_or(0);
    if repeated_degree > 0 && repeated_degree < degree {
        let (quotient, remainder) = poly_div_rem(&polynomial, &repeated)?;
        if !remainder.is_zero() {
            return Err(PrimeEcologyError::PolynomialFactorizationResidual);
        }
        factor_monic(&repeated, population, work)?;
        factor_monic(&quotient, population, work)?;
        return Ok(());
    }

    let basis = berlekamp_basis(&polynomial, work)?;
    if basis.len() == 1 {
        *population.entry(polynomial).or_default() += 1;
        return Ok(());
    }
    let (left, right) = berlekamp_split(&polynomial, &basis, work)?;
    factor_monic(&left, population, work)?;
    factor_monic(&right, population, work)?;
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FactoredPrimePolynomial {
    derivative_gcd: PrimePolynomial,
    factors: Vec<IrreduciblePrimeFactor>,
    signature: PolynomialFiberSignature,
    work: PolynomialFactorizationWork,
}

fn factor_prime_polynomial(
    reduced: &PrimePolynomial,
) -> Result<FactoredPrimePolynomial, PrimeEcologyError> {
    reduced.validate()?;
    let degree = reduced
        .degree()
        .ok_or(PrimeEcologyError::MalformedPrimePolynomial)?;
    if degree == 0 || reduced.leading() != 1 {
        return Err(PrimeEcologyError::MalformedPrimePolynomial);
    }
    let derivative = poly_derivative(reduced)?;
    let mut work = PolynomialFactorizationWork::default();
    let derivative_gcd = poly_gcd(reduced, &derivative, &mut work)?;
    let mut population = BTreeMap::new();
    factor_monic(reduced, &mut population, &mut work)?;
    let mut factors = Vec::new();
    let mut grouped = BTreeMap::<(u32, u32, u32), u32>::new();
    let mut roots = 0_u32;
    for (polynomial, multiplicity) in population {
        let factor_degree = u32::try_from(
            polynomial
                .degree()
                .ok_or(PrimeEcologyError::MalformedPrimePolynomial)?,
        )
        .map_err(|_| PrimeEcologyError::CarrierOverflow)?;
        let (frobenius, frobenius_order) = frobenius_matrix(&polynomial)?;
        if factor_degree == 1 {
            roots = roots
                .checked_add(1)
                .ok_or(PrimeEcologyError::CarrierOverflow)?;
        }
        *grouped
            .entry((factor_degree, frobenius_order, multiplicity))
            .or_default() += 1;
        factors.push(IrreduciblePrimeFactor {
            polynomial,
            multiplicity,
            frobenius,
            frobenius_order,
        });
    }
    let separable = derivative_gcd.degree() == Some(0);
    Ok(FactoredPrimePolynomial {
        derivative_gcd,
        factors,
        signature: PolynomialFiberSignature {
            degree: u32::try_from(degree).map_err(|_| PrimeEcologyError::CarrierOverflow)?,
            distinct_root_count: roots,
            separable,
            factor_phases: grouped
                .into_iter()
                .map(
                    |((degree, frobenius_order, multiplicity), population)| PrimeFactorPhaseType {
                        degree,
                        frobenius_order,
                        multiplicity,
                        population,
                    },
                )
                .collect(),
        },
        work,
    })
}

fn receive_polynomial_fiber(
    standing: &ArithmeticFiberStanding,
    prime: u64,
    probe_event: EventId,
    probe: &IntegerPolynomialProbe,
) -> Result<PolynomialPrimeFiber, PrimeEcologyError> {
    standing.validate()?;
    let prime_cell = standing.prime_cell(prime)?;
    let prime_event = standing
        .occurrences()
        .get(&prime)
        .ok_or(PrimeEcologyError::MissingPrimeOccurrence(prime))?
        .event;
    derive_polynomial_fiber(prime, prime_cell, prime_event, probe_event, probe)
}

fn derive_polynomial_fiber(
    prime: u64,
    prime_cell: CausalCellId,
    prime_event: EventId,
    probe_event: EventId,
    probe: &IntegerPolynomialProbe,
) -> Result<PolynomialPrimeFiber, PrimeEcologyError> {
    probe.validate()?;
    let reduced = reduce_integer_polynomial(prime, &probe.coefficients)?;
    if reduced.degree() != Some(probe.degree()) || reduced.leading() != 1 {
        return Err(PrimeEcologyError::ProbeDegreeCollapsed {
            prime,
            probe: probe.id,
        });
    }
    let factored = factor_prime_polynomial(&reduced)?;
    let fiber = PolynomialPrimeFiber {
        schema: "holonic-engine.polynomial-prime-fiber.v1".to_owned(),
        prime,
        prime_cell,
        probe: probe.id,
        reduced,
        derivative_gcd: factored.derivative_gcd,
        factors: factored.factors,
        signature: factored.signature,
        work: factored.work,
        lineage: CausalMaterialLineage::new(
            CausalMaterialKind::Enacted,
            BTreeSet::from([prime_event, probe_event]),
        ),
    };
    fiber.validate()?;
    Ok(fiber)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum PrimePhaseSource {
    InheritedProbe(PolynomialProbeId),
    HornFillerBranch(HornFillerBranchId),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PrimePhaseFeature {
    pub source: PrimePhaseSource,
    pub factor_phase: PrimeFactorPhaseType,
}

/// One affine family of monic integer polynomials.
///
/// For degree `d`, `coefficient_residues` stores the `d` free coefficients
/// `(a_0, ..., a_(d-1))`. Every member is
///
/// `x^d + Σ_i (a_i + modulus * z_i) x^i`, `z_i in Z`.
///
/// The least nonnegative coefficient vector is a presentation of the family,
/// not a privileged polynomial.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MonicPolynomialTorsor {
    pub modulus: BigInt,
    pub coefficient_residues: Vec<BigInt>,
}

impl MonicPolynomialTorsor {
    pub fn degree(&self) -> usize {
        self.coefficient_residues.len()
    }

    pub fn representative(&self) -> Vec<BigInt> {
        let mut coefficients = self.coefficient_residues.clone();
        coefficients.push(BigInt::one());
        coefficients
    }

    pub fn contains(&self, coefficients: &[BigInt]) -> bool {
        coefficients.len() == self.degree() + 1
            && coefficients.last() == Some(&BigInt::one())
            && self
                .coefficient_residues
                .iter()
                .zip(coefficients)
                .all(|(residue, coefficient)| {
                    normalized_bigint_mod(coefficient, &self.modulus) == *residue
                })
    }

    fn validate(&self) -> Result<(), PrimeEcologyError> {
        if !self.modulus.is_positive()
            || self.coefficient_residues.is_empty()
            || self
                .coefficient_residues
                .iter()
                .any(|coefficient| coefficient.is_negative() || coefficient >= &self.modulus)
        {
            return Err(PrimeEcologyError::MalformedPolynomialTorsor);
        }
        Ok(())
    }
}

/// One oriented continuation of a horn boundary phase.
///
/// A branch preserves the exact receiver polynomials on `source_face`, asks
/// the missing receiver for every monic local polynomial carrying the same
/// factor phase, and defines the coefficientwise CRT preimage of that entire
/// local stratum. Finite representatives are derived only when a receiver
/// requests them. The stratum can be empty: that is an exact obstruction, not
/// a failed random search.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MonicLocalPolynomialStratum {
    pub prime: u64,
    pub degree: u32,
    pub required_phase: PrimeFactorPhaseType,
    pub section_count: u64,
}

/// The chronology-free coefficient conditions underlying a causal branch.
///
/// `fixed_sections` are point fibers inherited from concrete local
/// reductions. `local_strata` are finite phase fibers retained symbolically.
/// Their pullbacks intersect coefficientwise over the pairwise-coprime
/// receivers. Equal values certify the same complete polynomial family even
/// when two causal boundary paths derived it in different orders.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MonicPolynomialConstraintFamily {
    pub degree: u32,
    pub modulus: BigInt,
    pub fixed_sections: BTreeMap<u64, PrimePolynomial>,
    pub local_strata: BTreeMap<u64, MonicLocalPolynomialStratum>,
    pub section_count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HornFillerBranch {
    pub id: HornFillerBranchId,
    pub source_face: Vec<u64>,
    pub missing_prime: u64,
    pub source_feature: PrimePhaseFeature,
    pub degree: u32,
    pub modulus: BigInt,
    pub fixed_sections: BTreeMap<u64, PrimePolynomial>,
    /// Variable receiver conditions inherited from prior filler families.
    pub carried_strata: BTreeMap<u64, MonicLocalPolynomialStratum>,
    /// The condition introduced by this branch's oriented missing receiver.
    pub missing_stratum: MonicLocalPolynomialStratum,
    /// Exact product of every variable receiver-stratum cardinality.
    pub section_count: u64,
    pub lineage: CausalMaterialLineage,
}

impl HornFillerBranch {
    pub fn is_obstructed(&self) -> bool {
        self.section_count == 0
    }

    pub fn torsor_count(&self) -> u64 {
        self.section_count
    }

    pub fn constraint_family(&self) -> Result<MonicPolynomialConstraintFamily, PrimeEcologyError> {
        let mut local_strata = self.carried_strata.clone();
        if local_strata
            .insert(self.missing_prime, self.missing_stratum.clone())
            .is_some()
        {
            return Err(PrimeEcologyError::MalformedHornFillerSpace(self.id.space));
        }
        Ok(MonicPolynomialConstraintFamily {
            degree: self.degree,
            modulus: self.modulus.clone(),
            fixed_sections: self.fixed_sections.clone(),
            local_strata,
            section_count: self.section_count,
        })
    }

    pub fn missing_local_sections(
        &self,
        limit: u64,
    ) -> Result<BTreeSet<PrimePolynomial>, PrimeEcologyError> {
        local_sections_for_stratum(&self.missing_stratum, limit)
    }

    pub fn torsors(&self, limit: u64) -> Result<Vec<MonicPolynomialTorsor>, PrimeEcologyError> {
        if self.torsor_count() > limit {
            return Err(PrimeEcologyError::HornTorsorInspectionSpaceExceeded {
                branch: self.id,
                sections: self.torsor_count(),
                limit,
            });
        }
        let family = self.constraint_family()?;
        let mut selections = vec![family.fixed_sections.clone()];
        for (prime, stratum) in &family.local_strata {
            let sections = local_sections_for_stratum(stratum, limit)?;
            if u64::try_from(sections.len()).map_err(|_| PrimeEcologyError::CarrierOverflow)?
                != stratum.section_count
            {
                return Err(PrimeEcologyError::MalformedHornFillerSpace(self.id.space));
            }
            let next_len = selections
                .len()
                .checked_mul(sections.len())
                .ok_or(PrimeEcologyError::CarrierOverflow)?;
            if u64::try_from(next_len).map_err(|_| PrimeEcologyError::CarrierOverflow)? > limit {
                return Err(PrimeEcologyError::HornTorsorInspectionSpaceExceeded {
                    branch: self.id,
                    sections: self.torsor_count(),
                    limit,
                });
            }
            let mut expanded = Vec::with_capacity(next_len);
            for selected in selections {
                for section in &sections {
                    let mut child = selected.clone();
                    if child.insert(*prime, section.clone()).is_some() {
                        return Err(PrimeEcologyError::MalformedHornFillerSpace(self.id.space));
                    }
                    expanded.push(child);
                }
            }
            selections = expanded;
        }
        let support = self.support();
        let mut torsors = selections
            .into_iter()
            .map(|selected| glue_local_polynomial_sections(&support, &selected, self.degree))
            .collect::<Result<Vec<_>, _>>()?;
        torsors.sort();
        torsors.dedup();
        if u64::try_from(torsors.len()).map_err(|_| PrimeEcologyError::CarrierOverflow)?
            != self.torsor_count()
            || torsors.iter().any(|torsor| torsor.modulus != self.modulus)
        {
            return Err(PrimeEcologyError::MalformedHornFillerSpace(self.id.space));
        }
        Ok(torsors)
    }

    pub fn contains(&self, coefficients: &[BigInt]) -> bool {
        if coefficients.len()
            != usize::try_from(self.degree)
                .ok()
                .and_then(|degree| degree.checked_add(1))
                .unwrap_or_default()
            || coefficients.last() != Some(&BigInt::one())
        {
            return false;
        }
        if self.fixed_sections.iter().any(|(prime, expected)| {
            match reduce_integer_polynomial(*prime, coefficients) {
                Ok(received) => received != *expected,
                Err(_) => true,
            }
        }) {
            return false;
        }
        self.constraint_family().is_ok_and(|family| {
            family.local_strata.values().all(|stratum| {
                reduce_integer_polynomial(stratum.prime, coefficients)
                    .and_then(|polynomial| factor_prime_polynomial(&polynomial))
                    .is_ok_and(|factored| {
                        factored
                            .signature
                            .factor_phases
                            .contains(&stratum.required_phase)
                    })
            })
        })
    }

    fn support(&self) -> Vec<u64> {
        let mut support = self.source_face.clone();
        support.push(self.missing_prime);
        support.sort_unstable();
        support
    }
}

/// The complete finite set of boundary-induced continuation branches for one
/// horn at one causal occurrence. It is generally a union of affine torsors,
/// not itself one torsor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HornFillerSpace {
    pub schema: String,
    pub id: HornFillerSpaceId,
    pub support: Vec<u64>,
    pub caused_at: EventId,
    pub boundary_features: BTreeMap<Vec<u64>, BTreeSet<PrimePhaseFeature>>,
    pub branches: Vec<HornFillerBranch>,
    pub lineage: CausalMaterialLineage,
}

impl HornFillerSpace {
    pub fn realised_branches(&self) -> impl Iterator<Item = &HornFillerBranch> {
        self.branches
            .iter()
            .filter(|branch| !branch.is_obstructed())
    }

    pub fn contains(&self, coefficients: &[BigInt]) -> bool {
        self.branches
            .iter()
            .any(|branch| branch.contains(coefficients))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactReceiverMeasure {
    pub section_count: u64,
    pub total_sections: u64,
    pub numerator: u64,
    pub denominator: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HornFillerRefinementStratum {
    pub signature: PolynomialFiberSignature,
    pub local_sections: BTreeSet<PrimePolynomial>,
    pub measure: ExactReceiverMeasure,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HornFillerRefinementReceipt {
    pub schema: String,
    pub branch: HornFillerBranchId,
    pub receiver_prime: u64,
    pub parent_modulus: BigInt,
    pub child_modulus: BigInt,
    pub parent_torsor_count: u64,
    pub children_per_parent: u64,
    pub child_torsor_count: u64,
    pub strata: Vec<HornFillerRefinementStratum>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InheritedPolynomialProbe {
    pub probe: IntegerPolynomialProbe,
    pub inherited_at: EventId,
    pub lineage: CausalMaterialLineage,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimePhaseCell {
    pub support: Vec<u64>,
    pub cell: CausalCellId,
    pub grade: u32,
    pub witness_features: BTreeSet<PrimePhaseFeature>,
    pub witness_events: BTreeSet<EventId>,
    pub lineage: CausalMaterialLineage,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrimeHornStatus {
    Open,
    Filled {
        cell: CausalCellId,
        filled_at: EventId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PotentialPrimeHorn {
    pub support: Vec<u64>,
    pub grade: u32,
    /// Immediate boundary cells in alternating-deletion order.
    pub boundary_cells: Vec<CausalCellId>,
    pub first_observed_at: EventId,
    pub status: PrimeHornStatus,
    pub lineage: CausalMaterialLineage,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PolynomialPresentationReceipt {
    pub schema: String,
    pub prime: u64,
    pub probe: PolynomialProbeId,
    pub supplied_coefficients: Vec<BigInt>,
    pub canonical_reduction: PrimePolynomial,
    pub supplied_reduction: PrimePolynomial,
    pub same_reduction: bool,
    pub same_signature: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeEcologyGeometryReceipt {
    pub schema: String,
    pub primes: Vec<u64>,
    pub probes: BTreeMap<PolynomialProbeId, IntegerPolynomialProbe>,
    pub fibers: BTreeMap<(u64, PolynomialProbeId), PolynomialFiberSignature>,
    pub filler_spaces: BTreeMap<HornFillerSpaceId, HornFillerSpace>,
    pub phase_cells: BTreeMap<Vec<u64>, BTreeSet<PrimePhaseFeature>>,
    pub open_horns: BTreeSet<Vec<u64>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeEcologyStanding {
    pub schema: String,
    pub max_phase_grade: u32,
    pub max_horn_local_sections: u64,
    arithmetic: ArithmeticFiberStanding,
    probes: BTreeMap<PolynomialProbeId, InheritedPolynomialProbe>,
    fibers: BTreeMap<(u64, PolynomialProbeId), PolynomialPrimeFiber>,
    filler_spaces: BTreeMap<HornFillerSpaceId, HornFillerSpace>,
    prime_features: BTreeMap<u64, BTreeSet<PrimePhaseFeature>>,
    phase_cells: BTreeMap<Vec<u64>, PrimePhaseCell>,
    horns: BTreeMap<Vec<u64>, PotentialPrimeHorn>,
    used_events: BTreeSet<EventId>,
}

impl PrimeEcologyStanding {
    pub fn new(max_phase_grade: u32) -> Result<Self, PrimeEcologyError> {
        Self::with_horn_local_section_limit(max_phase_grade, DEFAULT_HORN_LOCAL_SECTION_LIMIT)
    }

    pub fn with_horn_local_section_limit(
        max_phase_grade: u32,
        max_horn_local_sections: u64,
    ) -> Result<Self, PrimeEcologyError> {
        if max_phase_grade == 0 {
            return Err(PrimeEcologyError::ZeroPhaseGrade);
        }
        if max_horn_local_sections == 0 {
            return Err(PrimeEcologyError::ZeroHornLocalSectionLimit);
        }
        Ok(Self {
            schema: "holonic-engine.prime-ecology-standing.v3".to_owned(),
            max_phase_grade,
            max_horn_local_sections,
            arithmetic: ArithmeticFiberStanding::default(),
            probes: BTreeMap::new(),
            fibers: BTreeMap::new(),
            filler_spaces: BTreeMap::new(),
            prime_features: BTreeMap::new(),
            phase_cells: BTreeMap::new(),
            horns: BTreeMap::new(),
            used_events: BTreeSet::new(),
        })
    }

    pub fn arithmetic(&self) -> &ArithmeticFiberStanding {
        &self.arithmetic
    }

    pub fn probes(&self) -> &BTreeMap<PolynomialProbeId, InheritedPolynomialProbe> {
        &self.probes
    }

    pub fn fibers(&self) -> &BTreeMap<(u64, PolynomialProbeId), PolynomialPrimeFiber> {
        &self.fibers
    }

    pub fn filler_spaces(&self) -> &BTreeMap<HornFillerSpaceId, HornFillerSpace> {
        &self.filler_spaces
    }

    pub fn prime_features(&self) -> &BTreeMap<u64, BTreeSet<PrimePhaseFeature>> {
        &self.prime_features
    }

    pub fn phase_cells(&self) -> &BTreeMap<Vec<u64>, PrimePhaseCell> {
        &self.phase_cells
    }

    pub fn horns(&self) -> &BTreeMap<Vec<u64>, PotentialPrimeHorn> {
        &self.horns
    }

    pub fn open_horns(&self) -> impl Iterator<Item = &PotentialPrimeHorn> {
        self.horns
            .values()
            .filter(|horn| horn.status == PrimeHornStatus::Open)
    }

    pub fn geometry_receipt(&self) -> PrimeEcologyGeometryReceipt {
        self.geometry_receipt_for(
            &self
                .arithmetic
                .prime_cells()
                .keys()
                .copied()
                .collect::<BTreeSet<_>>(),
        )
    }

    pub fn geometry_receipt_for(
        &self,
        selected_primes: &BTreeSet<u64>,
    ) -> PrimeEcologyGeometryReceipt {
        PrimeEcologyGeometryReceipt {
            schema: "holonic-engine.prime-ecology-geometry-receipt.v3".to_owned(),
            primes: selected_primes.iter().copied().collect(),
            probes: self
                .probes
                .iter()
                .map(|(id, inherited)| (*id, inherited.probe.clone()))
                .collect(),
            fibers: self
                .fibers
                .iter()
                .filter_map(|((prime, probe), fiber)| {
                    selected_primes
                        .contains(prime)
                        .then_some(((*prime, *probe), fiber.signature.clone()))
                })
                .collect(),
            filler_spaces: self
                .filler_spaces
                .iter()
                .filter_map(|(id, space)| {
                    space
                        .support
                        .iter()
                        .all(|prime| selected_primes.contains(prime))
                        .then_some((*id, space.clone()))
                })
                .collect(),
            phase_cells: self
                .phase_cells
                .iter()
                .filter_map(|(support, cell)| {
                    support
                        .iter()
                        .all(|prime| selected_primes.contains(prime))
                        .then_some((support.clone(), cell.witness_features.clone()))
                })
                .collect(),
            open_horns: self
                .horns
                .iter()
                .filter_map(|(support, horn)| {
                    (horn.status == PrimeHornStatus::Open
                        && support.iter().all(|prime| selected_primes.contains(prime)))
                    .then_some(support.clone())
                })
                .collect(),
        }
    }

    pub fn compare_presentation(
        &self,
        prime: u64,
        probe: PolynomialProbeId,
        supplied_coefficients: Vec<BigInt>,
    ) -> Result<PolynomialPresentationReceipt, PrimeEcologyError> {
        self.validate()?;
        let canonical = self
            .fibers
            .get(&(prime, probe))
            .ok_or(PrimeEcologyError::MissingPolynomialFiber { prime, probe })?;
        let supplied_reduction = reduce_integer_polynomial(prime, &supplied_coefficients)?;
        let same_reduction = supplied_reduction == canonical.reduced;
        // A coefficient-wise equal reduction is the same receiver polynomial,
        // even when the integer presentation itself is not monic. The
        // canonical fiber was already re-factored and validated in standing.
        let same_signature = same_reduction;
        Ok(PolynomialPresentationReceipt {
            schema: "holonic-engine.polynomial-presentation-receipt.v1".to_owned(),
            prime,
            probe,
            supplied_coefficients,
            canonical_reduction: canonical.reduced.clone(),
            supplied_reduction,
            same_reduction,
            same_signature,
        })
    }

    /// Refine one coefficient family through an additional founded prime.
    ///
    /// Every parent torsor has exactly `prime^degree` children. The receipt
    /// groups the complete local polynomial population by exact factorization
    /// signature, so its relative measures are normalized cardinalities of
    /// deterministic receiver strata rather than samples.
    pub fn refine_filler_branch_at_prime(
        &self,
        branch: HornFillerBranchId,
        prime: u64,
    ) -> Result<HornFillerRefinementReceipt, PrimeEcologyError> {
        self.validate()?;
        if !self.arithmetic.prime_cells().contains_key(&prime) {
            return Err(PrimeEcologyError::MissingRefinementPrime(prime));
        }
        let space = self
            .filler_spaces
            .get(&branch.space)
            .ok_or(PrimeEcologyError::MissingHornFillerSpace(branch.space))?;
        let branch_standing = space
            .branches
            .iter()
            .find(|candidate| candidate.id == branch)
            .ok_or(PrimeEcologyError::MissingHornFillerBranch(branch))?;
        if space.support.contains(&prime) {
            return Err(PrimeEcologyError::RefinementPrimeAlreadyInSupport {
                space: space.id,
                prime,
            });
        }
        let local_population = enumerate_monic_polynomial_population(
            prime,
            branch_standing.degree,
            self.max_horn_local_sections,
        )?;
        let total_sections = u64::try_from(local_population.len())
            .map_err(|_| PrimeEcologyError::CarrierOverflow)?;
        let mut grouped = BTreeMap::<PolynomialFiberSignature, BTreeSet<PrimePolynomial>>::new();
        for (polynomial, signature) in local_population {
            grouped.entry(signature).or_default().insert(polynomial);
        }
        let strata = grouped
            .into_iter()
            .map(|(signature, local_sections)| {
                let section_count = u64::try_from(local_sections.len())
                    .map_err(|_| PrimeEcologyError::CarrierOverflow)?;
                let divisor = greatest_common_divisor(section_count, total_sections);
                Ok(HornFillerRefinementStratum {
                    signature,
                    local_sections,
                    measure: ExactReceiverMeasure {
                        section_count,
                        total_sections,
                        numerator: section_count / divisor,
                        denominator: total_sections / divisor,
                    },
                })
            })
            .collect::<Result<Vec<_>, PrimeEcologyError>>()?;
        let parent_torsor_count = branch_standing.torsor_count();
        let child_torsor_count = parent_torsor_count
            .checked_mul(total_sections)
            .ok_or(PrimeEcologyError::CarrierOverflow)?;
        Ok(HornFillerRefinementReceipt {
            schema: "holonic-engine.horn-filler-refinement-receipt.v1".to_owned(),
            branch,
            receiver_prime: prime,
            parent_modulus: branch_standing.modulus.clone(),
            child_modulus: &branch_standing.modulus * prime,
            parent_torsor_count,
            children_per_parent: total_sections,
            child_torsor_count,
            strata,
        })
    }

    pub fn validate(&self) -> Result<(), PrimeEcologyError> {
        if self.schema != "holonic-engine.prime-ecology-standing.v3"
            || self.max_phase_grade == 0
            || self.max_horn_local_sections == 0
        {
            return Err(PrimeEcologyError::MalformedPrimeEcologyStanding);
        }
        self.arithmetic.validate()?;

        let arithmetic_events = self
            .arithmetic
            .occurrences()
            .values()
            .map(|occurrence| occurrence.event)
            .collect::<BTreeSet<_>>();
        let probe_events = self
            .probes
            .values()
            .map(|inherited| inherited.inherited_at)
            .collect::<BTreeSet<_>>();
        let filler_events = self
            .filler_spaces
            .values()
            .map(|space| space.caused_at)
            .collect::<BTreeSet<_>>();
        if arithmetic_events.len() + probe_events.len() + filler_events.len()
            != self.used_events.len()
            || arithmetic_events
                .union(&probe_events)
                .copied()
                .chain(filler_events.iter().copied())
                .collect::<BTreeSet<_>>()
                != self.used_events
        {
            return Err(PrimeEcologyError::EcologyEventMismatch);
        }
        for (id, inherited) in &self.probes {
            inherited.probe.validate()?;
            if *id != inherited.probe.id
                || inherited.lineage.kind != CausalMaterialKind::Inherited
                || inherited.lineage.source_events != BTreeSet::from([inherited.inherited_at])
            {
                return Err(PrimeEcologyError::MalformedInheritedProbe(*id));
            }
        }

        let expected_fiber_keys = self
            .arithmetic
            .prime_cells()
            .keys()
            .flat_map(|prime| self.probes.keys().map(move |probe| (*prime, *probe)))
            .collect::<BTreeSet<_>>();
        if self.fibers.keys().copied().collect::<BTreeSet<_>>() != expected_fiber_keys {
            return Err(PrimeEcologyError::FiberPopulationMismatch);
        }
        for ((prime, probe), fiber) in &self.fibers {
            fiber.validate()?;
            let inherited = &self.probes[probe];
            let prime_cell = self.arithmetic.prime_cell(*prime)?;
            let prime_event = self.arithmetic.occurrences()[prime].event;
            let expected = derive_polynomial_fiber(
                *prime,
                prime_cell,
                prime_event,
                inherited.inherited_at,
                &inherited.probe,
            )?;
            if fiber.prime != *prime
                || fiber.probe != *probe
                || fiber.prime_cell != prime_cell
                || fiber.lineage.source_events
                    != BTreeSet::from([prime_event, inherited.inherited_at])
                || fiber != &expected
            {
                return Err(PrimeEcologyError::MalformedPolynomialFiber {
                    prime: *prime,
                    probe: *probe,
                });
            }
        }
        for (id, space) in &self.filler_spaces {
            if *id != space.id {
                return Err(PrimeEcologyError::MalformedHornFillerSpace(*id));
            }
            validate_horn_filler_space(self, space)?;
        }

        let mut expected_features = collect_prime_features(&self.fibers, &self.filler_spaces);
        for prime in self.arithmetic.prime_cells().keys() {
            expected_features.entry(*prime).or_default();
        }
        if self.prime_features != expected_features {
            return Err(PrimeEcologyError::PrimeFeatureMismatch);
        }
        for prime in self.arithmetic.prime_cells().keys() {
            if !self.prime_features.contains_key(prime) {
                return Err(PrimeEcologyError::PrimeFeatureMismatch);
            }
        }

        for (support, cell) in &self.phase_cells {
            validate_support(support)?;
            let expected_grade =
                u32::try_from(support.len() - 1).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
            if cell.support != *support
                || cell.grade != expected_grade
                || expected_grade > self.max_phase_grade
                || cell.lineage.kind != CausalMaterialKind::Induced
            {
                return Err(PrimeEcologyError::MalformedPhaseCell(support.clone()));
            }
            let witnesses = common_features(support, &self.prime_features)?;
            if witnesses.is_empty() || witnesses != cell.witness_features {
                return Err(PrimeEcologyError::MalformedPhaseCell(support.clone()));
            }
            let witness_events = feature_events(&witnesses, &self.probes, &self.filler_spaces)?;
            if witness_events != cell.witness_events {
                return Err(PrimeEcologyError::MalformedPhaseCell(support.clone()));
            }
            let expected_boundary = phase_boundary(support, &self.arithmetic, &self.phase_cells)?.0;
            let body = self.arithmetic.incidence().cell(cell.cell)?;
            if body.grade != expected_grade
                || body.boundary != expected_boundary
                || body.source_events != cell.lineage.source_events
            {
                return Err(PrimeEcologyError::MalformedPhaseCell(support.clone()));
            }
        }

        for (support, horn) in &self.horns {
            validate_support(support)?;
            if horn.support != *support
                || horn.grade
                    != u32::try_from(support.len() - 1)
                        .map_err(|_| PrimeEcologyError::CarrierOverflow)?
                || horn.lineage.kind != CausalMaterialKind::Proposed
            {
                return Err(PrimeEcologyError::MalformedPrimeHorn(support.clone()));
            }
            let (_, boundary_cells) = phase_boundary(support, &self.arithmetic, &self.phase_cells)?;
            if boundary_cells != horn.boundary_cells {
                return Err(PrimeEcologyError::MalformedPrimeHorn(support.clone()));
            }
            match horn.status {
                PrimeHornStatus::Open => {
                    if !common_features(support, &self.prime_features)?.is_empty()
                        || self.phase_cells.contains_key(support)
                    {
                        return Err(PrimeEcologyError::MalformedPrimeHorn(support.clone()));
                    }
                }
                PrimeHornStatus::Filled { cell, .. } => {
                    if self.phase_cells.get(support).map(|phase| phase.cell) != Some(cell) {
                        return Err(PrimeEcologyError::MalformedPrimeHorn(support.clone()));
                    }
                }
            }
        }
        self.validate_complete_geometry()?;
        Ok(())
    }

    fn validate_complete_geometry(&self) -> Result<(), PrimeEcologyError> {
        let primes = self
            .arithmetic
            .prime_cells()
            .keys()
            .copied()
            .collect::<Vec<_>>();
        let maximum_size = usize::try_from(self.max_phase_grade)
            .map_err(|_| PrimeEcologyError::CarrierOverflow)?
            .checked_add(1)
            .ok_or(PrimeEcologyError::CarrierOverflow)?
            .min(primes.len());
        for size in 2..=maximum_size {
            for support in combinations(&primes, size) {
                let witnesses = common_features(&support, &self.prime_features)?;
                if !witnesses.is_empty() {
                    if !self.phase_cells.contains_key(&support) {
                        return Err(PrimeEcologyError::MissingPhaseCell(support));
                    }
                } else if boundary_complete(&support, &self.phase_cells)
                    && self
                        .horns
                        .get(&support)
                        .is_none_or(|horn| horn.status != PrimeHornStatus::Open)
                {
                    return Err(PrimeEcologyError::MissingPrimeHorn(support));
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CausalWorld;

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

    fn ecology_probes() -> Vec<(EventId, IntegerPolynomialProbe)> {
        vec![
            (
                EventId(100),
                IntegerPolynomialProbe::cyclotomic(PolynomialProbeId(1), 3).unwrap(),
            ),
            (
                EventId(101),
                IntegerPolynomialProbe::cyclotomic(PolynomialProbeId(2), 5).unwrap(),
            ),
            (
                EventId(102),
                IntegerPolynomialProbe::cyclotomic(PolynomialProbeId(3), 7).unwrap(),
            ),
        ]
    }

    fn recurrent_quadratic_probes() -> Vec<(EventId, IntegerPolynomialProbe)> {
        [(6_u64, 100_u64), (10, 101), (14, 102)]
            .into_iter()
            .map(|(linear, event)| {
                (
                    EventId(event),
                    IntegerPolynomialProbe::new(
                        PolynomialProbeId(linear),
                        format!("quadratic-pairing[{linear}]"),
                        vec![BigInt::zero(), BigInt::from(linear), BigInt::one()],
                    )
                    .unwrap(),
                )
            })
            .collect()
    }

    fn ecology_primes_then_probes(limit: u64) -> CausalWorld<PrimeEcologyLaw> {
        let law = PrimeEcologyLaw::new(2).unwrap();
        let standing = PrimeEcologyStanding::new(2).unwrap();
        let mut world = CausalWorld::new(law, standing);
        for value in 2..=limit {
            world
                .receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                }))
                .unwrap();
        }
        for (event, probe) in ecology_probes() {
            world
                .receive(&PrimeEcologyEvent::InheritPolynomial { event, probe })
                .unwrap();
        }
        world
            .receive(&PrimeEcologyEvent::ResolveHorn {
                event: EventId(103),
                support: vec![2, 3, 5],
            })
            .unwrap();
        world
    }

    #[test]
    fn exact_factorization_carries_repeated_and_extension_field_frobenius_phases() {
        let arithmetic = arithmetic_through(7);
        let probe = IntegerPolynomialProbe::cyclotomic(PolynomialProbeId(1), 3).unwrap();

        let binary = receive_polynomial_fiber(&arithmetic, 2, EventId(100), &probe).unwrap();
        assert_eq!(
            binary.signature.factor_phases,
            vec![PrimeFactorPhaseType {
                degree: 2,
                frobenius_order: 2,
                multiplicity: 1,
                population: 1,
            }]
        );
        assert!(binary.signature.separable);
        assert_eq!(
            binary.factors[0].frobenius.entries,
            vec![vec![1, 1], vec![0, 1]]
        );
        assert_eq!(binary.factors[0].frobenius_order, 2);

        let ramified = receive_polynomial_fiber(&arithmetic, 3, EventId(100), &probe).unwrap();
        assert_eq!(
            ramified.signature.factor_phases,
            vec![PrimeFactorPhaseType {
                degree: 1,
                frobenius_order: 1,
                multiplicity: 2,
                population: 1,
            }]
        );
        assert!(!ramified.signature.separable);
        assert_eq!(ramified.signature.distinct_root_count, 1);

        let split = receive_polynomial_fiber(&arithmetic, 7, EventId(100), &probe).unwrap();
        assert_eq!(
            split.signature.factor_phases,
            vec![PrimeFactorPhaseType {
                degree: 1,
                frobenius_order: 1,
                multiplicity: 1,
                population: 2,
            }]
        );
        assert_eq!(split.signature.distinct_root_count, 2);
        split.validate().unwrap();
    }

    #[test]
    fn symbolic_phase_stratum_counts_equal_exhaustive_small_receiver_populations() {
        for prime in [2_u64, 3, 5] {
            for degree in 1..=4 {
                let population =
                    enumerate_monic_polynomial_population(prime, degree, 1_000).unwrap();
                let phases = population
                    .iter()
                    .flat_map(|(_, signature)| signature.factor_phases.iter().cloned())
                    .collect::<BTreeSet<_>>();
                for phase in phases {
                    let exhaustive = u64::try_from(
                        population
                            .iter()
                            .filter(|(_, signature)| signature.factor_phases.contains(&phase))
                            .count(),
                    )
                    .unwrap();
                    assert_eq!(
                        count_monic_polynomials_with_phase(prime, degree, &phase, 1_000).unwrap(),
                        exhaustive,
                        "prime={prime}, degree={degree}, phase={phase:?}"
                    );
                }
            }
        }
        assert_eq!(
            count_monic_polynomials_with_phase(
                2,
                3,
                &PrimeFactorPhaseType {
                    degree: 1,
                    frobenius_order: 1,
                    multiplicity: 1,
                    population: 3,
                },
                1_000,
            )
            .unwrap(),
            0
        );
    }

    #[test]
    fn induced_face_families_recombine_into_exact_tetrahedral_families() {
        let support = vec![2_u64, 3, 5, 7];
        let triangle_supports = combinations(&support, 3);
        let law = PrimeEcologyLaw::new(3).unwrap();
        let standing = PrimeEcologyStanding::new(3).unwrap();
        let mut world = CausalWorld::new(law, standing);
        for value in 2..=7 {
            world
                .receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                }))
                .unwrap();
        }
        for (event, probe) in recurrent_quadratic_probes() {
            world
                .receive(&PrimeEcologyEvent::InheritPolynomial { event, probe })
                .unwrap();
        }

        assert_eq!(
            combinations(&support, 2)
                .into_iter()
                .filter(|pair| world.standing().phase_cells.contains_key(pair))
                .count(),
            6
        );
        for triangle in &triangle_supports {
            assert_eq!(
                world.standing().horns[triangle].status,
                PrimeHornStatus::Open
            );
            assert!(!world.standing().phase_cells.contains_key(triangle));
        }
        assert!(!world.standing().phase_cells.contains_key(&support));
        assert!(!world.standing().horns.contains_key(&support));

        for (offset, triangle) in triangle_supports.iter().enumerate() {
            let receipt = world
                .receive(&PrimeEcologyEvent::ResolveHorn {
                    event: EventId(200 + u64::try_from(offset).unwrap()),
                    support: triangle.clone(),
                })
                .unwrap();
            let filler = receipt.radiation[0].induced_filler_space.as_ref().unwrap();
            assert_eq!(filler.branches.len(), 3);
            assert!(filler.branches.iter().all(|branch| {
                branch.carried_strata.is_empty()
                    && matches!(
                        &branch.source_feature.source,
                        PrimePhaseSource::InheritedProbe(_)
                    )
            }));
        }

        assert_eq!(
            world.standing().horns[&support].status,
            PrimeHornStatus::Open
        );
        let boundary_before = boundary_feature_snapshot(world.standing(), &support).unwrap();
        assert_eq!(boundary_before.len(), 4);
        assert!(boundary_before.values().all(|features| {
            !features.is_empty()
                && features
                    .iter()
                    .all(|feature| matches!(&feature.source, PrimePhaseSource::HornFillerBranch(_)))
        }));

        let receipt = world
            .receive(&PrimeEcologyEvent::ResolveHorn {
                event: EventId(204),
                support: support.clone(),
            })
            .unwrap();
        let filler = receipt.radiation[0].induced_filler_space.as_ref().unwrap();
        assert_eq!(filler.id, HornFillerSpaceId(204));
        assert_eq!(filler.branches.len(), 12);
        assert!(filler.realised_branches().count() == filler.branches.len());
        assert!(filler.branches.iter().all(|branch| {
            branch.degree == 2
                && branch.modulus == BigInt::from(210)
                && branch.fixed_sections.len() == 2
                && branch.carried_strata.len() == 1
                && matches!(
                    &branch.source_feature.source,
                    PrimePhaseSource::HornFillerBranch(_)
                )
        }));

        let mut homologous =
            BTreeMap::<MonicPolynomialConstraintFamily, Vec<&HornFillerBranch>>::new();
        for branch in &filler.branches {
            homologous
                .entry(branch.constraint_family().unwrap())
                .or_default()
                .push(branch);
            let parent_id = match &branch.source_feature.source {
                PrimePhaseSource::HornFillerBranch(parent_id) => *parent_id,
                PrimePhaseSource::InheritedProbe(_) => unreachable!(),
            };
            let parent_space = &world.standing().filler_spaces[&parent_id.space];
            assert_eq!(branch.source_face, parent_space.support);
            assert!(
                branch
                    .lineage
                    .source_events
                    .contains(&parent_space.caused_at)
            );
        }
        assert_eq!(homologous.len(), 6);
        assert!(homologous.values().all(|branches| branches.len() == 2));
        let mut family_counts = homologous
            .keys()
            .map(|family| family.section_count)
            .collect::<Vec<_>>();
        family_counts.sort_unstable();
        assert_eq!(family_counts, vec![3, 10, 15, 21, 21, 35]);

        for branches in homologous.values() {
            let left = branches[0]
                .torsors(DEFAULT_HORN_LOCAL_SECTION_LIMIT)
                .unwrap();
            let right = branches[1]
                .torsors(DEFAULT_HORN_LOCAL_SECTION_LIMIT)
                .unwrap();
            assert_eq!(left, right);
            assert_eq!(
                u64::try_from(left.len()).unwrap(),
                branches[0].torsor_count()
            );
            for torsor in left {
                let presentation = torsor.representative();
                assert!(branches[0].contains(&presentation));
                assert!(branches[1].contains(&presentation));
            }
        }

        let tetrahedron = &world.standing().phase_cells[&support];
        assert_eq!(tetrahedron.grade, 3);
        assert_eq!(
            world.standing().horns[&support].status,
            PrimeHornStatus::Filled {
                cell: tetrahedron.cell,
                filled_at: EventId(204),
            }
        );
        let body = world
            .standing()
            .arithmetic
            .incidence()
            .cell(tetrahedron.cell)
            .unwrap();
        assert!(
            world
                .standing()
                .arithmetic
                .incidence()
                .boundary_of_chain(&body.boundary)
                .unwrap()
                .is_zero()
        );
        world.standing().validate().unwrap();

        let closed = world.standing().clone();
        assert_eq!(
            world.receive(&PrimeEcologyEvent::ResolveHorn {
                event: EventId(205),
                support: support.clone(),
            }),
            Err(PrimeEcologyError::PrimeHornNotOpen(support.clone()))
        );
        assert_eq!(world.standing(), &closed);

        let mut malformed = closed;
        malformed
            .filler_spaces
            .get_mut(&HornFillerSpaceId(204))
            .unwrap()
            .branches[0]
            .section_count += 1;
        assert_eq!(
            malformed.validate(),
            Err(PrimeEcologyError::MalformedHornFillerSpace(
                HornFillerSpaceId(204)
            ))
        );
    }

    #[test]
    fn three_pairwise_phase_channels_derive_the_complete_horn_filler_space() {
        let law = PrimeEcologyLaw::new(2).unwrap();
        let standing = PrimeEcologyStanding::new(2).unwrap();
        let mut world = CausalWorld::new(law, standing);
        for value in 2..=5 {
            world
                .receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                }))
                .unwrap();
        }
        let probes = ecology_probes();
        for (event, probe) in probes {
            world
                .receive(&PrimeEcologyEvent::InheritPolynomial { event, probe })
                .unwrap();
        }
        let open = world.standing();
        assert!(open.phase_cells.contains_key(&vec![2, 3]));
        assert!(open.phase_cells.contains_key(&vec![2, 5]));
        assert!(open.phase_cells.contains_key(&vec![3, 5]));
        assert!(!open.phase_cells.contains_key(&vec![2, 3, 5]));
        assert_eq!(open.horns[&vec![2, 3, 5]].status, PrimeHornStatus::Open);
        assert_eq!(
            open.horns[&vec![2, 3, 5]].lineage.kind,
            CausalMaterialKind::Proposed
        );

        let receipt = world
            .receive(&PrimeEcologyEvent::ResolveHorn {
                event: EventId(103),
                support: vec![2, 3, 5],
            })
            .unwrap();
        let radiation = &receipt.radiation[0];
        let filler = radiation.induced_filler_space.as_ref().unwrap();
        assert_eq!(filler.id, HornFillerSpaceId(103));
        assert_eq!(filler.branches.len(), 3);
        assert_eq!(
            filler
                .branches
                .iter()
                .map(|branch| (branch.source_face.clone(), branch.torsor_count()))
                .collect::<BTreeMap<_, _>>(),
            BTreeMap::from([(vec![2, 3], 150), (vec![2, 5], 3), (vec![3, 5], 9),])
        );
        let quadratic = filler
            .branches
            .iter()
            .find(|branch| branch.source_face == vec![2, 5])
            .unwrap();
        assert_eq!(quadratic.degree, 2);
        assert_eq!(quadratic.modulus, BigInt::from(30));
        assert_eq!(quadratic.missing_stratum.section_count, 3);
        let quadratic_torsors = quadratic.torsors(DEFAULT_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert_eq!(
            quadratic_torsors
                .iter()
                .map(|torsor| torsor.coefficient_residues.clone())
                .collect::<Vec<_>>(),
            vec![
                vec![BigInt::one(), BigInt::from(21)],
                vec![BigInt::from(11), BigInt::one()],
                vec![BigInt::from(11), BigInt::from(11)],
            ]
        );
        assert!(quadratic.contains(&[BigInt::from(11), BigInt::one(), BigInt::one()]));
        assert!(quadratic.contains(&[BigInt::from(-19), BigInt::from(61), BigInt::one()]));
        assert!(
            radiation
                .filled_horns
                .iter()
                .any(|horn| horn.support == vec![2, 3, 5])
        );
        assert!(
            radiation
                .induced_cells
                .iter()
                .any(|cell| cell.support == vec![2, 3, 5])
        );
        let closed = world.standing();
        let triangle = &closed.phase_cells[&vec![2, 3, 5]];
        assert_eq!(triangle.lineage.kind, CausalMaterialKind::Induced);
        assert_eq!(
            closed.horns[&vec![2, 3, 5]].status,
            PrimeHornStatus::Filled {
                cell: triangle.cell,
                filled_at: EventId(103),
            }
        );
        assert!(
            closed
                .arithmetic
                .incidence()
                .boundary_of_chain(
                    &closed
                        .arithmetic
                        .incidence()
                        .cell(triangle.cell)
                        .unwrap()
                        .boundary
                )
                .unwrap()
                .is_zero()
        );
        assert_eq!(
            triangle
                .witness_features
                .iter()
                .filter(|feature| {
                    matches!(&feature.source, PrimePhaseSource::HornFillerBranch(_))
                })
                .count(),
            3
        );
        closed.validate().unwrap();

        for value in 6..=7 {
            world
                .receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                }))
                .unwrap();
        }
        let refinement = world
            .standing()
            .refine_filler_branch_at_prime(quadratic.id, 7)
            .unwrap();
        assert_eq!(refinement.children_per_parent, 49);
        assert_eq!(refinement.parent_torsor_count, 3);
        assert_eq!(refinement.child_torsor_count, 147);
        assert_eq!(refinement.child_modulus, BigInt::from(210));
        let mut measures = refinement
            .strata
            .iter()
            .map(|stratum| {
                (
                    stratum.measure.section_count,
                    stratum.measure.numerator,
                    stratum.measure.denominator,
                )
            })
            .collect::<Vec<_>>();
        measures.sort();
        assert_eq!(measures, vec![(7, 1, 7), (21, 3, 7), (21, 3, 7)]);
    }

    #[test]
    fn inherited_probe_and_prime_choreography_converge_to_one_geometry() {
        let primes_then_probes = ecology_primes_then_probes(5);

        let law = PrimeEcologyLaw::new(2).unwrap();
        let standing = PrimeEcologyStanding::new(2).unwrap();
        let mut probes_then_primes = CausalWorld::new(law, standing);
        for (event, probe) in ecology_probes() {
            probes_then_primes
                .receive(&PrimeEcologyEvent::InheritPolynomial { event, probe })
                .unwrap();
        }
        for value in 2..=5 {
            probes_then_primes
                .receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                }))
                .unwrap();
        }
        probes_then_primes
            .receive(&PrimeEcologyEvent::ResolveHorn {
                event: EventId(103),
                support: vec![2, 3, 5],
            })
            .unwrap();

        assert_eq!(
            primes_then_probes.standing().geometry_receipt(),
            probes_then_primes.standing().geometry_receipt()
        );
        assert!(
            primes_then_probes
                .standing()
                .horns
                .contains_key(&vec![2, 3, 5])
        );
        assert!(
            probes_then_primes
                .standing()
                .horns
                .contains_key(&vec![2, 3, 5])
        );
        probes_then_primes.standing().validate().unwrap();
    }

    #[test]
    fn presentation_and_ecology_enlargement_preserve_prior_receiver_geometry() {
        let mut world = ecology_primes_then_probes(5);
        let selected = BTreeSet::from([2, 3, 5]);
        let before = world.standing().geometry_receipt_for(&selected);
        let presentation = world
            .standing()
            .compare_presentation(
                3,
                PolynomialProbeId(2),
                vec![
                    BigInt::from(4),
                    BigInt::from(-2),
                    BigInt::from(7),
                    BigInt::from(-5),
                    BigInt::from(4),
                ],
            )
            .unwrap();
        assert!(presentation.same_reduction);
        assert!(presentation.same_signature);

        for value in 6..=11 {
            world
                .receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                }))
                .unwrap();
        }
        let after = world.standing().geometry_receipt_for(&selected);
        assert_eq!(before, after);
        world.standing().validate().unwrap();
    }

    #[test]
    fn a_common_receiver_phase_founds_a_grade_three_cell_with_closed_boundary() {
        let law = PrimeEcologyLaw::new(3).unwrap();
        let standing = PrimeEcologyStanding::new(3).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let probe = IntegerPolynomialProbe::cyclotomic(PolynomialProbeId(1), 2).unwrap();
        world
            .receive(&PrimeEcologyEvent::InheritPolynomial {
                event: EventId(100),
                probe,
            })
            .unwrap();
        for value in 2..=7 {
            world
                .receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                }))
                .unwrap();
        }
        let tetrahedron = &world.standing().phase_cells[&vec![2, 3, 5, 7]];
        assert_eq!(tetrahedron.grade, 3);
        let body = world
            .standing()
            .arithmetic
            .incidence()
            .cell(tetrahedron.cell)
            .unwrap();
        assert_eq!(body.boundary.support().len(), 4);
        assert!(
            world
                .standing()
                .arithmetic
                .incidence()
                .boundary_of_chain(&body.boundary)
                .unwrap()
                .is_zero()
        );
        world.standing().validate().unwrap();
    }

    #[test]
    fn duplicate_inheritance_is_refused_without_partial_ecology() {
        let mut world = ecology_primes_then_probes(5);
        let before = world.standing().clone();
        let probe = IntegerPolynomialProbe::cyclotomic(PolynomialProbeId(3), 2).unwrap();
        assert_eq!(
            world.receive(&PrimeEcologyEvent::InheritPolynomial {
                event: EventId(104),
                probe,
            }),
            Err(PrimeEcologyError::RepeatedPolynomialProbe(
                PolynomialProbeId(3)
            ))
        );
        assert_eq!(world.standing(), &before);
    }

    #[test]
    fn horn_search_limit_refuses_the_whole_resolution_atomically() {
        let law = PrimeEcologyLaw::with_horn_local_section_limit(2, 100).unwrap();
        let standing = PrimeEcologyStanding::with_horn_local_section_limit(2, 100).unwrap();
        let mut world = CausalWorld::new(law, standing);
        for value in 2..=5 {
            world
                .receive(&PrimeEcologyEvent::AdmitInteger(ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                }))
                .unwrap();
        }
        for (event, probe) in ecology_probes() {
            world
                .receive(&PrimeEcologyEvent::InheritPolynomial { event, probe })
                .unwrap();
        }
        let before = world.standing().clone();
        assert_eq!(
            world.receive(&PrimeEcologyEvent::ResolveHorn {
                event: EventId(103),
                support: vec![2, 3, 5],
            }),
            Err(PrimeEcologyError::HornLocalSectionSpaceExceeded {
                prime: 5,
                degree: 4,
                sections: BigInt::from(625),
                limit: 100,
            })
        );
        assert_eq!(world.standing(), &before);
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum PrimeEcologyError {
    #[error("prime ecology requires at least grade-one phase relations")]
    ZeroPhaseGrade,
    #[error("horn continuation requires a positive local-section limit")]
    ZeroHornLocalSectionLimit,
    #[error("prime-ecology law grade {law} does not match standing grade {standing}")]
    PhaseGradeMismatch { law: u32, standing: u32 },
    #[error(
        "prime-ecology horn local-section limit {law} does not match standing limit {standing}"
    )]
    HornLocalSectionLimitMismatch { law: u64, standing: u64 },
    #[error("source occurrence {0:?} was already used by this prime ecology")]
    RepeatedEcologyEvent(EventId),
    #[error("finite prime ecology exceeded an exact carrier")]
    CarrierOverflow,
    #[error("cyclotomic order must be positive")]
    ZeroCyclotomicOrder,
    #[error("cyclotomic polynomial division was not exact")]
    NonexactCyclotomicDivision,
    #[error("polynomial probe {0:?} is malformed")]
    MalformedPolynomialProbe(PolynomialProbeId),
    #[error("polynomial probe {0:?} has already entered this ecology")]
    RepeatedPolynomialProbe(PolynomialProbeId),
    #[error("polynomial probe {0:?} is absent")]
    MissingPolynomialProbe(PolynomialProbeId),
    #[error("inherited polynomial probe {0:?} has malformed lineage")]
    MalformedInheritedProbe(PolynomialProbeId),
    #[error("prime modulus {0} is invalid")]
    InvalidPrimeModulus(u64),
    #[error("a prime-field polynomial is malformed")]
    MalformedPrimePolynomial,
    #[error("polynomial division by zero is undefined")]
    PolynomialDivisionByZero,
    #[error("polynomials inhabit different prime fields: {left} and {right}")]
    PolynomialModulusMismatch { left: u64, right: u64 },
    #[error("probe {probe:?} loses degree at prime receiver {prime}")]
    ProbeDegreeCollapsed {
        prime: u64,
        probe: PolynomialProbeId,
    },
    #[error("prime {0} is missing its founding arithmetic occurrence")]
    MissingPrimeOccurrence(u64),
    #[error("finite-field factorization retained a nonzero product residual")]
    PolynomialFactorizationResidual,
    #[error("a reported finite-field factor is reducible")]
    ReducibleReportedFactor,
    #[error("a characteristic-p perfect-power extraction failed")]
    PerfectPowerExtractionFailure,
    #[error("Berlekamp factorization could not separate a reducible squarefree polynomial")]
    BerlekampSplitFailure,
    #[error("an exact prime-field matrix is malformed")]
    MalformedPrimeMatrix,
    #[error("prime-field matrices have incompatible modulus or dimension")]
    PrimeMatrixMismatch,
    #[error("a quotient-field Frobenius action failed to return at its exact order")]
    FrobeniusOrderFailure,
    #[error("polynomial fiber ({prime}, {probe:?}) is malformed")]
    MalformedPolynomialFiber {
        prime: u64,
        probe: PolynomialProbeId,
    },
    #[error("polynomial fiber ({prime}, {probe:?}) is absent")]
    MissingPolynomialFiber {
        prime: u64,
        probe: PolynomialProbeId,
    },
    #[error("prime ecology standing is malformed")]
    MalformedPrimeEcologyStanding,
    #[error("prime-ecology events do not match arithmetic and probe lineage")]
    EcologyEventMismatch,
    #[error("the polynomial fiber population does not cover every prime/probe pair")]
    FiberPopulationMismatch,
    #[error("derived prime phase features do not match retained fibers")]
    PrimeFeatureMismatch,
    #[error("prime {0} has no derived feature receiver")]
    MissingPrimeFeatures(u64),
    #[error("prime support is malformed: {0:?}")]
    MalformedPrimeSupport(Vec<u64>),
    #[error("phase support is missing immediate face {0:?}")]
    MissingPhaseFace(Vec<u64>),
    #[error("phase support is missing caused cell {0:?}")]
    MissingPhaseCell(Vec<u64>),
    #[error("boundary-complete support is missing potential horn {0:?}")]
    MissingPrimeHorn(Vec<u64>),
    #[error("potential prime horn is not open over support {0:?}")]
    PrimeHornNotOpen(Vec<u64>),
    #[error("phase cell is malformed over support {0:?}")]
    MalformedPhaseCell(Vec<u64>),
    #[error("potential prime horn is malformed over support {0:?}")]
    MalformedPrimeHorn(Vec<u64>),
    #[error("a monic polynomial coefficient torsor is malformed")]
    MalformedPolynomialTorsor,
    #[error("horn filler space {0:?} has already entered this ecology")]
    RepeatedHornFillerSpace(HornFillerSpaceId),
    #[error("horn filler space {0:?} is absent")]
    MissingHornFillerSpace(HornFillerSpaceId),
    #[error("horn filler branch {0:?} is absent")]
    MissingHornFillerBranch(HornFillerBranchId),
    #[error("horn filler space {0:?} is malformed")]
    MalformedHornFillerSpace(HornFillerSpaceId),
    #[error("an obstructed horn filler branch cannot witness a caused cell: {0:?}")]
    ObstructedHornFillerWitness(HornFillerBranchId),
    #[error(
        "receiver {prime} has {sections} monic degree-{degree} local sections, exceeding the declared limit {limit}"
    )]
    HornLocalSectionSpaceExceeded {
        prime: u64,
        degree: u32,
        sections: BigInt,
        limit: u64,
    },
    #[error(
        "horn filler branch {branch:?} has {sections} coefficient torsors, exceeding the requested inspection limit {limit}"
    )]
    HornTorsorInspectionSpaceExceeded {
        branch: HornFillerBranchId,
        sections: u64,
        limit: u64,
    },
    #[error("prime receiver {0} must be founded before refining a horn filler")]
    MissingRefinementPrime(u64),
    #[error("prime receiver {prime} already belongs to horn filler space {space:?}")]
    RefinementPrimeAlreadyInSupport {
        space: HornFillerSpaceId,
        prime: u64,
    },
    #[error("the nested arithmetic law returned no radiation")]
    MissingArithmeticRadiation,
    #[error(transparent)]
    Arithmetic(#[from] ArithmeticFiberError),
    #[error(transparent)]
    Algebraic(#[from] CausalAlgebraicError),
}

fn collect_prime_features(
    fibers: &BTreeMap<(u64, PolynomialProbeId), PolynomialPrimeFiber>,
    filler_spaces: &BTreeMap<HornFillerSpaceId, HornFillerSpace>,
) -> BTreeMap<u64, BTreeSet<PrimePhaseFeature>> {
    let mut features = BTreeMap::<u64, BTreeSet<PrimePhaseFeature>>::new();
    for ((prime, probe), fiber) in fibers {
        let receiver = features.entry(*prime).or_default();
        for factor_phase in &fiber.signature.factor_phases {
            receiver.insert(PrimePhaseFeature {
                source: PrimePhaseSource::InheritedProbe(*probe),
                factor_phase: factor_phase.clone(),
            });
        }
    }
    for space in filler_spaces.values() {
        for branch in space.realised_branches() {
            let feature = PrimePhaseFeature {
                source: PrimePhaseSource::HornFillerBranch(branch.id),
                factor_phase: branch.source_feature.factor_phase.clone(),
            };
            for prime in &space.support {
                features.entry(*prime).or_default().insert(feature.clone());
            }
        }
    }
    features
}

fn common_features(
    support: &[u64],
    prime_features: &BTreeMap<u64, BTreeSet<PrimePhaseFeature>>,
) -> Result<BTreeSet<PrimePhaseFeature>, PrimeEcologyError> {
    validate_support(support)?;
    let mut common = prime_features
        .get(&support[0])
        .cloned()
        .ok_or(PrimeEcologyError::MissingPrimeFeatures(support[0]))?;
    for prime in &support[1..] {
        let received = prime_features
            .get(prime)
            .ok_or(PrimeEcologyError::MissingPrimeFeatures(*prime))?;
        common = common.intersection(received).cloned().collect();
        if common.is_empty() {
            break;
        }
    }
    Ok(common)
}

fn feature_events(
    features: &BTreeSet<PrimePhaseFeature>,
    probes: &BTreeMap<PolynomialProbeId, InheritedPolynomialProbe>,
    filler_spaces: &BTreeMap<HornFillerSpaceId, HornFillerSpace>,
) -> Result<BTreeSet<EventId>, PrimeEcologyError> {
    let mut events = BTreeSet::new();
    for feature in features {
        match &feature.source {
            PrimePhaseSource::InheritedProbe(probe) => {
                events.insert(
                    probes
                        .get(probe)
                        .map(|inherited| inherited.inherited_at)
                        .ok_or(PrimeEcologyError::MissingPolynomialProbe(*probe))?,
                );
            }
            PrimePhaseSource::HornFillerBranch(branch) => {
                let space = filler_spaces
                    .get(&branch.space)
                    .ok_or(PrimeEcologyError::MissingHornFillerSpace(branch.space))?;
                let actual = space
                    .branches
                    .iter()
                    .find(|candidate| candidate.id == *branch)
                    .ok_or(PrimeEcologyError::MissingHornFillerBranch(*branch))?;
                if actual.is_obstructed() {
                    return Err(PrimeEcologyError::ObstructedHornFillerWitness(*branch));
                }
                events.extend(space.lineage.source_events.iter().copied());
            }
        }
    }
    Ok(events)
}

fn normalized_bigint_mod(value: &BigInt, modulus: &BigInt) -> BigInt {
    let residue = value % modulus;
    if residue.is_negative() {
        residue + modulus
    } else {
        residue
    }
}

fn greatest_common_divisor(mut left: u64, mut right: u64) -> u64 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

fn irreducible_polynomial_counts(
    prime: u64,
    maximum_degree: u32,
    limit: u64,
) -> Result<Vec<u64>, PrimeEcologyError> {
    let maximum =
        usize::try_from(maximum_degree).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
    let mut counts = vec![0_u64; maximum + 1];
    for degree in 1..=maximum {
        let exponent = u32::try_from(degree).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
        let all_monic = BigInt::from(prime).pow(exponent);
        if all_monic > BigInt::from(limit) {
            return Err(PrimeEcologyError::HornLocalSectionSpaceExceeded {
                prime,
                degree: maximum_degree,
                sections: BigInt::from(prime).pow(maximum_degree),
                limit,
            });
        }
        let all_monic = all_monic
            .to_u64()
            .ok_or(PrimeEcologyError::CarrierOverflow)?;
        let lower = (1..degree)
            .filter(|divisor| degree.is_multiple_of(*divisor))
            .try_fold(0_u64, |sum, divisor| {
                let contribution = u64::try_from(divisor)
                    .map_err(|_| PrimeEcologyError::CarrierOverflow)?
                    .checked_mul(counts[divisor])
                    .ok_or(PrimeEcologyError::CarrierOverflow)?;
                sum.checked_add(contribution)
                    .ok_or(PrimeEcologyError::CarrierOverflow)
            })?;
        let numerator = all_monic
            .checked_sub(lower)
            .ok_or(PrimeEcologyError::CarrierOverflow)?;
        let divisor = u64::try_from(degree).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
        if !numerator.is_multiple_of(divisor) {
            return Err(PrimeEcologyError::PolynomialFactorizationResidual);
        }
        counts[degree] = numerator / divisor;
    }
    Ok(counts)
}

fn count_monic_polynomials_with_phase(
    prime: u64,
    total_degree: u32,
    phase: &PrimeFactorPhaseType,
    limit: u64,
) -> Result<u64, PrimeEcologyError> {
    let ambient = BigInt::from(prime).pow(total_degree);
    if ambient > BigInt::from(limit) {
        return Err(PrimeEcologyError::HornLocalSectionSpaceExceeded {
            prime,
            degree: total_degree,
            sections: ambient,
            limit,
        });
    }
    if phase.degree == 0
        || phase.frobenius_order != phase.degree
        || phase.multiplicity == 0
        || phase.population == 0
    {
        return Ok(0);
    }
    let consumed = phase
        .degree
        .checked_mul(phase.multiplicity)
        .and_then(|degree| degree.checked_mul(phase.population))
        .ok_or(PrimeEcologyError::CarrierOverflow)?;
    if consumed > total_degree {
        return Ok(0);
    }
    let degree = usize::try_from(total_degree).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
    let target_degree =
        usize::try_from(phase.degree).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
    let target_multiplicity =
        usize::try_from(phase.multiplicity).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
    let target_population =
        usize::try_from(phase.population).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
    let irreducibles = irreducible_polynomial_counts(prime, total_degree, limit)?;
    if irreducibles[target_degree]
        < u64::try_from(target_population).map_err(|_| PrimeEcologyError::CarrierOverflow)?
    {
        return Ok(0);
    }

    let mut paths = vec![vec![0_u64; target_population + 1]; degree + 1];
    paths[0][0] = 1;
    for (factor_degree, irreducible_count) in
        irreducibles.iter().enumerate().take(degree + 1).skip(1)
    {
        let factor_population =
            usize::try_from(*irreducible_count).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
        for _ in 0..factor_population {
            let mut next = vec![vec![0_u64; target_population + 1]; degree + 1];
            for (used_degree, matched_paths) in paths.iter().enumerate() {
                for (matched, path_count) in matched_paths.iter().copied().enumerate() {
                    if path_count == 0 {
                        continue;
                    }
                    let maximum_exponent = (degree - used_degree) / factor_degree;
                    for exponent in 0..=maximum_exponent {
                        let next_matched = matched
                            + usize::from(
                                factor_degree == target_degree && exponent == target_multiplicity,
                            );
                        if next_matched > target_population {
                            continue;
                        }
                        let next_degree = used_degree + exponent * factor_degree;
                        next[next_degree][next_matched] = next[next_degree][next_matched]
                            .checked_add(path_count)
                            .ok_or(PrimeEcologyError::CarrierOverflow)?;
                    }
                }
            }
            paths = next;
        }
    }
    Ok(paths[degree][target_population])
}

fn checked_stratum_section_product(
    carried: &BTreeMap<u64, MonicLocalPolynomialStratum>,
    missing: &MonicLocalPolynomialStratum,
) -> Result<u64, PrimeEcologyError> {
    if missing.section_count == 0 || carried.values().any(|stratum| stratum.section_count == 0) {
        return Ok(0);
    }
    carried
        .values()
        .try_fold(missing.section_count, |product, stratum| {
            product
                .checked_mul(stratum.section_count)
                .ok_or(PrimeEcologyError::CarrierOverflow)
        })
}

fn local_sections_for_stratum(
    stratum: &MonicLocalPolynomialStratum,
    limit: u64,
) -> Result<BTreeSet<PrimePolynomial>, PrimeEcologyError> {
    enumerate_monic_polynomial_population(stratum.prime, stratum.degree, limit).map(|population| {
        population
            .into_iter()
            .filter_map(|(polynomial, signature)| {
                signature
                    .factor_phases
                    .contains(&stratum.required_phase)
                    .then_some(polynomial)
            })
            .collect()
    })
}

fn enumerate_monic_polynomial_population(
    prime: u64,
    degree: u32,
    limit: u64,
) -> Result<Vec<(PrimePolynomial, PolynomialFiberSignature)>, PrimeEcologyError> {
    if degree == 0 {
        return Err(PrimeEcologyError::MalformedPrimePolynomial);
    }
    let section_count = BigInt::from(prime).pow(degree);
    if section_count > BigInt::from(limit) {
        return Err(PrimeEcologyError::HornLocalSectionSpaceExceeded {
            prime,
            degree,
            sections: section_count,
            limit,
        });
    }
    let section_count = section_count
        .to_u64()
        .ok_or(PrimeEcologyError::CarrierOverflow)?;
    let degree = usize::try_from(degree).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
    let mut population = Vec::with_capacity(
        usize::try_from(section_count).map_err(|_| PrimeEcologyError::CarrierOverflow)?,
    );
    for encoded in 0..section_count {
        let mut digits = encoded;
        let mut coefficients = Vec::with_capacity(degree + 1);
        for _ in 0..degree {
            coefficients.push(digits % prime);
            digits /= prime;
        }
        coefficients.push(1);
        let polynomial = PrimePolynomial::new(prime, coefficients)?;
        let signature = factor_prime_polynomial(&polynomial)?.signature;
        population.push((polynomial, signature));
    }
    Ok(population)
}

fn glue_local_polynomial_sections(
    support: &[u64],
    local_sections: &BTreeMap<u64, PrimePolynomial>,
    degree: u32,
) -> Result<MonicPolynomialTorsor, PrimeEcologyError> {
    validate_support(support)?;
    let degree = usize::try_from(degree).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
    let mut coefficient_residues = Vec::with_capacity(degree);
    let mut modulus = None;
    for coefficient in 0..degree {
        let mut congruence = None;
        for prime in support {
            let polynomial = local_sections
                .get(prime)
                .ok_or_else(|| PrimeEcologyError::MalformedPrimeSupport(support.to_vec()))?;
            if polynomial.prime != *prime
                || polynomial.degree() != Some(degree)
                || polynomial.leading() != 1
            {
                return Err(PrimeEcologyError::MalformedPrimePolynomial);
            }
            let local =
                ExactCongruence::new(polynomial.coefficients[coefficient], BigInt::from(*prime))?;
            congruence = Some(match congruence {
                None => local,
                Some(received) => chinese_remainder_pair(received, local)?.combined,
            });
        }
        let received =
            congruence.ok_or_else(|| PrimeEcologyError::MalformedPrimeSupport(support.to_vec()))?;
        if let Some(expected) = &modulus {
            if expected != &received.modulus {
                return Err(PrimeEcologyError::MalformedPolynomialTorsor);
            }
        } else {
            modulus = Some(received.modulus.clone());
        }
        coefficient_residues.push(received.residue);
    }
    let torsor = MonicPolynomialTorsor {
        modulus: modulus
            .ok_or_else(|| PrimeEcologyError::MalformedPrimeSupport(support.to_vec()))?,
        coefficient_residues,
    };
    torsor.validate()?;
    Ok(torsor)
}

fn boundary_feature_snapshot(
    standing: &PrimeEcologyStanding,
    support: &[u64],
) -> Result<BTreeMap<Vec<u64>, BTreeSet<PrimePhaseFeature>>, PrimeEcologyError> {
    validate_support(support)?;
    let mut snapshot = BTreeMap::new();
    for removed in 0..support.len() {
        let mut face = support.to_vec();
        face.remove(removed);
        let features = if face.len() == 1 {
            standing
                .prime_features
                .get(&face[0])
                .cloned()
                .ok_or(PrimeEcologyError::MissingPrimeFeatures(face[0]))?
        } else {
            standing
                .phase_cells
                .get(&face)
                .map(|cell| cell.witness_features.clone())
                .ok_or_else(|| PrimeEcologyError::MissingPhaseFace(face.clone()))?
        };
        snapshot.insert(face, features);
    }
    Ok(snapshot)
}

fn derive_horn_filler_space_from_snapshot(
    standing: &PrimeEcologyStanding,
    caused_at: EventId,
    support: &[u64],
    boundary_features: BTreeMap<Vec<u64>, BTreeSet<PrimePhaseFeature>>,
    limit: u64,
) -> Result<HornFillerSpace, PrimeEcologyError> {
    validate_support(support)?;
    let horn = standing
        .horns
        .get(support)
        .ok_or_else(|| PrimeEcologyError::MissingPrimeHorn(support.to_vec()))?;
    let id = HornFillerSpaceId(caused_at.0);
    let mut source_events = horn.lineage.source_events.clone();
    source_events.insert(caused_at);
    let lineage = CausalMaterialLineage::new(CausalMaterialKind::Induced, source_events);
    let mut branches = Vec::new();
    let expected_faces = (0..support.len())
        .map(|removed| {
            let mut face = support.to_vec();
            face.remove(removed);
            face
        })
        .collect::<BTreeSet<_>>();
    if boundary_features.keys().cloned().collect::<BTreeSet<_>>() != expected_faces {
        return Err(PrimeEcologyError::MalformedHornFillerSpace(id));
    }

    for (source_face, features) in &boundary_features {
        if source_face.len() + 1 != support.len()
            || source_face.iter().any(|prime| !support.contains(prime))
        {
            return Err(PrimeEcologyError::MalformedHornFillerSpace(id));
        }
        let missing_primes = support
            .iter()
            .copied()
            .filter(|prime| !source_face.contains(prime))
            .collect::<Vec<_>>();
        if missing_primes.len() != 1 {
            return Err(PrimeEcologyError::MalformedHornFillerSpace(id));
        }
        let missing_prime = missing_primes[0];
        for source_feature in features {
            let (degree, fixed_sections, carried_strata) = match &source_feature.source {
                PrimePhaseSource::InheritedProbe(probe_id) => {
                    let probe_id = *probe_id;
                    let inherited = standing
                        .probes
                        .get(&probe_id)
                        .ok_or(PrimeEcologyError::MissingPolynomialProbe(probe_id))?;
                    let degree = u32::try_from(inherited.probe.degree())
                        .map_err(|_| PrimeEcologyError::CarrierOverflow)?;
                    let mut fixed_sections = BTreeMap::<u64, PrimePolynomial>::new();
                    for prime in source_face {
                        let fiber = standing.fibers.get(&(*prime, probe_id)).ok_or(
                            PrimeEcologyError::MissingPolynomialFiber {
                                prime: *prime,
                                probe: probe_id,
                            },
                        )?;
                        if !fiber
                            .signature
                            .factor_phases
                            .contains(&source_feature.factor_phase)
                        {
                            return Err(PrimeEcologyError::MalformedHornFillerSpace(id));
                        }
                        fixed_sections.insert(*prime, fiber.reduced.clone());
                    }
                    (degree, fixed_sections, BTreeMap::new())
                }
                PrimePhaseSource::HornFillerBranch(parent_id) => {
                    let parent_space = standing
                        .filler_spaces
                        .get(&parent_id.space)
                        .ok_or(PrimeEcologyError::MissingHornFillerSpace(parent_id.space))?;
                    let parent = parent_space
                        .branches
                        .iter()
                        .find(|candidate| candidate.id == *parent_id)
                        .ok_or(PrimeEcologyError::MissingHornFillerBranch(*parent_id))?;
                    // A parent family may recur only from the complete face on
                    // which it was caused. Reusing it from a proper subface
                    // would silently quotient away one or more prior
                    // receiver constraints.
                    if parent_space.support != *source_face {
                        continue;
                    }
                    if parent.is_obstructed()
                        || parent.source_feature.factor_phase != source_feature.factor_phase
                    {
                        return Err(PrimeEcologyError::MalformedHornFillerSpace(id));
                    }
                    let family = parent.constraint_family()?;
                    let constraint_support = family
                        .fixed_sections
                        .keys()
                        .chain(family.local_strata.keys())
                        .copied()
                        .collect::<BTreeSet<_>>();
                    if constraint_support != source_face.iter().copied().collect()
                        || family.local_strata.values().any(|stratum| {
                            stratum.degree != family.degree
                                || stratum.required_phase != source_feature.factor_phase
                        })
                    {
                        return Err(PrimeEcologyError::MalformedHornFillerSpace(id));
                    }
                    (family.degree, family.fixed_sections, family.local_strata)
                }
            };
            let section_count = count_monic_polynomials_with_phase(
                missing_prime,
                degree,
                &source_feature.factor_phase,
                limit,
            )?;
            let missing_stratum = MonicLocalPolynomialStratum {
                prime: missing_prime,
                degree,
                required_phase: source_feature.factor_phase.clone(),
                section_count,
            };
            let section_count = checked_stratum_section_product(&carried_strata, &missing_stratum)?;
            let modulus = support
                .iter()
                .fold(BigInt::one(), |product, prime| product * prime);
            branches.push(HornFillerBranch {
                id: HornFillerBranchId {
                    space: id,
                    ordinal: 0,
                },
                source_face: source_face.clone(),
                missing_prime,
                source_feature: source_feature.clone(),
                degree,
                modulus,
                fixed_sections,
                carried_strata,
                missing_stratum,
                section_count,
                lineage: lineage.clone(),
            });
        }
    }
    branches.sort_by(|left, right| {
        (&left.source_face, &left.source_feature).cmp(&(&right.source_face, &right.source_feature))
    });
    for (ordinal, branch) in branches.iter_mut().enumerate() {
        branch.id.ordinal =
            u32::try_from(ordinal).map_err(|_| PrimeEcologyError::CarrierOverflow)?;
    }
    Ok(HornFillerSpace {
        schema: "holonic-engine.horn-filler-space.v2".to_owned(),
        id,
        support: support.to_vec(),
        caused_at,
        boundary_features,
        branches,
        lineage,
    })
}

fn derive_horn_filler_space(
    standing: &PrimeEcologyStanding,
    caused_at: EventId,
    support: &[u64],
    limit: u64,
) -> Result<HornFillerSpace, PrimeEcologyError> {
    let boundary_features = boundary_feature_snapshot(standing, support)?;
    derive_horn_filler_space_from_snapshot(standing, caused_at, support, boundary_features, limit)
}

fn validate_horn_filler_space(
    standing: &PrimeEcologyStanding,
    space: &HornFillerSpace,
) -> Result<(), PrimeEcologyError> {
    if space.schema != "holonic-engine.horn-filler-space.v2"
        || space.id != HornFillerSpaceId(space.caused_at.0)
        || space.lineage.kind != CausalMaterialKind::Induced
    {
        return Err(PrimeEcologyError::MalformedHornFillerSpace(space.id));
    }
    let contemporary = boundary_feature_snapshot(standing, &space.support)?;
    if space.boundary_features.iter().any(|(face, features)| {
        contemporary
            .get(face)
            .is_none_or(|received| !features.is_subset(received))
    }) {
        return Err(PrimeEcologyError::MalformedHornFillerSpace(space.id));
    }
    let expected = derive_horn_filler_space_from_snapshot(
        standing,
        space.caused_at,
        &space.support,
        space.boundary_features.clone(),
        standing.max_horn_local_sections,
    )?;
    if &expected != space {
        return Err(PrimeEcologyError::MalformedHornFillerSpace(space.id));
    }
    if space.realised_branches().next().is_some()
        && standing
            .horns
            .get(&space.support)
            .is_none_or(|horn| !matches!(horn.status, PrimeHornStatus::Filled { .. }))
    {
        return Err(PrimeEcologyError::MalformedHornFillerSpace(space.id));
    }
    Ok(())
}

fn validate_support(support: &[u64]) -> Result<(), PrimeEcologyError> {
    if support.len() < 2 || support.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(PrimeEcologyError::MalformedPrimeSupport(support.to_vec()));
    }
    Ok(())
}

fn boundary_complete(support: &[u64], phase_cells: &BTreeMap<Vec<u64>, PrimePhaseCell>) -> bool {
    support.len() == 2
        || (0..support.len()).all(|removed| {
            let mut face = support.to_vec();
            face.remove(removed);
            phase_cells.contains_key(&face)
        })
}

fn phase_boundary(
    support: &[u64],
    arithmetic: &ArithmeticFiberStanding,
    phase_cells: &BTreeMap<Vec<u64>, PrimePhaseCell>,
) -> Result<(CausalChain, Vec<CausalCellId>), PrimeEcologyError> {
    validate_support(support)?;
    let mut boundary = CausalChain::default();
    let mut cells = Vec::with_capacity(support.len());
    for removed in 0..support.len() {
        let cell = if support.len() == 2 {
            arithmetic.prime_cell(support[1 - removed])?
        } else {
            let mut face = support.to_vec();
            face.remove(removed);
            phase_cells
                .get(&face)
                .map(|phase| phase.cell)
                .ok_or(PrimeEcologyError::MissingPhaseFace(face))?
        };
        cells.push(cell);
        boundary.add_term(
            cell,
            ComparativeMultiplicity::from_hand(if removed % 2 == 0 { 1 } else { -1 }, 1_u8)?,
        );
    }
    Ok((boundary, cells))
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

    if size == 0 || size > population.len() {
        return Vec::new();
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrimeEcologyEvent {
    AdmitInteger(ArithmeticFiberEvent),
    InheritPolynomial {
        event: EventId,
        probe: IntegerPolynomialProbe,
    },
    ResolveHorn {
        event: EventId,
        support: Vec<u64>,
    },
}

impl PrimeEcologyEvent {
    fn event_id(&self) -> EventId {
        match self {
            Self::AdmitInteger(event) => event.event,
            Self::InheritPolynomial { event, .. } => *event,
            Self::ResolveHorn { event, .. } => *event,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrimeEcologyOccurrence {
    Integer { value: u64 },
    Polynomial { probe: PolynomialProbeId },
    HornResolution { space: HornFillerSpaceId },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeEcologyRadiation {
    pub schema: String,
    pub event: EventId,
    pub occurrence: PrimeEcologyOccurrence,
    pub arithmetic: Option<ArithmeticFiberRadiation>,
    pub inherited_probe: Option<InheritedPolynomialProbe>,
    pub induced_filler_space: Option<HornFillerSpace>,
    pub enacted_fibers: Vec<PolynomialPrimeFiber>,
    pub induced_cells: Vec<PrimePhaseCell>,
    pub proposed_horns: Vec<PotentialPrimeHorn>,
    pub filled_horns: Vec<PotentialPrimeHorn>,
    pub expanded_cells: Vec<PrimePhaseCell>,
}

impl PrimeEcologyRadiation {
    fn integer(event: EventId, value: u64, arithmetic: ArithmeticFiberRadiation) -> Self {
        Self {
            schema: "holonic-engine.prime-ecology-radiation.v2".to_owned(),
            event,
            occurrence: PrimeEcologyOccurrence::Integer { value },
            arithmetic: Some(arithmetic),
            inherited_probe: None,
            induced_filler_space: None,
            enacted_fibers: Vec::new(),
            induced_cells: Vec::new(),
            proposed_horns: Vec::new(),
            filled_horns: Vec::new(),
            expanded_cells: Vec::new(),
        }
    }

    fn polynomial(event: EventId, inherited_probe: InheritedPolynomialProbe) -> Self {
        Self {
            schema: "holonic-engine.prime-ecology-radiation.v2".to_owned(),
            event,
            occurrence: PrimeEcologyOccurrence::Polynomial {
                probe: inherited_probe.probe.id,
            },
            arithmetic: None,
            inherited_probe: Some(inherited_probe),
            induced_filler_space: None,
            enacted_fibers: Vec::new(),
            induced_cells: Vec::new(),
            proposed_horns: Vec::new(),
            filled_horns: Vec::new(),
            expanded_cells: Vec::new(),
        }
    }

    fn horn(event: EventId, filler_space: HornFillerSpace) -> Self {
        Self {
            schema: "holonic-engine.prime-ecology-radiation.v2".to_owned(),
            event,
            occurrence: PrimeEcologyOccurrence::HornResolution {
                space: filler_space.id,
            },
            arithmetic: None,
            inherited_probe: None,
            induced_filler_space: Some(filler_space),
            enacted_fibers: Vec::new(),
            induced_cells: Vec::new(),
            proposed_horns: Vec::new(),
            filled_horns: Vec::new(),
            expanded_cells: Vec::new(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrimeEcologyLaw {
    max_phase_grade: u32,
    max_horn_local_sections: u64,
}

impl PrimeEcologyLaw {
    pub fn new(max_phase_grade: u32) -> Result<Self, PrimeEcologyError> {
        Self::with_horn_local_section_limit(max_phase_grade, DEFAULT_HORN_LOCAL_SECTION_LIMIT)
    }

    pub fn with_horn_local_section_limit(
        max_phase_grade: u32,
        max_horn_local_sections: u64,
    ) -> Result<Self, PrimeEcologyError> {
        if max_phase_grade == 0 {
            return Err(PrimeEcologyError::ZeroPhaseGrade);
        }
        if max_horn_local_sections == 0 {
            return Err(PrimeEcologyError::ZeroHornLocalSectionLimit);
        }
        Ok(Self {
            max_phase_grade,
            max_horn_local_sections,
        })
    }

    pub fn max_phase_grade(&self) -> u32 {
        self.max_phase_grade
    }

    pub fn max_horn_local_sections(&self) -> u64 {
        self.max_horn_local_sections
    }
}

impl ExactEventLaw for PrimeEcologyLaw {
    type Standing = PrimeEcologyStanding;
    type Event = PrimeEcologyEvent;
    type Radiation = PrimeEcologyRadiation;
    type Error = PrimeEcologyError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.validate()?;
        if standing_before.max_phase_grade != self.max_phase_grade {
            return Err(PrimeEcologyError::PhaseGradeMismatch {
                law: self.max_phase_grade,
                standing: standing_before.max_phase_grade,
            });
        }
        if standing_before.max_horn_local_sections != self.max_horn_local_sections {
            return Err(PrimeEcologyError::HornLocalSectionLimitMismatch {
                law: self.max_horn_local_sections,
                standing: standing_before.max_horn_local_sections,
            });
        }
        let event_id = event.event_id();
        if standing_before.used_events.contains(&event_id) {
            return Err(PrimeEcologyError::RepeatedEcologyEvent(event_id));
        }
        let mut standing_after = standing_before.clone();
        let mut radiation = match event {
            PrimeEcologyEvent::AdmitInteger(arithmetic_event) => {
                let successor =
                    ArithmeticFiberLaw.enact(&standing_after.arithmetic, arithmetic_event)?;
                let arithmetic_radiation = successor
                    .radiation
                    .into_iter()
                    .next()
                    .ok_or(PrimeEcologyError::MissingArithmeticRadiation)?;
                standing_after.arithmetic = successor.standing_after;
                let mut radiation = PrimeEcologyRadiation::integer(
                    event_id,
                    arithmetic_event.value,
                    arithmetic_radiation.clone(),
                );
                if let Some(founded) = &arithmetic_radiation.founded_prime {
                    for inherited in standing_after.probes.values() {
                        let fiber = receive_polynomial_fiber(
                            &standing_after.arithmetic,
                            founded.prime,
                            inherited.inherited_at,
                            &inherited.probe,
                        )?;
                        standing_after
                            .fibers
                            .insert((founded.prime, inherited.probe.id), fiber.clone());
                        radiation.enacted_fibers.push(fiber);
                    }
                    standing_after
                        .prime_features
                        .entry(founded.prime)
                        .or_default();
                    standing_after.reconcile_phase_topology(event_id, &mut radiation)?;
                }
                radiation
            }
            PrimeEcologyEvent::InheritPolynomial { event, probe } => {
                probe.validate()?;
                if standing_after.probes.contains_key(&probe.id) {
                    return Err(PrimeEcologyError::RepeatedPolynomialProbe(probe.id));
                }
                let inherited = InheritedPolynomialProbe {
                    probe: probe.clone(),
                    inherited_at: *event,
                    lineage: CausalMaterialLineage::new(
                        CausalMaterialKind::Inherited,
                        BTreeSet::from([*event]),
                    ),
                };
                standing_after.probes.insert(probe.id, inherited.clone());
                let mut radiation = PrimeEcologyRadiation::polynomial(*event, inherited);
                for prime in standing_after
                    .arithmetic
                    .prime_cells()
                    .keys()
                    .copied()
                    .collect::<Vec<_>>()
                {
                    let fiber =
                        receive_polynomial_fiber(&standing_after.arithmetic, prime, *event, probe)?;
                    standing_after
                        .fibers
                        .insert((prime, probe.id), fiber.clone());
                    radiation.enacted_fibers.push(fiber);
                }
                standing_after.reconcile_phase_topology(*event, &mut radiation)?;
                radiation
            }
            PrimeEcologyEvent::ResolveHorn { event, support } => {
                validate_support(support)?;
                let horn = standing_after
                    .horns
                    .get(support)
                    .ok_or_else(|| PrimeEcologyError::MissingPrimeHorn(support.clone()))?;
                if horn.status != PrimeHornStatus::Open {
                    return Err(PrimeEcologyError::PrimeHornNotOpen(support.clone()));
                }
                let filler_space = derive_horn_filler_space(
                    &standing_after,
                    *event,
                    support,
                    self.max_horn_local_sections,
                )?;
                if standing_after
                    .filler_spaces
                    .insert(filler_space.id, filler_space.clone())
                    .is_some()
                {
                    return Err(PrimeEcologyError::RepeatedHornFillerSpace(filler_space.id));
                }
                let mut radiation = PrimeEcologyRadiation::horn(*event, filler_space);
                standing_after.reconcile_phase_topology(*event, &mut radiation)?;
                radiation
            }
        };
        standing_after.used_events.insert(event_id);
        standing_after.validate()?;
        radiation
            .induced_cells
            .sort_by(|left, right| left.support.cmp(&right.support));
        radiation
            .proposed_horns
            .sort_by(|left, right| left.support.cmp(&right.support));
        radiation
            .filled_horns
            .sort_by(|left, right| left.support.cmp(&right.support));
        radiation
            .expanded_cells
            .sort_by(|left, right| left.support.cmp(&right.support));
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

impl PrimeEcologyStanding {
    fn reconcile_phase_topology(
        &mut self,
        event: EventId,
        radiation: &mut PrimeEcologyRadiation,
    ) -> Result<(), PrimeEcologyError> {
        self.prime_features = collect_prime_features(&self.fibers, &self.filler_spaces);
        for prime in self.arithmetic.prime_cells().keys() {
            self.prime_features.entry(*prime).or_default();
        }
        let primes = self
            .arithmetic
            .prime_cells()
            .keys()
            .copied()
            .collect::<Vec<_>>();
        let maximum_size = usize::try_from(self.max_phase_grade)
            .map_err(|_| PrimeEcologyError::CarrierOverflow)?
            .checked_add(1)
            .ok_or(PrimeEcologyError::CarrierOverflow)?
            .min(primes.len());
        for size in 2..=maximum_size {
            for support in combinations(&primes, size) {
                let witnesses = common_features(&support, &self.prime_features)?;
                if witnesses.is_empty() {
                    if !boundary_complete(&support, &self.phase_cells)
                        || self.horns.contains_key(&support)
                    {
                        continue;
                    }
                    let (_, boundary_cells) =
                        phase_boundary(&support, &self.arithmetic, &self.phase_cells)?;
                    let mut source_events = BTreeSet::from([event]);
                    for cell in &boundary_cells {
                        source_events.extend(
                            self.arithmetic
                                .incidence()
                                .cell(*cell)?
                                .source_events
                                .iter()
                                .copied(),
                        );
                    }
                    let grade = u32::try_from(support.len() - 1)
                        .map_err(|_| PrimeEcologyError::CarrierOverflow)?;
                    let horn = PotentialPrimeHorn {
                        support: support.clone(),
                        grade,
                        boundary_cells,
                        first_observed_at: event,
                        status: PrimeHornStatus::Open,
                        lineage: CausalMaterialLineage::new(
                            CausalMaterialKind::Proposed,
                            source_events,
                        ),
                    };
                    self.horns.insert(support, horn.clone());
                    radiation.proposed_horns.push(horn);
                    continue;
                }

                let witness_events = feature_events(&witnesses, &self.probes, &self.filler_spaces)?;
                if let Some(existing) = self.phase_cells.get_mut(&support) {
                    if existing.witness_features != witnesses {
                        existing.witness_features = witnesses;
                        existing.witness_events = witness_events;
                        radiation.expanded_cells.push(existing.clone());
                    }
                    continue;
                }

                let (boundary, _) = phase_boundary(&support, &self.arithmetic, &self.phase_cells)?;
                let mut source_events = witness_events.clone();
                for prime in &support {
                    source_events.insert(
                        self.arithmetic
                            .occurrences()
                            .get(prime)
                            .ok_or(PrimeEcologyError::MissingPrimeOccurrence(*prime))?
                            .event,
                    );
                }
                let grade = u32::try_from(support.len() - 1)
                    .map_err(|_| PrimeEcologyError::CarrierOverflow)?;
                let name = format!(
                    "prime-phase[{}]",
                    support
                        .iter()
                        .map(u64::to_string)
                        .collect::<Vec<_>>()
                        .join(",")
                );
                let cell = self.arithmetic.incidence_mut().found_cell(
                    name,
                    source_events.clone(),
                    grade,
                    boundary,
                )?;
                let phase_cell = PrimePhaseCell {
                    support: support.clone(),
                    cell,
                    grade,
                    witness_features: witnesses,
                    witness_events,
                    lineage: CausalMaterialLineage::new(CausalMaterialKind::Induced, source_events),
                };
                self.phase_cells.insert(support.clone(), phase_cell.clone());
                radiation.induced_cells.push(phase_cell);
                if let Some(horn) = self.horns.get_mut(&support)
                    && horn.status == PrimeHornStatus::Open
                {
                    horn.status = PrimeHornStatus::Filled {
                        cell,
                        filled_at: event,
                    };
                    radiation.filled_horns.push(horn.clone());
                }
            }
        }
        Ok(())
    }
}
