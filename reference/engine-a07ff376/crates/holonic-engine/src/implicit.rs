//! Exact local implicit supports and receiver-ray fibers.
//!
//! A local torus is retained as its quartic zero law. It is never tessellated
//! into triangles or renamed as a conic. Substituting one exact receiver ray
//! produces one univariate quartic whose rational and algebraic depth roots
//! carry Sturm certificates.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::{Rat, RatVec3};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    AlgebraicRoot, EventId, ExactInterval, ExactValueError, IntegerPolynomial,
    canonical_homogeneous,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ImplicitCellId(pub u64);

/// Exact local three-dimensional quadric
///
/// ```text
/// ax² + by² + cz² + dxy + exz + fyz + gx + hy + iz + j = 0.
/// ```
///
/// The coefficient scale is projective gauge. Construction canonicalizes that
/// gauge, while evaluation, differentials, and receiver-ray restriction remain
/// exact. A quadric is a local analytical support; it is never tessellated in
/// order to become visible to a receiver.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactQuadric3 {
    pub id: ImplicitCellId,
    pub source_event: EventId,
    pub last_event: EventId,
    pub coefficients: [Rat; 10],
}

impl ExactQuadric3 {
    pub fn new(
        id: ImplicitCellId,
        source_event: EventId,
        coefficients: [Rat; 10],
    ) -> Result<Self, ImplicitError> {
        if coefficients.iter().all(Zero::is_zero) {
            return Err(ImplicitError::ZeroQuadric);
        }
        Ok(Self {
            id,
            source_event,
            last_event: source_event,
            coefficients: canonical_homogeneous(coefficients),
        })
    }

    pub fn evaluate(&self, point: &RatVec3) -> Rat {
        let [a, b, c, d, e, f, g, h, i, j] = &self.coefficients;
        a * &point.x * &point.x
            + b * &point.y * &point.y
            + c * &point.z * &point.z
            + d * &point.x * &point.y
            + e * &point.x * &point.z
            + f * &point.y * &point.z
            + g * &point.x
            + h * &point.y
            + i * &point.z
            + j
    }

    /// Exact first differential in the local chart.
    pub fn gradient(&self, point: &RatVec3) -> RatVec3 {
        let [a, b, c, d, e, f, g, h, i, _] = &self.coefficients;
        RatVec3::new(
            Rat::from_integer(2.into()) * a * &point.x + d * &point.y + e * &point.z + g,
            Rat::from_integer(2.into()) * b * &point.y + d * &point.x + f * &point.z + h,
            Rat::from_integer(2.into()) * c * &point.z + e * &point.x + f * &point.y + i,
        )
    }

    /// Exact constant Hessian in the local chart.
    pub fn hessian(&self) -> [[Rat; 3]; 3] {
        let [a, b, c, d, e, f, ..] = &self.coefficients;
        [
            [Rat::from_integer(2.into()) * a, d.clone(), e.clone()],
            [d.clone(), Rat::from_integer(2.into()) * b, f.clone()],
            [e.clone(), f.clone(), Rat::from_integer(2.into()) * c],
        ]
    }

    /// Coefficients in ascending powers of the receiver-ray parameter.
    pub fn restrict_ray(&self, origin: &RatVec3, direction: &RatVec3) -> [Rat; 3] {
        let [a, b, c, d, e, f, ..] = &self.coefficients;
        let quadratic = a * &direction.x * &direction.x
            + b * &direction.y * &direction.y
            + c * &direction.z * &direction.z
            + d * &direction.x * &direction.y
            + e * &direction.x * &direction.z
            + f * &direction.y * &direction.z;
        [
            self.evaluate(origin),
            self.gradient(origin).dot(direction),
            quadratic,
        ]
    }

    pub fn ray_fiber(
        &self,
        origin: &RatVec3,
        direction: &RatVec3,
        interval: ExactInterval,
    ) -> Result<QuadricRayFiber, ImplicitError> {
        let polynomial = integer_polynomial(&self.restrict_ray(origin, direction))?;
        let roots = isolate_polynomial_roots(&polynomial, &interval)?;
        Ok(QuadricRayFiber {
            quadric: self.id,
            polynomial,
            interval,
            roots,
        })
    }

    pub fn ray_fiber_all(
        &self,
        origin: &RatVec3,
        direction: &RatVec3,
    ) -> Result<QuadricRayFiber, ImplicitError> {
        let polynomial = integer_polynomial(&self.restrict_ray(origin, direction))?;
        let mut bound = cauchy_root_bound(&polynomial);
        while polynomial.evaluate(&bound).is_zero()
            || polynomial.evaluate(&(-bound.clone())).is_zero()
        {
            bound += Rat::one();
        }
        let interval = ExactInterval::new(-bound.clone(), bound)?;
        let roots = isolate_polynomial_roots(&polynomial, &interval)?;
        Ok(QuadricRayFiber {
            quadric: self.id,
            polynomial,
            interval,
            roots,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuadricRayFiber {
    pub quadric: ImplicitCellId,
    pub polynomial: IntegerPolynomial,
    pub interval: ExactInterval,
    pub roots: Vec<CertifiedPolynomialRoot>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTorus {
    pub id: ImplicitCellId,
    pub source_event: EventId,
    pub last_event: EventId,
    pub center: RatVec3,
    /// Nonzero local symmetry axis. It need not be normalized, so rational
    /// source geometry never has to introduce a square root.
    pub axis: RatVec3,
    pub major_radius: Rat,
    pub minor_radius: Rat,
}

impl ExactTorus {
    pub fn new(
        id: ImplicitCellId,
        source_event: EventId,
        center: RatVec3,
        axis: RatVec3,
        major_radius: Rat,
        minor_radius: Rat,
    ) -> Result<Self, ImplicitError> {
        if axis.dot(&axis).is_zero() {
            return Err(ImplicitError::ZeroTorusAxis);
        }
        if !major_radius.is_positive() || !minor_radius.is_positive() {
            return Err(ImplicitError::NonPositiveTorusRadius);
        }
        Ok(Self {
            id,
            source_event,
            last_event: source_event,
            center,
            axis,
            major_radius,
            minor_radius,
        })
    }

    /// Evaluate a denominator-cleared quartic with the same zero locus as the
    /// ordinary torus equation.
    pub fn evaluate(&self, point: &RatVec3) -> Rat {
        let offset = point.subtract(&self.center);
        let axis_square = self.axis.dot(&self.axis);
        let distance_square = offset.dot(&offset);
        let axial = offset.dot(&self.axis);
        let radial_term = &axis_square * &distance_square - &axial * &axial;
        let radius_offset = distance_square + &self.major_radius * &self.major_radius
            - &self.minor_radius * &self.minor_radius;
        &axis_square * &radius_offset * &radius_offset
            - Rat::from_integer(4.into()) * &self.major_radius * &self.major_radius * radial_term
    }

    /// Exact first differential of the denominator-cleared quartic.
    pub fn gradient(&self, point: &RatVec3) -> RatVec3 {
        let offset = point.subtract(&self.center);
        let axis_square = self.axis.dot(&self.axis);
        let distance_square = offset.dot(&offset);
        let axial = offset.dot(&self.axis);
        let radius_square = &self.major_radius * &self.major_radius;
        let curvature_factor =
            distance_square - &radius_square - &self.minor_radius * &self.minor_radius;
        offset
            .scale(&(Rat::from_integer(4.into()) * &axis_square * curvature_factor))
            .add(
                &self
                    .axis
                    .scale(&(Rat::from_integer(8.into()) * radius_square * axial)),
            )
    }

    /// Exact Hessian of the denominator-cleared quartic in the local chart.
    pub fn hessian(&self, point: &RatVec3) -> [[Rat; 3]; 3] {
        let offset = point.subtract(&self.center);
        let components = [&offset.x, &offset.y, &offset.z];
        let axis = [&self.axis.x, &self.axis.y, &self.axis.z];
        let axis_square = self.axis.dot(&self.axis);
        let distance_square = offset.dot(&offset);
        let radius_square = &self.major_radius * &self.major_radius;
        let curvature_factor =
            distance_square - &radius_square - &self.minor_radius * &self.minor_radius;
        std::array::from_fn(|row| {
            std::array::from_fn(|column| {
                Rat::from_integer(8.into()) * &axis_square * components[row] * components[column]
                    + if row == column {
                        Rat::from_integer(4.into()) * &axis_square * &curvature_factor
                    } else {
                        Rat::zero()
                    }
                    + Rat::from_integer(8.into()) * &radius_square * axis[row] * axis[column]
            })
        })
    }

    /// Coefficients in ascending powers of the ray parameter.
    pub fn restrict_ray(&self, origin: &RatVec3, direction: &RatVec3) -> [Rat; 5] {
        let offset = origin.subtract(&self.center);
        let axis_square = self.axis.dot(&self.axis);
        let distance = [
            offset.dot(&offset),
            Rat::from_integer(2.into()) * offset.dot(direction),
            direction.dot(direction),
        ];
        let axial = [offset.dot(&self.axis), direction.dot(&self.axis)];
        let radius_offset = [
            &distance[0] + &self.major_radius * &self.major_radius
                - &self.minor_radius * &self.minor_radius,
            distance[1].clone(),
            distance[2].clone(),
        ];
        let squared_radius_offset = multiply_polynomials(&radius_offset, &radius_offset);
        let axial_square = multiply_polynomials(&axial, &axial);
        let mut radial_term = scale_polynomial(&distance, &axis_square);
        subtract_polynomial_in_place(&mut radial_term, &axial_square);
        let mut quartic = scale_polynomial(&squared_radius_offset, &axis_square);
        subtract_polynomial_in_place(
            &mut quartic,
            &scale_polynomial(
                &radial_term,
                &(Rat::from_integer(4.into()) * &self.major_radius * &self.major_radius),
            ),
        );
        std::array::from_fn(|index| quartic.get(index).cloned().unwrap_or_else(Rat::zero))
    }

    pub fn ray_fiber(
        &self,
        origin: &RatVec3,
        direction: &RatVec3,
        interval: ExactInterval,
    ) -> Result<TorusRayFiber, ImplicitError> {
        let polynomial = integer_polynomial(&self.restrict_ray(origin, direction))?;
        let roots = isolate_polynomial_roots(&polynomial, &interval)?;
        Ok(TorusRayFiber {
            torus: self.id,
            polynomial,
            interval,
            roots,
        })
    }

    pub fn ray_fiber_all(
        &self,
        origin: &RatVec3,
        direction: &RatVec3,
    ) -> Result<TorusRayFiber, ImplicitError> {
        let polynomial = integer_polynomial(&self.restrict_ray(origin, direction))?;
        let mut bound = cauchy_root_bound(&polynomial);
        while polynomial.evaluate(&bound).is_zero()
            || polynomial.evaluate(&(-bound.clone())).is_zero()
        {
            bound += Rat::one();
        }
        let interval = ExactInterval::new(-bound.clone(), bound)?;
        let roots = isolate_polynomial_roots(&polynomial, &interval)?;
        Ok(TorusRayFiber {
            torus: self.id,
            polynomial,
            interval,
            roots,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CertifiedPolynomialRoot {
    Rational {
        value: Rat,
        multiplicity: u32,
    },
    Algebraic {
        root: AlgebraicRoot,
        multiplicity: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TorusRayFiber {
    pub torus: ImplicitCellId,
    pub polynomial: IntegerPolynomial,
    pub interval: ExactInterval,
    pub roots: Vec<CertifiedPolynomialRoot>,
}

/// Additive numerator/denominator carrier for a normalized local field.
///
/// Local assembly and any certified exterior fold act componentwise. Division
/// occurs only at the receiver query, where a zero denominator remains a typed
/// seam.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactNormalizedField {
    pub numerator: Rat,
    pub denominator: Rat,
}

impl ExactNormalizedField {
    pub fn weighted(value: Rat, weight: Rat) -> Self {
        Self {
            numerator: &value * &weight,
            denominator: weight,
        }
    }

    pub fn assemble<'a>(parts: impl IntoIterator<Item = &'a Self>) -> Self {
        parts.into_iter().fold(Self::default(), |sum, part| Self {
            numerator: sum.numerator + &part.numerator,
            denominator: sum.denominator + &part.denominator,
        })
    }

    pub fn quotient(&self) -> ExactNormalizedFieldValue {
        if self.denominator.is_zero() {
            ExactNormalizedFieldValue::ZeroDenominator
        } else {
            ExactNormalizedFieldValue::Defined(&self.numerator / &self.denominator)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactNormalizedFieldValue {
    Defined(Rat),
    ZeroDenominator,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct NormalizedFieldTermId(pub u64);

/// One provenance-preserving local testimony in a normalized field.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactNormalizedFieldTerm {
    pub id: NormalizedFieldTermId,
    pub source: ImplicitCellId,
    pub event: EventId,
    pub value: Rat,
    pub weight: Rat,
}

impl ExactNormalizedFieldTerm {
    pub fn field(&self) -> ExactNormalizedField {
        ExactNormalizedField::weighted(self.value.clone(), self.weight.clone())
    }
}

/// One exact additive fold in an already-evaluated local field.
///
/// This is lawful recurrence of `(N,D)` contributions. It is not presented as
/// a general multipole expansion: a kernel-specific exterior law must still
/// explain how unevaluated distant constituents translate to a receiver and
/// certify any nonzero remainder.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactNormalizedFieldFold {
    pub members: BTreeSet<NormalizedFieldTermId>,
    pub field: ExactNormalizedField,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactNormalizedFieldFoldReceipt {
    pub terms: BTreeMap<NormalizedFieldTermId, ExactNormalizedFieldTerm>,
    pub folds: Vec<ExactNormalizedFieldFold>,
    pub direct: ExactNormalizedField,
    pub folded: ExactNormalizedField,
    pub numerator_residual: Rat,
    pub denominator_residual: Rat,
}

impl ExactNormalizedFieldFoldReceipt {
    /// Form a declared partition of exact local contributions and verify that
    /// folding it componentwise is identical to direct assembly.
    pub fn form(
        terms: impl IntoIterator<Item = ExactNormalizedFieldTerm>,
        partition: impl IntoIterator<Item = BTreeSet<NormalizedFieldTermId>>,
    ) -> Result<Self, ImplicitError> {
        let mut indexed = BTreeMap::new();
        for term in terms {
            if indexed.insert(term.id, term).is_some() {
                return Err(ImplicitError::DuplicateNormalizedFieldTerm);
            }
        }
        let mut covered = BTreeSet::new();
        let mut folds = Vec::new();
        for members in partition {
            if members.is_empty() {
                return Err(ImplicitError::EmptyNormalizedFieldFold);
            }
            let mut fields = Vec::new();
            for member in &members {
                if !covered.insert(*member) {
                    return Err(ImplicitError::OverlappingNormalizedFieldFold(*member));
                }
                let term = indexed
                    .get(member)
                    .ok_or(ImplicitError::MissingNormalizedFieldTerm(*member))?;
                fields.push(term.field());
            }
            folds.push(ExactNormalizedFieldFold {
                members,
                field: ExactNormalizedField::assemble(fields.iter()),
            });
        }
        let population = indexed.keys().copied().collect::<BTreeSet<_>>();
        if covered != population {
            return Err(ImplicitError::IncompleteNormalizedFieldPartition {
                population,
                covered,
            });
        }
        let direct_parts = indexed
            .values()
            .map(ExactNormalizedFieldTerm::field)
            .collect::<Vec<_>>();
        let direct = ExactNormalizedField::assemble(direct_parts.iter());
        let folded = ExactNormalizedField::assemble(folds.iter().map(|fold| &fold.field));
        let numerator_residual = &folded.numerator - &direct.numerator;
        let denominator_residual = &folded.denominator - &direct.denominator;
        debug_assert!(numerator_residual.is_zero() && denominator_residual.is_zero());
        Ok(Self {
            terms: indexed,
            folds,
            direct,
            folded,
            numerator_residual,
            denominator_residual,
        })
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ImplicitError {
    #[error("an exact quadric cannot have an all-zero coefficient presentation")]
    ZeroQuadric,
    #[error("a torus symmetry axis cannot be zero")]
    ZeroTorusAxis,
    #[error("torus radii must be positive")]
    NonPositiveTorusRadius,
    #[error("a receiver ray is wholly coincident with the implicit quartic")]
    CoincidentRay,
    #[error("one normalized-field term identity was supplied more than once")]
    DuplicateNormalizedFieldTerm,
    #[error("an exact normalized-field fold cannot be empty")]
    EmptyNormalizedFieldFold,
    #[error("normalized-field term {0:?} occurs in more than one fold")]
    OverlappingNormalizedFieldFold(NormalizedFieldTermId),
    #[error("normalized-field term {0:?} is absent from the supplied population")]
    MissingNormalizedFieldTerm(NormalizedFieldTermId),
    #[error("normalized-field folds do not partition the exact term population")]
    IncompleteNormalizedFieldPartition {
        population: BTreeSet<NormalizedFieldTermId>,
        covered: BTreeSet<NormalizedFieldTermId>,
    },
    #[error(transparent)]
    Exact(#[from] ExactValueError),
}

fn multiply_polynomials(left: &[Rat], right: &[Rat]) -> Vec<Rat> {
    let mut product = vec![Rat::zero(); left.len() + right.len() - 1];
    for (left_degree, left_coefficient) in left.iter().enumerate() {
        for (right_degree, right_coefficient) in right.iter().enumerate() {
            product[left_degree + right_degree] += left_coefficient * right_coefficient;
        }
    }
    trim(&mut product);
    product
}

fn scale_polynomial(polynomial: &[Rat], scalar: &Rat) -> Vec<Rat> {
    let mut scaled = polynomial
        .iter()
        .map(|coefficient| coefficient * scalar)
        .collect::<Vec<_>>();
    trim(&mut scaled);
    scaled
}

fn subtract_polynomial_in_place(target: &mut Vec<Rat>, subtraction: &[Rat]) {
    target.resize(target.len().max(subtraction.len()), Rat::zero());
    for (target, subtraction) in target.iter_mut().zip(subtraction) {
        *target -= subtraction;
    }
    trim(target);
}

fn trim(polynomial: &mut Vec<Rat>) {
    while polynomial.last().is_some_and(Zero::is_zero) {
        polynomial.pop();
    }
}

fn derivative(polynomial: &[Rat]) -> Vec<Rat> {
    let mut result = polynomial
        .iter()
        .enumerate()
        .skip(1)
        .map(|(degree, coefficient)| coefficient * Rat::from_integer(BigInt::from(degree)))
        .collect::<Vec<_>>();
    trim(&mut result);
    result
}

fn monic(mut polynomial: Vec<Rat>) -> Vec<Rat> {
    trim(&mut polynomial);
    if polynomial.is_empty() {
        return polynomial;
    }
    let leading = polynomial.last().unwrap().clone();
    for coefficient in &mut polynomial {
        *coefficient /= &leading;
    }
    polynomial
}

fn divide_with_remainder(dividend: &[Rat], divisor: &[Rat]) -> (Vec<Rat>, Vec<Rat>) {
    let mut remainder = dividend.to_vec();
    trim(&mut remainder);
    let mut quotient = if remainder.len() >= divisor.len() {
        vec![Rat::zero(); remainder.len() - divisor.len() + 1]
    } else {
        Vec::new()
    };
    while !remainder.is_empty() && remainder.len() >= divisor.len() {
        let shift = remainder.len() - divisor.len();
        let factor = remainder.last().unwrap() / divisor.last().unwrap();
        quotient[shift] = factor.clone();
        for (index, coefficient) in divisor.iter().enumerate() {
            remainder[index + shift] -= &factor * coefficient;
        }
        trim(&mut remainder);
    }
    trim(&mut quotient);
    (quotient, remainder)
}

fn divide_exact(dividend: &[Rat], divisor: &[Rat]) -> Vec<Rat> {
    let (quotient, remainder) = divide_with_remainder(dividend, divisor);
    debug_assert!(remainder.is_empty());
    quotient
}

fn polynomial_gcd(mut left: Vec<Rat>, mut right: Vec<Rat>) -> Vec<Rat> {
    trim(&mut left);
    trim(&mut right);
    while !right.is_empty() {
        let (_, remainder) = divide_with_remainder(&left, &right);
        left = right;
        right = remainder;
    }
    monic(left)
}

fn is_one(polynomial: &[Rat]) -> bool {
    polynomial.len() == 1 && polynomial[0].is_one()
}

fn squarefree_factors(polynomial: &IntegerPolynomial) -> Vec<(Vec<Rat>, u32)> {
    let function = monic(
        polynomial
            .coefficients
            .iter()
            .cloned()
            .map(Rat::from_integer)
            .collect(),
    );
    let derivative = derivative(&function);
    let mut repeated = polynomial_gcd(function.clone(), derivative);
    let mut remaining = divide_exact(&function, &repeated);
    let mut multiplicity = 1_u32;
    let mut factors = Vec::new();
    while !is_one(&remaining) {
        let shared = polynomial_gcd(remaining.clone(), repeated.clone());
        let factor = monic(divide_exact(&remaining, &shared));
        if !is_one(&factor) {
            factors.push((factor, multiplicity));
        }
        remaining = shared;
        repeated = divide_exact(&repeated, &remaining);
        multiplicity += 1;
    }
    factors
}

fn bigint_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn integer_polynomial(coefficients: &[Rat]) -> Result<IntegerPolynomial, ImplicitError> {
    let mut coefficients = coefficients.to_vec();
    trim(&mut coefficients);
    if coefficients.is_empty() {
        return Err(ImplicitError::CoincidentRay);
    }
    let denominator = coefficients.iter().fold(BigInt::one(), |lcm, value| {
        let denominator = value.denom().clone();
        &lcm / bigint_gcd(lcm.clone(), denominator.clone()) * denominator
    });
    let mut integers = coefficients
        .iter()
        .map(|value| value.numer() * (&denominator / value.denom()))
        .collect::<Vec<_>>();
    let content = integers.iter().cloned().fold(BigInt::zero(), bigint_gcd);
    if !content.is_zero() && !content.is_one() {
        for coefficient in &mut integers {
            *coefficient /= &content;
        }
    }
    if integers.last().is_some_and(Signed::is_negative) {
        for coefficient in &mut integers {
            *coefficient = -coefficient.clone();
        }
    }
    Ok(IntegerPolynomial::new(integers)?)
}

fn cauchy_root_bound(polynomial: &IntegerPolynomial) -> Rat {
    let leading = polynomial.coefficients.last().unwrap().abs();
    Rat::one()
        + polynomial.coefficients[..polynomial.coefficients.len() - 1]
            .iter()
            .map(|coefficient| Rat::new(coefficient.abs(), leading.clone()))
            .max()
            .unwrap_or_else(Rat::zero)
}

enum Isolation {
    Complete(Vec<ExactInterval>),
    RationalMidpoint(Rat),
}

fn isolate_intervals(
    polynomial: &IntegerPolynomial,
    interval: &ExactInterval,
) -> Result<Isolation, ExactValueError> {
    let count = polynomial.distinct_root_count(interval)?;
    if count == 0 {
        return Ok(Isolation::Complete(Vec::new()));
    }
    if count == 1 {
        return Ok(Isolation::Complete(vec![interval.clone()]));
    }
    let midpoint = (&interval.lower + &interval.upper) / Rat::from_integer(2.into());
    if polynomial.evaluate(&midpoint).is_zero() {
        return Ok(Isolation::RationalMidpoint(midpoint));
    }
    let left = ExactInterval::new(interval.lower.clone(), midpoint.clone())?;
    let right = ExactInterval::new(midpoint, interval.upper.clone())?;
    match isolate_intervals(polynomial, &left)? {
        Isolation::RationalMidpoint(root) => Ok(Isolation::RationalMidpoint(root)),
        Isolation::Complete(mut left_roots) => match isolate_intervals(polynomial, &right)? {
            Isolation::RationalMidpoint(root) => Ok(Isolation::RationalMidpoint(root)),
            Isolation::Complete(right_roots) => {
                left_roots.extend(right_roots);
                Ok(Isolation::Complete(left_roots))
            }
        },
    }
}

fn isolate_polynomial_roots(
    polynomial: &IntegerPolynomial,
    interval: &ExactInterval,
) -> Result<Vec<CertifiedPolynomialRoot>, ImplicitError> {
    let mut roots = Vec::new();
    for (factor, multiplicity) in squarefree_factors(polynomial) {
        let mut factor = integer_polynomial(&factor)?;
        loop {
            if factor.degree() == 0 {
                break;
            }
            match isolate_intervals(&factor, interval)? {
                Isolation::RationalMidpoint(value) => {
                    roots.push(CertifiedPolynomialRoot::Rational {
                        value: value.clone(),
                        multiplicity,
                    });
                    let rational = factor
                        .coefficients
                        .iter()
                        .cloned()
                        .map(Rat::from_integer)
                        .collect::<Vec<_>>();
                    factor = integer_polynomial(&divide_exact(&rational, &[-value, Rat::one()]))?;
                }
                Isolation::Complete(intervals) => {
                    for isolating_interval in intervals {
                        roots.push(CertifiedPolynomialRoot::Algebraic {
                            root: AlgebraicRoot::isolate(factor.clone(), isolating_interval)?,
                            multiplicity,
                        });
                    }
                    break;
                }
            }
        }
    }
    roots.sort_by(|left, right| {
        let lower = |root: &CertifiedPolynomialRoot| match root {
            CertifiedPolynomialRoot::Rational { value, .. } => value.clone(),
            CertifiedPolynomialRoot::Algebraic { root, .. } => {
                root.isolating_interval.lower.clone()
            }
        };
        lower(left).cmp(&lower(right))
    });
    Ok(roots)
}

#[cfg(test)]
mod tests {
    use relational_geometry::integer;

    use super::*;

    #[test]
    fn exact_quadric_carries_curvature_and_plural_receiver_depth() {
        let quadric = ExactQuadric3::new(
            ImplicitCellId(1),
            EventId(1),
            [
                integer(1),
                integer(1),
                integer(1),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(-4),
            ],
        )
        .unwrap();
        let point = RatVec3::from_i64(2, 0, 0);
        assert_eq!(quadric.evaluate(&point), Rat::zero());
        assert_eq!(quadric.gradient(&point), RatVec3::from_i64(4, 0, 0));
        assert_eq!(
            quadric.hessian(),
            [
                [integer(2), integer(0), integer(0)],
                [integer(0), integer(2), integer(0)],
                [integer(0), integer(0), integer(2)],
            ]
        );

        let fiber = quadric
            .ray_fiber_all(&RatVec3::from_i64(-3, 0, 0), &RatVec3::from_i64(1, 0, 0))
            .unwrap();
        assert_eq!(fiber.polynomial.degree(), 2);
        assert_eq!(fiber.roots.len(), 2);
        for (root, expected) in fiber.roots.iter().zip([integer(1), integer(5)]) {
            match root {
                CertifiedPolynomialRoot::Rational {
                    value,
                    multiplicity,
                } => {
                    assert_eq!(value, &expected);
                    assert_eq!(*multiplicity, 1);
                }
                CertifiedPolynomialRoot::Algebraic { root, multiplicity } => {
                    assert!(root.isolating_interval.lower < expected);
                    assert!(expected < root.isolating_interval.upper);
                    assert!(root.polynomial.evaluate(&expected).is_zero());
                    assert_eq!(*multiplicity, 1);
                }
            }
        }
    }

    #[test]
    fn exact_torus_exposes_first_and_second_differentials() {
        let torus = ExactTorus::new(
            ImplicitCellId(2),
            EventId(1),
            RatVec3::zero(),
            RatVec3::from_i64(0, 0, 1),
            integer(3),
            integer(1),
        )
        .unwrap();
        let point = RatVec3::from_i64(4, 0, 0);
        assert_eq!(torus.evaluate(&point), Rat::zero());
        assert_eq!(torus.gradient(&point), RatVec3::from_i64(96, 0, 0));
        assert_eq!(
            torus.hessian(&point),
            [
                [integer(152), integer(0), integer(0)],
                [integer(0), integer(24), integer(0)],
                [integer(0), integer(0), integer(96)],
            ]
        );
    }

    #[test]
    fn receiver_ray_meets_exact_torus_in_four_certified_depths() {
        let torus = ExactTorus::new(
            ImplicitCellId(1),
            EventId(1),
            RatVec3::zero(),
            RatVec3::from_i64(0, 0, 1),
            integer(3),
            integer(1),
        )
        .unwrap();
        let fiber = torus
            .ray_fiber(
                &RatVec3::from_i64(-5, 0, 0),
                &RatVec3::from_i64(1, 0, 0),
                ExactInterval::new(integer(0), integer(10)).unwrap(),
            )
            .unwrap();
        assert_eq!(fiber.polynomial.degree(), 4);
        assert_eq!(fiber.roots.len(), 4);
        for (root, expected) in
            fiber
                .roots
                .iter()
                .zip([integer(1), integer(3), integer(7), integer(9)])
        {
            match root {
                CertifiedPolynomialRoot::Rational {
                    value,
                    multiplicity,
                } => {
                    assert_eq!(value, &expected);
                    assert_eq!(*multiplicity, 1);
                }
                CertifiedPolynomialRoot::Algebraic { root, multiplicity } => {
                    assert!(root.isolating_interval.lower < expected);
                    assert!(expected < root.isolating_interval.upper);
                    assert!(root.polynomial.evaluate(&expected).is_zero());
                    assert_eq!(*multiplicity, 1);
                }
            }
        }
    }

    #[test]
    fn tangent_torus_root_retains_even_multiplicity() {
        let torus = ExactTorus::new(
            ImplicitCellId(2),
            EventId(1),
            RatVec3::zero(),
            RatVec3::from_i64(0, 0, 1),
            integer(3),
            integer(1),
        )
        .unwrap();
        let fiber = torus
            .ray_fiber(
                &RatVec3::from_i64(-5, 4, 0),
                &RatVec3::from_i64(1, 0, 0),
                ExactInterval::new(integer(0), integer(10)).unwrap(),
            )
            .unwrap();
        assert!(fiber.roots.iter().any(|root| match root {
            CertifiedPolynomialRoot::Rational { multiplicity, .. }
            | CertifiedPolynomialRoot::Algebraic { multiplicity, .. } => *multiplicity == 2,
        }));
    }

    #[test]
    fn normalized_field_assembles_before_quotient_and_keeps_zero_seam() {
        let first = ExactNormalizedField::weighted(integer(2), integer(3));
        let second = ExactNormalizedField::weighted(integer(-1), integer(1));
        let assembled = ExactNormalizedField::assemble([&first, &second]);
        assert_eq!(
            assembled.quotient(),
            ExactNormalizedFieldValue::Defined(integer(5) / integer(4))
        );
        assert_eq!(
            ExactNormalizedField::default().quotient(),
            ExactNormalizedFieldValue::ZeroDenominator
        );
    }

    #[test]
    fn normalized_field_fold_retains_provenance_and_exact_zero_residual() {
        let terms = [
            ExactNormalizedFieldTerm {
                id: NormalizedFieldTermId(1),
                source: ImplicitCellId(11),
                event: EventId(3),
                value: integer(2),
                weight: integer(3),
            },
            ExactNormalizedFieldTerm {
                id: NormalizedFieldTermId(2),
                source: ImplicitCellId(12),
                event: EventId(3),
                value: integer(-1),
                weight: integer(1),
            },
            ExactNormalizedFieldTerm {
                id: NormalizedFieldTermId(3),
                source: ImplicitCellId(13),
                event: EventId(4),
                value: integer(4),
                weight: integer(2),
            },
        ];
        let receipt = ExactNormalizedFieldFoldReceipt::form(
            terms,
            [
                BTreeSet::from([NormalizedFieldTermId(1), NormalizedFieldTermId(2)]),
                BTreeSet::from([NormalizedFieldTermId(3)]),
            ],
        )
        .unwrap();
        assert_eq!(receipt.folds.len(), 2);
        assert_eq!(receipt.numerator_residual, Rat::zero());
        assert_eq!(receipt.denominator_residual, Rat::zero());
        assert_eq!(receipt.direct, receipt.folded);
        assert_eq!(
            receipt.folded.quotient(),
            ExactNormalizedFieldValue::Defined(integer(13) / integer(6))
        );
        assert_eq!(
            receipt
                .terms
                .keys()
                .copied()
                .collect::<BTreeSet<NormalizedFieldTermId>>(),
            BTreeSet::from([
                NormalizedFieldTermId(1),
                NormalizedFieldTermId(2),
                NormalizedFieldTermId(3),
            ])
        );
    }
}
