//! Native exact conics and receiver-relative root fibers.
//!
//! A conic is carried by its homogeneous quadratic law in one caused local
//! two-dimensional chart.  Its species is derived from that law.  Sampling,
//! tessellation, and a display approximation are never its identity.

use std::cmp::Ordering;
use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::{FrameId, Rat, RatMat3, RatVec3};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    AlgebraicRoot, EventId, EvolutionShape, ExactInterval, ExactValue, ExactValueError,
    IntegerPolynomial, canonical_homogeneous,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ConicCellId(pub u64);

/// Coefficients of
///
/// `xx*x^2 + xy*x*y + yy*y^2 + xw*x*w + yw*y*w + ww*w^2 = 0`.
///
/// The six-coefficient face avoids hidden halves while retaining the complete
/// symmetric homogeneous quadratic.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HomogeneousConic {
    pub xx: Rat,
    pub xy: Rat,
    pub yy: Rat,
    pub xw: Rat,
    pub yw: Rat,
    pub ww: Rat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConicClass {
    CircleInThisChart,
    EllipseInThisChart,
    ParabolaInThisChart,
    HyperbolaInThisChart,
    IntersectingLinePair,
    ParallelLinePair,
    Degenerate,
}

impl HomogeneousConic {
    pub fn new(coefficients: [Rat; 6]) -> Result<Self, ConicError> {
        if coefficients.iter().all(Zero::is_zero) {
            return Err(ConicError::ZeroConic);
        }
        let coefficients = canonical_homogeneous(coefficients);
        Ok(Self {
            xx: coefficients[0].clone(),
            xy: coefficients[1].clone(),
            yy: coefficients[2].clone(),
            xw: coefficients[3].clone(),
            yw: coefficients[4].clone(),
            ww: coefficients[5].clone(),
        })
    }

    pub fn coefficients(&self) -> [Rat; 6] {
        [
            self.xx.clone(),
            self.xy.clone(),
            self.yy.clone(),
            self.xw.clone(),
            self.yw.clone(),
            self.ww.clone(),
        ]
    }

    pub fn evaluate(&self, point: &[Rat; 3]) -> Rat {
        let [x, y, w] = point;
        &self.xx * x * x
            + &self.xy * x * y
            + &self.yy * y * y
            + &self.xw * x * w
            + &self.yw * y * w
            + &self.ww * w * w
    }

    /// Twice the usual symmetric conic matrix. Scaling does not change the
    /// zero locus, rank, or degeneracy.
    pub fn doubled_matrix(&self) -> RatMat3 {
        RatMat3::new([
            [
                &self.xx * Rat::from_integer(2.into()),
                self.xy.clone(),
                self.xw.clone(),
            ],
            [
                self.xy.clone(),
                &self.yy * Rat::from_integer(2.into()),
                self.yw.clone(),
            ],
            [
                self.xw.clone(),
                self.yw.clone(),
                &self.ww * Rat::from_integer(2.into()),
            ],
        ])
    }

    /// Recover the six-coefficient face from twice a symmetric quadratic
    /// matrix.  The constructor refuses a nonsymmetric carrier rather than
    /// silently choosing one triangular half.
    pub fn from_doubled_matrix(matrix: &RatMat3) -> Result<Self, ConicError> {
        if matrix.rows[0][1] != matrix.rows[1][0]
            || matrix.rows[0][2] != matrix.rows[2][0]
            || matrix.rows[1][2] != matrix.rows[2][1]
        {
            return Err(ConicError::NonsymmetricMatrix);
        }
        let two = Rat::from_integer(2.into());
        Self::new([
            &matrix.rows[0][0] / &two,
            matrix.rows[0][1].clone(),
            &matrix.rows[1][1] / &two,
            matrix.rows[0][2].clone(),
            matrix.rows[1][2].clone(),
            &matrix.rows[2][2] / two,
        ])
    }

    /// Classification is explicitly relative to the current affine chart.
    /// Degeneracy is projectively invariant; circle/ellipse/parabola/
    /// hyperbola terminology is not.
    pub fn classify(&self) -> ConicClass {
        let discriminant = &self.xy * &self.xy - Rat::from_integer(4.into()) * &self.xx * &self.yy;
        if self.doubled_matrix().determinant().is_zero() {
            return if discriminant.is_positive() {
                ConicClass::IntersectingLinePair
            } else if discriminant.is_zero()
                && self.xy.is_zero()
                && self.yy.is_zero()
                && self.xw.is_zero()
                && self.yw.is_zero()
                && (&self.xx * &self.ww).is_negative()
            {
                ConicClass::ParallelLinePair
            } else {
                ConicClass::Degenerate
            };
        }
        match discriminant.cmp(&Rat::zero()) {
            Ordering::Less if self.xy.is_zero() && self.xx == self.yy => {
                ConicClass::CircleInThisChart
            }
            Ordering::Less => ConicClass::EllipseInThisChart,
            Ordering::Equal => ConicClass::ParabolaInThisChart,
            Ordering::Greater => ConicClass::HyperbolaInThisChart,
        }
    }

    pub fn restrict_line(
        &self,
        origin: &[Rat; 2],
        direction: &[Rat; 2],
    ) -> Result<ConicLineRelation, ConicError> {
        let [x0, y0] = origin;
        let [dx, dy] = direction;
        let quadratic = &self.xx * dx * dx + &self.xy * dx * dy + &self.yy * dy * dy;
        let linear = Rat::from_integer(2.into()) * &self.xx * x0 * dx
            + &self.xy * (x0 * dy + y0 * dx)
            + Rat::from_integer(2.into()) * &self.yy * y0 * dy
            + &self.xw * dx
            + &self.yw * dy;
        let constant = self.evaluate(&[x0.clone(), y0.clone(), Rat::one()]);
        solve_quadratic(quadratic, linear, constant)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConicChart {
    pub origin: RatVec3,
    pub axis_x: RatVec3,
    pub axis_y: RatVec3,
}

impl ConicChart {
    pub fn new(origin: RatVec3, axis_x: RatVec3, axis_y: RatVec3) -> Result<Self, ConicError> {
        if axis_x.cross(&axis_y).norm_squared().is_zero() {
            return Err(ConicError::CollapsedChart);
        }
        Ok(Self {
            origin,
            axis_x,
            axis_y,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeConic {
    pub id: ConicCellId,
    pub name: String,
    pub source_event: EventId,
    pub last_event: EventId,
    pub frame: FrameId,
    pub chart: ConicChart,
    pub form: HomogeneousConic,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeConicPopulation {
    pub schema: String,
    pub cells: BTreeMap<ConicCellId, NativeConic>,
    next_id: u64,
}

impl Default for NativeConicPopulation {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.native-conic-population.v1".to_owned(),
            cells: BTreeMap::new(),
            next_id: 1,
        }
    }
}

impl NativeConicPopulation {
    pub fn found(
        &mut self,
        name: impl Into<String>,
        source_event: EventId,
        frame: FrameId,
        chart: ConicChart,
        form: HomogeneousConic,
    ) -> ConicCellId {
        let id = ConicCellId(self.next_id);
        self.next_id += 1;
        self.cells.insert(
            id,
            NativeConic {
                id,
                name: name.into(),
                source_event,
                last_event: source_event,
                frame,
                chart,
                form,
            },
        );
        id
    }

    pub fn replace_form(
        &mut self,
        id: ConicCellId,
        event: EventId,
        form: HomogeneousConic,
    ) -> Result<(), ConicError> {
        let cell = self.cells.get_mut(&id).ok_or(ConicError::MissingCell(id))?;
        cell.form = form;
        cell.last_event = event;
        Ok(())
    }

    pub fn validate_sources(&self, shape: &EvolutionShape) -> Result<(), ConicError> {
        for cell in self.cells.values() {
            if !shape.occurrences.contains_key(&cell.source_event) {
                return Err(ConicError::MissingSourceEvent {
                    cell: cell.id,
                    event: cell.source_event,
                });
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConicRoot {
    pub parameter: ExactValue,
    pub multiplicity: u32,
    pub hand: i8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConicLineRelation {
    Finite(Vec<ConicRoot>),
    Coincident,
}

fn solve_quadratic(
    quadratic: Rat,
    linear: Rat,
    constant: Rat,
) -> Result<ConicLineRelation, ConicError> {
    if quadratic.is_zero() {
        if linear.is_zero() {
            return if constant.is_zero() {
                Ok(ConicLineRelation::Coincident)
            } else {
                Ok(ConicLineRelation::Finite(Vec::new()))
            };
        }
        return Ok(ConicLineRelation::Finite(vec![ConicRoot {
            parameter: ExactValue::rational(-constant / &linear),
            multiplicity: 1,
            hand: sign(&linear),
        }]));
    }

    let discriminant = &linear * &linear - Rat::from_integer(4.into()) * &quadratic * &constant;
    match discriminant.cmp(&Rat::zero()) {
        Ordering::Less => Ok(ConicLineRelation::Finite(Vec::new())),
        Ordering::Equal => Ok(ConicLineRelation::Finite(vec![ConicRoot {
            parameter: ExactValue::rational(-linear / (Rat::from_integer(2.into()) * quadratic)),
            multiplicity: 2,
            hand: 0,
        }])),
        Ordering::Greater => {
            if let Some(square_root) = exact_rational_square_root(&discriminant) {
                let denominator = Rat::from_integer(2.into()) * &quadratic;
                let mut roots = [
                    (-&linear - &square_root) / &denominator,
                    (-linear + square_root) / denominator,
                ];
                roots.sort();
                return Ok(ConicLineRelation::Finite(vec![
                    ConicRoot {
                        parameter: ExactValue::rational(roots[0].clone()),
                        multiplicity: 1,
                        hand: -sign(&quadratic),
                    },
                    ConicRoot {
                        parameter: ExactValue::rational(roots[1].clone()),
                        multiplicity: 1,
                        hand: sign(&quadratic),
                    },
                ]));
            }

            let polynomial = integer_polynomial_from_rationals(&[
                constant.clone(),
                linear.clone(),
                quadratic.clone(),
            ])?;
            let mut bound = Rat::one()
                + std::cmp::max((&linear / &quadratic).abs(), (&constant / &quadratic).abs());
            while polynomial.evaluate(&-bound.clone()).is_zero()
                || polynomial.evaluate(&bound).is_zero()
            {
                bound += Rat::one();
            }
            let vertex = -linear / (Rat::from_integer(2.into()) * &quadratic);
            let left = AlgebraicRoot::isolate(
                polynomial.clone(),
                ExactInterval::new(-bound.clone(), vertex.clone())?,
            )?;
            let right = AlgebraicRoot::isolate(polynomial, ExactInterval::new(vertex, bound)?)?;
            Ok(ConicLineRelation::Finite(vec![
                ConicRoot {
                    parameter: ExactValue::Algebraic(left),
                    multiplicity: 1,
                    hand: -sign(&quadratic),
                },
                ConicRoot {
                    parameter: ExactValue::Algebraic(right),
                    multiplicity: 1,
                    hand: sign(&quadratic),
                },
            ]))
        }
    }
}

fn integer_polynomial_from_rationals(
    coefficients: &[Rat],
) -> Result<IntegerPolynomial, ExactValueError> {
    let denominator_product = coefficients
        .iter()
        .fold(BigInt::one(), |product, coefficient| {
            product * coefficient.denom()
        });
    IntegerPolynomial::new(
        coefficients
            .iter()
            .map(|coefficient| {
                (coefficient * Rat::from_integer(denominator_product.clone())).to_integer()
            })
            .collect(),
    )
}

fn exact_rational_square_root(value: &Rat) -> Option<Rat> {
    if value.is_negative() {
        return None;
    }
    let numerator = value.numer().to_biguint()?;
    let denominator = value.denom().to_biguint()?;
    let numerator_root = square_root_floor(&numerator);
    let denominator_root = square_root_floor(&denominator);
    (&numerator_root * &numerator_root == numerator
        && &denominator_root * &denominator_root == denominator)
        .then(|| Rat::new(numerator_root.into(), denominator_root.into()))
}

fn square_root_floor(value: &BigUint) -> BigUint {
    if value <= &BigUint::one() {
        return value.clone();
    }
    let mut lower = BigUint::zero();
    let mut upper = value + BigUint::one();
    while &lower + BigUint::one() < upper {
        let middle = (&lower + &upper) >> 1_usize;
        if &middle * &middle <= *value {
            lower = middle;
        } else {
            upper = middle;
        }
    }
    lower
}

fn sign(value: &Rat) -> i8 {
    match value.cmp(&Rat::zero()) {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ConicError {
    #[error("the zero homogeneous quadratic does not define a conic")]
    ZeroConic,
    #[error("a homogeneous conic matrix must be symmetric")]
    NonsymmetricMatrix,
    #[error("a conic chart requires two independent local axes")]
    CollapsedChart,
    #[error("native conic cell {0:?} is absent")]
    MissingCell(ConicCellId),
    #[error("conic {cell:?} names source event {event:?}, which is absent from its evolution")]
    MissingSourceEvent { cell: ConicCellId, event: EventId },
    #[error(transparent)]
    Exact(#[from] ExactValueError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::{integer, rat};

    use super::*;

    fn unit_circle() -> HomogeneousConic {
        HomogeneousConic::new([
            integer(1),
            integer(0),
            integer(1),
            integer(0),
            integer(0),
            integer(-1),
        ])
        .unwrap()
    }

    #[test]
    fn conic_species_and_line_pair_are_derived_from_the_quadratic() {
        assert_eq!(unit_circle().classify(), ConicClass::CircleInThisChart);
        let hyperbola = HomogeneousConic::new([
            integer(1),
            integer(0),
            integer(-1),
            integer(0),
            integer(0),
            integer(-1),
        ])
        .unwrap();
        assert_eq!(hyperbola.classify(), ConicClass::HyperbolaInThisChart);
        let line_pair = HomogeneousConic::new([
            integer(1),
            integer(0),
            integer(0),
            integer(0),
            integer(0),
            integer(-1),
        ])
        .unwrap();
        assert_eq!(line_pair.classify(), ConicClass::ParallelLinePair);
    }

    #[test]
    fn line_restriction_retains_rational_algebraic_and_tangent_roots() {
        let rational = unit_circle()
            .restrict_line(&[integer(-2), integer(0)], &[integer(1), integer(0)])
            .unwrap();
        let ConicLineRelation::Finite(rational) = rational else {
            panic!("the diameter has two finite contacts");
        };
        assert_eq!(
            rational
                .iter()
                .map(|root| root.parameter.as_rational().unwrap())
                .collect::<Vec<_>>(),
            vec![integer(1), integer(3)]
        );

        let algebraic = unit_circle()
            .restrict_line(&[integer(-2), rat(1, 2)], &[integer(1), integer(0)])
            .unwrap();
        let ConicLineRelation::Finite(algebraic) = algebraic else {
            panic!("the offset line has two finite contacts");
        };
        assert!(
            algebraic
                .iter()
                .all(|root| matches!(root.parameter, ExactValue::Algebraic(_)))
        );

        let tangent = unit_circle()
            .restrict_line(&[integer(-2), integer(1)], &[integer(1), integer(0)])
            .unwrap();
        let ConicLineRelation::Finite(tangent) = tangent else {
            panic!("the tangent has one repeated contact");
        };
        assert_eq!(tangent[0].multiplicity, 2);
        assert_eq!(tangent[0].parameter.as_rational(), Some(integer(2)));
    }
}
