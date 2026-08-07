//! Exact arithmetic carried by the relational geometry kernel.
//!
//! This module deliberately has no rendering scalar.  Bevy-compatible
//! approximations are produced only by the application membrane after an
//! exact receiver projection has been formed.

use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};

pub type Rat = BigRational;

pub fn rat(numerator: i64, denominator: i64) -> Rat {
    assert_ne!(
        denominator, 0,
        "an exact ratio cannot have denominator zero"
    );
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

pub fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

pub fn ratio(numerator: BigInt, denominator: BigInt) -> Rat {
    assert!(
        !denominator.is_zero(),
        "an exact ratio cannot have denominator zero"
    );
    Rat::new(numerator, denominator)
}

pub fn format_rat(value: &Rat) -> String {
    if value.denom().is_one() {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactExpr {
    Rational(Rat),
    Symbol(String),
    Neg(Box<ExactExpr>),
    Sum(Vec<ExactExpr>),
    Product(Vec<ExactExpr>),
    Power {
        base: Box<ExactExpr>,
        exponent: i32,
    },
    Root {
        degree: u32,
        radicand: Box<ExactExpr>,
    },
    Function {
        name: String,
        arguments: Vec<ExactExpr>,
    },
    FormalSeries {
        index: String,
        start: BigInt,
        term: Box<ExactExpr>,
        condition: String,
    },
}

impl ExactExpr {
    pub fn rational(value: Rat) -> Self {
        Self::Rational(value)
    }

    pub fn symbol(name: impl Into<String>) -> Self {
        Self::Symbol(name.into())
    }

    pub fn root(degree: u32, radicand: ExactExpr) -> Self {
        assert!(degree > 1, "a radical degree must exceed one");
        Self::Root {
            degree,
            radicand: Box::new(radicand),
        }
    }

    pub fn sqrt_int(value: i64) -> Self {
        Self::root(2, Self::rational(integer(value)))
    }

    pub fn function(name: impl Into<String>, arguments: Vec<ExactExpr>) -> Self {
        Self::Function {
            name: name.into(),
            arguments,
        }
    }

    pub fn formal_series(
        index: impl Into<String>,
        start: BigInt,
        term: ExactExpr,
        condition: impl Into<String>,
    ) -> Self {
        Self::FormalSeries {
            index: index.into(),
            start,
            term: Box::new(term),
            condition: condition.into(),
        }
    }

    pub fn neg(self) -> Self {
        match self {
            Self::Rational(value) => Self::Rational(-value),
            Self::Neg(inner) => *inner,
            other => Self::Neg(Box::new(other)),
        }
    }

    pub fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Rational(left), Self::Rational(right)) => Self::Rational(left + right),
            (Self::Rational(left), right) if left.is_zero() => right,
            (left, Self::Rational(right)) if right.is_zero() => left,
            (Self::Sum(mut left), Self::Sum(right)) => {
                left.extend(right);
                Self::Sum(left)
            }
            (Self::Sum(mut terms), right) => {
                terms.push(right);
                Self::Sum(terms)
            }
            (left, Self::Sum(mut terms)) => {
                terms.insert(0, left);
                Self::Sum(terms)
            }
            (left, right) => Self::Sum(vec![left, right]),
        }
    }

    pub fn subtract(self, other: Self) -> Self {
        self.add(other.neg())
    }

    pub fn multiply(self, other: Self) -> Self {
        match (self, other) {
            (Self::Rational(left), Self::Rational(right)) => Self::Rational(left * right),
            (Self::Rational(left), _) if left.is_zero() => Self::Rational(Rat::zero()),
            (_, Self::Rational(right)) if right.is_zero() => Self::Rational(Rat::zero()),
            (Self::Rational(left), right) if left.is_one() => right,
            (left, Self::Rational(right)) if right.is_one() => left,
            (Self::Product(mut left), Self::Product(right)) => {
                left.extend(right);
                Self::Product(left)
            }
            (Self::Product(mut factors), right) => {
                factors.push(right);
                Self::Product(factors)
            }
            (left, Self::Product(mut factors)) => {
                factors.insert(0, left);
                Self::Product(factors)
            }
            (left, right) => Self::Product(vec![left, right]),
        }
    }

    pub fn divide(self, other: Self) -> Self {
        self.multiply(Self::Power {
            base: Box::new(other),
            exponent: -1,
        })
    }

    pub fn pow(self, exponent: i32) -> Self {
        if exponent == 1 {
            self
        } else if exponent == 0 {
            Self::Rational(Rat::one())
        } else {
            Self::Power {
                base: Box::new(self),
                exponent,
            }
        }
    }

    pub fn as_rational(&self) -> Option<&Rat> {
        match self {
            Self::Rational(value) => Some(value),
            _ => None,
        }
    }
}

impl From<Rat> for ExactExpr {
    fn from(value: Rat) -> Self {
        Self::Rational(value)
    }
}

impl fmt::Display for ExactExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rational(value) => formatter.write_str(&format_rat(value)),
            Self::Symbol(name) => formatter.write_str(name),
            Self::Neg(inner) => write!(formatter, "-({inner})"),
            Self::Sum(terms) => {
                formatter.write_str("(")?;
                for (index, term) in terms.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(" + ")?;
                    }
                    write!(formatter, "{term}")?;
                }
                formatter.write_str(")")
            }
            Self::Product(factors) => {
                formatter.write_str("(")?;
                for (index, factor) in factors.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(" · ")?;
                    }
                    write!(formatter, "{factor}")?;
                }
                formatter.write_str(")")
            }
            Self::Power { base, exponent } => write!(formatter, "({base})^{exponent}"),
            Self::Root { degree, radicand } if *degree == 2 => {
                write!(formatter, "sqrt({radicand})")
            }
            Self::Root { degree, radicand } => write!(formatter, "root_{degree}({radicand})"),
            Self::Function { name, arguments } => {
                write!(formatter, "{name}(")?;
                for (index, argument) in arguments.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{argument}")?;
                }
                formatter.write_str(")")
            }
            Self::FormalSeries {
                index,
                start,
                term,
                condition,
            } => write!(
                formatter,
                "sum_{{{index}={start}}}^infinity ({term})  [{condition}]"
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RatVec2 {
    pub x: Rat,
    pub y: Rat,
}

impl RatVec2 {
    pub fn new(x: Rat, y: Rat) -> Self {
        Self { x, y }
    }

    pub fn zero() -> Self {
        Self::new(Rat::zero(), Rat::zero())
    }

    pub fn add(&self, other: &Self) -> Self {
        Self::new(&self.x + &other.x, &self.y + &other.y)
    }

    pub fn subtract(&self, other: &Self) -> Self {
        Self::new(&self.x - &other.x, &self.y - &other.y)
    }

    pub fn scale(&self, scalar: &Rat) -> Self {
        Self::new(&self.x * scalar, &self.y * scalar)
    }

    pub fn cross(&self, other: &Self) -> Rat {
        &self.x * &other.y - &self.y * &other.x
    }

    pub fn dot(&self, other: &Self) -> Rat {
        &self.x * &other.x + &self.y * &other.y
    }

    pub fn norm_squared(&self) -> Rat {
        self.dot(self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RatVec3 {
    pub x: Rat,
    pub y: Rat,
    pub z: Rat,
}

impl RatVec3 {
    pub fn new(x: Rat, y: Rat, z: Rat) -> Self {
        Self { x, y, z }
    }

    pub fn from_i64(x: i64, y: i64, z: i64) -> Self {
        Self::new(integer(x), integer(y), integer(z))
    }

    pub fn zero() -> Self {
        Self::new(Rat::zero(), Rat::zero(), Rat::zero())
    }

    pub fn add(&self, other: &Self) -> Self {
        Self::new(&self.x + &other.x, &self.y + &other.y, &self.z + &other.z)
    }

    pub fn subtract(&self, other: &Self) -> Self {
        Self::new(&self.x - &other.x, &self.y - &other.y, &self.z - &other.z)
    }

    pub fn scale(&self, scalar: &Rat) -> Self {
        Self::new(&self.x * scalar, &self.y * scalar, &self.z * scalar)
    }

    pub fn dot(&self, other: &Self) -> Rat {
        &self.x * &other.x + &self.y * &other.y + &self.z * &other.z
    }

    pub fn cross(&self, other: &Self) -> Self {
        Self::new(
            &self.y * &other.z - &self.z * &other.y,
            &self.z * &other.x - &self.x * &other.z,
            &self.x * &other.y - &self.y * &other.x,
        )
    }

    pub fn norm_squared(&self) -> Rat {
        self.dot(self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactVec2 {
    pub x: ExactExpr,
    pub y: ExactExpr,
}

impl ExactVec2 {
    pub fn new(x: ExactExpr, y: ExactExpr) -> Self {
        Self { x, y }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RatMat3 {
    pub rows: [[Rat; 3]; 3],
}

impl RatMat3 {
    pub fn new(rows: [[Rat; 3]; 3]) -> Self {
        Self { rows }
    }

    pub fn from_i64(rows: [[i64; 3]; 3]) -> Self {
        Self::new(rows.map(|row| row.map(integer)))
    }

    pub fn identity() -> Self {
        Self::from_i64([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
    }

    pub fn transpose(&self) -> Self {
        Self::new([
            [
                self.rows[0][0].clone(),
                self.rows[1][0].clone(),
                self.rows[2][0].clone(),
            ],
            [
                self.rows[0][1].clone(),
                self.rows[1][1].clone(),
                self.rows[2][1].clone(),
            ],
            [
                self.rows[0][2].clone(),
                self.rows[1][2].clone(),
                self.rows[2][2].clone(),
            ],
        ])
    }

    pub fn apply(&self, vector: &RatVec3) -> RatVec3 {
        let component = |row: usize| {
            &self.rows[row][0] * &vector.x
                + &self.rows[row][1] * &vector.y
                + &self.rows[row][2] * &vector.z
        };
        RatVec3::new(component(0), component(1), component(2))
    }

    pub fn multiply(&self, other: &Self) -> Self {
        let entry = |row: usize, column: usize| {
            &self.rows[row][0] * &other.rows[0][column]
                + &self.rows[row][1] * &other.rows[1][column]
                + &self.rows[row][2] * &other.rows[2][column]
        };
        Self::new([
            [entry(0, 0), entry(0, 1), entry(0, 2)],
            [entry(1, 0), entry(1, 1), entry(1, 2)],
            [entry(2, 0), entry(2, 1), entry(2, 2)],
        ])
    }

    pub fn scale(&self, scalar: &Rat) -> Self {
        Self::new(self.rows.clone().map(|row| row.map(|value| value * scalar)))
    }

    pub fn bilinear(&self, left: &RatVec3, right: &RatVec3) -> Rat {
        left.dot(&self.apply(right))
    }

    pub fn determinant(&self) -> Rat {
        let a = &self.rows;
        &a[0][0] * (&a[1][1] * &a[2][2] - &a[1][2] * &a[2][1])
            - &a[0][1] * (&a[1][0] * &a[2][2] - &a[1][2] * &a[2][0])
            + &a[0][2] * (&a[1][0] * &a[2][1] - &a[1][1] * &a[2][0])
    }

    pub fn inverse(&self) -> Option<Self> {
        let determinant = self.determinant();
        if determinant.is_zero() {
            return None;
        }
        let a = &self.rows;
        let cofactor = [
            [
                &a[1][1] * &a[2][2] - &a[1][2] * &a[2][1],
                -(&a[1][0] * &a[2][2] - &a[1][2] * &a[2][0]),
                &a[1][0] * &a[2][1] - &a[1][1] * &a[2][0],
            ],
            [
                -(&a[0][1] * &a[2][2] - &a[0][2] * &a[2][1]),
                &a[0][0] * &a[2][2] - &a[0][2] * &a[2][0],
                -(&a[0][0] * &a[2][1] - &a[0][1] * &a[2][0]),
            ],
            [
                &a[0][1] * &a[1][2] - &a[0][2] * &a[1][1],
                -(&a[0][0] * &a[1][2] - &a[0][2] * &a[1][0]),
                &a[0][0] * &a[1][1] - &a[0][1] * &a[1][0],
            ],
        ];
        let adjugate = Self::new(cofactor).transpose();
        Some(Self::new(
            adjugate
                .rows
                .map(|row| row.map(|value| value / &determinant)),
        ))
    }

    pub fn is_special_orthogonal(&self) -> bool {
        self.transpose().multiply(self) == Self::identity() && self.determinant().is_one()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AffineMap3 {
    pub linear: RatMat3,
    pub translation: RatVec3,
}

impl AffineMap3 {
    pub fn identity() -> Self {
        Self {
            linear: RatMat3::identity(),
            translation: RatVec3::zero(),
        }
    }

    pub fn apply(&self, point: &RatVec3) -> RatVec3 {
        self.linear.apply(point).add(&self.translation)
    }

    /// Return the map obtained by applying `self`, then `next`.
    pub fn followed_by(&self, next: &Self) -> Self {
        Self {
            linear: next.linear.multiply(&self.linear),
            translation: next.linear.apply(&self.translation).add(&next.translation),
        }
    }

    pub fn inverse(&self) -> Option<Self> {
        let inverse_linear = self.linear.inverse()?;
        let inverse_translation = inverse_linear.apply(&self.translation).scale(&-Rat::one());
        Some(Self {
            linear: inverse_linear,
            translation: inverse_translation,
        })
    }

    pub fn rotation_about(pivot: &RatVec3, rotation: RatMat3) -> Self {
        let translation = pivot.subtract(&rotation.apply(pivot));
        Self {
            linear: rotation,
            translation,
        }
    }
}

pub fn cayley_rotation_x(parameter: &Rat) -> RatMat3 {
    let (cosine, sine) = rational_circle(parameter);
    RatMat3::new([
        [Rat::one(), Rat::zero(), Rat::zero()],
        [Rat::zero(), cosine.clone(), -sine.clone()],
        [Rat::zero(), sine, cosine],
    ])
}

pub fn cayley_rotation_y(parameter: &Rat) -> RatMat3 {
    let (cosine, sine) = rational_circle(parameter);
    RatMat3::new([
        [cosine.clone(), Rat::zero(), sine.clone()],
        [Rat::zero(), Rat::one(), Rat::zero()],
        [-sine, Rat::zero(), cosine],
    ])
}

pub fn cayley_rotation_z(parameter: &Rat) -> RatMat3 {
    let (cosine, sine) = rational_circle(parameter);
    RatMat3::new([
        [cosine.clone(), -sine.clone(), Rat::zero()],
        [sine, cosine, Rat::zero()],
        [Rat::zero(), Rat::zero(), Rat::one()],
    ])
}

pub fn rational_circle(parameter: &Rat) -> (Rat, Rat) {
    let square = parameter * parameter;
    let denominator = Rat::one() + &square;
    let cosine = (Rat::one() - square) / &denominator;
    let sine = (integer(2) * parameter) / denominator;
    (cosine, sine)
}

pub fn sign(value: &Rat) -> i8 {
    if value.is_positive() {
        1
    } else if value.is_negative() {
        -1
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rational_circle_is_an_exact_unit_point() {
        let parameter = rat(1, 2);
        let (cosine, sine) = rational_circle(&parameter);
        assert_eq!(cosine, rat(3, 5));
        assert_eq!(sine, rat(4, 5));
        assert_eq!(&cosine * &cosine + &sine * &sine, Rat::one());
    }

    #[test]
    fn cayley_rotations_are_special_orthogonal() {
        for rotation in [
            cayley_rotation_x(&rat(2, 3)),
            cayley_rotation_y(&rat(-3, 5)),
            cayley_rotation_z(&rat(1, 2)),
        ] {
            assert!(rotation.is_special_orthogonal());
        }
    }

    #[test]
    fn affine_inverse_returns_every_exact_point() {
        let map =
            AffineMap3::rotation_about(&RatVec3::from_i64(2, -1, 0), cayley_rotation_z(&rat(1, 2)));
        let point = RatVec3::new(rat(7, 3), rat(-2, 5), rat(11, 7));
        let inverse = map.inverse().expect("rotation is invertible");
        assert_eq!(inverse.apply(&map.apply(&point)), point);
    }
}
