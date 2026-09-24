//! **Exact frame carriers: rational points, linear maps and rigid transports of one frame.**
//!
//! A frame is a local chart joined to others by declared exact maps; [`AffineMap3`] is such a map,
//! and its `followed_by` and `inverse` are the group operation cell holonomy reads. Rotations are
//! reached through the Cayley chart of the circle, `t ↦ ((1 − t²)/(1 + t²), 2t/(1 + t²))`, so every
//! rotation here is a rational point of `SO(3)` and no angle is formed.

use num_traits::{One, Zero};

use crate::ratio::{Rat, integer};

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

/// A coordinate axis of the frame: the rotation axis of a revolute joint, or a hinge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Axis {
    X,
    Y,
    Z,
}

impl Axis {
    /// The unit vector along the axis.
    pub fn unit(self) -> RatVec3 {
        match self {
            Self::X => RatVec3::from_i64(1, 0, 0),
            Self::Y => RatVec3::from_i64(0, 1, 0),
            Self::Z => RatVec3::from_i64(0, 0, 1),
        }
    }

    /// The rotation about this axis at a Cayley half-angle parameter.
    pub fn cayley_rotation(self, parameter: &Rat) -> RatMat3 {
        match self {
            Self::X => cayley_rotation_x(parameter),
            Self::Y => cayley_rotation_y(parameter),
            Self::Z => cayley_rotation_z(parameter),
        }
    }
}

/// The Cayley chart of the circle, `t ↦ ((1 − t²)/(1 + t²), 2t/(1 + t²))`: a rational point of the
/// unit circle for every rational half-angle parameter `t`.
pub fn rational_circle(parameter: &Rat) -> (Rat, Rat) {
    let square = parameter * parameter;
    let denominator = Rat::one() + &square;
    let cosine = (Rat::one() - square) / &denominator;
    let sine = (integer(2) * parameter) / denominator;
    (cosine, sine)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::rat;

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
