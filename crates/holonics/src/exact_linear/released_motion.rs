//! Exact weak-field release and constant-acceleration transport operators.
//!
//! The caller supplies a common unit/frame chart and positive inertial mass. The carrier is
//! [position, velocity, acceleration]; release additionally receives an impulse. These are
//! reusable operators for a GR-derived weak-field motion simulation with prescribed acceleration.
use super::{ExactLinearError, ExactRatMatrix};
use num_traits::{One, Signed};
use crate::geometry::Rat;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ReleasedMotionError {
    #[error("release requires a positive mass in its declared unit chart")]
    NonPositiveMass,
    #[error("a release chart requires at least one spatial coordinate")]
    EmptySpace,
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}

/// Immutable constitutive chart. It owns no trajectory, event sequence, or mutable organism.
#[derive(Debug)]
pub struct ConstantAccelerationRelease {
    dimension: usize,
    mass: Rat,
}

impl ConstantAccelerationRelease {
    pub fn new(dimension: usize, mass: Rat) -> Result<Self, ReleasedMotionError> {
        if dimension == 0 {
            return Err(ReleasedMotionError::EmptySpace);
        }
        if !mass.is_positive() {
            return Err(ReleasedMotionError::NonPositiveMass);
        }
        dimension
            .checked_mul(4)
            .ok_or(ExactLinearError::ExtentOverflow)?;
        Ok(Self { dimension, mass })
    }

    /// Exact exp(tN), N^3=0: x'=x+t v+t^2 a/2, v'=v+t a, a'=a.
    /// A signed interval is allowed for algebraic comparison; physical forward use declares t>=0.
    pub fn flow(&self, duration: &Rat) -> Result<ExactRatMatrix, ExactLinearError> {
        let d = self.dimension;
        let mut rows = ExactRatMatrix::identity(3 * d)?.to_rows();
        let half_square = duration * duration / Rat::from_integer(2.into());
        for i in 0..d {
            rows[i][d + i] = duration.clone();
            rows[i][2 * d + i] = half_square.clone();
            rows[d + i][2 * d + i] = duration.clone();
        }
        ExactRatMatrix::new(rows)
    }

    /// [x,v,a,J] -> [x,v+J/m,a]. Preparation work is supplied, not created by this map.
    pub fn release(&self) -> Result<ExactRatMatrix, ExactLinearError> {
        let d = self.dimension;
        let mut rows = ExactRatMatrix::zero(3 * d, 4 * d)?.to_rows();
        for (i, row) in rows.iter_mut().enumerate() {
            row[i] = Rat::one();
        }
        for i in 0..d {
            rows[d + i][3 * d + i] = Rat::one() / &self.mass;
        }
        ExactRatMatrix::new(rows)
    }

    pub fn position_receiver(&self) -> Result<ExactRatMatrix, ExactLinearError> {
        let d = self.dimension;
        let mut rows = ExactRatMatrix::zero(d, 3 * d)?.to_rows();
        for (i, row) in rows.iter_mut().enumerate() {
            row[i] = Rat::one();
        }
        ExactRatMatrix::new(rows)
    }

    /// Complete release-source to endpoint map, suitable for the standing preimage/factor solver.
    pub fn endpoint(&self, duration: &Rat) -> Result<ExactRatMatrix, ExactLinearError> {
        self.position_receiver()?
            .multiply(&self.flow(duration)?)?
            .multiply(&self.release()?)
    }

    /// Linear action from supplied impulse to displacement at the declared receiving time.
    pub fn impulse_receiver(&self, duration: &Rat) -> Result<ExactRatMatrix, ExactLinearError> {
        Ok(ExactRatMatrix::identity(self.dimension)?.scaled(&(duration / &self.mass)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;
    fn q(n: i64, d: i64) -> Rat {
        Rat::new(n.into(), d.into())
    }

    #[test]
    fn constant_acceleration_composes_without_stepping_or_history() {
        let source = ConstantAccelerationRelease::new(2, q(2, 1)).unwrap();
        let t = q(1, 3);
        let s = q(2, 5);
        assert_eq!(
            source
                .flow(&s)
                .unwrap()
                .multiply(&source.flow(&t).unwrap())
                .unwrap(),
            source.flow(&(&s + &t)).unwrap()
        );
        assert_eq!(
            source
                .flow(&(-&t))
                .unwrap()
                .multiply(&source.flow(&t).unwrap())
                .unwrap(),
            ExactRatMatrix::identity(6).unwrap()
        );
    }

    #[test]
    fn requested_landing_infers_impulse_through_shared_preimage_solver() {
        let source = ConstantAccelerationRelease::new(2, q(2, 1)).unwrap();
        let (impulse, fibre) = source
            .impulse_receiver(&q(1, 1))
            .unwrap()
            .preimage_fibre(&[q(4, 1), q(5, 1)])
            .unwrap()
            .unwrap();
        assert!(fibre.is_empty());
        assert_eq!(impulse, vec![q(8, 1), q(10, 1)]);
        let mut packed = vec![q(0, 1), q(1, 1), q(0, 1), q(0, 1), q(0, 1), q(-10, 1)];
        packed.extend(impulse);
        assert_eq!(
            source.endpoint(&q(1, 1)).unwrap().apply(&packed).unwrap(),
            vec![q(4, 1), q(1, 1)]
        );
        assert!(
            source
                .impulse_receiver(&Rat::zero())
                .unwrap()
                .preimage_fibre(&[q(1, 1), q(0, 1)])
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn mass_and_dimension_are_constitutive_inputs() {
        assert!(matches!(
            ConstantAccelerationRelease::new(1, Rat::zero()),
            Err(ReleasedMotionError::NonPositiveMass)
        ));
        assert!(matches!(
            ConstantAccelerationRelease::new(0, Rat::one()),
            Err(ReleasedMotionError::EmptySpace)
        ));
    }
}
