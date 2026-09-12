//! Exact relativistic energy-momentum and vacuum electromagnetic receiver charts.
//!
//! Momentum coordinates are c*p, so every component has energy units. Signed vectors may
//! represent subsystem exchange; `is_future_causal` distinguishes physical future-directed
//! total momenta. Maxwell faces retain their six field coordinates before contraction.
use super::{ExactLinearError, ExactRatMatrix};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum EnergyMomentumError {
    #[error("photon energy must be nonnegative and its direction must be unit length")]
    InvalidPhoton,
    #[error("boost requires gamma>0, |beta|<1 and gamma^2(1-beta^2)=1")]
    InvalidBoost,
    #[error("vacuum chart requires positive c, epsilon and mu with c^2 epsilon mu=1")]
    InvalidVacuumChart,
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}

fn dot(a: &[Rat; 3], b: &[Rat; 3]) -> Rat {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}
fn cross(a: &[Rat; 3], b: &[Rat; 3]) -> [Rat; 3] {
    [
        &a[1] * &b[2] - &a[2] * &b[1],
        &a[2] * &b[0] - &a[0] * &b[2],
        &a[0] * &b[1] - &a[1] * &b[0],
    ]
}
fn boost_valid(beta: &Rat, gamma: &Rat) -> bool {
    gamma.is_positive()
        && beta.abs() < Rat::one()
        && gamma * gamma * (Rat::one() - beta * beta) == Rat::one()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnergyMomentum {
    pub energy: Rat,
    pub c_momentum: [Rat; 3],
}

impl EnergyMomentum {
    pub fn new(energy: Rat, c_momentum: [Rat; 3]) -> Self {
        Self { energy, c_momentum }
    }
    pub fn photon(energy: Rat, direction: [Rat; 3]) -> Result<Self, EnergyMomentumError> {
        if energy.is_negative() || dot(&direction, &direction) != Rat::one() {
            return Err(EnergyMomentumError::InvalidPhoton);
        }
        let c_momentum = direction.map(|n| &energy * n);
        Ok(Self { energy, c_momentum })
    }
    pub fn add(&self, other: &Self) -> Self {
        Self::new(
            &self.energy + &other.energy,
            std::array::from_fn(|i| &self.c_momentum[i] + &other.c_momentum[i]),
        )
    }
    pub fn subtract(&self, other: &Self) -> Self {
        Self::new(
            &self.energy - &other.energy,
            std::array::from_fn(|i| &self.c_momentum[i] - &other.c_momentum[i]),
        )
    }
    pub fn pairing(&self, other: &Self) -> Rat {
        &self.energy * &other.energy - dot(&self.c_momentum, &other.c_momentum)
    }
    /// M^2 c^4 for a physical total; a signed exchange can have another Lorentz norm.
    pub fn invariant_square(&self) -> Rat {
        self.pairing(self)
    }
    pub fn is_future_causal(&self) -> bool {
        !self.energy.is_negative() && !self.invariant_square().is_negative()
    }
    /// Observer boost along x; beta=v/c, with the exact Lorentz-factor constraint.
    pub fn boost_x(&self, beta: &Rat, gamma: &Rat) -> Result<Self, EnergyMomentumError> {
        if !boost_valid(beta, gamma) {
            return Err(EnergyMomentumError::InvalidBoost);
        }
        let zero = Rat::zero();
        let one = Rat::one();
        let boost = ExactRatMatrix::new(vec![
            vec![gamma.clone(), -gamma * beta, zero.clone(), zero.clone()],
            vec![-gamma * beta, gamma.clone(), zero.clone(), zero.clone()],
            vec![zero.clone(), zero.clone(), one.clone(), zero.clone()],
            vec![zero.clone(), zero.clone(), zero, one],
        ])?;
        let face = boost.apply(&[
            self.energy.clone(),
            self.c_momentum[0].clone(),
            self.c_momentum[1].clone(),
            self.c_momentum[2].clone(),
        ])?;
        Ok(Self::new(
            face[0].clone(),
            [face[1].clone(), face[2].clone(), face[3].clone()],
        ))
    }
}

#[derive(Debug)]
pub struct VacuumEnergyChart {
    speed: Rat,
    epsilon: Rat,
    mu: Rat,
}

#[derive(Debug)]
pub struct MaxwellEnergyFace {
    pub energy_density: Rat,
    pub poynting: [Rat; 3],
    /// c^2 u^2 - |S|^2, with flux-squared units.
    pub cone_residual: Rat,
    pub electric_minus_magnetic: Rat,
    pub electric_dot_magnetic: Rat,
}

impl VacuumEnergyChart {
    pub fn new(speed: Rat, epsilon: Rat, mu: Rat) -> Result<Self, EnergyMomentumError> {
        if !speed.is_positive()
            || !epsilon.is_positive()
            || !mu.is_positive()
            || &speed * &speed * &epsilon * &mu != Rat::one()
        {
            return Err(EnergyMomentumError::InvalidVacuumChart);
        }
        Ok(Self { speed, epsilon, mu })
    }
    pub fn impedance_squared(&self) -> Rat {
        &self.mu / &self.epsilon
    }
    pub fn read(&self, electric: &[Rat; 3], magnetic: &[Rat; 3]) -> MaxwellEnergyFace {
        let e2 = dot(electric, electric);
        let b2 = dot(magnetic, magnetic);
        let energy_density = (&self.epsilon * &e2 + &b2 / &self.mu) / Rat::from_integer(2.into());
        let poynting = cross(electric, magnetic).map(|v| v / &self.mu);
        let cone_residual = &self.speed * &self.speed * &energy_density * &energy_density
            - dot(&poynting, &poynting);
        MaxwellEnergyFace {
            energy_density,
            poynting,
            cone_residual,
            electric_minus_magnetic: e2 - &self.speed * &self.speed * b2,
            electric_dot_magnetic: dot(electric, magnetic),
        }
    }
    /// Transform E and B before measuring a new observer's energy flux and density.
    /// The energy-current face alone is not treated as a four-momentum vector.
    pub fn boost_fields_x(
        &self,
        electric: &[Rat; 3],
        magnetic: &[Rat; 3],
        beta: &Rat,
        gamma: &Rat,
    ) -> Result<([Rat; 3], [Rat; 3]), EnergyMomentumError> {
        if !boost_valid(beta, gamma) {
            return Err(EnergyMomentumError::InvalidBoost);
        }
        let v = beta * &self.speed;
        let v_over_c2 = beta / &self.speed;
        Ok((
            [
                electric[0].clone(),
                gamma * (&electric[1] - &v * &magnetic[2]),
                gamma * (&electric[2] + &v * &magnetic[1]),
            ],
            [
                magnetic[0].clone(),
                gamma * (&magnetic[1] + &v_over_c2 * &electric[2]),
                gamma * (&magnetic[2] - &v_over_c2 * &electric[1]),
            ],
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn q(n: i64, d: i64) -> Rat {
        Rat::new(n.into(), d.into())
    }
    fn v(x: i64, y: i64, z: i64) -> [Rat; 3] {
        [q(x, 1), q(y, 1), q(z, 1)]
    }
    #[test]
    fn massless_constituents_have_direction_dependent_system_mass() {
        let right = EnergyMomentum::photon(q(1, 1), v(1, 0, 0)).unwrap();
        let left = EnergyMomentum::photon(q(1, 1), v(-1, 0, 0)).unwrap();
        assert!(right.invariant_square().is_zero());
        assert_eq!(right.add(&left).invariant_square(), q(4, 1));
        assert!(right.add(&right).invariant_square().is_zero());
    }
    #[test]
    fn boost_and_exchange_retain_the_full_lorentz_pairing() {
        let body = EnergyMomentum::new(q(5, 1), v(0, 0, 0));
        let photon = EnergyMomentum::photon(q(8, 5), v(1, 0, 0)).unwrap();
        let recoil = body.subtract(&photon);
        assert_eq!(recoil.invariant_square(), q(9, 1));
        assert!(recoil.is_future_causal());
        assert_eq!(
            recoil
                .boost_x(&q(4, 5), &q(5, 3))
                .unwrap()
                .invariant_square(),
            q(9, 1)
        );
        let change = recoil.subtract(&body);
        assert_eq!(
            recoil.invariant_square() - body.invariant_square(),
            q(2, 1) * body.pairing(&change) + change.invariant_square()
        );
        assert!(body.boost_x(&q(1, 1), &q(1, 1)).is_err());
    }
    #[test]
    fn maxwell_cone_and_boost_keep_both_field_invariants() {
        let vacuum = VacuumEnergyChart::new(q(1, 1), q(1, 1), q(1, 1)).unwrap();
        for (e, b) in [
            (v(1, 0, 0), v(0, 1, 0)),
            (v(1, 0, 0), v(1, 0, 0)),
            (v(2, 1, 3), v(1, -2, 1)),
        ] {
            let first = vacuum.read(&e, &b);
            assert!(!first.cone_residual.is_negative());
            let (eb, bb) = vacuum.boost_fields_x(&e, &b, &q(4, 5), &q(5, 3)).unwrap();
            let next = vacuum.read(&eb, &bb);
            assert_eq!(first.electric_minus_magnetic, next.electric_minus_magnetic);
            assert_eq!(first.electric_dot_magnetic, next.electric_dot_magnetic);
            assert!(!next.cone_residual.is_negative());
        }
        assert!(
            vacuum
                .read(&v(1, 0, 0), &v(0, 1, 0))
                .cone_residual
                .is_zero()
        );
        assert!(VacuumEnergyChart::new(q(1, 1), q(2, 1), q(1, 1)).is_err());
    }
}
