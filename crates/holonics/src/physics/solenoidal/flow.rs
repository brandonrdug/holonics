//! A declared longitudinal clock consuming the existing LC wave evolution.
//!
//! [definition; agent-inferred] The retained current is a compatible finite tower chart and the
//! wave state, never a record of ticks. A tick publishes both successors together:
//! `chart_next = chart.advance(turns_per_time * medium.tick())`,
//! `state_next = medium.propagate(state, source).next`.
//! Restriction changes the transverse chart; it changes neither the physical state nor its
//! time step. Thus restriction commutes with this evolution on every declared finite level.
//!
//! [physical-model hypothesis] The caller supplies the relation between the wave's time unit
//! and longitudinal turns. This is a clocked realization of the finite chart, not an assertion
//! that every wave/fluid is an adelic solenoid. The full inverse limit, continuum passage,
//! pressure solve, and a pump's stable locking orbit are separate obligations (#62).
//!
//! [proved-derived; formal-checked] The reused wave operator's energy balance and strict
//! Courant energy norm are owned by `Physics/Wave/Energy.{energy_balance,energy_definite}`.
//! The new chart/evolution commuting square is checked exactly at runtime and in controls; no
//! Lean proof of that new join is claimed.

use num_traits::{Signed, Zero};
use thiserror::Error;

use crate::geometry::solenoid::{SolenoidError, SolenoidalChart};
use crate::physics::wave::{WaveBalance, WaveChain, WaveError, WaveState};
use crate::ratio::{Rat, integer};

#[derive(Debug, Error)]
pub enum FlowError {
    #[error(transparent)]
    Chart(#[from] SolenoidError),
    #[error(transparent)]
    Wave(#[from] WaveError),
    #[error("the longitudinal rate must be a well-formed exact rational")]
    InvalidRate,
    #[error("the supplied wave and clock do not satisfy the strict Courant energy condition")]
    UnstableClock,
    #[error("the actual wave tick returned a nonzero energy-balance residual")]
    EnergyResidual,
}

/// The current alone suffices for the admitted next wave tick and every transverse restriction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolenoidalWave {
    chart: SolenoidalChart,
    turns_per_time: Rat,
    medium: WaveChain,
    state: WaveState,
}

/// A receipt of the actual tick. It is returned, not appended to the retained current.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlowReading {
    pub chart: SolenoidalChart,
    pub longitudinal_step: Rat,
    pub balance: WaveBalance,
}

impl SolenoidalWave {
    pub fn new(
        chart: SolenoidalChart,
        turns_per_time: Rat,
        medium: WaveChain,
        state: WaveState,
    ) -> Result<Self, FlowError> {
        if !turns_per_time.denom().is_positive() {
            return Err(FlowError::InvalidRate);
        }
        // The existing convenience predicate admits equality; the energy norm needs strictness.
        if medium.tick() * medium.tick() * medium.courant_bound() >= integer(4) {
            return Err(FlowError::UnstableClock);
        }
        // The producing medium checks the actual voltage/current extents before publication.
        medium.energy(&state)?;
        Ok(Self {
            chart,
            turns_per_time,
            medium,
            state,
        })
    }

    pub fn chart(&self) -> &SolenoidalChart {
        &self.chart
    }

    pub fn state(&self) -> &WaveState {
        &self.state
    }

    pub fn medium(&self) -> &WaveChain {
        &self.medium
    }

    pub fn restrict(&self, level_count: usize) -> Result<Self, FlowError> {
        Ok(Self {
            chart: self.chart.restrict(level_count)?,
            turns_per_time: self.turns_per_time.clone(),
            medium: self.medium.clone(),
            state: self.state.clone(),
        })
    }

    /// Advance the actual wave, then publish its state and compatible clock atomically.
    /// Any chart/source refusal leaves the whole current unchanged.
    pub fn advance(&mut self, source: &[Rat]) -> Result<FlowReading, FlowError> {
        let longitudinal_step = &self.turns_per_time * self.medium.tick();
        let next_chart = self.chart.advance(&longitudinal_step)?;
        let propagation = self.medium.propagate(&self.state, source)?;
        if !propagation.balance.residual.is_zero() {
            return Err(FlowError::EnergyResidual);
        }
        self.chart = next_chart.clone();
        self.state = propagation.next;
        Ok(FlowReading {
            chart: next_chart,
            longitudinal_step,
            balance: propagation.balance,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::solenoid::FiniteSolenoidalTower;
    use crate::physics::wave::{Incidence, WaveMaterial};
    use crate::ratio::{integer, rat};
    use num_bigint::BigUint;

    fn current(tick: Rat) -> Result<SolenoidalWave, FlowError> {
        let tower = FiniteSolenoidalTower::new(vec![
            BigUint::from(1u8),
            BigUint::from(3u8),
            BigUint::from(15u8),
        ])?;
        let chart = SolenoidalChart::from_transverse(
            tower,
            rat(4, 5),
            vec![BigUint::from(0u8), BigUint::from(2u8), BigUint::from(2u8)],
        )?;
        let incidence = Incidence::ring(3)?;
        let material = WaveMaterial::uniform(&incidence, &integer(1), &rat(1, 3), &integer(1))?;
        let medium = WaveChain::new(incidence, material, tick)?;
        let state = WaveState::new(
            vec![integer(1), integer(0), integer(-1)],
            vec![integer(0); 3],
        );
        SolenoidalWave::new(chart, integer(1), medium, state)
    }

    #[test]
    fn transverse_restriction_commutes_with_actual_dissipative_wave_tick() {
        let mut full = current(rat(1, 2)).unwrap();
        let mut coarse = full.restrict(2).unwrap();
        let source = vec![integer(0); 3];
        let full_reading = full.advance(&source).unwrap();
        let coarse_reading = coarse.advance(&source).unwrap();
        assert_eq!(full.restrict(2).unwrap(), coarse);
        assert_eq!(full_reading.balance, coarse_reading.balance);
        assert!(full_reading.balance.is_exact());
        assert!(full_reading.balance.dissipated > integer(0));
        assert_eq!(full.chart().phase(), &rat(3, 10));
        assert_eq!(full.chart().winding(), &1.into());
    }

    #[test]
    fn malformed_source_preserves_both_state_and_clock() {
        let mut flow = current(rat(1, 2)).unwrap();
        let before = flow.clone();
        assert!(flow.advance(&[integer(0)]).is_err());
        assert_eq!(flow, before);
        assert!(matches!(current(integer(1)), Err(FlowError::UnstableClock)));
        assert!(matches!(current(integer(2)), Err(FlowError::UnstableClock)));
    }
}
