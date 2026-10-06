//! A continuing loaded parametron on its declared pump cycle.
//!
//! The mount admits the actual primitive forward cycle and the exact finite-domain
//! certificate. Each cycle executes those laws, checks every intermediate domain,
//! and carries only its contemporary displacement/rate and clock lift. Work from
//! changing stiffness is charged at the held point. A failed cycle leaves the
//! mounted point untouched. This is a component mount, not a rounded HNN field mount.

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use super::PeriodicDomain;
use crate::aeon::{ClockLift, Cycle};
use crate::holon::law::{EnergyBalance, HolonLaw};
use crate::holon::{Holon, HolonError, HolonState};
use crate::ratio::Rat;

fn refused(what: &'static str) -> HolonError {
    HolonError::ConformanceFailed { what }
}

/// The whole-cycle observable: its continuing point, exact work balance and
/// translated clock cycle. Intermediate states are not retained.
#[derive(Clone, Debug)]
pub struct PeriodAdvance {
    pub state: HolonState,
    pub balance: EnergyBalance,
    pub cycle: Cycle<ClockLift>,
}

/// One loaded component, mounted at phase zero on a declared closing boundary.
/// The period may contain expanding ticks in changing metrics; only the checked
/// composition is required to contract. No sheet Lock is inferred from contraction.
#[derive(Clone, Debug)]
pub struct MountedParametron {
    domain: PeriodicDomain,
    clock: ClockLift,
    primitive_cycle: Cycle<ClockLift>,
    point: HolonState,
}

impl MountedParametron {
    pub fn mount(
        domain: PeriodicDomain,
        clock: ClockLift,
        primitive_cycle: Cycle<ClockLift>,
        point: HolonState,
    ) -> Result<Self, HolonError> {
        let period = u64::try_from(domain.period())
            .map_err(|_| refused("the pump period fits the material clock"))?;
        if clock.periods() != [BigUint::from(period)] {
            return Err(refused(
                "the component clock is the declared material period",
            ));
        }
        let actual = clock
            .forward(vec![BigInt::zero()], &[BigInt::from(period)])
            .map_err(|_| refused("the primitive forward pump aeon"))?;
        if primitive_cycle.aeon() != &actual {
            return Err(refused(
                "the supplied cycle is exactly one forward pump winding",
            ));
        }
        if !point.commit.is_multiple_of(period) {
            return Err(refused("the mount lies on the phase-zero closing boundary"));
        }
        if !domain.step(0)?.contains(&point.configuration)? {
            return Err(refused("the mounted point lies in its certified domain"));
        }
        // The native opening at tick zero holds K_0, while a continuing cyclic
        // boundary holds K_last. Refuse a changing-material zero opening until
        // its initial holding relation is declared, rather than invent pump work.
        if point.commit == 0 {
            let first = domain
                .step(0)?
                .law()
                .holon()
                .loaded_parametron()
                .ok_or(refused("the mounted quartic material"))?;
            let last = domain
                .step(domain.period() - 1)?
                .law()
                .holon()
                .loaded_parametron()
                .ok_or(refused("the held quartic material"))?;
            if first.stiffness() != last.stiffness() {
                return Err(refused("a changing pump needs an entered closing boundary"));
            }
        }
        Ok(Self {
            domain,
            clock,
            primitive_cycle,
            point,
        })
    }

    pub fn point(&self) -> &HolonState {
        &self.point
    }
    pub fn domain(&self) -> &PeriodicDomain {
        &self.domain
    }
    pub fn clock(&self) -> &ClockLift {
        &self.clock
    }
    pub fn primitive_cycle(&self) -> &Cycle<ClockLift> {
        &self.primitive_cycle
    }
    /// At a phase-zero closing boundary the held material is the last phase's.
    pub fn held_holon(&self) -> Result<&Holon, HolonError> {
        Ok(self.domain.step(self.domain.period() - 1)?.law().holon())
    }

    /// Execute exactly one admitted forward winding and publish its continuing
    /// point only after every domain, balance and clock check succeeds.
    pub fn advance_cycle(&mut self) -> Result<PeriodAdvance, HolonError> {
        let period = u64::try_from(self.domain.period())
            .map_err(|_| refused("the pump period fits the material clock"))?;
        let end = self
            .point
            .commit
            .checked_add(period)
            .ok_or(refused("the material clock does not overflow"))?;
        let aeon = self
            .clock
            .forward(vec![BigInt::from(self.point.commit)], &[BigInt::from(end)])
            .map_err(|_| refused("the executed forward pump aeon"))?;
        let cycle = Cycle::close(&self.clock, aeon)
            .map_err(|_| refused("the executed pump aeon closes"))?;
        let mut current = self.point.clone();
        let mut stored = Rat::zero();
        let mut dissipated = Rat::zero();
        let mut port = Rat::zero();
        let mut active = Rat::zero();
        let mut work = Rat::zero();
        let mut defect = Rat::zero();
        for phase in 0..self.domain.period() {
            let advanced = self.domain.advance(phase, &current)?;
            if !advanced.balance.is_exact() {
                return Err(refused("the executed component balance closes"));
            }
            stored += advanced.balance.stored_change;
            dissipated += advanced.balance.dissipated;
            port += advanced.balance.port;
            active += advanced.balance.active;
            work += advanced.balance.deposition_work;
            defect += advanced.balance.discretization_defect;
            current = advanced.state;
        }
        if current.commit != end {
            return Err(refused("the executed material and pump clocks agree"));
        }
        let balance = EnergyBalance::closed(stored, dissipated, port, active, work, defect);
        if !balance.is_exact() {
            return Err(refused("the whole-cycle balance closes"));
        }
        self.point = current.clone();
        Ok(PeriodAdvance {
            state: current,
            balance,
            cycle,
        })
    }
}
