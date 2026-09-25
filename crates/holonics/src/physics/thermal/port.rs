//! The thermal side of the viscous-work port.

use num_traits::{Signed, Zero};

use crate::physics::fluid::control_volume::{CellReturn, ViscousHeat};
use crate::ratio::Rat;

use super::exchange::{EntropyEnclosure, ThermalCell};
use super::{ThermalError, positive};

/// [definition] **The admitted viscous work** entering a cell: a power `W ≥ 0` (Lean
/// `Physics/Thermal/ViscousPort.ViscousWork`). The fluid side, the dissipation
/// `W = V(2μ|Def u|² + λ(tr G)²)` and the mechanical energy it removes, belongs to the fluid
/// instance: Lean `Physics/Fluid/ControlVolume.viscousHeat`, `cell_heat_port`,
/// `dissipation_nonneg`; Rust [`ViscousHeat`], received here ([`ViscousWork::received`], Lean
/// `ViscousWork.ofFluid`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViscousWork {
    power: Rat,
}

/// [definition] **What the port returns over a tick**: the cell after it, the internal energy it
/// gained and the entropy of the tick at the port.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortReturn {
    pub next: ThermalCell,
    /// `hW`.
    pub internal_gain: Rat,
    /// `hW · C/U' ≤ C log(U'/U) ≤ hW · C/U` (Lean `port_entropy_enclosure`).
    pub entropy: EntropyEnclosure,
}

impl PortReturn {
    /// [proved-derived; implemented-exact] **The joined first law across the port**: the internal
    /// energy the cell gained over the tick minus `h` times the fluid cell's mechanical deficit
    /// (traction power minus pressure work, [`CellReturn::mechanical_deficit`]); zero when the port
    /// received that cell's viscous heat (Lean `ViscousPort.cell_port_join`, `port_first_law`).
    /// The two sides are computed independently: the gain from the thermal update, the deficit
    /// from the fluid's face tractions.
    pub fn energy_residual(&self, cell: &CellReturn, tick: &Rat) -> Rat {
        &self.internal_gain - tick * cell.mechanical_deficit()
    }
}

impl ViscousWork {
    /// The port admits only work that enters (Lean `withdrawn_work_lowers_entropy`).
    pub fn new(power: Rat) -> Result<Self, ThermalError> {
        if power.is_negative() {
            return Err(ThermalError::WithdrawnWork { power });
        }
        Ok(Self { power })
    }

    /// [definition] **The port's receiving end**: the fluid's signed viscous heat, admitted when it
    /// enters (`dissipation_nonneg` holds for a dissipative material; Lean `ViscousWork.ofFluid`)
    /// and refused otherwise.
    pub fn received(heat: &ViscousHeat) -> Result<Self, ThermalError> {
        Self::new(heat.rate().clone())
    }

    /// A closed port.
    pub fn none() -> Self {
        Self { power: Rat::zero() }
    }

    pub fn power(&self) -> &Rat {
        &self.power
    }

    /// [proved-derived; implemented-exact] **The port's production rate** `W/T ≥ 0`, zero exactly
    /// without work (Lean `portProduction`, `port_production_eq_zero_iff`).
    pub fn production_rate(&self, cell: &ThermalCell) -> Rat {
        &self.power * cell.inverse_temperature()
    }

    /// [proved-derived; implemented-exact] **The work enters the cell over a tick**: `U' = U + hW`,
    /// with the tick's entropy enclosed (Lean `port_entropy_enclosure`, nonnegative by
    /// `port_entropy_nonneg`).
    pub fn receive(&self, cell: &ThermalCell, tick: &Rat) -> Result<PortReturn, ThermalError> {
        positive("a tick", tick)?;
        let internal_gain = tick * &self.power;
        let next = cell.at(cell.energy() + &internal_gain)?;
        let entropy = EntropyEnclosure::of_cell(cell, &next);
        Ok(PortReturn {
            next,
            internal_gain,
            entropy,
        })
    }
}
