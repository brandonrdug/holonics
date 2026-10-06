//! **The thermal instance: exchange with a first law and a certified entropy production, the
//! production across a neck, and the time and entropy axes of an oriented chain.**
//!
//! [definition] Rebuild step 6, K3 (#74), battle test 5, issue #5; ELEMENTARY_OBJECTS operator
//! contract, "Physical instances" (`exchange`, `entropy_production`). Lean owner
//! `Physics/Thermal` (library root `lean/Holonics/`).
//!
//! **Exchange** ([`exchange`]): two [`ThermalCell`]s under the caloric law `U = C T` share a
//! [`Contact`] of conductance `κ`; over a tick `h` it carries the heat `q = hκ(T₀ − T₁)`, and each
//! cell may also receive the work of a port ([`ViscousWork`], the thermal side of the fluid's
//! viscous-work port). The return carries the first law (stored change equals port work, residual
//! zero by construction of the update, `Thermal/Exchange.first_law`), the exact production rate
//! `κ(T₀ − T₁)²/(T₀T₁) + W₀/T₀ + W₁/T₁` (`productionRate_eq`, `hasDerivAt_entropy`), and the tick's
//! entropy `ΔS = Σ C log(U'/U)` enclosed by two rational Clausius readings for the contact and for
//! each port (`cell_entropy_enclosure`). Under the tick condition `hκ(1/C₀ + 1/C₁) ≤ 1` the
//! contact's lower reading is `hκ(T₀ − T₁)²(1 − hκ(1/C₀ + 1/C₁))/(T₀'T₁') ≥ 0`
//! (`lower_reading_eq`, `exchange_entropy_nonneg`) and the ports' are `hW C/U' ≥ 0`
//! (`ViscousPort.port_entropy_enclosure`): the sign is certified on the rationals. A tick that
//! breaks the condition overshoots and can destroy entropy (`overshoot_destroys_entropy`), so it is
//! refused. Entropy is in the chart `S = C log U` (capacities in units of `k_B`, log natural).
//!
//! **The contact is a Holon** ([`Contact::holon`], Lean `Holon/Conformance.mediumHolon`,
//! `diffusion_dissipates`): the
//! diffusion medium on the internal energies, storage `diag(1/C)`, resistance `κ` times the
//! Laplacian, one port per cell for its work. [`exchange`] is that medium's explicit step; the
//! reference law's midpoint and backward-Euler steps are other integrators of the same Holon.
//!
//! **Production across a neck** ([`NeckProduction`]): Schnakenberg's
//! `σ = Σ (J₊ − J₋) log(J₊/J₋)` over the neck's junctions. The operands are the exact pairs
//! `(J₊ − J₋, J₊/J₋)`; `σ` is carried as the exact ℚ-linear form in `log₂ p`
//! ([`crate::ratio::surprisal::SymbolicSurprisal::log2_of_ratio`], in bits,
//! `Thermal/Schnakenberg.neckProduction_eq_edgeCode`), and its sign is certified by the rational
//! certificate `Σ (J₊ − J₋)²/J₋` (`certificate_eq`, `term_pos_iff_certificate_pos`). It is zero
//! exactly when the neck is balanced (`neckProduction_eq_zero_iff`), decided exactly.
//! [`cut_production`] reads the neck of a [`crate::aeon::MarkovChain`]'s section, a set of states
//! (`cutProduction_le_epochProduction`).
//!
//! **The axes of an oriented chain** ([`OrientedChain`], #5): the longitudinal axis is the signed
//! epochs at the chain's **carry section** (Lean `Aeon/Clock/Epoch.signed_count_is_flux`), the
//! entropy axis the aeon's heat, the ratio product of its step affinities
//! ([`crate::aeon::MarkovChain::heat`], `PathReversal.pathLogRatio_split`). Their crossing
//! ([`TwoAxisReading`]) is exact: `heat = (R(end)/R(start)) · turnⁿ`, `n` the signed epochs at the
//! carry section, `R` the entropy coordinate as a ratio product and `turn` the ring's cycle ratio
//! product (`Thermal/ChainAxes.entropy_reading`, `helix_step`); an open chain has `turn = 1` and no
//! stationary arrow (`path_no_arrow`). The production at any law is Schnakenberg's across the
//! junctions ([`OrientedChain::production`], `ringProduction_eq_neck`); at a stationary law a ring
//! carries one current (`ring_one_current`) and produces `J · log turn` per epoch
//! ([`OrientedChain::cycle_production`], `stationary_ringProduction_eq`, `cycleAffinity_law_free`).
//! The carry section is where the entropy coordinate takes its carry; the **neck**, the junction of
//! least forward flow (`neckFlow`), is a different object: every junction's forward flow bounds the
//! current and the production (`current_lt_forward`, `production_le_junction`), and the neck's is
//! the sharpest of these bounds (`production_le_neck`).
//!
//! | Lean (`lean/Holonics/`) | Rust |
//! |---|---|
//! | `Physics/Thermal/Exchange.first_law`, `productionRate_eq`, `productionRate_eq_zero_iff`, `hasDerivAt_entropy` | [`exchange`], [`ExchangeReturn`] |
//! | `Physics/Thermal/Exchange.cell_entropy_enclosure`, `exchange_entropy_enclosure`, `lower_reading_eq`, `exchange_entropy_nonneg`, `overshoot_destroys_entropy` | [`EntropyEnclosure`], [`ThermalError::Overshoot`] |
//! | `Holon/Conformance.mediumHolon`, `medium_rate_agrees`, `diffusion_dissipates`; `Holon/Element.backwardEuler_balance` | [`Contact::holon`] |
//! | `Physics/Thermal/ViscousPort.ViscousWork.ofFluid`, `cell_port_join`, `port_first_law`, `port_production_eq_zero_iff`, `port_entropy_enclosure`, `withdrawn_work_lowers_entropy` | [`ViscousWork`], [`ViscousWork::received`], [`PortReturn`], [`PortReturn::energy_residual`] |
//! | `Physics/Thermal/Schnakenberg.certificate_eq`, `neckProduction_eq_edgeCode`, `neckProduction_eq_zero_iff`, `twoCell_is_neck` | [`JunctionFlow`], [`NeckProduction`] |
//! | `Physics/Thermal/Schnakenberg.epochProduction_eq_cut_add_interior`, `cutProduction_le_epochProduction` | [`cut_production`] |
//! | `Physics/Thermal/ChainAxes.stationary_cut_balance`, `path_detailedBalance`, `path_no_arrow` | [`OrientedChain::open`], [`OrientedChain::current`] |
//! | `Physics/Thermal/ChainAxes.ring_one_current`, `ring_nets_eq`, `stationary_ringProduction_eq`, `ringProduction_eq`, `ringProduction_eq_neck`, `neckProduction_ring_eq`, `cycleAffinity_law_free`, `current_affinity_sign`, `ring_reversal` | [`OrientedChain::ring`], [`OrientedChain::turn`], [`OrientedChain::production`], [`OrientedChain::cycle_production`] |
//! | `Physics/Thermal/ChainAxes.current_lt_forward`, `production_le_junction`, `neckFlow`, `production_le_neck` | [`OrientedChain::junction_flows`] |
//! | `Physics/Thermal/ChainAxes.helix_step`, `entropy_reading`, `cycle_reading`, `backward_step_reads_negative` | [`OrientedChain::axes`], [`OrientedChain::carry_section`], [`TwoAxisReading`] |
//!
//! The fluid side of the viscous-work port, the dissipation `V(2μ|Def u|² + λ(tr G)²)` and the
//! mechanical energy it removes, is the fluid instance's
//! ([`crate::physics::fluid::control_volume::ViscousHeat`], produced only by
//! [`crate::physics::fluid::control_volume::ControlVolume::cell_return`]; Lean
//! `Physics/Fluid/ControlVolume.viscousHeat`, `cell_heat_port`); this module receives it
//! ([`ViscousWork::received`]) and closes the joined first law against the cell's mechanical
//! deficit ([`PortReturn::energy_residual`]).
//!
//! [definition] **The retired diffusion receipt.** `holonics-cuda/src/diffusion.rs`
//! (`DiffusionReceipt::energy_balance`: implicit diffusion on an incidence complex, with source
//! work, conductive dissipation and the backward-Euler defect `½⟨Δφ, CΔφ⟩`) was retired in
//! `bb73054a`. Its balance now lives in the Holon law: [`Contact::holon`] under
//! [`crate::holon::law::Scheme::BackwardEuler`] carries the same three terms exactly
//! (`Holon/Element.backwardEuler_balance`), and [`exchange`] carries the two-cell first law.
//!
//! [open] Owed in #62: `diffuse`, heat conduction on a many-cell incidence (the retired receipt's
//! complex); a relaxation (finite-speed) heat law; the kinetic-energy side of the viscous port,
//! which needs the fluid's time advance; the identification of a chain's occurrence rates with
//! physical heat through a local detailed-balance law; and the two statements of the
//! `ChainAxes` [open] paragraph, Rust-tested only: the lift's `entropyForm` read along a lifted
//! ring path equals its path log-ratio (`PathReversal.pathLogRatio_split`), and the mean signed
//! crossings of the carry section over `n` steps from the stationary law are `n · J`.

use num_traits::Signed;
use thiserror::Error;

use crate::aeon::AeonError;
use crate::holon::HolonError;
use crate::ratio::Rat;
use crate::ratio::surprisal::SurprisalError;

mod axes;
mod exchange;
mod neck;
mod port;
#[cfg(test)]
mod tests;

pub use axes::{OrientedChain, TwoAxisReading};
pub use exchange::{Contact, EntropyEnclosure, ExchangeReturn, ThermalCell, exchange};
pub use neck::{JunctionFlow, NeckProduction, cut_production};
pub use port::{PortReturn, ViscousWork};

/// Every refusal of the thermal instance. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ThermalError {
    #[error("{what} is {value}; it must be {requirement}")]
    Coefficient {
        what: &'static str,
        value: Rat,
        requirement: &'static str,
    },
    #[error(
        "the tick overshoots: hκ(1/C₀ + 1/C₁) = {factor} > 1 reverses the temperature order and can destroy entropy"
    )]
    Overshoot { factor: Rat },
    #[error("a port that withdraws work ({power}) is not viscous heating")]
    WithdrawnWork { power: Rat },
    #[error("the junction {from} → {to} carries flow one way only: its log ratio has no value")]
    IrreversibleJunction { from: usize, to: usize },
    #[error("the transition {from} → {to} skips a cell: the chain is not nearest-neighbour")]
    NotNearestNeighbour { from: usize, to: usize },
    #[error("{what} needs at least {least} cells, found {found}")]
    TooFewCells {
        what: &'static str,
        least: usize,
        found: usize,
    },
    #[error("junction {junction} carries a net flow different from junction 0: not one current")]
    NotOneCurrent { junction: usize },
    #[error("the law is not stationary: its mass at cell {cell} changes over one epoch")]
    NotStationary { cell: usize },
    #[error("cell {cell} is repeated: a section is a set of cells")]
    RepeatedCell { cell: usize },
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    /// Boxed: an aeon refusal carries its obstruction.
    #[error(transparent)]
    Aeon(Box<AeonError>),
    #[error(transparent)]
    Surprisal(#[from] SurprisalError),
    #[error(transparent)]
    Holon(#[from] HolonError),
}

impl From<AeonError> for ThermalError {
    fn from(error: AeonError) -> Self {
        Self::Aeon(Box::new(error))
    }
}

/// A strictly positive coefficient, or its refusal.
fn positive(what: &'static str, value: &Rat) -> Result<(), ThermalError> {
    if value.is_positive() {
        Ok(())
    } else {
        Err(ThermalError::Coefficient {
            what,
            value: value.clone(),
            requirement: "positive",
        })
    }
}

/// A nonnegative coefficient, or its refusal.
fn nonnegative(what: &'static str, value: &Rat) -> Result<(), ThermalError> {
    if value.is_negative() {
        Err(ThermalError::Coefficient {
            what,
            value: value.clone(),
            requirement: "nonnegative",
        })
    } else {
        Ok(())
    }
}
