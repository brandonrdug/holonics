//! **The information instance: the ratio covector at a physical port, its rate on plural clocks, and
//! the two-parameter flow square.**
//!
//! [definition] Rebuild step 6, K4 (#75); restructure plan §3.6 at `13f8c734`; CLAUDE.md, "loss is
//! the logarithm of a ratio of Holons". Cross-entropy acts physically only through a stated material
//! or port return; a bare cross-entropy number, or bits multiplied by a temperature without that
//! source/constitutive map, is only a face. Lean owner `Physics/Information`.
//!
//! **Units.** Every logarithm is carried as the exact ℚ-linear form in `log₂ p` of
//! [`crate::ratio::surprisal::SymbolicSurprisal`], never evaluated. Energies at a thermal port are in units of `k_B T ln 2`
//! (one bit of free energy), entropies in units of `k_B ln 2` (bits); a rate in nats is carried as
//! `ln 2 · (form) + (rational)` ([`RateForm`]).
//!
//! - [`apply`]: a covector (per level, the owner's [`crate::ratio::LogRatio`] of the amplitude
//!   ratio `ψ_T/ψ_H`, whose modulus face `|R|² = q/p` is the intensity ratio, or that face declared
//!   directly) reaches a [`ThermalPort`] constituted by its own levels, a K3 bath cell and a
//!   reference verified canonical for the levels. Its modulus face shifts the levels; the protocol
//!   (quench, relaxation at the shifted levels to their computed canonical state, quasi-static
//!   restoration) returns the works, the heats of each leg from its energy balance, the computed
//!   end state and the production from the entropies. Each law relating them is a residual decided
//!   exactly: the restoring leg produces nothing, the protocol produces `D(p‖q′)`, the work
//!   extracted is the free-energy drop less that production, the Gibbs/KL identity
//!   `F(p) − F(q) = k_B T·D(p‖q)`, and free relaxation's production `D(p‖q)`. The matched covector
//!   `log(q/p)` is reversible. The heat returns to the bath cell ([`PortApply::bath_after`]), and
//!   through it to the stress–energy source. The phase face is retained, not consumed.
//! - [`cross_entropy_rate`]: `dC/dλ = −Σ ṗ log q − Σ p q̇/q`, both motions, exactly, over the owner
//!   [`crate::aeon::PositiveLaw`]; the two terms are the infinitesimal
//!   [`crate::aeon::exchange`] and [`crate::aeon::deposition`] of the first law of learning.
//!   [`cross_entropy_rate_on_clocks`] converts each dot from its own clock through a join of the
//!   clock axes ([`crate::aeon::join_axes`]) or returns the join's defect.
//! - [`flow_square`]: two column-stochastic steps (fluid, thermal) of one population close on the
//!   state and return one cross-entropy, or return both orders, the commutator on the state and the
//!   exact difference of their cross-entropies.
//!
//! | Lean (`lean/Holonics/`) | Rust |
//! |---|---|
//! | `Physics/Information/PortWork.Canonical`, `partition`, `canonicalState`, `canonicalState_canonical`, `canonicalState_eq` | [`ThermalPort`], [`canonical_state`] |
//! | `PortWork.shifted`, `quenchWork`, `relaxed`, `relaxHeat`, `restoreWork`, `restoreHeat`, `restore_production_zero`, `protocol_production`, `protocol_first_law`, `extracted_work_general`, `extracted_work_le`, `free_relaxation_production`, `work_or_production`; `Physics/InformationDifference.freeEnergy_difference_eq_thermalScale_mul_kl` | [`apply`], [`PortApply`], [`LevelCovector`] |
//! | `PortWork.effort`, `quenchWork_eq`, `quenched_canonical`, `matched_relaxed`, `reversible_production_zero`, `matched_restoreWork`, `extracted_work` | tests |
//! | `Physics/Thermal/Exchange.cell_entropy_enclosure` (the bath's return) | [`PortApply::bath_after`], [`PortApply::bath_entropy`] |
//! | `PortWork.equal_face_different_effort`; `InformationDifference.no_current_factor_of_equal_crossEntropy` | tests |
//! | `Aeon/Production/FirstLaw.hasDerivAt_crossEntropy`; `Physics/Information/CrossEntropyRate.hasDerivAt_section_crossEntropy`, `hasDerivAt_crossEntropy_clocks`, `sum_rate_eq_zero`, `hasDerivAt_kl`, `moving_reference_rate` | [`cross_entropy_rate`], [`cross_entropy_rate_on_clocks`], [`free_energy_rate`], [`RateForm`] |
//! | `Physics/Information/ClockJoin.commuting_square_reads_alike`, `square_defect`, `flow_square_orders`, `flow_square_crossEntropy_differs` | [`flow_square`], [`FlowSquare`] |
//! | `Physics/Information/CrossEntropyRate` over `Foundation/FiniteCrossEntropyReceiver.finiteCrossEntropy`; `Aeon/Production/FirstLaw.exchange`, `deposition` | [`crate::aeon::PositiveLaw::cross_entropy`] and the crate's weighted surprisal |
//!
//! [open] Owed in #62: a moving support (a one-sided or measure transport of the aperture); a port
//! that receives the covector's phase face; the HNN's own `R⁻¹dR` covector (Lean `HNN/Ratio`, when
//! its Rust owner lands) joined to [`apply`] as a [`LevelCovector`] source; the finite-step
//! quasi-static limit the restoring leg presupposes; a heat whose form is irrational entering the
//! bath (an enclosure of the bath's energy).

use thiserror::Error;

use crate::aeon::AeonError;
use crate::physics::thermal::ThermalError;
use crate::ratio::GaussianError;
use crate::ratio::exponentiated::RatioError;
use crate::ratio::linear::ExactLinearError;
use crate::ratio::surprisal::SurprisalError;

mod apply;
mod rate;
#[cfg(test)]
mod tests;

pub use apply::{LevelCovector, PortApply, ThermalPort, apply, canonical_state};
pub use rate::{
    Clocked, FlowSquare, RateForm, cross_entropy_rate, cross_entropy_rate_on_clocks, flow_square,
    free_energy_rate,
};

/// Every refusal of the information instance. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum InformationError {
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("{what} changes the total mass: a moving support needs a measure transport")]
    MovingSupport { what: &'static str },
    #[error("the reference is not canonical for the levels: level {level} breaks the common gauge")]
    NotCanonical { level: usize },
    #[error("{what} is not column-stochastic at column {column}")]
    NotAStep { what: &'static str, column: usize },
    #[error(
        "the heat {heat:?} is irrational in bits: the bath's rational energy cannot receive it"
    )]
    IrrationalHeat {
        heat: crate::ratio::surprisal::SymbolicSurprisal,
    },
    #[error(transparent)]
    Surprisal(#[from] SurprisalError),
    #[error(transparent)]
    Gaussian(#[from] GaussianError),
    #[error(transparent)]
    Ratio(#[from] RatioError),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    /// Boxed: an aeon refusal carries its obstruction.
    #[error(transparent)]
    Aeon(Box<AeonError>),
    /// Boxed: a thermal refusal carries its aeon and Holon refusals.
    #[error(transparent)]
    Thermal(Box<ThermalError>),
}

impl From<ThermalError> for InformationError {
    fn from(error: ThermalError) -> Self {
        Self::Thermal(Box::new(error))
    }
}

impl From<AeonError> for InformationError {
    fn from(error: AeonError) -> Self {
        Self::Aeon(Box::new(error))
    }
}
