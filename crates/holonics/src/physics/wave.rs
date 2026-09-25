//! **The wave instance: interference before intensity, and propagation under a supplied
//! operator, material, boundary and clock.**
//!
//! [definition] Rebuild step 6, K3 (#74), battle test 2; ELEMENTARY_OBJECTS operator contract,
//! "Physical instances" (`propagate`, `interfere`). Lean owner `Physics/Wave` (library root
//! `lean/Holonics/`).
//!
//! **Interference** ([`interfere`]): complex amplitudes, each already carried along its path by
//! its connection phase (multiplication by the unit amplitude
//! [`crate::holon::parametron::Carrier::as_gaussian`] of a carrier of the unit circle), are joined
//! before any intensity is read. The coherent intensity is `|Σu|² = Σ|u|² + 2 Re Σ_(j<k) ū_j u_k`
//! (`Wave/Interference.intensity_eq`); reading the intensities first returns only `Σ|u|²` and has
//! lost the cross terms, so `1 + (−1)` reads `0` coherently and `2` incoherently
//! (`opposite_amplitudes_cancel`, `coherent_not_a_function_of_incoherent`).
//!
//! **Propagation** ([`WaveChain::propagate`]): the telegrapher's constitution
//! `εμ∂²u + σμ∂u = ∇²u` on LC cells. The operator is **supplied** as an [`Incidence`] (nodes and
//! oriented junctions; an open chain, a ring, any graph), the **boundary** is that incidence's (an
//! open end is a node with one junction, a ring has none), the **material** is a
//! [`WaveMaterial`] (node capacitance `C`, leakage `G`, junction inductance `L`) and the **clock**
//! is the staggered tick `h`:
//!
//! ```text
//! L (I⁺ − I) = −h D V                       C (V⁺ − V) = h Dᵀ I⁺ − h G (V⁺ + V)/2 + h s
//! ```
//!
//! (`Wave/Telegrapher.step_is_the_telegrapher`, `Wave/Energy.Tick`). Each tick is explicit and
//! local: a junction reads its two nodes, a node its own junctions, and no global solve enters
//! (the light record §8.1). Every tick returns its exact energy balance, whose residual is zero
//! (`Wave/Energy.energy_balance`): the staggered energy `½ΣCV² + ½ΣL I⁻I⁺` changes by the source
//! power minus the leakage heat `hΣGV̄²`. Under the strict Courant condition `h²β < 4` the
//! staggered energy is a norm on the state `(V, I)` (`energy_lower_bound`, `energy_definite`); the
//! condition is the scheme's stability (CFL) statement.
//!
//! **The field is a Holon** ([`WaveChain::holon`], Lean `Holon/Conformance.mediumHolon`): the
//! port-Hamiltonian medium on the charges and fluxes `(CV, LI)` with storage `diag(1/C, 1/L)`, the
//! skew interconnection `[[0, Dᵀ], [−D, 0]]` of the supplied incidence, the leakage as its
//! resistive relation and one source port per node. The staggered tick is a different integrator
//! of this Holon than the reference law's midpoint: its conserved quantity is the staggered energy,
//! the midpoint's the storage energy `½ΣCV² + ½ΣLI²`.
//!
//! | Lean (`lean/Holonics/`) | Rust |
//! |---|---|
//! | `Physics/Wave/Interference.intensity_eq`, `cross_is_the_difference` | [`interfere`], [`Interference`] |
//! | `Physics/Wave/Interference.common_phase_invariant`, `incoherent_phase_blind` | [`crate::holon::parametron::Carrier::as_gaussian`] |
//! | `Physics/Wave/Energy.Tick`, `grad`, `div`, `pairing` | [`Incidence::grad`], [`Incidence::div`], [`WaveChain::propagate`] |
//! | `Physics/Wave/Energy.energy`, `energy_balance`, `energy_nonincreasing` | [`WaveChain::energy`], [`WaveBalance`] |
//! | `Physics/Wave/Energy.operator_bound_of_rows`, `energy_lower_bound`, `energy_definite`, `chain_beta`, `chain_energy_lower_bound`, `chain_energy_definite` | [`WaveChain::courant_bound`], [`WaveChain::energy_floor`] |
//! | `Holon/Conformance.mediumHolon`, `medium_rate_agrees` | [`WaveChain::holon`], [`WaveChain::configuration`] |
//! | `Physics/Wave/Telegrapher.step_supported`, `run_cone`, `change_moves_one_cell_per_tick` | [`WaveChain::propagate`] on [`Incidence::open_chain`] |
//! | `Physics/Wave/Telegrapher.step_front_right`, `impulse_front_damped`, `damping` | [`WaveChain::front_factor`], [`damping`] |
//! | `Physics/Wave/Radiation.stationary_emits_nothing`, `radiation_is_the_change`, `receiver_reads_the_change` | [`WaveChain::is_stationary`] |
//!
//! [open] The cone is proved on the unbounded chain (`ℤ` nodes) and exercised here on finite open
//! chains away from their ends; the cone on a general incidence (one graph neighbourhood per
//! tick) and the continuum consistency of the staggered scheme with the telegrapher equation are
//! owed in #62. No float enters a law.

use num_traits::{One, Signed};
use thiserror::Error;

use crate::holon::HolonError;
use crate::ratio::{Rat, integer};

mod chain;
mod interference;
#[cfg(test)]
mod tests;

pub use chain::{
    Incidence, Junction, Propagation, WaveBalance, WaveChain, WaveMaterial, WaveState, damping,
};
pub use interference::{Interference, interfere};

/// Every refusal of the wave instance. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum WaveError {
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("junction {junction} joins node {node}, outside the {nodes} nodes")]
    NodeOutside {
        junction: usize,
        node: usize,
        nodes: usize,
    },
    #[error("junction {junction} returns to its own node: a junction joins two nodes")]
    Loop { junction: usize },
    #[error("{what} {index} is {value}; the constitution needs it {requirement}")]
    Material {
        what: &'static str,
        index: usize,
        value: Rat,
        requirement: &'static str,
    },
    #[error("the tick {tick} is not positive: the clock must advance")]
    Tick { tick: Rat },
    #[error("{what} needs at least {least} nodes, found {found}")]
    TooFewNodes {
        what: &'static str,
        least: usize,
        found: usize,
    },
    #[error(transparent)]
    Holon(#[from] HolonError),
}

/// `x²` for an exact rational.
fn square(value: &Rat) -> Rat {
    value * value
}

/// The declared positivity of a constitutive coefficient, checked one index at a time.
fn check_coefficients(what: &'static str, values: &[Rat], strictly: bool) -> Result<(), WaveError> {
    for (index, value) in values.iter().enumerate() {
        let admitted = if strictly {
            value.is_positive()
        } else {
            !value.is_negative()
        };
        if !admitted {
            return Err(WaveError::Material {
                what,
                index,
                value: value.clone(),
                requirement: if strictly { "positive" } else { "nonnegative" },
            });
        }
    }
    Ok(())
}

/// `½`.
fn half() -> Rat {
    Rat::one() / integer(2)
}
