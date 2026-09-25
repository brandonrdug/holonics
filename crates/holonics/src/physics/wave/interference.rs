//! Interference: coherent amplitudes join before the intensity is read.
//!
//! An amplitude at a receiving locus is a Gaussian rational `re + i·im` ([`GaussianRat`], the
//! ratio owner's exact complex scalar). Transport along a connection is multiplication by the unit
//! amplitude of its phase, the parametron carrier read in `ℚ(i)`
//! ([`crate::holon::parametron::Carrier::as_gaussian`]); a joint phase leaves every coherent
//! intensity unchanged (Lean `Physics/Wave/Interference.common_phase_invariant`).

use num_traits::Zero;

use crate::ratio::{GaussianRat, Rat, integer};

/// [definition] **An interference return**: the coherent join, its intensity, the incoherent
/// reading (intensities first) and the cross terms that separate them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interference {
    /// `Σ u_j`.
    pub coherent: GaussianRat,
    /// `|Σ u_j|²`: what the receiver reads after the join.
    pub intensity: Rat,
    /// `Σ |u_j|²`: what a receiver reads that takes intensities first.
    pub incoherent: Rat,
    /// `2 Re Σ_(j<k) ū_j u_k`: the cross terms, `intensity − incoherent`.
    pub cross: Rat,
}

/// [proved-derived; implemented-exact] **Join the amplitudes, then read.** Lean
/// `Physics/Wave/Interference.intensity_eq`: `intensity = incoherent + cross`, each term computed
/// on its own.
pub fn interfere(amplitudes: &[GaussianRat]) -> Interference {
    let coherent = amplitudes
        .iter()
        .fold(GaussianRat::zero(), |sum, amplitude| sum.add(amplitude));
    let incoherent = amplitudes.iter().map(GaussianRat::norm_sq).sum();
    let mut pairs = Rat::zero();
    for (k, later) in amplitudes.iter().enumerate() {
        for earlier in &amplitudes[..k] {
            pairs += earlier.conj().mul(later).re;
        }
    }
    Interference {
        intensity: coherent.norm_sq(),
        coherent,
        incoherent,
        cross: integer(2) * pairs,
    }
}
