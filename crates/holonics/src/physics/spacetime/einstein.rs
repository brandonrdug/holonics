//! Einstein's residual, the conservation return, and the discrete Bianchi identity.

use num_traits::Zero;

use crate::geometry::complex::CellComplex;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::is_zero;

use super::SpacetimeError;

fn same_extent(what: &'static str, expected: usize, found: usize) -> Result<(), SpacetimeError> {
    if expected == found {
        Ok(())
    } else {
        Err(SpacetimeError::Shape {
            what,
            expected,
            found,
        })
    }
}

/// [definition] **The Einstein residual** `𝓡 = G + Λg − κT` (Lean
/// `Fluid/NavierStokesCurvedTransport.einsteinResidual`), componentwise on any carrier of the
/// tensor; the field equation is `𝓡 = 0` (`einsteinResidual_eq_zero_iff`).
pub fn einstein_residual(
    einstein: &[Rat],
    metric: &[Rat],
    stress: &[Rat],
    cosmological: &Rat,
    coupling: &Rat,
) -> Result<Vec<Rat>, SpacetimeError> {
    same_extent("metric components", einstein.len(), metric.len())?;
    same_extent("stress components", einstein.len(), stress.len())?;
    Ok(einstein
        .iter()
        .zip(metric)
        .zip(stress)
        .map(|((g, m), t)| g + cosmological * m - coupling * t)
        .collect())
}

/// [definition] **A conservation return**: the source's divergence `∇·T`, computed directly, and the
/// residual's `∇·𝓡`, related by `κ ∇·T = −∇·𝓡`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConservationReturn {
    pub source_divergence: Vec<Rat>,
    pub residual_divergence: Vec<Rat>,
    pub residual: Vec<Rat>,
}

impl ConservationReturn {
    /// Whether the source is conserved, `∇·T = 0`.
    pub fn is_conserved(&self) -> bool {
        is_zero(&self.source_divergence)
    }
}

/// [proved-derived; implemented-exact] **The conservation return** (Lean
/// `Fluid/NavierStokesCurvedTransport.conservation_return`, `conservation_return_eq`): over a linear
/// divergence with the contracted Bianchi port `∇·G = 0`
/// and metric compatibility `∇·g = 0`, `κ ∇·T = −∇·𝓡`. Both ports are read, not assumed: a failing
/// one is refused with its defect (Lean `field_equation_without_bianchi`: without it the field
/// equation does not conserve its source). A zero coupling is refused.
pub fn conservation_return(
    divergence: &ExactRatMatrix,
    einstein: &[Rat],
    metric: &[Rat],
    stress: &[Rat],
    cosmological: &Rat,
    coupling: &Rat,
) -> Result<ConservationReturn, SpacetimeError> {
    if coupling.is_zero() {
        return Err(SpacetimeError::ZeroCoupling);
    }
    let bianchi = divergence.apply(einstein)?;
    if !is_zero(&bianchi) {
        return Err(SpacetimeError::NoBianchi { defect: bianchi });
    }
    let metric_divergence = divergence.apply(metric)?;
    if !is_zero(&metric_divergence) {
        return Err(SpacetimeError::MetricNotCompatible {
            defect: metric_divergence,
        });
    }
    let residual = einstein_residual(einstein, metric, stress, cosmological, coupling)?;
    Ok(ConservationReturn {
        source_divergence: divergence.apply(stress)?,
        residual_divergence: divergence.apply(&residual)?,
        residual,
    })
}

/// [definition] **The discrete Einstein side** of a field on a cell complex: `G = ∂_(k+1) F`, a
/// `k`-chain, and its **Bianchi reading** `∂_k G`, which vanishes because `∂∂ = 0` (Lean
/// `Einstein.discrete_bianchi`; the complex's constructor checks `∂∂ = 0`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellEinstein {
    pub einstein: Vec<Rat>,
    pub bianchi: Vec<Rat>,
    /// `∂_k`, the divergence the conservation return consumes.
    pub divergence: ExactRatMatrix,
}

/// [proved-derived; implemented-exact] **The discrete Einstein side and its derived Bianchi
/// identity** at degree `k ≥ 1`: the field is a `(k+1)`-chain; the Einstein side `∂_(k+1) F` is a
/// `k`-chain whose boundary is zero. The conservation return then forces `∂_k j = 0` for every
/// source with `G + Λg = κj` and a metric cycle `∂_k g = 0` (Lean `cell_field_conserves`,
/// `grid_field_conserves`).
pub fn cell_einstein(
    complex: &CellComplex,
    degree: usize,
    field: &[Rat],
) -> Result<CellEinstein, SpacetimeError> {
    let (Some(lower), Some(upper)) = (complex.boundary(degree), complex.boundary(degree + 1))
    else {
        return Err(SpacetimeError::FieldDegree {
            degree,
            most: complex.dimension().saturating_sub(1),
        });
    };
    let einstein = upper.apply(field)?;
    let bianchi = lower.apply(&einstein)?;
    Ok(CellEinstein {
        einstein,
        bianchi,
        divergence: lower.clone(),
    })
}
