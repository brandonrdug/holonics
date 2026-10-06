//! **The spacetime instance: the stress–energy source of a constituted cell, Einstein's residual
//! and its conservation return, the observer current, and the Lorentz transformation on aeon
//! clocks.**
//!
//! [definition] Rebuild step 6, K4 (#75); restructure plan §3.6 at `13f8c734`; null-cone record
//! (2026-09-24) §1–§2. Lean owner `Physics/Spacetime` (library root `lean/Holonics/`). Every law
//! computes over exact rationals; no float and no evaluated logarithm enters a law.
//!
//! - [`source`]: the **source map** from a constituted K3 cell (the fluid's Newtonian stress, the
//!   thermal cell's internal energy, the contact's heat flux) to the Eckart stress–energy `T`; its
//!   **trace reversal** `T̄ = T − ½(tr_η T)η`, by which the field equation reads `Ric = κT̄` and dust
//!   at `κ = 8πG` reads `R₀₀ = 4πGρ`; a [`LorentzMap`] carrying vectors, the source and a receiver's
//!   gradient; and the **observer current** `j_U = −T·u` whose divergence is the force power plus
//!   the observer's deformation term, invariant when source, receiver and force are carried
//!   together; for the comoving receiver the deformation is the fluid's pressure work plus the
//!   viscous heat of the thermal port.
//! - [`einstein`]: the **Einstein residual** `𝓡 = G + Λg − κT`, the **conservation return**
//!   `κ ∇·T = −∇·𝓡` over a linear divergence with the Bianchi and metric ports, and the **discrete
//!   Bianchi identity**: when the Einstein side is the boundary of a field on a cell complex, `∂∂ = 0`
//!   derives the Bianchi port and forces conservation; a potential-sourced current has no flux
//!   through any block of a Holarchy at any grain.
//! - [`lorentz`]: the boost as the **Doppler ratio** `(u, v) ↦ (ku, k⁻¹v)`, composition by products
//!   (velocity addition through the landmark owner's Doppler chart,
//!   [`crate::compression::landmark::doppler_chart`]), time dilation as the owner's aeon **rate** of
//!   two inertial clocks, the twin read from its displacement, and the **Thomas–Wigner rotation** of
//!   a loop of perpendicular boosts as the oriented angle defect of its velocity triangle, read from
//!   the triangle's vertices.
//! - [`clocks`]: **non-closed clocks**: Sagnac and the gravitational redshift read on a cycle as the
//!   production time of the owner's Hodge split ([`crate::aeon::hodge_split`]); the redshift as the
//!   owner's rate of two static clocks ([`crate::aeon::rate`]).
//!
//! | Lean (`lean/Holonics/`) | Rust |
//! |---|---|
//! | `Physics/Spacetime/StressEnergy.sourceMap`, `sourceMap_symmetric`, `sourceMap_restReading`, `sourceMap_perfect`, `sourceMap_spatialTrace`, `sourceMap_boostedEnergy` | [`source_map`], [`StressEnergy`], [`ConstitutedState`] |
//! | `StressEnergy.minkowskiTrace`, `traceReversed`, `trace_reversal`, `traceReversed_zero_zero`, `sourceMap_traceReversed`, `perfectFluid_traceReversed`, `dust_newtonian_source`, `sourceMap_newtonian_source` | [`StressEnergy::minkowski_trace`], [`StressEnergy::trace_reversed`] |
//! | `StressEnergy.transport`, `lorentz_inverse`, `observerBilinear_transport`, `boosted_reads_transported`, `boostT`, `boostT_lorentz`, `boostedObserver_eq`, `sourceMap_boosted_transport` | [`LorentzMap`], [`ReceiverWorldline::transported`] |
//! | `StressEnergy.comoving_observerDivergence`, `rigid_comoving_reads_force`, `expanding_receiver_reads_pressure_work`, `sheared_receiver_reads_viscous_heat`; `ObserverBoundaryCurrent.observerCurrentDivergence` | [`observer_current`], [`ReceiverWorldline`], [`ObserverCurrent`] |
//! | `Fluid/NavierStokesCurvedTransport.einsteinResidual`, `conservation_return`, `conservation_return_eq`, `conserved_of_residual_zero`; `Physics/Spacetime/Einstein.field_equation_without_bianchi` | [`einstein_residual`], [`conservation_return`], [`ConservationReturn`] |
//! | `Einstein.discrete_bianchi`, `cell_field_conserves`, `grid_field_conserves`, `segment_current_not_conserved`, `potential_field_block_flux_zero`, `potential_field_total_flux_zero` | [`cell_einstein`], [`CellEinstein`] |
//! | `Physics/Spacetime/Boost.boost_pairing`, `boost_mul`, `boost_tx`, `doppler_betaOf`, `velocity_addition` (through `Compression/Landmark/FixedPoint.doppler_vadd`), `clockReading_boost`, `time_dilation`, `dilation_is_rate`, `twin_interval`, `one_lt_gammaOf` | [`DopplerBoost`], [`LightCone`], [`time_dilation`], [`twin`] |
//! | `Physics/Spacetime/Wigner.wigner_decomposition`, `loop_returns_rotation`, `vertex_pairings`, `right_angle_at_P`, `rest_vertex_angle`, `far_vertex_angle`, `vertexAngles_nonneg`, `vertexAngles_on_circle`, `orientedArea_triangle`, `wigner_angle_is_defect`, `wigner_two_three`, `boostX_mul_boostX` | [`wigner_rotation`], [`WignerRotation`], [`VelocityTriangle`] |
//! | `Physics/Spacetime/NonClosedClock.sagnac_reading`, `sagnac_is_production`, `sagnac_not_closed`, `static_reading`, `static_is_production`, `staticClock`, `redshift_rate`, `inertial_clock_silent` | [`square_complex`], [`sagnac_clock`], [`static_clock`], [`read_on_cycle`], [`redshift_rate`] |
//!
//! [open] Owed in #62: a nontrivial continuum Einstein realization (a Lorentzian metric, its
//! connection and curvature, and a fluid-plus-thermal constitution solving `G + Λg = κT`); the weak
//! static limit `R₀₀ = ∇²Φ`; the Regge construction of the discrete Einstein side; the hyperbolic
//! Gauss–Bonnet identification of the Wigner defect with the velocity triangle's area, the
//! non-perpendicular composition and the join to the gyration reading; a frame-dragging clock; the
//! relativistic (finite-speed) heat law.

use thiserror::Error;

use crate::aeon::AeonError;
use crate::compression::landmark::LandmarkError;
use crate::geometry::RatVec3;
use crate::holon::HolonError;
use crate::ratio::Rat;
use crate::ratio::linear::ExactLinearError;

mod clocks;
mod einstein;
mod lorentz;
mod source;
#[cfg(test)]
mod tests;

pub use clocks::{
    CycleReading, read_on_cycle, redshift_rate, sagnac_clock, square_complex, static_clock,
};
pub use einstein::{
    CellEinstein, ConservationReturn, cell_einstein, conservation_return, einstein_residual,
};
pub use lorentz::{
    DopplerBoost, LightCone, TwinReading, VelocityTriangle, WignerRotation, clock_reading,
    receiver_velocity, time_dilation, twin, wigner_rotation,
};
pub use source::{
    ConstitutedState, LorentzMap, ObserverCurrent, ReceiverWorldline, StressEnergy, Tensor4,
    Vector4, observer_current, source_map,
};

/// Every refusal of the spacetime instance. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum SpacetimeError {
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("{what} is {value}; it must be {requirement}")]
    Coefficient {
        what: &'static str,
        value: Rat,
        requirement: &'static str,
    },
    #[error(
        "the receiver's velocity reads {norm} on itself, not −1: it is not a unit timelike velocity"
    )]
    NotUnitTimelike { norm: Rat },
    #[error("the receiver's velocity is past-directed")]
    PastDirected,
    #[error(
        "row {row} of the receiver's gradient does not annihilate its velocity (U^ν ∂_μ u_ν ≠ 0): it is not the gradient of a unit timelike field"
    )]
    GradientNotUnitPreserving { row: usize },
    #[error(
        "the flow moves at the event (velocity {velocity:?}): its comoving receiver is not at rest"
    )]
    FlowNotAtRest {
        /// Boxed: three exact rationals.
        velocity: Box<RatVec3>,
    },
    #[error("the field's boundary degree {degree} is outside 1..={most}")]
    FieldDegree { degree: usize, most: usize },
    #[error("the displacement's interval {interval} is not the square of a rational proper time")]
    NotARationalProperTime { interval: Rat },
    #[error("the divergence of the Einstein side is {defect:?}, not zero: the Bianchi port fails")]
    NoBianchi { defect: Vec<Rat> },
    #[error("the divergence of the metric is {defect:?}, not zero: the metric port fails")]
    MetricNotCompatible { defect: Vec<Rat> },
    #[error("a zero coupling does not constitute the source")]
    ZeroCoupling,
    #[error("the loop of boosts does not return a rotation of the spatial plane")]
    NotARotation,
    #[error("the matrix does not preserve the Minkowski metric: Λᵀ η Λ ≠ η")]
    NotLorentz,
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    /// Boxed: the Holon refusals carry exact inertia witnesses.
    #[error(transparent)]
    Holon(Box<HolonError>),
    /// Boxed: a landmark refusal carries its chart.
    #[error(transparent)]
    Landmark(Box<LandmarkError>),
    /// Boxed: an aeon refusal carries its obstruction.
    #[error(transparent)]
    Aeon(Box<AeonError>),
}

impl From<HolonError> for SpacetimeError {
    fn from(error: HolonError) -> Self {
        Self::Holon(Box::new(error))
    }
}

impl From<LandmarkError> for SpacetimeError {
    fn from(error: LandmarkError) -> Self {
        Self::Landmark(Box::new(error))
    }
}

impl From<AeonError> for SpacetimeError {
    fn from(error: AeonError) -> Self {
        Self::Aeon(Box::new(error))
    }
}
