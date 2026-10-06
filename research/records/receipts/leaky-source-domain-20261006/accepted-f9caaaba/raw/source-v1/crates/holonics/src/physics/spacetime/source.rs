//! The source map from a constituted cell to stress–energy, and the observer current.

use num_traits::{One, Signed, Zero};

use crate::geometry::{RatMat3, RatVec3};
use crate::physics::fluid::control_volume::{AffineFlow, ControlVolume, NewtonianMaterial};
use crate::physics::thermal::ThermalCell;
use crate::ratio::Rat;

use super::{DopplerBoost, SpacetimeError};

/// A rank-two tensor in the chart `(t, x, y, z)`, `c = 1`, signature `(−,+,+,+)`.
pub type Tensor4 = [[Rat; 4]; 4];
/// A vector (or covector) in the same chart.
pub type Vector4 = [Rat; 4];

/// The Minkowski sign `η_μμ` (Lean `ReceiverStressEnergy.minkowskiSign`).
fn sign(index: usize) -> Rat {
    if index == 0 { -Rat::one() } else { Rat::one() }
}

fn zero_tensor() -> Tensor4 {
    std::array::from_fn(|_| std::array::from_fn(|_| Rat::zero()))
}

/// [definition] **A constituted cell in its rest chart** (Lean
/// `Physics/Spacetime/StressEnergy.ConstitutedState`): rest-mass energy density, the thermal cell's
/// internal energy density, and the fluid's pressure, Newtonian material and velocity gradient
/// `G_ab = ∂_b u_a`, with the contact's heat flux.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstitutedState {
    pub rest_energy: Rat,
    pub internal_energy: Rat,
    pub pressure: Rat,
    pub material: NewtonianMaterial,
    pub gradient: RatMat3,
    pub heat_flux: RatVec3,
}

impl ConstitutedState {
    /// [definition] **The constituted state of the K3 owners**: a control volume's cell, the
    /// thermal cell whose internal energy per volume enters `T⁰⁰`, the affine flow and material
    /// whose Newtonian stress enters `Tⁱʲ`, and the contact's heat flux `T⁰ⁱ`.
    pub fn of_cells(
        volume: &ControlVolume,
        rest_energy: Rat,
        thermal: &ThermalCell,
        pressure: Rat,
        material: NewtonianMaterial,
        flow: &AffineFlow,
        heat_flux: RatVec3,
    ) -> Self {
        Self {
            rest_energy,
            internal_energy: thermal.energy() / volume.volume(),
            pressure,
            material,
            gradient: flow.gradient.clone(),
            heat_flux,
        }
    }

    /// `ε = ρ₀ + e`.
    pub fn energy_density(&self) -> Rat {
        &self.rest_energy + &self.internal_energy
    }

    /// The K3 Newtonian stress `σ = −pI + τ` (Lean `ControlVolume.stress`).
    pub fn cauchy(&self) -> RatMat3 {
        self.material.stress(&self.pressure, &self.gradient)
    }
}

/// [definition] **A stress–energy tensor** `T^{μν}` in the owner's sixteen-component chart (Lean
/// `ReceiverStressEnergy.Tensor`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StressEnergy {
    components: Tensor4,
}

impl StressEnergy {
    pub fn new(components: Tensor4) -> Self {
        Self { components }
    }

    pub fn components(&self) -> &Tensor4 {
        &self.components
    }

    pub fn at(&self, mu: usize, nu: usize) -> &Rat {
        &self.components[mu][nu]
    }

    /// [proved-derived; implemented-exact] Whether `T^{μν} = T^{νμ}` (Lean `sourceMap_symmetric` for
    /// the source map).
    pub fn is_symmetric(&self) -> bool {
        (0..4).all(|mu| (0..4).all(|nu| self.components[mu][nu] == self.components[nu][mu]))
    }

    /// [definition] **An observer's reading** `T(u, v) = Σ η u T η v` of two contravariant vectors
    /// (Lean `ReceiverStressEnergy.observerBilinear`); `T(u, u)` is the energy density `u` reads.
    pub fn observer_bilinear(&self, u: &Vector4, v: &Vector4) -> Rat {
        let mut total = Rat::zero();
        for (mu, (row, u_mu)) in self.components.iter().zip(u).enumerate() {
            for (nu, (entry, v_nu)) in row.iter().zip(v).enumerate() {
                total += sign(mu) * u_mu * entry * sign(nu) * v_nu;
            }
        }
        total
    }

    /// [definition] The spatial trace `T¹¹ + T²² + T³³` (Lean `spatialPressureTrace`).
    pub fn spatial_trace(&self) -> Rat {
        (1..4).fold(Rat::zero(), |sum, i| sum + &self.components[i][i])
    }

    /// [definition] The Minkowski trace `tr_η T = Σ_μ η_μμ T^{μμ}` (Lean `minkowskiTrace`).
    pub fn minkowski_trace(&self) -> Rat {
        (0..4).fold(Rat::zero(), |sum, mu| {
            sum + sign(mu) * &self.components[mu][mu]
        })
    }

    /// [proved-derived; implemented-exact] **The trace reversal** `T̄ = T − ½(tr_η T)η` (Lean
    /// `traceReversed`, `traceReversed_zero_zero`): its time component is `(T⁰⁰ + Σᵢ Tⁱⁱ)/2`. In four
    /// dimensions it is an involution, and the field equation `Ric − ½(tr_η Ric)η = κT` (`Λ = 0`) is
    /// `Ric = κT̄` (Lean `trace_reversal`); at `κ = 8πG` a dust source reads `R₀₀ = 4πGρ` (Lean
    /// `dust_newtonian_source`).
    pub fn trace_reversed(&self) -> Self {
        let half_trace = self.minkowski_trace() / Rat::from_integer(2.into());
        Self::new(std::array::from_fn(|mu| {
            std::array::from_fn(|nu| {
                let metric = if mu == nu { sign(mu) } else { Rat::zero() };
                &self.components[mu][nu] - &half_trace * metric
            })
        }))
    }

    /// The tensor scaled by `κ`.
    pub fn scaled(&self, factor: &Rat) -> Self {
        Self::new(std::array::from_fn(|mu| {
            std::array::from_fn(|nu| factor * &self.components[mu][nu])
        }))
    }
}

/// [definition] **A Lorentz transformation** `Λ` of the chart, `Λᵀ η Λ = η` (Lean
/// `StressEnergy.transport`, `lorentz_inverse`, `boostT`): it carries a contravariant vector to
/// `Λv`, a covector to `wΛ⁻¹`, the stress–energy to `ΛTΛᵀ` and a covariant gradient to
/// `Λ⁻ᵀDΛ⁻¹`, with `Λ⁻¹ = ηΛᵀη`; every contraction of the observer current is invariant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LorentzMap {
    matrix: Tensor4,
}

fn multiply4(a: &Tensor4, b: &Tensor4) -> Tensor4 {
    std::array::from_fn(|i| {
        std::array::from_fn(|j| (0..4).fold(Rat::zero(), |sum, k| sum + &a[i][k] * &b[k][j]))
    })
}

fn transpose4(a: &Tensor4) -> Tensor4 {
    std::array::from_fn(|i| std::array::from_fn(|j| a[j][i].clone()))
}

fn eta4() -> Tensor4 {
    std::array::from_fn(|i| std::array::from_fn(|j| if i == j { sign(i) } else { Rat::zero() }))
}

impl LorentzMap {
    /// A Lorentz transformation, refused unless `Λᵀ η Λ = η`.
    pub fn new(matrix: Tensor4) -> Result<Self, SpacetimeError> {
        if multiply4(&multiply4(&transpose4(&matrix), &eta4()), &matrix) != eta4() {
            return Err(SpacetimeError::NotLorentz);
        }
        Ok(Self { matrix })
    }

    /// [definition] **The Doppler boost along `x`** (Lean `boostT`, `boostT_lorentz`).
    pub fn boost_x(boost: &DopplerBoost) -> Self {
        let (g, s, z, one) = (boost.gamma(), boost.gamma_beta(), Rat::zero(), Rat::one());
        Self {
            matrix: [
                [g.clone(), s.clone(), z.clone(), z.clone()],
                [s, g, z.clone(), z.clone()],
                [z.clone(), z.clone(), one.clone(), z.clone()],
                [z.clone(), z.clone(), z, one],
            ],
        }
    }

    pub fn matrix(&self) -> &Tensor4 {
        &self.matrix
    }

    /// [proved-derived; implemented-exact] The inverse `ηΛᵀη` (Lean `lorentz_inverse`).
    pub fn inverse(&self) -> Self {
        Self {
            matrix: multiply4(&multiply4(&eta4(), &transpose4(&self.matrix)), &eta4()),
        }
    }

    /// `Λv`.
    pub fn vector(&self, vector: &Vector4) -> Vector4 {
        std::array::from_fn(|i| {
            (0..4).fold(Rat::zero(), |sum, k| sum + &self.matrix[i][k] * &vector[k])
        })
    }

    /// `ΛTΛᵀ`.
    pub fn tensor(&self, stress: &StressEnergy) -> StressEnergy {
        StressEnergy::new(multiply4(
            &multiply4(&self.matrix, stress.components()),
            &transpose4(&self.matrix),
        ))
    }

    /// `Λ⁻ᵀDΛ⁻¹` for a covariant two-index array.
    fn cotensor(&self, gradient: &Tensor4) -> Tensor4 {
        let inverse = self.inverse().matrix;
        multiply4(&multiply4(&transpose4(&inverse), gradient), &inverse)
    }
}

/// [proved-derived; implemented-exact] **The source map** (Lean `sourceMap`): `T⁰⁰ = ε`,
/// `T⁰ⁱ = Tⁱ⁰ = qⁱ`, `Tⁱʲ = −σᵢⱼ`. Symmetric (`sourceMap_symmetric`); without viscosity or heat flux
/// it is the perfect fluid `diag(ε, p, p, p)` (`sourceMap_perfect`); its spatial trace is
/// `3p − (2μ + 3λ) tr G` (`sourceMap_spatialTrace`).
pub fn source_map(state: &ConstitutedState) -> StressEnergy {
    let cauchy = state.cauchy();
    let heat = [
        state.heat_flux.x.clone(),
        state.heat_flux.y.clone(),
        state.heat_flux.z.clone(),
    ];
    let mut components = zero_tensor();
    components[0][0] = state.energy_density();
    for i in 0..3 {
        components[0][i + 1] = heat[i].clone();
        components[i + 1][0] = heat[i].clone();
        for j in 0..3 {
            components[i + 1][j + 1] = -cauchy.rows[i][j].clone();
        }
    }
    StressEnergy::new(components)
}

/// [definition] **A receiver's worldline at one event**: its covariant velocity `u_ν` and its
/// gradient `∂_μ u_ν` (Lean `ObserverBoundaryCurrent.observerCurrentDivergence`'s `u` and `dU`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverWorldline {
    covelocity: Vector4,
    gradient: Tensor4,
}

impl ReceiverWorldline {
    /// A receiver from its contravariant velocity `U^μ`, refused unless it is a future-directed unit
    /// timelike velocity, `⟨U, U⟩ = −1`, `U⁰ > 0`, and `gradient`, its `∂_μ u_ν`, preserves the unit
    /// norm, `U^ν ∂_μ u_ν = 0` for every `μ` (the gradient of a unit timelike field).
    pub fn new(velocity: Vector4, gradient: Tensor4) -> Result<Self, SpacetimeError> {
        let norm = (0..4).fold(Rat::zero(), |sum, mu| {
            sum + sign(mu) * &velocity[mu] * &velocity[mu]
        });
        if norm != -Rat::one() {
            return Err(SpacetimeError::NotUnitTimelike { norm });
        }
        if !velocity[0].is_positive() {
            return Err(SpacetimeError::PastDirected);
        }
        if let Some(row) = (0..4).find(|mu| {
            !(0..4)
                .fold(Rat::zero(), |sum, nu| {
                    sum + &velocity[nu] * &gradient[*mu][nu]
                })
                .is_zero()
        }) {
            return Err(SpacetimeError::GradientNotUnitPreserving { row });
        }
        let covelocity = std::array::from_fn(|mu| sign(mu) * &velocity[mu]);
        Ok(Self {
            covelocity,
            gradient,
        })
    }

    /// [definition] **The comoving receiver of an affine flow** at an event where the flow is at
    /// rest (Lean `restCovector`, `comovingGradient`): `u_ν = (−1, 0, 0, 0)` and `∂ᵢu_ⱼ = Gⱼᵢ`.
    /// Refused where the flow moves.
    pub fn comoving(flow: &AffineFlow, event: &RatVec3) -> Result<Self, SpacetimeError> {
        let velocity = flow.at(event);
        if !(velocity.x.is_zero() && velocity.y.is_zero() && velocity.z.is_zero()) {
            return Err(SpacetimeError::FlowNotAtRest {
                velocity: Box::new(velocity),
            });
        }
        let mut gradient = zero_tensor();
        for i in 0..3 {
            for j in 0..3 {
                gradient[i + 1][j + 1] = flow.gradient.rows[j][i].clone();
            }
        }
        Self::new(
            [Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()],
            gradient,
        )
    }

    /// The contravariant velocity `U^μ = η^{μν} u_ν`.
    pub fn velocity(&self) -> Vector4 {
        std::array::from_fn(|mu| sign(mu) * &self.covelocity[mu])
    }

    /// [proved-derived; implemented-exact] **The receiver carried by a Lorentz transformation**:
    /// velocity `ΛU`, gradient `Λ⁻ᵀDΛ⁻¹`, validated again.
    pub fn transported(&self, map: &LorentzMap) -> Result<Self, SpacetimeError> {
        Self::new(map.vector(&self.velocity()), map.cotensor(&self.gradient))
    }

    pub fn covelocity(&self) -> &Vector4 {
        &self.covelocity
    }

    pub fn gradient(&self) -> &Tensor4 {
        &self.gradient
    }

    /// Whether the receiver is rigid (Killing): `∂_μ u_ν + ∂_ν u_μ = 0`.
    pub fn is_killing(&self) -> bool {
        (0..4)
            .all(|mu| (0..4).all(|nu| (&self.gradient[mu][nu] + &self.gradient[nu][mu]).is_zero()))
    }
}

/// [definition] **The observer current and its divergence**: `j^μ = −T^{μν} u_ν`, and
/// `∂_μ j^μ = −f^ν u_ν − T^{μν} ∂_μ u_ν`, the force power plus the deformation term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObserverCurrent {
    pub current: Vector4,
    /// `−f^ν u_ν`.
    pub force_power: Rat,
    /// `−T^{μν} ∂_μ u_ν`, the observer's deformation term.
    pub deformation: Rat,
    /// `force_power + deformation`.
    pub divergence: Rat,
}

/// [proved-derived; implemented-exact] **The observer current of a receiver** (Lean
/// `ObserverBoundaryCurrent.observerCurrentDivergence_eq`,
/// `Spacetime/StressEnergy.comoving_observerDivergence`): conserved only up to the force the
/// receiver reads and its own deformation. A Killing receiver reads the force alone
/// (`observerCurrentDivergence_killing`, `rigid_comoving_reads_force`); for the comoving receiver
/// the deformation is `−p tr G + Φ`, the pressure work and the viscous heat.
pub fn observer_current(
    stress: &StressEnergy,
    receiver: &ReceiverWorldline,
    force: &Vector4,
) -> ObserverCurrent {
    let u = receiver.covelocity();
    let current = std::array::from_fn(|mu| {
        -(0..4).fold(Rat::zero(), |sum, nu| sum + stress.at(mu, nu) * &u[nu])
    });
    let force_power = -(0..4).fold(Rat::zero(), |sum, nu| sum + &force[nu] * &u[nu]);
    let mut contraction = Rat::zero();
    for mu in 0..4 {
        for nu in 0..4 {
            contraction += stress.at(mu, nu) * &receiver.gradient()[mu][nu];
        }
    }
    let deformation = -contraction;
    ObserverCurrent {
        current,
        divergence: &force_power + &deformation,
        force_power,
        deformation,
    }
}
