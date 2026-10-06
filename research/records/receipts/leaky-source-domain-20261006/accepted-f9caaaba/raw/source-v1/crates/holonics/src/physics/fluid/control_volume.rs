//! **The Euler/Navier–Stokes control volume** (battle test 3).
//!
//! [definition] A control volume is a unit cubical cell of the three-dimensional grid chart with
//! the grid's Euclidean metric declared ([`ControlVolume`]). Each oriented face carries a
//! **transported normal**, the Hodge reading of its orientation (`sgn(univ,i)·eᵢ` on a face missing
//! direction `i`, unit area; Lean `Physics/Fluid/ControlVolume.normal`), and its centroid. The
//! per-face returns of a fluid of density `ρ`, velocity `u` and stress `σ` are
//!
//! ```text
//! mass flux   ρ (u·N)          momentum flux   ρ u (u·N)          traction   σ N
//! ```
//!
//! ([`face_flux`]), and **storage plus outflow equals the source** cell by cell ([`Balance`]),
//! checked against the continuity equation's own storage rate `ρ̇V = −ρ (tr G) V`. The Newtonian
//! stress `σ = −pI + 2μ Def u + λ (tr G) I` ([`NewtonianMaterial`]) splits the traction power into
//! pressure work and the **viscous heat** `Φ = 2μ|Def u|² + λ (tr G)²`, the signed exact quantity
//! handed to the thermal instance through its port ([`ViscousHeat`]).
//!
//! | Lean `Physics/Fluid/ControlVolume` | Rust |
//! |---|---|
//! | `normal`, `centroid`, `closed_surface`, `first_moment` | [`transported_normal`], [`ControlVolume::faces`] |
//! | `FaceReturn`, `faceReturn` | [`FaceReturn`], [`face_flux`] |
//! | `massOutflow_eq`, `momentumOutflow_eq`, `tractionOutflow_eq_zero`, `tractionPower_eq` | [`ControlVolume::cell_return`] |
//! | `faceRead`, `outflow_join`, `outflow_join_ignores_sharedFace`, `joined_massOutflow_eq`, `Balances`, `balance_join` | [`outflow`], [`Balance`] |
//! | `strain`, `viscousStress`, `stress`, `dissipation`, `dissipation_eq`, `stress_power_split`, `stress_power_reversal`, `dissipation_nonneg`, `dissipation_even` | [`NewtonianMaterial`] |
//! | `viscousHeat`, `cell_heat_port`; `Thermal/ViscousPort.ViscousWork.ofFluid`, `cell_port_join` | [`ViscousHeat`], [`CellReturn::heat`], [`CellReturn::mechanical_deficit`] |
//! | `vorticity`, `circulation`, `pressurePart`, `pressure_vorticity_zero`, `pressure_circulation_zero`, `dormant_vortex`; `Objects/Pairing.coordinate_stokes`, `classPairing_representatives` | [`vorticity`], [`circulation`], [`pressure_part`] |
//! | `advection_split`, `lamb_no_work`, `curl`, `lamb_eq_cross`, `kinetic_difference` | [`lamb`], [`bernoulli`], [`curl`] |
//!
//! [definition] **The heat port.** [`ViscousHeat`] is the value this instance hands to the thermal
//! instance ([`crate::physics::thermal::ViscousWork::received`]): the dissipation times the cell's
//! volume, produced only by [`ControlVolume::cell_return`]. The mechanical side is the cell's
//! **mechanical deficit** `traction power − pressure work` ([`CellReturn::mechanical_deficit`]),
//! the power the stress delivers that is not reversible pressure work; `stress_power_split` makes
//! it equal to the viscous heat, and the thermal port's residual
//! ([`crate::physics::thermal::PortReturn::energy_residual`]) checks that the internal energy the
//! thermal cell gains over a tick is `h` times it (Lean `Thermal/ViscousPort.cell_port_join`).
//!
//! [open] The returns are read at one instant with uniform density and an affine velocity in the
//! cell. Owed in #62 for battle test 3 (#74 stays open on them): the **time advance** (the momentum
//! balance `ρ(∂ₜu + Gu) = div σ` stepped with its exact energy balance, so that the fluid's
//! kinetic-energy change is computed rather than read as the mechanical deficit), the **pressure
//! solve** (the projection of a provisional face flux onto the divergence-free fluxes, `∂ᵀ∂ p =
//! ∂ᵀu*/h` on the cells of a joined complex, with its Lean counterpart), and the discretization
//! defect of a non-affine field.

use num_traits::{One, Signed, Zero};

use crate::geometry::complex::CellComplex;
use crate::geometry::{RatMat3, RatVec3};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

use super::FluidError;
use super::cells::{GridCell, parity, unit};

/// [definition] **The transported normal** of a face of the three-dimensional chart:
/// `Σ_{i ∉ S} sgn(univ,i) eᵢ` with `sgn(univ,i) = (−1)^i` (Lean `normal`). On a face missing
/// direction `i` it is `(−1)^i eᵢ`, of unit area.
pub fn transported_normal(face: &GridCell) -> RatVec3 {
    (0..3)
        .filter(|i| !face.directions().contains(i))
        .fold(RatVec3::zero(), |sum, i| {
            sum.add(&unit(i).scale(&integer(parity(i))))
        })
}

/// [definition] **An oriented face of a control volume**: the face, its incidence `±1` in the
/// cell's boundary, its outward area normal (incidence times the transported normal) and its
/// centroid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrientedFace {
    pub face: GridCell,
    pub incidence: i64,
    pub outward: RatVec3,
    pub centroid: RatVec3,
}

/// [definition] **The per-face returns** (Lean `FaceReturn`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaceReturn {
    /// `ρ (u·N)`.
    pub mass: Rat,
    /// `ρ u (u·N)`.
    pub momentum: RatVec3,
    /// `σ N`.
    pub traction: RatVec3,
}

/// [definition] **The face returns** of density `ρ`, velocity `u` and stress `σ` on a face of area
/// normal `N` (Lean `faceReturn`).
pub fn face_flux(
    density: &Rat,
    velocity: &RatVec3,
    stress: &RatMat3,
    normal: &RatVec3,
) -> FaceReturn {
    let rate = density * velocity.dot(normal);
    FaceReturn {
        momentum: velocity.scale(&rate),
        mass: rate,
        traction: stress.apply(normal),
    }
}

/// [definition] An affine velocity field `u(x) = u₀ + G x`, `G_ab = ∂_b u_a` (Lean `affine`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineFlow {
    pub velocity: RatVec3,
    pub gradient: RatMat3,
}

impl AffineFlow {
    pub fn at(&self, point: &RatVec3) -> RatVec3 {
        self.velocity.add(&self.gradient.apply(point))
    }
}

/// `tr G`.
pub fn trace(matrix: &RatMat3) -> Rat {
    &matrix.rows[0][0] + &matrix.rows[1][1] + &matrix.rows[2][2]
}

/// The Frobenius pairing `A : B = Σ A_ab B_ab` (Lean `frob`).
pub fn frobenius(a: &RatMat3, b: &RatMat3) -> Rat {
    (0..3).fold(Rat::zero(), |sum, i| {
        (0..3).fold(sum, |sum, j| sum + &a.rows[i][j] * &b.rows[i][j])
    })
}

fn add_mat(a: &RatMat3, b: &RatMat3) -> RatMat3 {
    RatMat3::new(std::array::from_fn(|i| {
        std::array::from_fn(|j| &a.rows[i][j] + &b.rows[i][j])
    }))
}

fn sub_mat(a: &RatMat3, b: &RatMat3) -> RatMat3 {
    add_mat(a, &b.scale(&-Rat::one()))
}

/// [definition] **A Newtonian material**: shear viscosity `μ` and bulk coefficient `λ` (Lean
/// `viscousStress`, `stress`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NewtonianMaterial {
    pub shear: Rat,
    pub bulk: Rat,
}

impl NewtonianMaterial {
    pub fn new(shear: Rat, bulk: Rat) -> Self {
        Self { shear, bulk }
    }

    /// The rate of deformation `Def u = (G + Gᵀ)/2` (Lean `strain`).
    pub fn strain(gradient: &RatMat3) -> RatMat3 {
        add_mat(gradient, &gradient.transpose()).scale(&rat(1, 2))
    }

    /// `τ = 2μ Def u + λ (tr G) I` (Lean `viscousStress`).
    pub fn viscous_stress(&self, gradient: &RatMat3) -> RatMat3 {
        add_mat(
            &Self::strain(gradient).scale(&(integer(2) * &self.shear)),
            &RatMat3::identity().scale(&(&self.bulk * trace(gradient))),
        )
    }

    /// **The Newtonian stress** `σ = −pI + τ` (Lean `stress`).
    pub fn stress(&self, pressure: &Rat, gradient: &RatMat3) -> RatMat3 {
        add_mat(
            &RatMat3::identity().scale(&-pressure.clone()),
            &self.viscous_stress(gradient),
        )
    }

    /// [proved-derived; implemented-exact] **The dissipation** `Φ = τ : G = 2μ|Def u|² + λ (tr G)²`
    /// (Lean `dissipation`, `dissipation_eq`). Even under `G ↦ −G` (Lean `dissipation_even`) and
    /// nonnegative when [`Self::is_dissipative`] (Lean `dissipation_nonneg`).
    pub fn dissipation(&self, gradient: &RatMat3) -> Rat {
        frobenius(&self.viscous_stress(gradient), gradient)
    }

    /// The hypotheses of `dissipation_nonneg` in three dimensions: `μ ≥ 0` and `3λ + 2μ ≥ 0`. Each
    /// is load-bearing (Lean `negative_shear_viscosity`, `negative_bulk_viscosity`).
    pub fn is_dissipative(&self) -> bool {
        !self.shear.is_negative()
            && !(integer(3) * &self.bulk + integer(2) * &self.shear).is_negative()
    }
}

/// [definition] **The viscous heat handed to the thermal port** (Lean `viscousHeat`): the signed
/// exact rate `V Φ` that the cell's internal energy receives and its mechanical energy loses. Only
/// [`ControlVolume::cell_return`] produces it; its consumer is the thermal instance's port
/// ([`crate::physics::thermal::ViscousWork::received`], Lean `ViscousWork.ofFluid`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViscousHeat {
    rate: Rat,
}

impl ViscousHeat {
    /// `V Φ`.
    pub fn rate(&self) -> &Rat {
        &self.rate
    }
}

/// [definition] **A cell's returns summed over its oriented faces.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellReturn {
    /// `Σ_f ρ (u·N)`.
    pub mass_outflow: Rat,
    /// `Σ_f ρ u (u·N)`.
    pub momentum_outflow: RatVec3,
    /// `Σ_f σ N`, the net traction on the cell.
    pub traction_outflow: RatVec3,
    /// `Σ_f (σ N)·u`, the traction power delivered to the cell.
    pub traction_power: Rat,
    /// `−p (tr G) V`, the reversible pressure work.
    pub pressure_work: Rat,
    /// `Φ V`, the heat port value.
    pub heat: ViscousHeat,
}

impl CellReturn {
    /// [proved-derived; implemented-exact] **The mechanical deficit** `traction power − pressure
    /// work`: the power the stress delivers to the cell beyond reversible pressure work, which the
    /// mechanical energy loses to heat. It equals the viscous heat (Lean `stress_power_split`,
    /// `cell_heat_port`), computed here from the face tractions, independently of the dissipation
    /// formula.
    pub fn mechanical_deficit(&self) -> Rat {
        &self.traction_power - &self.pressure_work
    }
}

/// [definition] **A control volume**: a unit cube of the three-dimensional chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ControlVolume {
    cell: GridCell,
}

impl ControlVolume {
    /// A control volume on a top cell of the three-dimensional chart.
    pub fn new(cell: GridCell) -> Result<Self, FluidError> {
        if cell.degree() != 3 {
            return Err(FluidError::NotATopCell {
                what: "control volume (it must be a cube of the three-dimensional chart)",
            });
        }
        Ok(Self { cell })
    }

    pub fn cell(&self) -> &GridCell {
        &self.cell
    }

    /// The unit volume of a grid cube.
    pub fn volume(&self) -> Rat {
        Rat::one()
    }

    /// [proved-derived; implemented-exact] **The oriented faces**, with outward normals: they close,
    /// `Σ N = 0`, and their first moment is the volume times the identity, `Σ N ⊗ x = V I` (Lean
    /// `closed_surface`, `first_moment`).
    pub fn faces(&self) -> Vec<OrientedFace> {
        self.cell
            .faces()
            .into_iter()
            .map(|(face, incidence)| OrientedFace {
                outward: transported_normal(&face).scale(&integer(incidence)),
                centroid: face.centroid(),
                face,
                incidence,
            })
            .collect()
    }

    /// The per-face returns of an affine flow of uniform density under a Newtonian stress, each
    /// read at its face's centroid.
    pub fn face_returns(
        &self,
        density: &Rat,
        flow: &AffineFlow,
        pressure: &Rat,
        material: &NewtonianMaterial,
    ) -> Vec<(OrientedFace, FaceReturn)> {
        let stress = material.stress(pressure, &flow.gradient);
        self.faces()
            .into_iter()
            .map(|face| {
                let returned = face_flux(density, &flow.at(&face.centroid), &stress, &face.outward);
                (face, returned)
            })
            .collect()
    }

    /// [proved-derived; implemented-exact] **The cell's returns**: for an affine flow the
    /// face-centroid returns are exact (Lean `massOutflow_eq`: `ρ tr G`; `momentumOutflow_eq`:
    /// `ρ(G u_c + (tr G) u_c)`; `tractionOutflow_eq_zero`; `tractionPower_eq`: `σ : G`), and the
    /// traction power is the pressure work plus the viscous heat (`stress_power_split`,
    /// `cell_heat_port`).
    pub fn cell_return(
        &self,
        density: &Rat,
        flow: &AffineFlow,
        pressure: &Rat,
        material: &NewtonianMaterial,
    ) -> CellReturn {
        let mut mass_outflow = Rat::zero();
        let mut momentum_outflow = RatVec3::zero();
        let mut traction_outflow = RatVec3::zero();
        let mut traction_power = Rat::zero();
        for (face, returned) in self.face_returns(density, flow, pressure, material) {
            mass_outflow += &returned.mass;
            momentum_outflow = momentum_outflow.add(&returned.momentum);
            traction_power += returned.traction.dot(&flow.at(&face.centroid));
            traction_outflow = traction_outflow.add(&returned.traction);
        }
        let volume = self.volume();
        CellReturn {
            mass_outflow,
            momentum_outflow,
            traction_outflow,
            traction_power,
            pressure_work: -pressure.clone() * trace(&flow.gradient) * &volume,
            heat: ViscousHeat {
                rate: volume * material.dissipation(&flow.gradient),
            },
        }
    }
}

/// [definition] **A per-face return read against an oriented chain** (Lean `faceRead`):
/// `Σ_f x_f φ_f`. With `x` a cell's or a joined whole's boundary it is that region's outflow.
pub fn outflow(chain: &[Rat], values: &[Rat]) -> Result<Rat, FluidError> {
    if chain.len() != values.len() {
        return Err(FluidError::Shape {
            what: "per-face returns (one per face of the chain)",
            expected: chain.len(),
            found: values.len(),
        });
    }
    Ok(chain
        .iter()
        .zip(values)
        .fold(Rat::zero(), |sum, (x, v)| sum + x * v))
}

/// [definition] **A cell balance** (Lean `Balances`): storage rate, outflow and source, each read
/// on its own; the law is `storage + outflow = source`, and a balance of the joined cells is the
/// sum of the parts' (`balance_join`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Balance {
    pub storage: Rat,
    pub outflow: Rat,
    pub source: Rat,
}

impl Balance {
    /// `storage + outflow − source`, zero on a balance.
    pub fn residual(&self) -> Rat {
        &self.storage + &self.outflow - &self.source
    }
}

/// [definition] **The vorticity** of a velocity coholon on edges, `du♭ = ∂₂ᵀ u` on faces (Lean
/// `vorticity`).
pub fn vorticity(complex: &CellComplex, velocity: &[Rat]) -> Result<Vec<Rat>, FluidError> {
    let boundary = complex.boundary(2).ok_or(FluidError::Shape {
        what: "complex dimension for vorticity",
        expected: 2,
        found: complex.dimension(),
    })?;
    Ok(boundary.transpose()?.apply(velocity)?)
}

/// [definition] **The circulation** `⟨u, γ⟩` of a velocity coholon around a 1-chain (Lean
/// `circulation`); on a bounding cycle it is the vorticity flux (Stokes on the pairing, Lean
/// `Objects/Pairing.coordinate_stokes`), and on a cycle it reads only the velocity's class and the
/// cycle's class (Lean `Objects/Pairing.classPairing_representatives`). Kelvin's theorem, the
/// conservation of circulation along material loops in time, needs the time advance (#62).
pub fn circulation(velocity: &[Rat], cycle: &[Rat]) -> Result<Rat, FluidError> {
    outflow(cycle, velocity)
}

/// [definition] **The pressure part** `d p = ∂₁ᵀ p` of a vertex potential (Lean `pressurePart`): it
/// has no vorticity and no circulation around a cycle (Lean `pressure_vorticity_zero`,
/// `pressure_circulation_zero`).
pub fn pressure_part(complex: &CellComplex, pressure: &[Rat]) -> Result<Vec<Rat>, FluidError> {
    Ok(complex.incidence()?.apply(pressure)?)
}

/// Whether a velocity coholon is a pressure gradient `∂₁ᵀ p` for some vertex potential.
pub fn is_pressure_gradient(complex: &CellComplex, velocity: &[Rat]) -> Result<bool, FluidError> {
    let incidence: ExactRatMatrix = complex.incidence()?;
    Ok(incidence.preimage_fibre(velocity)?.is_some())
}

/// [definition] **The vorticity vector** of a gradient, `ω = curl u` (Lean `curl`).
pub fn curl(gradient: &RatMat3) -> RatVec3 {
    let g = &gradient.rows;
    RatVec3::new(
        &g[2][1] - &g[1][2],
        &g[0][2] - &g[2][0],
        &g[1][0] - &g[0][1],
    )
}

/// [definition] **The Lamb cross-current** `(G − Gᵀ) u = ω × u` (Lean `advection_split`,
/// `lamb_eq_cross`): it does no work, `u · (G − Gᵀ) u = 0` (Lean `lamb_no_work`).
pub fn lamb(gradient: &RatMat3, velocity: &RatVec3) -> RatVec3 {
    sub_mat(gradient, &gradient.transpose()).apply(velocity)
}

/// [definition] **The exact Bernoulli part** `Gᵀ u = ∇(|u|²/2)` of the advection `G u` (Lean
/// `advection_split`, `kinetic_difference`).
pub fn bernoulli(gradient: &RatMat3, velocity: &RatVec3) -> RatVec3 {
    gradient.transpose().apply(velocity)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::physics::fluid::cells::{component, reflect_across_face};

    fn coordinate(vector: &RatVec3, i: usize) -> Rat {
        component(vector, i).clone()
    }

    fn gradient() -> RatMat3 {
        RatMat3::new([
            [rat(1, 2), integer(2), rat(-1, 3)],
            [integer(-1), rat(3, 4), integer(1)],
            [rat(2, 5), integer(0), rat(-7, 4)],
        ])
    }

    fn flow() -> AffineFlow {
        AffineFlow {
            velocity: RatVec3::new(integer(1), rat(-2, 3), rat(1, 2)),
            gradient: gradient(),
        }
    }

    fn volume() -> ControlVolume {
        ControlVolume::new(
            GridCell::new(
                RatVec3::new(integer(2), rat(-1, 2), integer(3)),
                vec![0, 1, 2],
            )
            .unwrap(),
        )
        .unwrap()
    }

    /// Lean `closed_surface`, `first_moment`: the outward normals close and their first moment is
    /// the identity on the unit cube.
    #[test]
    fn the_transported_normals_close_with_the_identity_moment() {
        let faces = volume().faces();
        assert_eq!(faces.len(), 6);
        let sum = faces
            .iter()
            .fold(RatVec3::zero(), |sum, face| sum.add(&face.outward));
        assert_eq!(sum, RatVec3::zero());
        for a in 0..3 {
            for b in 0..3 {
                let moment = faces.iter().fold(Rat::zero(), |sum, face| {
                    sum + coordinate(&face.outward, a) * coordinate(&face.centroid, b)
                });
                assert_eq!(moment, if a == b { Rat::one() } else { Rat::zero() });
            }
        }
    }

    /// Lean `faceReturn`: the three returns of one face.
    #[test]
    fn a_face_returns_mass_momentum_and_traction() {
        let material = NewtonianMaterial::new(rat(1, 3), rat(1, 5));
        let stress = material.stress(&integer(2), &gradient());
        let normal = RatVec3::from_i64(0, -1, 0);
        let velocity = RatVec3::new(integer(3), integer(-2), integer(1));
        let returned = face_flux(&integer(2), &velocity, &stress, &normal);
        assert_eq!(returned.mass, integer(4));
        assert_eq!(returned.momentum, velocity.scale(&integer(4)));
        assert_eq!(returned.traction, stress.apply(&normal));
    }

    /// Lean `massOutflow_eq`, `momentumOutflow_eq`, `tractionOutflow_eq_zero`: the face-centroid
    /// returns of an affine flow are the exact divergences at the centre.
    #[test]
    fn the_face_returns_of_an_affine_flow_are_exact() {
        let rho = rat(3, 2);
        let material = NewtonianMaterial::new(rat(1, 3), rat(1, 5));
        let returned = volume().cell_return(&rho, &flow(), &integer(4), &material);
        assert_eq!(returned.mass_outflow, &rho * trace(&gradient()));
        let centre = flow().at(&volume().cell().centroid());
        let expected = gradient()
            .apply(&centre)
            .add(&centre.scale(&trace(&gradient())))
            .scale(&rho);
        assert_eq!(returned.momentum_outflow, expected);
        assert_eq!(returned.traction_outflow, RatVec3::zero());
    }

    /// Lean `tractionPower_eq`, `stress_power_split`, `cell_heat_port`: the traction power is
    /// `σ : G`, split exactly into pressure work and the viscous heat handed to the thermal port.
    #[test]
    fn viscous_work_enters_heat() {
        let material = NewtonianMaterial::new(rat(1, 3), rat(1, 5));
        let pressure = integer(4);
        let returned = volume().cell_return(&integer(1), &flow(), &pressure, &material);
        let stress = material.stress(&pressure, &gradient());
        assert_eq!(returned.traction_power, frobenius(&stress, &gradient()));
        assert_eq!(returned.mechanical_deficit(), *returned.heat.rate());
        assert!(returned.heat.rate() > &Rat::zero());
    }

    /// Lean `dissipation_eq`, `dissipation_even`, `dissipation_nonneg`: the dissipation formula,
    /// its evenness, and its sign for a dissipative material.
    #[test]
    fn dissipation_is_even_and_nonnegative_for_a_dissipative_material() {
        let material = NewtonianMaterial::new(rat(2, 3), rat(-1, 3));
        assert!(material.is_dissipative());
        let g = gradient();
        let strain = NewtonianMaterial::strain(&g);
        assert_eq!(
            material.dissipation(&g),
            integer(2) * &material.shear * frobenius(&strain, &strain)
                + &material.bulk * trace(&g) * trace(&g)
        );
        assert_eq!(
            material.dissipation(&g.scale(&-Rat::one())),
            material.dissipation(&g)
        );
        assert!(material.dissipation(&g) >= Rat::zero());
        assert!(material.dissipation(&RatMat3::identity()) >= Rat::zero());
    }

    /// Lean `negative_shear_viscosity`: `μ = −1`, `λ = 1` dissipates `−1` in a shear.
    #[test]
    fn a_negative_shear_viscosity_produces_negative_heat() {
        let material = NewtonianMaterial::new(integer(-1), integer(1));
        assert!(!material.is_dissipative());
        let shear = RatMat3::from_i64([[0, 1, 0], [0, 0, 0], [0, 0, 0]]);
        assert_eq!(material.dissipation(&shear), integer(-1));
    }

    /// Lean `negative_bulk_viscosity`: `μ = 1`, `λ = −1` dissipates `−3` in a dilation.
    #[test]
    fn a_negative_bulk_response_produces_negative_heat() {
        let material = NewtonianMaterial::new(integer(1), integer(-1));
        assert!(!material.is_dissipative());
        assert_eq!(material.dissipation(&RatMat3::identity()), integer(-3));
    }

    /// Lean `pressureWork_not_heat`, `stress_power_reversal`: pressure work changes sign with the motion.
    #[test]
    fn pressure_work_is_reversible_not_heat() {
        let material = NewtonianMaterial::new(Rat::zero(), Rat::zero());
        let compress = AffineFlow {
            velocity: RatVec3::zero(),
            gradient: RatMat3::identity().scale(&-Rat::one()),
        };
        let expand = AffineFlow {
            velocity: RatVec3::zero(),
            gradient: RatMat3::identity(),
        };
        let one = integer(1);
        let a = volume().cell_return(&one, &compress, &one, &material);
        let b = volume().cell_return(&one, &expand, &one, &material);
        assert_eq!(a.pressure_work, integer(3));
        assert_eq!(b.pressure_work, integer(-3));
        assert!(a.heat.rate().is_zero() && b.heat.rate().is_zero());
    }

    /// Lean `outflow_join`, `outflow_join_ignores_sharedFace`, `joined_massOutflow_eq`,
    /// `balance_join`: on
    /// the joined cubes the whole's outflow is the sum of the two cells' and does not read the
    /// shared face; it is the joined box's exact divergence integral `2ρ tr G`, since the
    /// face-centroid read is exact for an affine velocity; and each cell, and the whole, balances
    /// against the continuity equation's own storage rate `ρ̇V = −ρ (tr G) V`.
    #[test]
    fn the_joined_outflow_is_the_sum_and_ignores_the_shared_face() {
        let reflection = reflect_across_face(3, 0, true).unwrap();
        let holarchy = reflection.join().unwrap();
        let glued = reflection.glued.complex();
        let whole = glued
            .boundary(3)
            .unwrap()
            .apply(&holarchy.whole_interior().unwrap())
            .unwrap();
        let cube_chain = glued
            .boundary(3)
            .unwrap()
            .apply(&[Rat::one(), Rat::zero()])
            .unwrap();
        let neighbour_chain = glued
            .boundary(3)
            .unwrap()
            .apply(&[Rat::zero(), Rat::one()])
            .unwrap();
        let faces = reflection.glued.cells(2);
        let rho = rat(3, 2);
        let mass: Vec<Rat> = faces
            .iter()
            .map(|face| &rho * flow().at(&face.centroid()).dot(&transported_normal(face)))
            .collect();
        let total = outflow(&whole, &mass).unwrap();
        let left = outflow(&cube_chain, &mass).unwrap();
        let right = outflow(&neighbour_chain, &mass).unwrap();
        assert_eq!(total, &left + &right);
        let mut changed = mass.clone();
        changed[reflection.shared_face] += integer(17);
        assert_eq!(outflow(&whole, &changed).unwrap(), total);
        assert_ne!(outflow(&cube_chain, &changed).unwrap(), left);
        let divergence = &rho * trace(&gradient());
        assert_eq!(total, integer(2) * &divergence);
        assert_eq!(left, divergence);
        assert_eq!(right, divergence);
        // Uniform density under an affine velocity: continuity gives `ρ̇ = −ρ tr G` pointwise.
        let storage_rate = -divergence.clone();
        let cell_balance = |outflow: &Rat| Balance {
            storage: storage_rate.clone(),
            outflow: outflow.clone(),
            source: Rat::zero(),
        };
        let (bl, br) = (cell_balance(&left), cell_balance(&right));
        assert!(bl.residual().is_zero() && br.residual().is_zero());
        let joined = Balance {
            storage: integer(2) * &storage_rate,
            outflow: total,
            source: Rat::zero(),
        };
        assert!(joined.residual().is_zero());
        assert_eq!(joined.storage, &bl.storage + &br.storage);
        // A wrong storage rate does not balance.
        assert!(!cell_balance(&(&left + integer(1))).residual().is_zero());
    }

    /// Lean `Objects/Pairing.coordinate_stokes`, `pressure_vorticity_zero`,
    /// `pressure_circulation_zero`: on the joined squares the circulation around a face boundary is
    /// its vorticity, and a pressure part is silent.
    #[test]
    fn velocity_is_a_coholon_whose_vorticity_and_circulation_are_pairings() {
        let reflection = reflect_across_face(2, 0, true).unwrap();
        let complex = reflection.glued.complex();
        let edges = complex.cells(1);
        let u: Vec<Rat> = (0..edges as i64).map(|e| rat(2 * e - 3, e + 2)).collect();
        let omega = vorticity(complex, &u).unwrap();
        let sigma = vec![integer(1), integer(1)];
        let boundary = complex.boundary(2).unwrap().apply(&sigma).unwrap();
        assert_eq!(
            circulation(&u, &boundary).unwrap(),
            outflow(&omega, &sigma).unwrap()
        );
        let p: Vec<Rat> = (0..complex.cells(0) as i64)
            .map(|v| rat(v * v, 3))
            .collect();
        let dp = pressure_part(complex, &p).unwrap();
        assert!(vorticity(complex, &dp).unwrap().iter().all(Rat::is_zero));
        assert!(circulation(&dp, &boundary).unwrap().is_zero());
        assert!(is_pressure_gradient(complex, &dp).unwrap());
    }

    /// Lean `dormant_vortex`: on the square with one filled and one hollow triangle, the velocity
    /// reading `e₃` has no vorticity, circulates `1` around the hole, and is no pressure gradient.
    #[test]
    fn a_dormant_vortex_circulates_without_vorticity() {
        let rows = |r: &[&[i64]]| {
            ExactRatMatrix::new(
                r.iter()
                    .map(|row| row.iter().map(|v| integer(*v)).collect())
                    .collect(),
            )
            .unwrap()
        };
        let complex = CellComplex::new(
            vec![4, 5, 1],
            vec![
                rows(&[
                    &[-1, 0, 0, 1, -1],
                    &[1, -1, 0, 0, 0],
                    &[0, 1, -1, 0, 1],
                    &[0, 0, 1, -1, 0],
                ]),
                rows(&[&[1], &[1], &[0], &[0], &[-1]]),
            ],
        )
        .unwrap();
        let u = vec![
            Rat::zero(),
            Rat::zero(),
            Rat::zero(),
            Rat::one(),
            Rat::zero(),
        ];
        let hollow = vec![Rat::zero(), Rat::zero(), Rat::one(), Rat::one(), Rat::one()];
        assert!(vorticity(&complex, &u).unwrap().iter().all(Rat::is_zero));
        assert_eq!(circulation(&u, &hollow).unwrap(), Rat::one());
        assert!(!is_pressure_gradient(&complex, &u).unwrap());
    }

    /// Lean `advection_split`, `lamb_eq_cross`, `lamb_no_work`, `kinetic_difference`: the advection
    /// splits into the exact Bernoulli part and the Lamb cross-current `ω × u`, which does no work,
    /// and the Bernoulli part is the exact kinetic-energy difference.
    #[test]
    fn the_lamb_term_is_the_cross_current() {
        let g = gradient();
        let u = RatVec3::new(integer(2), rat(-1, 3), rat(5, 4));
        assert_eq!(g.apply(&u), bernoulli(&g, &u).add(&lamb(&g, &u)));
        assert_eq!(lamb(&g, &u), curl(&g).cross(&u));
        assert!(u.dot(&lamb(&g, &u)).is_zero());
        let flow = AffineFlow {
            velocity: u.clone(),
            gradient: g.clone(),
        };
        let x = RatVec3::new(rat(1, 2), integer(-1), integer(3));
        let h = RatVec3::new(rat(-2, 7), rat(1, 3), integer(1));
        let half = rat(1, 2);
        let lhs = &half * flow.at(&x.add(&h)).norm_squared() - &half * flow.at(&x).norm_squared();
        let rhs = bernoulli(&g, &flow.at(&x)).dot(&h) + &half * g.apply(&h).norm_squared();
        assert_eq!(lhs, rhs);
    }
}
