import ElementaryHolonics.Millennium.NavierStokesLinearFrameDynamics
import ElementaryHolonics.Millennium.NavierStokesLinearFrameEnergy
import ElementaryHolonics.Millennium.NavierStokesAnisotropicFrame

/-!
# The two-length frame is joined to the actual fluid source

The diagonal frame constructs every inverse and time derivative used by the general linear
source theorem. Its pressure metric and diffusion retain the separate radial and axial factors;
kinetic energy is integrated over the actual transported physical cell.
-/

noncomputable section
open ContDiff Set InnerProductSpace MeasureTheory
open scoped Topology Laplacian

namespace Soma.Holonics.Millennium.NavierStokesAnisotropicDynamics
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesAnisotropicFrame
open Soma.Holonics.Millennium.NavierStokesLinearFrameSpace
open Soma.Holonics.Millennium.NavierStokesLinearFrameDynamics
open Soma.Holonics.Millennium.NavierStokesLinearFrameEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate

def radialSecondJet (f : InitialVelocity) (y : Space) : Space :=
  fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.basisFun (Fin 3) ℝ 0)
      (EuclideanSpace.basisFun (Fin 3) ℝ 0) +
    fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.basisFun (Fin 3) ℝ 1)
      (EuclideanSpace.basisFun (Fin 3) ℝ 1)

def axialSecondJet (f : InitialVelocity) (y : Space) : Space :=
  fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.basisFun (Fin 3) ℝ 2)
    (EuclideanSpace.basisFun (Fin 3) ℝ 2)

/-- The exact two-component tensor diffusion, with its actual second derivatives. -/
theorem weightedLaplacian_inverseFrame (r z : ℝ) (f : InitialVelocity) (y : Space) :
    weightedLaplacian (inverseFrame r z) f y =
      r⁻¹ ^ 2 • radialSecondJet f y + z⁻¹ ^ 2 • axialSecondJet f y := by
  have he0 : inverseFrame r z (EuclideanSpace.basisFun (Fin 3) ℝ 0) =
      r⁻¹ • EuclideanSpace.basisFun (Fin 3) ℝ 0 := by
    ext i
    fin_cases i <;> simp [inverseFrame, diagonalFrame, EuclideanSpace.basisFun_apply]
  have he1 : inverseFrame r z (EuclideanSpace.basisFun (Fin 3) ℝ 1) =
      r⁻¹ • EuclideanSpace.basisFun (Fin 3) ℝ 1 := by
    ext i
    fin_cases i <;> simp [inverseFrame, diagonalFrame, EuclideanSpace.basisFun_apply]
  have he2 : inverseFrame r z (EuclideanSpace.basisFun (Fin 3) ℝ 2) =
      z⁻¹ • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
    ext i
    fin_cases i <;> simp [inverseFrame, diagonalFrame, EuclideanSpace.basisFun_apply]
  rw [weightedLaplacian_eq_fderiv]
  rw [Fin.sum_univ_three, he0, he1, he2]
  simp only [map_smul, ContinuousLinearMap.smul_apply,
    smul_smul, radialSecondJet, axialSecondJet]
  module

/-- An actual open fluid solution pays the anisotropic equation. There is no independently
assumed inverse jet or normalized PDE. -/
theorem OpenSmoothSolutionOn.anisotropic_momentum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField} {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (r z rate clock : ℝ → ℝ)
    (y : Space) (t : ℝ) (centreJet : Space) (rJet zJet rateJet : ℝ)
    (ht : clock t ∈ Ioo 0 T) (hc : HasDerivAt centre centreJet t)
    (hr : HasDerivAt r rJet t) (hz : HasDerivAt z zJet t)
    (hb : HasDerivAt rate rateJet t) (hclock : HasDerivAt clock (rate t) t)
    (hrne : r t ≠ 0) (hzne : z t ≠ 0) (hbne : rate t ≠ 0) :
    let A := fun τ ↦ diagonalFrame (r τ) (z τ)
    let B := fun τ ↦ inverseFrame (r τ) (z τ)
    let U := linearFrameVelocity centre A B rate clock velocity
    let P := linearFramePressure centre A rate clock pressure
    deriv (U y) t +
      fderiv ℝ (fun v ↦ U v t) y (U y t - B t (centreJet + diagonalFrame rJet zJet y)) +
      gridRate (r t) (z t) rJet zJet (U y t) - (rateJet / rate t) • U y t =
        (nu * rate t) •
          ((r t)⁻¹ ^ 2 • radialSecondJet (fun v ↦ U v t) y +
            (z t)⁻¹ ^ 2 • axialSecondJet (fun v ↦ U v t) y) -
          metricFrame (r t) (z t) (gradient (fun v ↦ P v t) y) +
          rate t ^ 2 • B t (force (centre t + A t y) (clock t)) := by
  dsimp only
  have h := Soma.Holonics.Millennium.NavierStokesLinearFrameDynamics.OpenSmoothSolutionOn.linearFrame_momentum
    solution centre (fun τ ↦ diagonalFrame (r τ) (z τ)) (fun τ ↦ inverseFrame (r τ) (z τ))
    rate clock y t centreJet (diagonalFrame rJet zJet) rateJet ht hc
    (diagonalFrame_hasDerivAt r z rJet zJet t hr hz)
    (inverseFrame_hasDerivAt r z rJet zJet t hr hz hrne hzne)
    hb hclock hbne (diagonalFrame_comp_inverseFrame (r t) (z t) hrne hzne)
  dsimp only at h
  rw [weightedLaplacian_inverseFrame] at h
  exact h

theorem anisotropic_kinetic_energy (r z b : ℝ) (centre : Space)
    (hr : r ≠ 0) (hz : z ≠ 0) (u : InitialVelocity) :
    (∫ y in transportedCell (diagonalFrame r z) centre,
      kineticMetric r z (velocityPullback b (diagonalFrame r z) (inverseFrame r z) centre u y)) =
      (b ^ 2 / |r ^ 2 * z|) * (∫ x in unitCube, ‖u x‖ ^ 2) := by
  have h := kinetic_energy_pullback (diagonalFrame r z) (inverseFrame r z) b centre
    (diagonalFrame_comp_inverseFrame r z hr hz) (inverseFrame_comp_diagonalFrame r z hr hz) u
  rw [diagonalFrame_det] at h
  simpa only [kineticDensity, velocityPullback, kineticMetric_eq_norm_sq] using h

/-- On the regular scalar chart the velocity is exactly the previous MFR1 construction. -/
theorem scalar_velocity_recovery (centre : ℝ → Space) (ell q clock : ℝ → ℝ)
    (velocity : VelocityField) (y : Space) (t : ℝ) (hell : ell t ≠ 0) :
    linearFrameVelocity centre (fun τ ↦ diagonalFrame (ell τ) (ell τ))
      (fun τ ↦ inverseFrame (ell τ) (ell τ)) (fun τ ↦ ell τ * q τ) clock velocity y t =
      NavierStokesDynamicRescaling.rescaledVelocity centre ell q clock velocity y t := by
  unfold linearFrameVelocity inverseFrame NavierStokesDynamicRescaling.rescaledVelocity
  dsimp only
  rw [diagonalFrame_scalar, diagonalFrame_scalar]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
  have hscale : (ell t * q t) * (ell t)⁻¹ = q t := by field_simp
  rw [hscale]

/-- The general-frame pressure uses b², so its scalar reduction retains an extra ell² which
the inverse pressure metric cancels in the PDE. -/
theorem scalar_pressure_recovery (centre : ℝ → Space) (ell q clock : ℝ → ℝ)
    (pressure : PressureField) (y : Space) (t : ℝ) :
    linearFramePressure centre (fun τ ↦ diagonalFrame (ell τ) (ell τ))
      (fun τ ↦ ell τ * q τ) clock pressure y t =
      ell t ^ 2 * NavierStokesDynamicRescaling.rescaledPressure centre ell q clock pressure y t := by
  unfold linearFramePressure NavierStokesDynamicRescaling.rescaledPressure
  dsimp only
  rw [diagonalFrame_scalar]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  ring

theorem OpenPeriodicSolutionOn.anisotropic_energy_hasDerivAt
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (r z rate clock : ℝ → ℝ) (centre : ℝ → Space) (t rJet zJet rateJet : ℝ)
    (hr : HasDerivAt r rJet t) (hz : HasDerivAt z zJet t) (hb : HasDerivAt rate rateJet t)
    (hrne : r t ≠ 0) (hzne : z t ≠ 0) (hbne : rate t ≠ 0)
    (hclock : HasDerivAt clock (rate t) t) (ht : clock t ∈ Ioo 0 T) :
    HasDerivAt (fun τ ↦ frameKineticEnergy (diagonalFrame (r τ) (z τ))
      (inverseFrame (r τ) (z τ)) (rate τ) (centre τ) (fun x ↦ velocity x (clock τ)))
      (-nu * rate t * coordinateH0Dissipation velocity (clock t)) t := by
  apply Soma.Holonics.Millennium.NavierStokesLinearFrameEnergy.OpenPeriodicSolutionOn.frame_energy_hasDerivAt
    solution (fun τ ↦ diagonalFrame (r τ) (z τ)) (fun τ ↦ inverseFrame (r τ) (z τ))
    rate clock centre t hclock ht
  filter_upwards [hr.continuousAt.eventually_ne hrne, hz.continuousAt.eventually_ne hzne,
    hb.continuousAt.eventually_ne hbne] with τ hrτ hzτ hbτ
  exact ⟨diagonalFrame_comp_inverseFrame (r τ) (z τ) hrτ hzτ,
    inverseFrame_comp_diagonalFrame (r τ) (z τ) hrτ hzτ, hbτ⟩

#print axioms weightedLaplacian_inverseFrame
#print axioms OpenSmoothSolutionOn.anisotropic_momentum
#print axioms anisotropic_kinetic_energy
#print axioms scalar_velocity_recovery
#print axioms scalar_pressure_recovery
#print axioms OpenPeriodicSolutionOn.anisotropic_energy_hasDerivAt
end Soma.Holonics.Millennium.NavierStokesAnisotropicDynamics
