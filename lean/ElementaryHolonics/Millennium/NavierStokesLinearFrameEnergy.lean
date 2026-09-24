import ElementaryHolonics.Millennium.NavierStokesRescaledEnergy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import ElementaryHolonics.Millennium.NavierStokesLinearFrameSpace

/-!
# The linear frame transports the physical kinetic-energy receiver

The integration population is the actual inverse image of the physical unit cell. The velocity
metric and the volume determinant are retained separately; an anisotropic frame does not carry
the Euclidean norm of the displayed velocity unchanged.
-/

noncomputable section
open ContDiff Set MeasureTheory Filter
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesLinearFrameEnergy
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesLinearFrameSpace
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate

def transportedCell (A : Space →L[ℝ] Space) (centre : Space) : Set Space :=
  (fun y ↦ centre + A y) ⁻¹' unitCube

def kineticDensity (A : Space →L[ℝ] Space) (U : InitialVelocity) (y : Space) : ℝ :=
  ‖A (U y)‖ ^ 2

theorem inverse_pair_det_ne_zero (A B : Space →L[ℝ] Space)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ Space) :
    LinearMap.det A.toLinearMap ≠ 0 := by
  let e := ContinuousLinearEquiv.equivOfInverse' A B hAB hBA
  exact e.toLinearEquiv.isUnit_det'.ne_zero

/-- The full affine chart changes Lebesgue measure by its actual determinant. -/
theorem map_affine_volume (A B : Space →L[ℝ] Space) (centre : Space)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ Space) :
    Measure.map (fun y ↦ centre + A y) volume =
      ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| • volume := by
  have hlinear := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Space)
    (inverse_pair_det_ne_zero A B hAB hBA)
  have hc : Measurable (fun y : Space ↦ centre + y) :=
    (Homeomorph.addLeft centre).continuous.measurable
  change Measure.map (fun y ↦ centre + A y) volume = _
  rw [show (fun y ↦ centre + A y) = (fun y ↦ centre + y) ∘ A by rfl,
    ← Measure.map_map hc A.continuous.measurable]
  change Measure.map (fun y ↦ centre + y) (Measure.map A.toLinearMap volume) = _
  rw [hlinear, Measure.map_smul, (measurePreserving_add_left volume centre).map_eq]

/-- Change variables on the actual transported cell, including the moving centre. -/
theorem integral_on_transportedCell (A B : Space →L[ℝ] Space) (centre : Space)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ Space) (f : Space → ℝ) :
    (∫ y in transportedCell A centre, f (centre + A y)) =
      |LinearMap.det A.toLinearMap|⁻¹ * (∫ x in unitCube, f x) := by
  let e := ContinuousLinearEquiv.equivOfInverse' A B hAB hBA
  let affine := e.toHomeomorph.trans (Homeomorph.addLeft centre)
  have h := affine.measurableEmbedding.setIntegral_map (μ := volume) f unitCube
  change (∫ x in unitCube, f x ∂Measure.map (fun y ↦ centre + A y) volume) =
    ∫ y in transportedCell A centre, f (centre + A y) at h
  rw [map_affine_volume A B centre hAB hBA, Measure.restrict_smul, integral_smul_measure] at h
  rw [ENNReal.toReal_ofReal (abs_nonneg ((LinearMap.det A.toLinearMap)⁻¹))] at h
  simpa only [smul_eq_mul, abs_inv] using h.symm

/-- The metric kinetic receiver returns exactly the physical energy with its volume factor. -/
theorem kinetic_energy_pullback (A B : Space →L[ℝ] Space) (b : ℝ) (centre : Space)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ Space) (u : InitialVelocity) :
    (∫ y in transportedCell A centre,
      kineticDensity A (fun z ↦ b • B (u (centre + A z))) y) =
      (b ^ 2 / |LinearMap.det A.toLinearMap|) * (∫ x in unitCube, ‖u x‖ ^ 2) := by
  have hab (v : Space) : A (B v) = v :=
    congrArg (fun L : Space →L[ℝ] Space ↦ L v) hAB
  have hdensity : kineticDensity A (fun z ↦ b • B (u (centre + A z))) =
      fun y ↦ b ^ 2 * ‖u (centre + A y)‖ ^ 2 := by
    funext y
    simp [kineticDensity, map_smul, hab, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [hdensity, integral_const_mul,
    integral_on_transportedCell A B centre hAB hBA (fun x ↦ ‖u x‖ ^ 2)]
  ring

theorem physical_energy_reconstruct (A B : Space →L[ℝ] Space) (b : ℝ) (centre : Space)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ Space) (hb : b ≠ 0) (u : InitialVelocity) :
    (∫ x in unitCube, ‖u x‖ ^ 2) =
      (|LinearMap.det A.toLinearMap| / b ^ 2) *
        (∫ y in transportedCell A centre,
          kineticDensity A (fun z ↦ b • B (u (centre + A z))) y) := by
  rw [kinetic_energy_pullback A B b centre hAB hBA]
  have hd := inverse_pair_det_ne_zero A B hAB hBA
  field_simp

def frameKineticEnergy (A B : Space →L[ℝ] Space) (b : ℝ) (centre : Space) (u : InitialVelocity) : ℝ :=
  (|LinearMap.det A.toLinearMap| / (2 * b ^ 2)) *
    (∫ y in transportedCell A centre, kineticDensity A (velocityPullback b A B centre u) y)

theorem frameKineticEnergy_eq (A B : Space →L[ℝ] Space) (b : ℝ) (centre : Space)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ Space)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ Space) (hb : b ≠ 0)
    (velocity : VelocityField) (t : ℝ) :
    frameKineticEnergy A B b centre (fun x ↦ velocity x t) = periodicKineticEnergy velocity t := by
  unfold frameKineticEnergy velocityPullback
  dsimp only
  rw [kinetic_energy_pullback A B b centre hAB hBA (fun x ↦ velocity x t)]
  unfold periodicKineticEnergy kineticEnergyDensity
  rw [integral_const_mul]
  have hd := inverse_pair_det_ne_zero A B hAB hBA
  field_simp

/-- The actual source energy law survives the moving integration cell. The neighborhood
inverse conditions ensure that the compared receiver is the same physical energy throughout. -/
theorem OpenPeriodicSolutionOn.frame_energy_hasDerivAt
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (A B : ℝ → Space →L[ℝ] Space) (rate clock : ℝ → ℝ) (centre : ℝ → Space) (t : ℝ)
    (hclock : HasDerivAt clock (rate t) t) (ht : clock t ∈ Ioo 0 T)
    (hregular : ∀ᶠ τ in 𝓝 t,
      (A τ).comp (B τ) = ContinuousLinearMap.id ℝ Space ∧
      (B τ).comp (A τ) = ContinuousLinearMap.id ℝ Space ∧ rate τ ≠ 0) :
    HasDerivAt (fun τ ↦ frameKineticEnergy (A τ) (B τ) (rate τ) (centre τ)
      (fun x ↦ velocity x (clock τ)))
      (-nu * rate t * coordinateH0Dissipation velocity (clock t)) t := by
  have heq : (fun τ ↦ frameKineticEnergy (A τ) (B τ) (rate τ) (centre τ)
      (fun x ↦ velocity x (clock τ))) =ᶠ[𝓝 t] fun τ ↦ periodicKineticEnergy velocity (clock τ) := by
    filter_upwards [hregular] with τ hτ
    exact frameKineticEnergy_eq (A τ) (B τ) (rate τ) (centre τ) hτ.1 hτ.2.1 hτ.2.2 velocity (clock τ)
  have h := (openPeriodicSolutionOn_hasDerivAt_periodicKineticEnergy_unforced solution ht).comp t hclock
  have h' := h.congr_of_eventuallyEq heq
  convert h' using 1 <;> first | rfl | ring

#print axioms map_affine_volume
#print axioms kinetic_energy_pullback
#print axioms physical_energy_reconstruct
#print axioms OpenPeriodicSolutionOn.frame_energy_hasDerivAt
end Soma.Holonics.Millennium.NavierStokesLinearFrameEnergy
