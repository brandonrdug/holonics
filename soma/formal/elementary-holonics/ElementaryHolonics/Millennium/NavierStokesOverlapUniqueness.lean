import ElementaryHolonics.Millennium.NavierStokesUniformRestart
import ElementaryHolonics.Millennium.NavierStokesFiniteTimeEnstrophy
import ElementaryHolonics.Millennium.NavierStokesTorusVorticity
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Uniqueness on overlapping open periodic Navier--Stokes lifespans

This file develops the analytic owner required by `OpenPeriodicOverlapUniqueness`.  The difference
of two solutions is read by its periodic `L²` kinetic energy.  Periodic transport and pressure work
cancel, nonnegative viscosity has the dissipative sign, and the remaining linearized convection
term is controlled by a compact spatial-Jacobian bound.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesOverlapUniqueness

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesUniformRestart
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-! ## The difference carrier and its periodic cancellations -/

/-- The velocity difference, retained as a time-dependent spatial field. -/
def velocityDifference (velocity₁ velocity₂ : VelocityField) : VelocityField :=
  fun x t => velocity₁ x t - velocity₂ x t

/-- The pressure difference.  Only its gradient is observable below. -/
def pressureDifference (pressure₁ pressure₂ : PressureField) : PressureField :=
  fun x t => pressure₁ x t - pressure₂ x t

/-- Difference preserves every unit period. -/
theorem velocityDifference_isOnePeriodic
    {velocity₁ velocity₂ : VelocityField} {t : ℝ}
    (h₁ : IsOnePeriodic (fun x => velocity₁ x t))
    (h₂ : IsOnePeriodic (fun x => velocity₂ x t)) :
    IsOnePeriodic (fun x => velocityDifference velocity₁ velocity₂ x t) := by
  intro x i
  simp only [velocityDifference]
  have hv₁ : velocity₁ (x + EuclideanSpace.single i 1) t = velocity₁ x t := by
    simpa using h₁ x i
  have hv₂ : velocity₂ (x + EuclideanSpace.single i 1) t = velocity₂ x t := by
    simpa using h₂ x i
  rw [hv₁, hv₂]

/-- Pressure difference preserves every unit period. -/
theorem pressureDifference_isOnePeriodic
    {pressure₁ pressure₂ : PressureField} {t : ℝ}
    (h₁ : IsOnePeriodic (fun x => pressure₁ x t))
    (h₂ : IsOnePeriodic (fun x => pressure₂ x t)) :
    IsOnePeriodic (fun x => pressureDifference pressure₁ pressure₂ x t) := by
  intro x i
  simp only [pressureDifference]
  have hp₁ : pressure₁ (x + EuclideanSpace.single i 1) t = pressure₁ x t := by
    simpa using h₁ x i
  have hp₂ : pressure₂ (x + EuclideanSpace.single i 1) t = pressure₂ x t := by
    simpa using h₂ x i
  rw [hp₁, hp₂]

/-- The trace divergence is additive across a velocity difference. -/
theorem divergence_velocityDifference
    (u₁ u₂ : InitialVelocity) (x : Space)
    (h₁ : DifferentiableAt ℝ u₁ x) (h₂ : DifferentiableAt ℝ u₂ x) :
    divergence (fun y => u₁ y - u₂ y) x = divergence u₁ x - divergence u₂ x := by
  unfold divergence
  have hfd : fderiv ℝ (fun y => u₁ y - u₂ y) x =
      fderiv ℝ u₁ x - fderiv ℝ u₂ x := by
    simpa only [Pi.sub_apply] using fderiv_sub h₁ h₂
  rw [hfd]
  simp only [ContinuousLinearMap.coe_sub, map_sub]

/-- The quadratic-density gradient may be read along an arbitrary transport direction. -/
theorem inner_gradient_kineticEnergyDensity_along
    (w : InitialVelocity) (x direction : Space) (hw : DifferentiableAt ℝ w x) :
    inner ℝ (gradient (kineticEnergyDensity w) x) direction =
      inner ℝ (fderiv ℝ w x direction) (w x) := by
  have hnorm : DifferentiableAt ℝ (fun y => ‖w y‖ ^ 2) x := hw.norm_sq ℝ
  have henergy : DifferentiableAt ℝ (kineticEnergyDensity w) x := by
    exact hnorm.const_mul (1 / 2 : ℝ)
  rw [inner_gradient_left henergy]
  unfold kineticEnergyDensity
  rw [fderiv_const_mul hnorm (1 / 2 : ℝ)]
  rw [(hw.hasFDerivAt.norm_sq).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [innerSL_apply_apply]
  rw [real_inner_comm]
  ring

/-- A periodic incompressible current transports the quadratic density of a second periodic field
with zero net work. -/
theorem integral_mixedTransportWork_unitCube_eq_zero
    (u w : InitialVelocity) (hu : ContDiff ℝ 1 u) (hw : ContDiff ℝ 1 w)
    (huPeriodic : IsOnePeriodic u) (hwPeriodic : IsOnePeriodic w)
    (huIncompressible : ∀ x, divergence u x = 0) :
    ∫ x in unitCube, inner ℝ (fderiv ℝ w x (u x)) (w x) = 0 := by
  have henergySmooth : ContDiff ℝ 1 (kineticEnergyDensity w) := by
    unfold kineticEnergyDensity
    exact contDiff_const.mul (hw.norm_sq ℝ)
  have henergyPeriodic : IsOnePeriodic (kineticEnergyDensity w) := by
    intro x i
    unfold kineticEnergyDensity
    rw [hwPeriodic x i]
  have hfluxSmooth : ContDiff ℝ 1
      (fun x => kineticEnergyDensity w x • u x) := henergySmooth.smul hu
  have hfluxPeriodic : IsOnePeriodic
      (fun x => kineticEnergyDensity w x • u x) :=
    pressureFlux_isOnePeriodic u (kineticEnergyDensity w) huPeriodic henergyPeriodic
  have hfluxIntegral := integral_divergence_unitCube_eq_zero_of_onePeriodic
    (fun x => kineticEnergyDensity w x • u x) hfluxPeriodic hfluxSmooth
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact measurableSet_Icc.preimage
      (EuclideanSpace.equiv (Fin 3) ℝ).continuous.measurable
  calc
    ∫ x in unitCube, inner ℝ (fderiv ℝ w x (u x)) (w x) =
        ∫ x in unitCube, divergence (fun y => kineticEnergyDensity w y • u y) x := by
      apply setIntegral_congr_fun hcubeMeasurable
      intro x _hx
      rw [divergence_pressureFlux u (kineticEnergyDensity w) x
        (hu.differentiable (by norm_num) x)
        (henergySmooth.differentiable (by norm_num) x),
        huIncompressible x, mul_zero, add_zero,
        inner_gradient_kineticEnergyDensity_along w x (u x)
          (hw.differentiable (by norm_num) x)]
    _ = 0 := hfluxIntegral

/-! ## Smooth spatial sections of an open solution -/

/-- Every admitted time, including the initial face, has a globally smooth spatial velocity
section.  This uses only spatial directions and therefore does not require the time face to be an
ambient neighbourhood. -/
theorem OpenPeriodicSolutionOn.velocitySpatialSmooth
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ openTimeSlab T) :
    ContDiff ℝ ∞ (fun x => velocity x t) := by
  rw [← contDiffOn_univ]
  exact solution.velocitySmooth.comp
    (contDiffOn_id.prodMk contDiffOn_const) (by
      intro x _hx
      exact ⟨Set.mem_univ x, ht⟩)

/-- The same spatial-section fact for pressure. -/
theorem OpenPeriodicSolutionOn.pressureSpatialSmooth
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ openTimeSlab T) :
    ContDiff ℝ ∞ (fun x => pressure x t) := by
  rw [← contDiffOn_univ]
  exact solution.pressureSmooth.comp
    (contDiffOn_id.prodMk contDiffOn_const) (by
      intro x _hx
      exact ⟨Set.mem_univ x, ht⟩)

/-! ## The linearized difference equation on a compact interior slab -/

/-- The Laplacian commutes with subtraction at every point where both fields are `C²`. -/
theorem laplacian_sub_at
    (u₁ u₂ : InitialVelocity) (x : Space)
    (h₁ : ContDiffAt ℝ 2 u₁ x) (h₂ : ContDiffAt ℝ 2 u₂ x) :
    Δ (fun y => u₁ y - u₂ y) x = Δ u₁ x - Δ u₂ x := by
  have hneg : Δ (fun y => -u₂ y) x = -Δ u₂ x := by
    have h := laplacian_smul (-1 : ℝ) h₂
    simpa only [Pi.smul_apply, neg_one_smul] using h
  have hadd := h₁.laplacian_add h₂.neg
  simpa only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, hneg] using hadd

/-- The joint Eulerian time jet commutes with subtraction at an interior event. -/
theorem eulerianTimeJet_velocityDifference
    {T : ℝ} {velocity₁ velocity₂ : VelocityField}
    (h₁ : ContDiffOn ℝ ∞ (Function.uncurry velocity₁) (spaceTimeSlab T))
    (h₂ : ContDiffOn ℝ ∞ (Function.uncurry velocity₂) (spaceTimeSlab T))
    (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t =
      eulerianTimeJet velocity₁ x t - eulerianTimeJet velocity₂ x t := by
  have hd₁ : DifferentiableAt ℝ (Function.uncurry velocity₁) (x, t) :=
    (contDiffAt_of_contDiffOn_spaceTimeSlab velocity₁ h₁ x ht0 htT).differentiableAt
      (by simp)
  have hd₂ : DifferentiableAt ℝ (Function.uncurry velocity₂) (x, t) :=
    (contDiffAt_of_contDiffOn_spaceTimeSlab velocity₂ h₂ x ht0 htT).differentiableAt
      (by simp)
  unfold eulerianTimeJet velocityDifference
  have hfd := fderiv_sub hd₁ hd₂
  have happly := congrArg
    (fun L : (Space × ℝ) →L[ℝ] Space => L (0, 1)) hfd
  simpa only [Function.uncurry_apply_pair, ContinuousLinearMap.sub_apply] using happly

/-- The quadratic convection difference has one transported-difference branch and one
Jacobian-times-difference branch. -/
theorem advection_sub_eq_linearized
    (u₁ u₂ : InitialVelocity) (x : Space)
    (h₁ : DifferentiableAt ℝ u₁ x) (h₂ : DifferentiableAt ℝ u₂ x) :
    fderiv ℝ u₁ x (u₁ x) - fderiv ℝ u₂ x (u₂ x) =
      fderiv ℝ (fun y => u₁ y - u₂ y) x (u₁ x) +
        fderiv ℝ u₂ x (u₁ x - u₂ x) := by
  have hfd : fderiv ℝ (fun y => u₁ y - u₂ y) x =
      fderiv ℝ u₁ x - fderiv ℝ u₂ x := by
    simpa only [Pi.sub_apply] using fderiv_sub h₁ h₂
  rw [hfd, ContinuousLinearMap.sub_apply, map_sub]
  abel

/-- The pointwise linearized momentum equation for the difference of two finite periodic
solutions with the same initial data and force. -/
theorem periodicSolutionOn_pointwiseDifferenceMomentum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t +
        fderiv ℝ (fun y => velocityDifference velocity₁ velocity₂ y t) x
          (velocity₁ x t) +
        fderiv ℝ (fun y => velocity₂ y t) x
          (velocityDifference velocity₁ velocity₂ x t) =
      nu • Δ (fun y => velocityDifference velocity₁ velocity₂ y t) x -
        gradient (fun y => pressure₁ y t) x +
        gradient (fun y => pressure₂ y t) x := by
  let u₁ : InitialVelocity := fun y => velocity₁ y t
  let u₂ : InitialVelocity := fun y => velocity₂ y t
  have hu₁ : ContDiff ℝ ∞ u₁ :=
    smoothSolutionOn_velocitySpatialSmooth solution₁.toSmoothSolutionOn ht0 htT
  have hu₂ : ContDiff ℝ ∞ u₂ :=
    smoothSolutionOn_velocitySpatialSmooth solution₂.toSmoothSolutionOn ht0 htT
  have hjet₁ := smoothSolutionOn_eulerianTimeJet_eq_derivWithin
    solution₁.toSmoothSolutionOn x ht0 htT
  have hjet₂ := smoothSolutionOn_eulerianTimeJet_eq_derivWithin
    solution₂.toSmoothSolutionOn x ht0 htT
  have hm₁ := solution₁.momentum x t ⟨ht0.le, htT.le⟩
  have hm₂ := solution₂.momentum x t ⟨ht0.le, htT.le⟩
  rw [← hjet₁] at hm₁
  rw [← hjet₂] at hm₂
  have hjet := eulerianTimeJet_velocityDifference
    solution₁.velocitySmooth solution₂.velocitySmooth x ht0 htT
  have hadv := advection_sub_eq_linearized u₁ u₂ x
    (hu₁.differentiable (by simp) x) (hu₂.differentiable (by simp) x)
  have hlap := laplacian_sub_at u₁ u₂ x
    (hu₁.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    (hu₂.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  change _ = _ at hadv hlap
  rw [hjet]
  change (eulerianTimeJet velocity₁ x t - eulerianTimeJet velocity₂ x t) +
      fderiv ℝ (fun y => u₁ y - u₂ y) x (u₁ x) +
        fderiv ℝ u₂ x (u₁ x - u₂ x) =
    nu • Δ (fun y => u₁ y - u₂ y) x -
      gradient (fun y => pressure₁ y t) x + gradient (fun y => pressure₂ y t) x
  rw [add_assoc, ← hadv, hlap, smul_sub]
  calc
    (eulerianTimeJet velocity₁ x t - eulerianTimeJet velocity₂ x t) +
        ((fderiv ℝ u₁ x) (u₁ x) - (fderiv ℝ u₂ x) (u₂ x)) =
      (eulerianTimeJet velocity₁ x t + (fderiv ℝ u₁ x) (u₁ x)) -
        (eulerianTimeJet velocity₂ x t + (fderiv ℝ u₂ x) (u₂ x)) := by
          abel
    _ = (nu • Δ u₁ x - gradient (fun y => pressure₁ y t) x + force x t) -
        (nu • Δ u₂ x - gradient (fun y => pressure₂ y t) x + force x t) := by
          exact congrArg₂ (fun a b : Space => a - b) hm₁ hm₂
    _ = nu • Δ u₁ x - nu • Δ u₂ x -
        gradient (fun y => pressure₁ y t) x +
          gradient (fun y => pressure₂ y t) x := by
          abel

/-! ## Exact `L²` receiver of the difference equation -/

/-- The complete component-gradient population of the velocity difference. -/
def periodicVelocityDifferenceDissipation
    (velocity₁ velocity₂ : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube, ∑ i : Fin 3,
    ‖gradient (fun y => velocityDifference velocity₁ velocity₂ y t i) x‖ ^ 2

/-- The sole noncancelling linearized-convection face in the difference-energy equation. -/
def periodicDifferenceJacobianWork
    (background velocity₁ velocity₂ : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube,
    inner ℝ
      (fderiv ℝ (fun y => background y t) x
        (velocityDifference velocity₁ velocity₂ x t))
      (velocityDifference velocity₁ velocity₂ x t)

/-- The exact integrated difference equation: transport and both pressure branches cancel, while
diffusion and the background-Jacobian interaction remain separately visible. -/
theorem periodicSolutionOn_integral_differenceTimeWork_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ∫ x in unitCube,
        inner ℝ (eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t)
          (velocityDifference velocity₁ velocity₂ x t) =
      -nu * periodicVelocityDifferenceDissipation velocity₁ velocity₂ t -
        periodicDifferenceJacobianWork velocity₂ velocity₁ velocity₂ t := by
  let u₁ : InitialVelocity := fun x => velocity₁ x t
  let u₂ : InitialVelocity := fun x => velocity₂ x t
  let w : InitialVelocity := fun x => velocityDifference velocity₁ velocity₂ x t
  let p₁ : Space → ℝ := fun x => pressure₁ x t
  let p₂ : Space → ℝ := fun x => pressure₂ x t
  have hu₁ : ContDiff ℝ ∞ u₁ :=
    smoothSolutionOn_velocitySpatialSmooth solution₁.toSmoothSolutionOn ht0 htT
  have hu₂ : ContDiff ℝ ∞ u₂ :=
    smoothSolutionOn_velocitySpatialSmooth solution₂.toSmoothSolutionOn ht0 htT
  have hw : ContDiff ℝ ∞ w := by
    exact hu₁.sub hu₂
  have hp₁ : ContDiff ℝ ∞ p₁ :=
    smoothSolutionOn_pressureSpatialSmooth solution₁.toSmoothSolutionOn ht0 htT
  have hp₂ : ContDiff ℝ ∞ p₂ :=
    smoothSolutionOn_pressureSpatialSmooth solution₂.toSmoothSolutionOn ht0 htT
  have hwPeriodic : IsOnePeriodic w := by
    exact velocityDifference_isOnePeriodic
      (solution₁.velocityPeriodic t ⟨ht0.le, htT.le⟩)
      (solution₂.velocityPeriodic t ⟨ht0.le, htT.le⟩)
  have hp₁Periodic : IsOnePeriodic p₁ :=
    solution₁.pressurePeriodic t ⟨ht0.le, htT.le⟩
  have hp₂Periodic : IsOnePeriodic p₂ :=
    solution₂.pressurePeriodic t ⟨ht0.le, htT.le⟩
  have hwIncompressible : ∀ x, divergence w x = 0 := by
    intro x
    change divergence (fun y => u₁ y - u₂ y) x = 0
    rw [divergence_velocityDifference u₁ u₂ x
      (hu₁.differentiable (by simp) x) (hu₂.differentiable (by simp) x)]
    rw [solution₁.incompressible x t ⟨ht0.le, htT.le⟩,
      solution₂.incompressible x t ⟨ht0.le, htT.le⟩, sub_self]
  have hu₁Incompressible : ∀ x, divergence u₁ x = 0 :=
    fun x => solution₁.incompressible x t ⟨ht0.le, htT.le⟩
  have hdiffSmooth : ContDiffOn ℝ ∞
      (Function.uncurry (velocityDifference velocity₁ velocity₂))
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    apply (solution₁.velocitySmooth.sub solution₂.velocitySmooth).mono
    rintro ⟨x, tau⟩ hxt
    exact ⟨Set.mem_univ x, hxt.2.1.le, hxt.2.2.le⟩
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have htimeContinuous : Continuous (fun x =>
      inner ℝ (eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t) (w x)) :=
    (eulerianTimeJet_continuous_of_contDiffOn_openSlab
      (velocityDifference velocity₁ velocity₂) hdiffSmooth ht0 htT).inner hw.continuous
  have htransportContinuous : Continuous (fun x =>
      inner ℝ (fderiv ℝ w x (u₁ x)) (w x)) := by
    have htransported : Continuous (fun x => fderiv ℝ w x (u₁ x)) :=
      (hw.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk hu₁.continuous)
    exact htransported.inner hw.continuous
  have hjacobianContinuous : Continuous (fun x =>
      inner ℝ (fderiv ℝ u₂ x (w x)) (w x)) := by
    have hacted : Continuous (fun x => fderiv ℝ u₂ x (w x)) :=
      (hu₂.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk hw.continuous)
    exact hacted.inner hw.continuous
  have hpressure₁Continuous : Continuous (fun x =>
      inner ℝ (gradient p₁ x) (w x)) :=
    (gradient_contDiff_one p₁ (hp₁.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.inner
      hw.continuous
  have hpressure₂Continuous : Continuous (fun x =>
      inner ℝ (gradient p₂ x) (w x)) :=
    (gradient_contDiff_one p₂ (hp₂.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.inner
      hw.continuous
  have htimeInt : IntegrableOn (fun x =>
      inner ℝ (eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t) (w x))
      unitCube := htimeContinuous.continuousOn.integrableOn_compact hcubeCompact
  have htransportInt : IntegrableOn (fun x =>
      inner ℝ (fderiv ℝ w x (u₁ x)) (w x)) unitCube :=
    htransportContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hjacobianInt : IntegrableOn (fun x =>
      inner ℝ (fderiv ℝ u₂ x (w x)) (w x)) unitCube :=
    hjacobianContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hviscousInt : IntegrableOn (fun x => inner ℝ (Δ w x) (w x)) unitCube :=
    integrableOn_inner_laplacian_unitCube w
      (hw.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpressure₁Int : IntegrableOn (fun x =>
      inner ℝ (gradient p₁ x) (w x)) unitCube :=
    hpressure₁Continuous.continuousOn.integrableOn_compact hcubeCompact
  have hpressure₂Int : IntegrableOn (fun x =>
      inner ℝ (gradient p₂ x) (w x)) unitCube :=
    hpressure₂Continuous.continuousOn.integrableOn_compact hcubeCompact
  have hpoint : ∀ x,
      (inner ℝ (eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t) (w x) +
        inner ℝ (fderiv ℝ w x (u₁ x)) (w x)) +
          inner ℝ (fderiv ℝ u₂ x (w x)) (w x) =
      (nu * inner ℝ (Δ w x) (w x) -
        inner ℝ (gradient p₁ x) (w x)) +
          inner ℝ (gradient p₂ x) (w x) := by
    intro x
    have hmomentum := congrArg (fun z : Space => inner ℝ z (w x))
      (periodicSolutionOn_pointwiseDifferenceMomentum solution₁ solution₂ ht0 htT x)
    simpa [w, u₁, u₂, p₁, p₂, inner_add_left, inner_sub_left,
      real_inner_smul_left] using hmomentum
  have hintegrated :
      ((∫ x in unitCube,
          inner ℝ (eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t) (w x)) +
        ∫ x in unitCube, inner ℝ (fderiv ℝ w x (u₁ x)) (w x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ u₂ x (w x)) (w x) =
      nu * (∫ x in unitCube, inner ℝ (Δ w x) (w x)) -
        (∫ x in unitCube, inner ℝ (gradient p₁ x) (w x)) +
          ∫ x in unitCube, inner ℝ (gradient p₂ x) (w x) := by
    calc
      ((∫ x in unitCube,
          inner ℝ (eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t) (w x)) +
        ∫ x in unitCube, inner ℝ (fderiv ℝ w x (u₁ x)) (w x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ u₂ x (w x)) (w x) =
        ∫ x in unitCube,
          ((inner ℝ (eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t) (w x) +
            inner ℝ (fderiv ℝ w x (u₁ x)) (w x)) +
              inner ℝ (fderiv ℝ u₂ x (w x)) (w x)) := by
          rw [← integral_add htimeInt htransportInt]
          have hadd := integral_add (htimeInt.add htransportInt) hjacobianInt
          simpa only [Pi.add_apply] using hadd.symm
      _ = ∫ x in unitCube,
          ((nu * inner ℝ (Δ w x) (w x) -
            inner ℝ (gradient p₁ x) (w x)) +
              inner ℝ (gradient p₂ x) (w x)) := by
          apply setIntegral_congr_fun hcubeMeasurable
          intro x _hx
          exact hpoint x
      _ = nu * (∫ x in unitCube, inner ℝ (Δ w x) (w x)) -
          (∫ x in unitCube, inner ℝ (gradient p₁ x) (w x)) +
            ∫ x in unitCube, inner ℝ (gradient p₂ x) (w x) := by
          have hadd := integral_add
            ((hviscousInt.const_mul nu).sub hpressure₁Int) hpressure₂Int
          have hsub := integral_sub (hviscousInt.const_mul nu) hpressure₁Int
          calc
            ∫ x in unitCube,
                ((nu * inner ℝ (Δ w x) (w x) -
                  inner ℝ (gradient p₁ x) (w x)) +
                    inner ℝ (gradient p₂ x) (w x)) =
              (∫ x in unitCube,
                  (nu * inner ℝ (Δ w x) (w x) -
                    inner ℝ (gradient p₁ x) (w x))) +
                ∫ x in unitCube, inner ℝ (gradient p₂ x) (w x) := by
                  simpa only [Pi.add_apply, Pi.sub_apply] using hadd
            _ = ((∫ x in unitCube, nu * inner ℝ (Δ w x) (w x)) -
                  ∫ x in unitCube, inner ℝ (gradient p₁ x) (w x)) +
                ∫ x in unitCube, inner ℝ (gradient p₂ x) (w x) := by
                  rw [hsub]
            _ = nu * (∫ x in unitCube, inner ℝ (Δ w x) (w x)) -
                  (∫ x in unitCube, inner ℝ (gradient p₁ x) (w x)) +
                    ∫ x in unitCube, inner ℝ (gradient p₂ x) (w x) := by
                  rw [integral_const_mul]
  have htransportZero := integral_mixedTransportWork_unitCube_eq_zero u₁ w
    (hu₁.of_le (by norm_num)) (hw.of_le (by norm_num))
    (solution₁.velocityPeriodic t ⟨ht0.le, htT.le⟩) hwPeriodic hu₁Incompressible
  have hpressure₁Zero := integral_pressureWork_unitCube_eq_zero w p₁
    (hw.of_le (by norm_num)) (hp₁.of_le (by norm_num)) hwPeriodic hp₁Periodic
    hwIncompressible
  have hpressure₂Zero := integral_pressureWork_unitCube_eq_zero w p₂
    (hw.of_le (by norm_num)) (hp₂.of_le (by norm_num)) hwPeriodic hp₂Periodic
    hwIncompressible
  have hviscous := integral_inner_laplacian_eq_neg_integral_component_gradient_sq w
    (hw.of_le (WithTop.coe_le_coe.mpr le_top)) hwPeriodic
  change (∫ x in unitCube,
      inner ℝ (eulerianTimeJet (velocityDifference velocity₁ velocity₂) x t)
        (velocityDifference velocity₁ velocity₂ x t)) = _
  change _ = -nu *
      (∫ x in unitCube, ∑ i : Fin 3, ‖gradient (fun y => w y i) x‖ ^ 2) -
        (∫ x in unitCube, inner ℝ (fderiv ℝ u₂ x (w x)) (w x))
  rw [htransportZero, hpressure₁Zero, hpressure₂Zero, hviscous] at hintegrated
  linarith

/-- The periodic kinetic-energy receiver of the difference has the exact linearized derivative. -/
theorem periodicSolutionOn_hasDerivAt_differenceEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (periodicKineticEnergy (velocityDifference velocity₁ velocity₂))
      (-nu * periodicVelocityDifferenceDissipation velocity₁ velocity₂ t -
        periodicDifferenceJacobianWork velocity₂ velocity₁ velocity₂ t) t := by
  have hdiffSmooth : ContDiffOn ℝ ∞
      (Function.uncurry (velocityDifference velocity₁ velocity₂))
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    apply (solution₁.velocitySmooth.sub solution₂.velocitySmooth).mono
    rintro ⟨x, tau⟩ hxt
    exact ⟨Set.mem_univ x, hxt.2.1.le, hxt.2.2.le⟩
  have hderiv := hasDerivAt_periodicKineticEnergy_eq_timeWork_of_contDiffOn_openSlab
    (velocityDifference velocity₁ velocity₂) hdiffSmooth ht0 htT
  rw [periodicSolutionOn_integral_differenceTimeWork_eq
    solution₁ solution₂ ht0 htT] at hderiv
  exact hderiv

/-! ## The remaining Jacobian face -/

/-- A uniform spatial-Jacobian bound controls the sole noncancelling interaction by twice that
bound times the difference energy. -/
theorem periodicSolutionOn_neg_differenceJacobianWork_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (K : ℝ)
    (hK : ∀ x ∈ unitCube, ‖fderiv ℝ (fun y => velocity₂ y t) x‖ ≤ K) :
    -periodicDifferenceJacobianWork velocity₂ velocity₁ velocity₂ t ≤
      2 * K * periodicKineticEnergy (velocityDifference velocity₁ velocity₂) t := by
  let u₂ : InitialVelocity := fun x => velocity₂ x t
  let w : InitialVelocity := fun x => velocityDifference velocity₁ velocity₂ x t
  have hu₂ : ContDiff ℝ ∞ u₂ :=
    smoothSolutionOn_velocitySpatialSmooth solution₂.toSmoothSolutionOn ht0 htT
  have hu₁ : ContDiff ℝ ∞ (fun x => velocity₁ x t) :=
    smoothSolutionOn_velocitySpatialSmooth solution₁.toSmoothSolutionOn ht0 htT
  have hw : ContDiff ℝ ∞ w := hu₁.sub hu₂
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hworkContinuous : Continuous (fun x =>
      inner ℝ (fderiv ℝ u₂ x (w x)) (w x)) := by
    have hacted : Continuous (fun x => fderiv ℝ u₂ x (w x)) :=
      (hu₂.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk hw.continuous)
    exact hacted.inner hw.continuous
  have hworkInt : IntegrableOn (fun x =>
      inner ℝ (fderiv ℝ u₂ x (w x)) (w x)) unitCube :=
    hworkContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hnormInt : IntegrableOn (fun x => K * ‖w x‖ ^ 2) unitCube :=
    (continuous_const.mul (hw.continuous.norm.pow 2)).continuousOn.integrableOn_compact
      hcubeCompact
  have hpoint : ∀ x ∈ unitCube,
      -inner ℝ (fderiv ℝ u₂ x (w x)) (w x) ≤ K * ‖w x‖ ^ 2 := by
    intro x hx
    calc
      -inner ℝ (fderiv ℝ u₂ x (w x)) (w x) ≤
          |inner ℝ (fderiv ℝ u₂ x (w x)) (w x)| := neg_le_abs _
      _ ≤ ‖fderiv ℝ u₂ x (w x)‖ * ‖w x‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖fderiv ℝ u₂ x‖ * ‖w x‖) * ‖w x‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ u₂ x‖ * ‖w x‖ ^ 2 := by ring
      _ ≤ K * ‖w x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hK x hx) (sq_nonneg _)
  calc
    -periodicDifferenceJacobianWork velocity₂ velocity₁ velocity₂ t =
        ∫ x in unitCube, -inner ℝ (fderiv ℝ u₂ x (w x)) (w x) := by
      simp only [periodicDifferenceJacobianWork, u₂, w]
      rw [integral_neg]
    _ ≤ ∫ x in unitCube, K * ‖w x‖ ^ 2 := by
      exact setIntegral_mono_on hworkInt.neg hnormInt hcubeMeasurable hpoint
    _ = 2 * K * periodicKineticEnergy (velocityDifference velocity₁ velocity₂) t := by
      unfold periodicKineticEnergy kineticEnergyDensity
      rw [integral_const_mul, integral_const_mul]
      change K * (∫ x in unitCube, ‖w x‖ ^ 2) =
        2 * K * ((1 / 2 : ℝ) * ∫ x in unitCube, ‖w x‖ ^ 2)
      ring

/-- Nonnegative viscosity makes the difference diffusion face nonpositive. -/
theorem differenceViscousContribution_nonpositive
    (velocity₁ velocity₂ : VelocityField) (t nu : ℝ) (hnu : 0 ≤ nu) :
    -nu * periodicVelocityDifferenceDissipation velocity₁ velocity₂ t ≤ 0 := by
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc |>.measurableSet
  have hD : 0 ≤ periodicVelocityDifferenceDissipation velocity₁ velocity₂ t := by
    unfold periodicVelocityDifferenceDissipation
    exact setIntegral_nonneg hcubeMeasurable
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnu) hD

/-- The exact difference derivative closes to the scalar Grönwall rate under one Jacobian
receiver bound. -/
theorem periodicSolutionOn_differenceEnergyRate_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (hnu : 0 ≤ nu) (K : ℝ)
    (hK : ∀ x ∈ unitCube, ‖fderiv ℝ (fun y => velocity₂ y t) x‖ ≤ K) :
    -nu * periodicVelocityDifferenceDissipation velocity₁ velocity₂ t -
        periodicDifferenceJacobianWork velocity₂ velocity₁ velocity₂ t ≤
      2 * K * periodicKineticEnergy (velocityDifference velocity₁ velocity₂) t := by
  have hviscous := differenceViscousContribution_nonpositive
    velocity₁ velocity₂ t nu hnu
  have hjacobian := periodicSolutionOn_neg_differenceJacobianWork_le
    solution₁ solution₂ ht0 htT K hK
  linarith

/-! ## Compact Jacobian supply, including the initial face -/

/-- Smoothness on a closed finite slab supplies one spatial-Jacobian bound on every compact
subslab, including `t = 0`.  The proof reads the spatial derivative as the joint within-derivative
composed with the isometric spatial inclusion. -/
theorem PeriodicSolutionOn.exists_uniform_spatialJacobian_bound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {b : ℝ} (hbT : b ≤ T) :
    ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K := by
  let slab : Set (Space × ℝ) := spaceTimeSlab T
  let compactSlab : Set (Space × ℝ) := unitCube ×ˢ Icc (0 : ℝ) b
  have hslabUnique : UniqueDiffOn ℝ slab := by
    dsimp [slab, spaceTimeSlab, timeSlab]
    exact uniqueDiffOn_univ.prod (uniqueDiffOn_Icc solution.terminal_pos)
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcompact : IsCompact compactSlab := hcubeCompact.prod isCompact_Icc
  have hcompactSubset : compactSlab ⊆ slab := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨Set.mem_univ x, ht.1, ht.2.trans hbT⟩
  have hjointContinuous : ContinuousOn
      (fderivWithin ℝ (Function.uncurry velocity) slab) slab :=
    solution.velocitySmooth.continuousOn_fderivWithin hslabUnique (by simp)
  have hnormContinuous : ContinuousOn
      (fun z => ‖fderivWithin ℝ (Function.uncurry velocity) slab z‖) compactSlab :=
    (hjointContinuous.mono hcompactSubset).norm
  obtain ⟨K, hK⟩ := bddAbove_def.mp
    (hcompact.bddAbove_image hnormContinuous)
  refine ⟨K, ?_⟩
  intro t ht x hx
  have htT : t ∈ timeSlab T := ⟨ht.1, ht.2.trans hbT⟩
  have hz : (x, t) ∈ compactSlab := ⟨hx, ht⟩
  have hjointBound :
      ‖fderivWithin ℝ (Function.uncurry velocity) slab (x, t)‖ ≤ K := by
    apply hK
    exact ⟨(x, t), hz, rfl⟩
  have hjointDiff : DifferentiableWithinAt ℝ
      (Function.uncurry velocity) slab (x, t) :=
    solution.velocitySmooth.differentiableOn (by simp) (x, t) ⟨Set.mem_univ x, htT⟩
  have hsliceDiff : DifferentiableWithinAt ℝ (fun y : Space => (y, t)) Set.univ x :=
    (hasFDerivAt_prodMk_left x t).differentiableAt.differentiableWithinAt
  have hmaps : MapsTo (fun y : Space => (y, t)) Set.univ slab := by
    intro y _hy
    exact ⟨Set.mem_univ y, htT⟩
  have hcomposition := fderivWithin_comp' x
    hjointDiff hsliceDiff hmaps (uniqueDiffWithinAt_univ : UniqueDiffWithinAt ℝ Set.univ x)
  have hsliceMap : fderiv ℝ (fun y : Space => (y, t)) x =
      ContinuousLinearMap.inl ℝ Space ℝ :=
    (hasFDerivAt_prodMk_left x t).fderiv
  have hsliceDerivative :
      fderiv ℝ (fun y => velocity y t) x =
        (fderivWithin ℝ (Function.uncurry velocity) slab (x, t)).comp
          (ContinuousLinearMap.inl ℝ Space ℝ) := by
    simpa [fderivWithin_univ, Function.uncurry_apply_pair, hsliceMap] using hcomposition
  rw [hsliceDerivative]
  have hcomp :
      ‖(fderivWithin ℝ (Function.uncurry velocity) slab (x, t)).comp
          (ContinuousLinearMap.inl ℝ Space ℝ)‖ ≤
        ‖fderivWithin ℝ (Function.uncurry velocity) slab (x, t)‖ := by
    have hop := ContinuousLinearMap.opNorm_comp_le
      (fderivWithin ℝ (Function.uncurry velocity) slab (x, t))
      (ContinuousLinearMap.inl ℝ Space ℝ)
    rw [ContinuousLinearMap.norm_inl] at hop
    simpa using hop
  exact hcomp.trans hjointBound

/-! ## Grönwall and closure of the initial face -/

/-- The difference-energy receiver is continuous on a closed finite slab, including at the
initial face. -/
theorem periodicSolutionOn_differenceEnergy_continuousOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂)
    {b : ℝ} (hbT : b ≤ T) :
    ContinuousOn (periodicKineticEnergy (velocityDifference velocity₁ velocity₂))
      (Icc (0 : ℝ) b) := by
  let timeSet : Set ℝ := Icc (0 : ℝ) b
  let swap : timeSet × Space → Space × ℝ := fun z => (z.2, z.1.1)
  have hswap : Continuous swap :=
    continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
  have hswapMem : ∀ z, swap z ∈ spaceTimeSlab T := by
    rintro ⟨t, x⟩
    exact ⟨Set.mem_univ x, t.2.1, t.2.2.trans hbT⟩
  have hv₁ : Continuous (fun z : timeSet × Space => velocity₁ z.2 z.1.1) := by
    simpa [swap, Function.comp_def] using
      solution₁.velocitySmooth.continuousOn.comp_continuous hswap hswapMem
  have hv₂ : Continuous (fun z : timeSet × Space => velocity₂ z.2 z.1.1) := by
    simpa [swap, Function.comp_def] using
      solution₂.velocitySmooth.continuousOn.comp_continuous hswap hswapMem
  have hdensity : Continuous (Function.uncurry
      (fun t : timeSet => fun x : Space =>
        kineticEnergyDensity
          (fun y => velocityDifference velocity₁ velocity₂ y t.1) x)) := by
    simpa [Function.uncurry, kineticEnergyDensity, velocityDifference] using
      continuous_const.mul ((hv₁.sub hv₂).norm.pow 2)
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hintegral : Continuous (fun t : timeSet =>
      ∫ x in unitCube,
        kineticEnergyDensity
          (fun y => velocityDifference velocity₁ velocity₂ y t.1) x) :=
    continuous_parametric_integral_of_continuous hdensity hcubeCompact
  rw [continuousOn_iff_continuous_restrict]
  simpa [Set.restrict, periodicKineticEnergy] using hintegral

/-- On a strictly positive compact interval, the difference energy obeys the exponential
Grönwall receiver generated by the single Jacobian interaction. -/
theorem periodicSolutionOn_differenceEnergy_le_exponential
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T)
    (hnu : 0 ≤ nu) (K : ℝ)
    (hK : ∀ t ∈ Ico a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity₂ y t) x‖ ≤ K) :
    ∀ t ∈ Icc a b,
      periodicKineticEnergy (velocityDifference velocity₁ velocity₂) t ≤
        periodicKineticEnergy (velocityDifference velocity₁ velocity₂) a *
          Real.exp ((2 * K) * (t - a)) := by
  let E : ℝ → ℝ := periodicKineticEnergy (velocityDifference velocity₁ velocity₂)
  let E' : ℝ → ℝ := fun t =>
    -nu * periodicVelocityDifferenceDissipation velocity₁ velocity₂ t -
      periodicDifferenceJacobianWork velocity₂ velocity₁ velocity₂ t
  have hcontinuous : ContinuousOn E (Icc a b) := by
    exact (periodicSolutionOn_differenceEnergy_continuousOn
      solution₁ solution₂ hbT.le).mono (Icc_subset_Icc_left ha.le)
  have hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt E (E' t) (Ici t) t := by
    intro t ht
    exact (periodicSolutionOn_hasDerivAt_differenceEnergy solution₁ solution₂
      (ha.trans_le ht.1) (ht.2.trans hbT)).hasDerivWithinAt
  have hrate : ∀ t ∈ Ico a b, E' t ≤ 2 * K * E t := by
    intro t ht
    exact periodicSolutionOn_differenceEnergyRate_le solution₁ solution₂
      (ha.trans_le ht.1) (ht.2.trans hbT) hnu K (hK t ht)
  intro t ht
  have hbound := le_gronwallBound_of_liminf_deriv_right_le
    (K := 2 * K) (ε := 0) hcontinuous
    (fun s hs r hr => (hderiv s hs).liminf_right_slope_le hr)
    (le_refl (E a)) (by simpa using hrate) t ht
  simpa [E, gronwallBound_ε0] using hbound

/-- The difference energy is nonnegative independently of the equation. -/
theorem periodicDifferenceEnergy_nonneg
    (velocity₁ velocity₂ : VelocityField) (t : ℝ) :
    0 ≤ periodicKineticEnergy (velocityDifference velocity₁ velocity₂) t := by
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc |>.measurableSet
  unfold periodicKineticEnergy kineticEnergyDensity
  exact setIntegral_nonneg hcubeMeasurable (fun _ _ => by positivity)

/-- Equal initial data make the initial difference-energy receiver exactly zero. -/
theorem periodicSolutionOn_differenceEnergy_zero_initial
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂) :
    periodicKineticEnergy (velocityDifference velocity₁ velocity₂) 0 = 0 := by
  unfold periodicKineticEnergy
  apply integral_eq_zero_of_ae
  filter_upwards with x
  unfold kineticEnergyDensity velocityDifference
  change (1 / 2 : ℝ) * ‖velocity₁ x 0 - velocity₂ x 0‖ ^ 2 = 0
  simp [solution₁.initial x, solution₂.initial x]

/-- Closing the positive-time estimates against continuity at the initial face forces the
difference energy to vanish on every strict compact subslab. -/
theorem periodicSolutionOn_differenceEnergy_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂)
    {b : ℝ} (hb : 0 < b) (hbT : b < T) (hnu : 0 ≤ nu) :
    periodicKineticEnergy (velocityDifference velocity₁ velocity₂) b = 0 := by
  obtain ⟨K, hK⟩ :=
    PeriodicSolutionOn.exists_uniform_spatialJacobian_bound solution₂ hbT.le
  let E : ℝ → ℝ := periodicKineticEnergy (velocityDifference velocity₁ velocity₂)
  let R : ℝ → ℝ := fun a => E a * Real.exp ((2 * K) * (b - a))
  have hpositive : ∀ a ∈ Ioc (0 : ℝ) b, E b ≤ R a := by
    intro a ha
    exact periodicSolutionOn_differenceEnergy_le_exponential
      solution₁ solution₂ ha.1 ha.2 hbT hnu K
        (fun t ht x hx => hK t ⟨ha.1.le.trans ht.1, ht.2.le⟩ x hx)
        b ⟨ha.2, le_rfl⟩
  have hzeroClosure : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) b) := by
    rw [closure_Ioc hb.ne]
    exact ⟨le_rfl, hb.le⟩
  have hEcontinuous := periodicSolutionOn_differenceEnergy_continuousOn
    solution₁ solution₂ hbT.le
  have hEatZero : ContinuousWithinAt E (Ioc (0 : ℝ) b) 0 :=
    (hEcontinuous 0 ⟨le_rfl, hb.le⟩).mono Ioc_subset_Icc_self
  have hRAtZero : ContinuousWithinAt R (Ioc (0 : ℝ) b) 0 := by
    exact hEatZero.mul
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub continuous_id))).continuousWithinAt
  have hlimit : E b ≤ R 0 :=
    ContinuousWithinAt.closure_le hzeroClosure continuousWithinAt_const hRAtZero hpositive
  have hinitial := periodicSolutionOn_differenceEnergy_zero_initial solution₁ solution₂
  have hnonneg := periodicDifferenceEnergy_nonneg velocity₁ velocity₂ b
  dsimp [R, E] at hlimit
  rw [hinitial, zero_mul] at hlimit
  linarith

/-! ## Null-cone separation and descent from the true torus quotient -/

/-- The closed unit cube is contained in the closure of its interior. -/
theorem unitCube_subset_closure_interior :
    unitCube ⊆ closure (interior unitCube) := by
  have hconvex : Convex ℝ unitCube := by
    unfold unitCube
    exact (convex_Icc (0 : Fin 3 → ℝ) (fun _ => 1)).linear_preimage
      (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap
  have hcoordinateInterior :
      (fun _ : Fin 3 => (1 / 2 : ℝ)) ∈
        interior (Icc (0 : Fin 3 → ℝ) (fun _ => 1)) := by
    have heq : Icc (0 : Fin 3 → ℝ) (fun _ => 1) =
        Set.pi Set.univ (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
      ext x
      simp only [mem_Icc, mem_pi, mem_univ, forall_const]
      constructor
      · intro h i
        exact ⟨h.1 i, h.2 i⟩
      · intro h
        exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    rw [heq, interior_pi_set Set.finite_univ]
    simp [interior_Icc]
    norm_num
  have hinterior : (interior unitCube).Nonempty := by
    let center : Space :=
      (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))
    refine ⟨center, ?_⟩
    unfold unitCube
    change center ∈ interior
      ((EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph ⁻¹'
        Icc (0 : Fin 3 → ℝ) (fun _ => 1))
    rw [← (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.preimage_interior]
    change (EuclideanSpace.equiv (Fin 3) ℝ) center ∈
      interior (Icc (0 : Fin 3 → ℝ) (fun _ => 1))
    simpa [center] using hcoordinateInterior
  have hclosure := hconvex.closure_interior_eq_closure_of_nonempty_interior hinterior
  have hclosed : IsClosed unitCube := by
    unfold unitCube
    exact isClosed_Icc.preimage (EuclideanSpace.equiv (Fin 3) ℝ).continuous
  rw [hclosure, hclosed.closure_eq]

/-- The coordinatewise fractional representative lies in the chosen unit cube. -/
def fractionalUnitCubeRepresentative (x : Space) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    (fun i => Int.fract ((EuclideanSpace.equiv (Fin 3) ℝ x) i))

theorem fractionalUnitCubeRepresentative_mem (x : Space) :
    fractionalUnitCubeRepresentative x ∈ unitCube := by
  unfold fractionalUnitCubeRepresentative unitCube
  change (fun i => Int.fract ((EuclideanSpace.equiv (Fin 3) ℝ x) i)) ∈
    Icc (0 : Fin 3 → ℝ) (fun _ => 1)
  constructor
  · exact fun i => Int.fract_nonneg _
  · exact fun i => (Int.fract_lt_one _).le

/-- The fractional representative is the same point of the true product torus quotient. -/
theorem euclideanToSpatialTorus_fractionalUnitCubeRepresentative (x : Space) :
    euclideanToSpatialTorus (fractionalUnitCubeRepresentative x) =
      euclideanToSpatialTorus x := by
  funext i
  simp [euclideanToSpatialTorus, piToSpatialTorus, fractionalUnitCubeRepresentative]

/-- Vanishing difference energy has no nonzero continuous null direction: the velocity fields
agree everywhere on the spatial torus, not merely almost everywhere on one chart. -/
theorem periodicSolutionOn_velocity_eq_of_differenceEnergy_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : PeriodicSolutionOn T nu initial force velocity₁ pressure₁)
    (solution₂ : PeriodicSolutionOn T nu initial force velocity₂ pressure₂)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T)
    (henergy : periodicKineticEnergy (velocityDifference velocity₁ velocity₂) t = 0) :
    ∀ x, velocity₁ x t = velocity₂ x t := by
  let w : InitialVelocity := fun x => velocityDifference velocity₁ velocity₂ x t
  let density : Space → ℝ := fun x => kineticEnergyDensity w x
  have hu₁ : ContDiff ℝ ∞ (fun x => velocity₁ x t) :=
    smoothSolutionOn_velocitySpatialSmooth solution₁.toSmoothSolutionOn ht0 htT
  have hu₂ : ContDiff ℝ ∞ (fun x => velocity₂ x t) :=
    smoothSolutionOn_velocitySpatialSmooth solution₂.toSmoothSolutionOn ht0 htT
  have hw : ContDiff ℝ ∞ w := hu₁.sub hu₂
  have hdensityContinuous : Continuous density := by
    exact continuous_const.mul (hw.continuous.norm.pow 2)
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hdensityInt : IntegrableOn density unitCube :=
    hdensityContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hintegral : ∫ x in unitCube, density x = 0 := by
    simpa [density, w, periodicKineticEnergy] using henergy
  have hae : density =ᵐ[volume.restrict unitCube] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => by simp [density, kineticEnergyDensity])
      hdensityInt).mp hintegral
  have heqOn : EqOn density 0 unitCube :=
    volume.eqOn_of_ae_eq hae hdensityContinuous.continuousOn continuous_const.continuousOn
      unitCube_subset_closure_interior
  have hzeroCube : ∀ x ∈ unitCube, w x = 0 := by
    intro x hx
    have hdensityZero := heqOn hx
    change (1 / 2 : ℝ) * ‖w x‖ ^ 2 = 0 at hdensityZero
    have hnorm : ‖w x‖ = 0 := by
      nlinarith [sq_nonneg ‖w x‖]
    exact norm_eq_zero.mp hnorm
  have hwPeriodic : IsOnePeriodic w :=
    velocityDifference_isOnePeriodic
      (solution₁.velocityPeriodic t ⟨ht0.le, htT.le⟩)
      (solution₂.velocityPeriodic t ⟨ht0.le, htT.le⟩)
  intro x
  have hquotient := isOnePeriodic_eq_of_euclideanToSpatialTorus_eq w hwPeriodic
    (euclideanToSpatialTorus_fractionalUnitCubeRepresentative x).symm
  have hrepZero := hzeroCube (fractionalUnitCubeRepresentative x)
    (fractionalUnitCubeRepresentative_mem x)
  have hwZero : w x = 0 := hquotient.trans hrepZero
  exact sub_eq_zero.mp hwZero

/-! ## Common-lifespan closure -/

/-- Two open periodic solutions with the same data and nonnegative viscosity have identical
velocity on every common positive open lifespan.  At a positive time `t`, a slightly longer
compact slab supplies the energy estimate without ever adjoining either open terminal face. -/
theorem openPeriodicSolutionOn_velocity_eq_before
    {S R nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : OpenPeriodicSolutionOn S nu initial force velocity₁ pressure₁)
    (solution₂ : OpenPeriodicSolutionOn R nu initial force velocity₂ pressure₂)
    (hnu : 0 ≤ nu) {U : ℝ} (hU : 0 < U) (hUS : U ≤ S) (hUR : U ≤ R) :
    ∀ x, ∀ t ∈ openTimeSlab U, velocity₁ x t = velocity₂ x t := by
  intro x t ht
  rcases eq_or_lt_of_le ht.1 with htzero | htpositive
  · subst t
    exact (solution₁.initial x).trans (solution₂.initial x).symm
  · let V : ℝ := (t + U) / 2
    have hVpositive : 0 < V := by
      dsimp [V]
      linarith
    have htV : t < V := by
      dsimp [V]
      linarith [ht.2]
    have hVU : V < U := by
      dsimp [V]
      linarith [ht.2]
    have hVS : V < S := hVU.trans_le hUS
    have hVR : V < R := hVU.trans_le hUR
    let closed₁ := solution₁.toClosedInterior hVpositive hVS
    let closed₂ := solution₂.toClosedInterior hVpositive hVR
    have henergy :
        periodicKineticEnergy (velocityDifference velocity₁ velocity₂) t = 0 :=
      periodicSolutionOn_differenceEnergy_eq_zero
        closed₁ closed₂ htpositive htV hnu
    exact periodicSolutionOn_velocity_eq_of_differenceEnergy_eq_zero
      closed₁ closed₂ htpositive htV henergy x

/-- Once the velocity difference has vanished on the common open slab, the two momentum equations
recover equality of pressure gradients.  This is exactly the physical pressure gauge: no equality
of pressure values is asserted. -/
theorem openPeriodicSolutionOn_pressureGradient_eq_before
    {S R nu : ℝ} {initial : InitialVelocity} {force velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (solution₁ : OpenPeriodicSolutionOn S nu initial force velocity₁ pressure₁)
    (solution₂ : OpenPeriodicSolutionOn R nu initial force velocity₂ pressure₂)
    {U : ℝ} (hU : 0 < U) (hUS : U ≤ S) (hUR : U ≤ R)
    (hvelocity : ∀ x, ∀ t ∈ openTimeSlab U, velocity₁ x t = velocity₂ x t) :
    ∀ x, ∀ t ∈ openTimeSlab U,
      gradient (fun y => pressure₁ y t) x = gradient (fun y => pressure₂ y t) x := by
  let base₁ := solution₁.restrict hU hUS
  let base₂ := solution₂.restrict hU hUR
  intro x t ht
  have htime :
      derivWithin (velocity₁ x) (openTimeSlab U) t =
        derivWithin (velocity₂ x) (openTimeSlab U) t := by
    exact derivWithin_congr (fun tau htau => hvelocity x tau htau) (hvelocity x t ht)
  have hspatial : (fun y => velocity₁ y t) = (fun y => velocity₂ y t) := by
    funext y
    exact hvelocity y t ht
  have hpoint : velocity₁ x t = velocity₂ x t := hvelocity x t ht
  have hm₁ := base₁.momentum x t ht
  have hm₂ := base₂.momentum x t ht
  rw [htime, hspatial, hpoint] at hm₁
  have hrhs := hm₁.symm.trans hm₂
  have hwithoutForce := add_right_cancel hrhs
  exact sub_right_inj.mp hwithoutForce

/-- The analytic overlap owner: transport and pressure cancel periodically, diffusion is
dissipative for `0 ≤ nu`, and the sole stretching obstruction is absorbed by the compact
spatial-Jacobian coefficient in Grönwall.  The resulting empty difference null-cone separates
velocity, and the momentum equation then separates the pressure-gradient gauge. -/
theorem openPeriodicOverlapUniqueness_of_nonnegativeViscosity
    {nu : ℝ} {initial : InitialVelocity} {force : VelocityField} (hnu : 0 ≤ nu) :
    OpenPeriodicOverlapUniqueness nu initial force := by
  refine ⟨?_⟩
  intro S R velocity₁ velocity₂ pressure₁ pressure₂ solution₁ solution₂ U hU hUS hUR
  have hvelocity := openPeriodicSolutionOn_velocity_eq_before
    solution₁ solution₂ hnu hU hUS hUR
  exact ⟨hvelocity,
    openPeriodicSolutionOn_pressureGradient_eq_before
      solution₁ solution₂ hU hUS hUR hvelocity⟩

section Audit

#print axioms integral_mixedTransportWork_unitCube_eq_zero
#print axioms OpenPeriodicSolutionOn.velocitySpatialSmooth
#print axioms openPeriodicOverlapUniqueness_of_nonnegativeViscosity

end Audit

end Soma.Holonics.Millennium.NavierStokesOverlapUniqueness
