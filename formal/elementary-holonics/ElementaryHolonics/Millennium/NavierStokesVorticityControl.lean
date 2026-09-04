import ElementaryHolonics.Millennium.NavierStokesCurlCommutation
import Mathlib.Analysis.ODE.Gronwall

/-!
# Conditional control of the periodic vorticity receiver

The exact enstrophy identity leaves one genuinely three-dimensional term: vortex
stretching.  This file converts the pointwise Jacobian estimate into an integrated
receiver inequality and then into a finite-interval Grönwall bound.

The result is deliberately conditional.  The official smooth momentum equation now supplies
the pointwise vorticity balance automatically at positive time; the remaining hypotheses are a
uniform spatial Jacobian bound and an upper bound on curl-forcing work.  The file proves what
those controls buy; it does not prove that a Leray solution supplies them or that they persist
globally.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesVorticityControl

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped Laplacian
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- Stretching work is integrable on the periodic cube at every positive-time smooth
solution occurrence. -/
theorem periodicSolution_vortexStretching_integrable
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x =>
      inner ℝ
        (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
        (vorticityField velocity x t)) unitCube := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hu : ContDiff ℝ ∞ (fun x => velocity x t) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
      solution.velocitySmooth ht
  have homega : ContDiff ℝ 2 (fun x => vorticityField velocity x t) :=
    periodicSolution_vorticityField_contDiff_two solution t ht
  have hstretched : Continuous (fun x =>
      fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t)) :=
    (hu.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk homega.continuous)
  exact (hstretched.inner homega.continuous).continuousOn.integrableOn_compact
    hcubeCompact

/-- A uniform velocity-Jacobian bound on one time slice controls the complete signed
stretching receiver by twice that bound times enstrophy. -/
theorem periodicVortexStretching_le_two_mul_jacobianBound_mul_enstrophy
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) (K : ℝ)
    (hK : ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K) :
    periodicVortexStretching velocity t ≤
      2 * K * periodicEnstrophy velocity t := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have homega : ContDiff ℝ 2 (fun x => vorticityField velocity x t) :=
    periodicSolution_vorticityField_contDiff_two solution t ht
  have hnormSqIntegrable : IntegrableOn
      (fun x => K * ‖vorticityField velocity x t‖ ^ 2) unitCube :=
    (continuous_const.mul (homega.continuous.norm.pow 2)).continuousOn.integrableOn_compact
      hcubeCompact
  have hstretchingIntegrable :=
    periodicSolution_vortexStretching_integrable solution t ht
  have hpoint : ∀ x ∈ unitCube,
      inner ℝ
          (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
          (vorticityField velocity x t)
        ≤ K * ‖vorticityField velocity x t‖ ^ 2 := by
    intro x hx
    calc
      inner ℝ
          (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
          (vorticityField velocity x t)
          ≤ |inner ℝ
              (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
              (vorticityField velocity x t)| := le_abs_self _
      _ ≤ ‖fderiv ℝ (fun y => velocity y t) x‖ *
            ‖vorticityField velocity x t‖ ^ 2 :=
        periodicSolution_abs_vortexStretching_le_jacobianNorm_mul_vorticityNormSq
          solution x t ht
      _ ≤ K * ‖vorticityField velocity x t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hK x hx) (sq_nonneg _)
  calc
    periodicVortexStretching velocity t
        ≤ ∫ x in unitCube, K * ‖vorticityField velocity x t‖ ^ 2 := by
          exact setIntegral_mono_on hstretchingIntegrable hnormSqIntegrable
            hcubeMeasurable hpoint
    _ = K * ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2 :=
      by rw [integral_const_mul]
    _ = 2 * K * periodicEnstrophy velocity t := by
      unfold periodicEnstrophy periodicKineticEnergy kineticEnergyDensity
      rw [integral_const_mul]
      ring

/-- Nonnegative viscosity, a spatial Jacobian bound, and a forcing-work bound give the
closed scalar differential inequality used by Grönwall. -/
theorem periodicEnstrophyRate_le_of_jacobian_and_forcing_bounds
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) (hnu : 0 ≤ nu)
    (K F : ℝ)
    (hK : ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K)
    (hforce : periodicCurlForcingWork force velocity t ≤ F) :
    periodicEnstrophyRate nu force velocity t ≤
      2 * K * periodicEnstrophy velocity t + F := by
  have hdiss := periodicSolution_viscousVorticityDissipation_nonneg
    solution t ht hnu
  have hstretch :=
    periodicVortexStretching_le_two_mul_jacobianBound_mul_enstrophy
      solution t ht K hK
  unfold periodicEnstrophyRate
  linarith

/-- A uniform-in-time version of the preceding controls gives an exact finite-interval
Grönwall receiver. -/
theorem periodicEnstrophy_le_gronwallBound
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hnu : 0 ≤ nu)
    (K F : ℝ)
    (hK : ∀ t ∈ Ico a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K)
    (hforce : ∀ t ∈ Ico a b,
      periodicCurlForcingWork force velocity t ≤ F) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        gronwallBound (periodicEnstrophy velocity a) (2 * K) F (t - a) := by
  let E : ℝ → ℝ := periodicEnstrophy velocity
  let E' : ℝ → ℝ := periodicEnstrophyRate nu force velocity
  have hcontinuous : ContinuousOn E (Icc a b) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    exact (periodicSolution_hasDerivAt_periodicEnstrophy_eq_timeWork
      solution t htpos).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt E (E' t) (Ici t) t := by
    intro t ht
    exact (periodicSolution_hasDerivAt_periodicEnstrophy_fromMomentum solution t
      (lt_of_lt_of_le ha ht.1)).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico a b, E' t ≤ 2 * K * E t + F := by
    intro t ht
    exact periodicEnstrophyRate_le_of_jacobian_and_forcing_bounds
      solution t (lt_of_lt_of_le ha ht.1) hnu K F (hK t ht) (hforce t ht)
  exact le_gronwallBound_of_liminf_deriv_right_le hcontinuous
    (fun t ht r hr => (hderiv t ht).liminf_right_slope_le hr)
    (le_refl _) hbound

/-- With nonpositive curl-forcing work, the finite-interval receiver becomes the
familiar exponential conditional bound. -/
theorem periodicEnstrophy_le_exponential_of_nonpositive_forcing
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hnu : 0 ≤ nu)
    (K : ℝ)
    (hK : ∀ t ∈ Ico a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K)
    (hforce : ∀ t ∈ Ico a b,
      periodicCurlForcingWork force velocity t ≤ 0) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        periodicEnstrophy velocity a * Real.exp ((2 * K) * (t - a)) := by
  intro t ht
  have h := periodicEnstrophy_le_gronwallBound solution ha hab hnu K 0
    hK hforce t ht
  simpa [gronwallBound_ε0] using h

end Soma.Holonics.Millennium.NavierStokesVorticityControl
