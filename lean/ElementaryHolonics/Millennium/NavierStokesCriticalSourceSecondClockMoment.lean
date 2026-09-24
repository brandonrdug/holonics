import ElementaryHolonics.Millennium.NavierStokesCriticalSourceClockMoment
import ElementaryHolonics.Millennium.NavierStokesWeightedJointSmoothnessScale

/-!
# Second clock moment of the native sharp source

**[proved-derived]**  The coherent smooth restart tower already differentiates every member of
its Sobolev scale in time.  This module spends that scale-wise passage once more to construct the
literal native acceleration `u_tt` in `H³`, then differentiates the signed sharp-source yank
before any coefficient norm:

`N'' = B(u_tt,u) + 2 B(u_t,u_t) + B(u,u_tt)`.

No terminal-uniform estimate is asserted.  The second reflected moment gains two powers of its
local clock aperture, but its coefficient is a compact-interior bound for this supercritical
second source jet.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators Interval NNReal

namespace Soma.Holonics.Millennium.NavierStokesCriticalSourceSecondClockMoment

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalSourceClockMoment
open Soma.Holonics.Millennium.NavierStokesCriticalSourceTimeJet
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessScale
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Native acceleration -/

/-- The three diagonal second-derivative passages, retained as one bounded native map. -/
def diagonalLaplacianToThree :
    PeriodicVectorWeightedSobolev 5 →L[ℂ]
      PeriodicVectorWeightedSobolev 3 :=
  ∑ coordinate : Fin 3, diagonalSecondDerivativeAtOrder 0 coordinate

@[simp]
theorem diagonalLaplacianToThree_apply
    (state : PeriodicVectorWeightedSobolev 5) :
    diagonalLaplacianToThree state =
      ∑ coordinate : Fin 3,
        diagonalSecondDerivativeAtOrder 0 coordinate state :=
  rfl

/-- The scale-zero projected vector field with its codomain fixed definitionally to native
`H³`.  Fixing this receiver avoids allowing natural-number normalization to choose a distinct
elaborated module instance for the same carrier. -/
def nativeProjectedFirstTimeDerivativeH3Extension
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (t : ℝ) : PeriodicVectorWeightedSobolev 3 :=
  (nu : ℝ) • diagonalLaplacianToThree
      (smoothTowerLiftExtension hT tower 2 t) -
    periodicVectorWeightedLerayDivergenceConvolution
      4 (by norm_num)
      (smoothTowerLiftExtension hT tower 1 t)
      (smoothTowerLiftExtension hT tower 1 t)

/-- The explicit native `H³` first vector field is the scale-zero field. -/
theorem nativeProjectedFirstTimeDerivativeH3Extension_eq_scale_zero
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) (t : ℝ) :
    nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t =
      nativeProjectedVectorFieldExtensionAtOrder hT tower nu 0 t := by
  unfold nativeProjectedFirstTimeDerivativeH3Extension
  unfold nativeProjectedVectorFieldExtensionAtOrder
  congr 1

/-- On the addressed clock aperture the explicit `H³` vector field is literally the native
first projected time-derivative path already used by the source yank. -/
theorem nativeProjectedFirstTimeDerivativeH3Extension_eq_native
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t =
      weightedPathExtension hT
        (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
          tower nu) t := by
  rw [nativeProjectedFirstTimeDerivativeH3Extension_eq_scale_zero]
  rw [nativeProjectedVectorFieldExtensionAtOrder_of_mem hT tower nu 0 ht]
  change Set.IccExtend hT
      (nativeProjectedTimeDerivativePathAtOrder tower nu 0) t =
    weightedPathExtension hT
      (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
        tower nu) t
  rw [Set.IccExtend_of_mem hT _ ht,
    weightedPathExtension_of_mem hT _ ht]
  change nativeProjectedTimeDerivativeAtOrder tower nu 0 ⟨t, ht⟩ =
    CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivative
      tower nu ⟨t, ht⟩
  apply periodicVectorWeightedSobolev_eq_of_coefficients_eq
  intro component k
  rw [weightedVectorSobolevCoefficientCLM_apply,
    weightedVectorSobolevCoefficientCLM_apply,
    weightedSobolevCoefficients_nativeProjectedTimeDerivativeAtOrder,
    CoherentWeightedSmoothPathTower.weightedSobolevCoefficients_nativeProjectedTimeDerivative]

/-- The scale-indexed projected vector field is continuous on its endpoint-totalized chart. -/
theorem continuous_nativeProjectedVectorFieldExtensionAtOrder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) (m : ℕ) :
    Continuous (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m) := by
  have hviscous : Continuous (fun t : ℝ ↦
      ∑ coordinate : Fin 3,
        diagonalSecondDerivativeAtOrder m coordinate
          (smoothTowerLiftExtension hT tower (m + 2) t)) := by
    apply continuous_finsetSum
    intro coordinate _
    exact (diagonalSecondDerivativeAtOrder m coordinate).continuous.comp
      (smoothTowerLiftExtension hT tower (m + 2)).continuous
  have hsource : Continuous (fun t : ℝ ↦
      periodicVectorWeightedLerayDivergenceConvolution
        (m + 4) (by omega)
          (smoothTowerLiftExtension hT tower (m + 1) t)
          (smoothTowerLiftExtension hT tower (m + 1) t)) := by
    exact (((periodicVectorWeightedLerayDivergenceConvolutionContinuous
      (m + 4) (by omega)).continuous.comp
        (smoothTowerLiftExtension hT tower (m + 1)).continuous).clm_apply
          (smoothTowerLiftExtension hT tower (m + 1)).continuous).congr
            (fun _ ↦ rfl)
  unfold nativeProjectedVectorFieldExtensionAtOrder
  exact ((continuous_const : Continuous
    (fun _ : ℝ ↦ (nu : ℂ))).smul hviscous).sub hsource

/-- The actual second native time derivative, defined by differentiating the first projected
vector field in the real time direction. -/
def nativeProjectedSecondTimeDerivative
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (t : ℝ) : PeriodicVectorWeightedSobolev 3 :=
  deriv (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu) t

/-- The scale-indexed first projected vector field differentiates to the exact native
acceleration on every strict-interior time face. -/
theorem hasDerivAt_nativeProjectedFirstTimeDerivativeH3Extension
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu)
      (nativeProjectedSecondTimeDerivative hT tower nu t) t := by
  have hfive := hasDerivAt_smoothTowerLiftExtension
    hT tower nu hnu initial hfixed hreal 2 ht
  have hfour := hasDerivAt_smoothTowerLiftExtension
    hT tower nu hnu initial hfixed hreal 1 ht
  rw [← nativeProjectedVectorFieldExtensionAtOrder_of_mem
    hT tower nu 2 ⟨ht.1.le, ht.2.le⟩] at hfive
  rw [← nativeProjectedVectorFieldExtensionAtOrder_of_mem
    hT tower nu 1 ⟨ht.1.le, ht.2.le⟩] at hfour
  have hviscous : HasDerivAt
      (fun tau : ℝ ↦ diagonalLaplacianToThree
        (smoothTowerLiftExtension hT tower 2 tau))
      (diagonalLaplacianToThree
        (nativeProjectedVectorFieldExtensionAtOrder hT tower nu 2 t)) t :=
    (diagonalLaplacianToThree.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      t hfive
  let B : PeriodicVectorWeightedSobolev 4 →L[ℝ]
      PeriodicVectorWeightedSobolev 4 →L[ℝ]
        PeriodicVectorWeightedSobolev 3 :=
    (periodicVectorWeightedLerayDivergenceConvolutionContinuous
      4 (by norm_num)).bilinearRestrictScalars ℝ
  have hoperator : HasDerivAt
      (fun tau ↦ B (smoothTowerLiftExtension hT tower 1 tau))
      (B (nativeProjectedVectorFieldExtensionAtOrder hT tower nu 1 t)) t := by
    change HasDerivAt
      (B ∘ fun tau ↦ smoothTowerLiftExtension hT tower 1 tau)
      (B (nativeProjectedVectorFieldExtensionAtOrder hT tower nu 1 t)) t
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one] using
        (B.hasFDerivAt.comp t hfour.hasFDerivAt).hasDerivAt
  have hsource : HasDerivAt
      (fun tau ↦ B (smoothTowerLiftExtension hT tower 1 tau)
        (smoothTowerLiftExtension hT tower 1 tau))
      (B (nativeProjectedVectorFieldExtensionAtOrder hT tower nu 1 t)
          (smoothTowerLiftExtension hT tower 1 t) +
        B (smoothTowerLiftExtension hT tower 1 t)
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu 1 t)) t :=
    hoperator.clm_apply hfour
  have htotal := (hviscous.const_smul (nu : ℝ)).sub hsource
  unfold nativeProjectedSecondTimeDerivative
  apply DifferentiableAt.hasDerivAt
  exact htotal.differentiableAt

/-- The exact first projected vector field is twice continuously differentiable on the strict
native aperture. -/
theorem contDiffOn_two_nativeProjectedFirstTimeDerivativeH3Extension
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    ContDiffOn ℝ 2
      (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu)
      (Ioo (0 : ℝ) T) := by
  have hlifts := contDiffOn_smoothTowerLiftExtension_allFiniteOrders
    hT tower nu hnu initial hfixed hreal 2
  have hfield := contDiffOn_nativeProjectedVectorFieldExtensionAtOrder
    hT tower nu 2 0 hlifts
  exact hfield.congr (fun t _ ↦
    (nativeProjectedFirstTimeDerivativeH3Extension_eq_scale_zero
      hT tower nu t).symm)

/-- The native acceleration varies continuously on every strict-interior time face. -/
theorem continuousOn_nativeProjectedSecondTimeDerivative
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    ContinuousOn (nativeProjectedSecondTimeDerivative hT tower nu)
      (Ioo (0 : ℝ) T) := by
  have htwo := contDiffOn_two_nativeProjectedFirstTimeDerivativeH3Extension
    hT tower nu hnu initial hfixed hreal
  rw [show (2 : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] at htwo
  exact htwo.2.2.continuousOn

attribute [irreducible] nativeProjectedSecondTimeDerivative

/-! ## The second sharp-source time jet -/

set_option maxHeartbeats 800000

/-- The exact four-incidence second derivative of the sharp quadratic source.  The two middle
incidences are retained separately rather than silently identifying their orientations. -/
def nativeSharpSourceSecondTimeJet
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (t : ℝ) : PeriodicVectorWeightedSobolev 2 :=
  let velocity := weightedPathExtension hT base t
  let timeJet := nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t
  let secondJet := nativeProjectedSecondTimeDerivative hT tower nu t
  weightedLerayDivergenceConvolution secondJet velocity +
    weightedLerayDivergenceConvolution timeJet timeJet +
    weightedLerayDivergenceConvolution timeJet timeJet +
    weightedLerayDivergenceConvolution velocity secondJet

/-- The source yank written through the explicit scale-zero first projected vector field. -/
def nativeSharpSourceTimeJetH3Extension
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (t : ℝ) : PeriodicVectorWeightedSobolev 2 :=
  weightedLerayDivergenceConvolution
      (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t)
      (weightedPathExtension hT base t) +
    weightedLerayDivergenceConvolution
      (weightedPathExtension hT base t)
      (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t)

/-- On every addressed time face the explicit source yank is the existing native source yank. -/
theorem nativeSharpSourceTimeJetH3Extension_eq_native
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    nativeSharpSourceTimeJetH3Extension hT tower nu t =
      nativeSharpSourceTimeJet hT tower nu t := by
  rw [nativeSharpSourceTimeJetH3Extension, nativeSharpSourceTimeJet,
    nativeProjectedFirstTimeDerivativeH3Extension_eq_native hT tower nu ht]

/-- The explicit first projected field is continuous on the totalized chart. -/
theorem continuous_nativeProjectedFirstTimeDerivativeH3Extension
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) :
    Continuous (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu) := by
  exact (continuous_nativeProjectedVectorFieldExtensionAtOrder hT tower nu 0).congr
    (fun t ↦ (nativeProjectedFirstTimeDerivativeH3Extension_eq_scale_zero
      hT tower nu t).symm)

/-- The exact four-incidence second source jet is continuous on the strict native aperture. -/
theorem continuousOn_nativeSharpSourceSecondTimeJet
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    ContinuousOn (nativeSharpSourceSecondTimeJet hT tower nu)
      (Ioo (0 : ℝ) T) := by
  let B : PeriodicVectorWeightedSobolev 3 →L[ℝ]
      PeriodicVectorWeightedSobolev 3 →L[ℝ]
        PeriodicVectorWeightedSobolev 2 :=
    weightedLerayDivergenceConvolutionContinuous.bilinearRestrictScalars ℝ
  have hu : Continuous (fun t : ℝ ↦ weightedPathExtension hT base t) :=
    (weightedPathExtension hT base).continuous
  have hut : Continuous
      (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu) :=
    continuous_nativeProjectedFirstTimeDerivativeH3Extension hT tower nu
  have hutt : ContinuousOn
      (nativeProjectedSecondTimeDerivative hT tower nu) (Ioo (0 : ℝ) T) :=
    continuousOn_nativeProjectedSecondTimeDerivative
      hT tower nu hnu initial hfixed hreal
  have hone : ContinuousOn (fun t ↦
      B (nativeProjectedSecondTimeDerivative hT tower nu t)
        (weightedPathExtension hT base t)) (Ioo (0 : ℝ) T) :=
    (B.continuous.comp_continuousOn hutt).clm_apply hu.continuousOn
  have htwo : ContinuousOn (fun t ↦
      B (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t)
        (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t))
      (Ioo (0 : ℝ) T) :=
    (B.continuous.comp hut).clm_apply hut |>.continuousOn
  have hfour : ContinuousOn (fun t ↦
      B (weightedPathExtension hT base t)
        (nativeProjectedSecondTimeDerivative hT tower nu t))
      (Ioo (0 : ℝ) T) :=
    (B.continuous.comp hu).continuousOn.clm_apply hutt
  apply (((hone.add htwo).add htwo).add hfour).congr
  intro t _ht
  rfl

/-- **Exact second source-jet FTC.**  The integral of the four-incidence source acceleration is
the returned difference of the explicit source yank on every compact strict-interior interval. -/
theorem intervalIntegral_nativeSharpSourceSecondTimeJet_eq_sub
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {sourceTime targetTime : ℝ}
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) :
    (∫ tau in sourceTime..targetTime,
        nativeSharpSourceSecondTimeJet hT tower nu tau) =
      nativeSharpSourceTimeJetH3Extension hT tower nu targetTime -
        nativeSharpSourceTimeJetH3Extension hT tower nu sourceTime := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le htimes] at ht
    have hinterior : t ∈ Ioo (0 : ℝ) T :=
      ⟨hsource.trans_le ht.1, ht.2.trans_lt htarget⟩
    have hu :=
      CoherentWeightedSmoothPathTower.hasDerivAt_weightedPathExtension_nativeProjectedTimeDerivative
        hT tower nu hnu initial hfixed hreal hinterior
    have hfield := hasDerivAt_nativeProjectedFirstTimeDerivativeH3Extension
      hT tower nu hnu initial hfixed hreal hinterior
    let B : PeriodicVectorWeightedSobolev 3 →L[ℝ]
        PeriodicVectorWeightedSobolev 3 →L[ℝ]
          PeriodicVectorWeightedSobolev 2 :=
      weightedLerayDivergenceConvolutionContinuous.bilinearRestrictScalars ℝ
    have hutOperator : HasDerivAt
        (fun tau ↦ B
          (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu tau))
        (B (nativeProjectedSecondTimeDerivative hT tower nu t)) t := by
      change HasDerivAt
        (B ∘ nativeProjectedFirstTimeDerivativeH3Extension hT tower nu)
        (B (nativeProjectedSecondTimeDerivative hT tower nu t)) t
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply_one] using
          (B.hasFDerivAt.comp t hfield.hasFDerivAt).hasDerivAt
    have huOperator : HasDerivAt
        (fun tau ↦ B (weightedPathExtension hT base tau))
        (B (weightedPathExtension hT
          (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
            tower nu) t)) t := by
      change HasDerivAt
        (B ∘ fun tau ↦ weightedPathExtension hT base tau)
        (B (weightedPathExtension hT
          (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
            tower nu) t)) t
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply_one] using
          (B.hasFDerivAt.comp t hu.hasFDerivAt).hasDerivAt
    have hleft := hutOperator.clm_apply hu
    have hright := huOperator.clm_apply hfield
    have htjet := nativeProjectedFirstTimeDerivativeH3Extension_eq_native
      hT tower nu ⟨hinterior.1.le, hinterior.2.le⟩
    rw [← htjet] at hleft hright
    rw [show nativeSharpSourceTimeJetH3Extension hT tower nu =
        ((fun y ↦ weightedLerayDivergenceConvolution
            (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu y)
            (weightedPathExtension hT base y)) +
          fun y ↦ weightedLerayDivergenceConvolution
            (weightedPathExtension hT base y)
            (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu y)) by
      funext y
      rfl]
    rw [show nativeSharpSourceSecondTimeJet hT tower nu t =
        weightedLerayDivergenceConvolution
            (nativeProjectedSecondTimeDerivative hT tower nu t)
            (weightedPathExtension hT base t) +
          weightedLerayDivergenceConvolution
              (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t)
              (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t) +
          weightedLerayDivergenceConvolution
              (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t)
              (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu t) +
          weightedLerayDivergenceConvolution
            (weightedPathExtension hT base t)
            (nativeProjectedSecondTimeDerivative hT tower nu t) by rfl]
    simpa only [B,
      ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      weightedLerayDivergenceConvolutionContinuous_apply,
      add_assoc] using hleft.add hright
  · exact ((continuousOn_nativeSharpSourceSecondTimeJet
      hT tower nu hnu initial hfixed hreal).mono
        (by
          intro t ht
          rw [uIcc_of_le htimes] at ht
          exact ⟨hsource.trans_le ht.1, ht.2.trans_lt htarget⟩)).intervalIntegrable

/-! ## The reflected second clock moment -/

/-- The second reflected source-clock moment.  Each outer clock face carries the returned
difference of the exact source yank between that face and the target face. -/
def nativeSharpSourceSecondClockMoment
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (target elapsed : ℝ) : PeriodicVectorWeightedSobolev 2 :=
  ∫ tau in (target - elapsed)..target,
    (nativeSharpSourceTimeJetH3Extension hT tower nu target -
      nativeSharpSourceTimeJetH3Extension hT tower nu tau)

/-- The second clock moment is literally the nested integral of the four-incidence source
acceleration over the reflected triangular clock population. -/
theorem nativeSharpSourceSecondClockMoment_eq_nested_secondTimeJet
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {target horizon elapsed : ℝ}
    (_hhorizon : 0 ≤ horizon) (helapsed : elapsed ∈ Icc (0 : ℝ) horizon)
    (hbefore : horizon < target) (htarget : target < T) :
    nativeSharpSourceSecondClockMoment hT tower nu target elapsed =
      ∫ tau in (target - elapsed)..target,
        (∫ sigma in tau..target,
          nativeSharpSourceSecondTimeJet hT tower nu sigma) := by
  unfold nativeSharpSourceSecondClockMoment
  apply intervalIntegral.integral_congr
  intro tau htau
  rw [uIcc_of_le (sub_le_self target helapsed.1)] at htau
  symm
  exact intervalIntegral_nativeSharpSourceSecondTimeJet_eq_sub
    hT tower nu hnu initial hfixed hreal
    ((by linarith [helapsed.2, hbefore] : 0 < target - elapsed).trans_le htau.1)
    htau.2 htarget

/-- **Exact second Taylor reflection.**  The first clock moment is the target yank multiplied
by the elapsed clock length minus the genuine second clock moment. -/
theorem nativeSharpSourceFirstClockMoment_eq_elapsed_smul_sub_secondClockMoment
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0)
    {target horizon elapsed : ℝ}
    (_hhorizon : 0 ≤ horizon) (helapsed : elapsed ∈ Icc (0 : ℝ) horizon)
    (hbefore : horizon < target) (htarget : target < T) :
    nativeSharpSourceFirstClockMoment hT tower nu target elapsed =
      elapsed • nativeSharpSourceTimeJetH3Extension hT tower nu target -
        nativeSharpSourceSecondClockMoment hT tower nu target elapsed := by
  have htimes : target - elapsed ≤ target := sub_le_self target helapsed.1
  have hinterior : ∀ tau ∈ uIcc (target - elapsed) target,
      tau ∈ Icc (0 : ℝ) T := by
    intro tau htau
    rw [uIcc_of_le htimes] at htau
    constructor
    · have : 0 < target - elapsed := by
        linarith [helapsed.2, hbefore]
      exact this.le.trans htau.1
    · exact htau.2.trans (le_of_lt htarget)
  have hyank : (∫ tau in (target - elapsed)..target,
      nativeSharpSourceTimeJetH3Extension hT tower nu tau) =
      nativeSharpSourceFirstClockMoment hT tower nu target elapsed := by
    unfold nativeSharpSourceFirstClockMoment
    apply intervalIntegral.integral_congr
    intro tau htau
    exact nativeSharpSourceTimeJetH3Extension_eq_native
      hT tower nu (hinterior tau htau)
  have hcontinuous : Continuous
      (nativeSharpSourceTimeJetH3Extension hT tower nu) := by
    let B : PeriodicVectorWeightedSobolev 3 →L[ℝ]
        PeriodicVectorWeightedSobolev 3 →L[ℝ]
          PeriodicVectorWeightedSobolev 2 :=
      weightedLerayDivergenceConvolutionContinuous.bilinearRestrictScalars ℝ
    have hu : Continuous (fun tau : ℝ ↦ weightedPathExtension hT base tau) :=
      (weightedPathExtension hT base).continuous
    have hut := continuous_nativeProjectedFirstTimeDerivativeH3Extension
      hT tower nu
    have hleft : Continuous (fun tau ↦
        B (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu tau)
          (weightedPathExtension hT base tau)) :=
      (B.continuous.comp hut).clm_apply hu
    have hright : Continuous (fun tau ↦
        B (weightedPathExtension hT base tau)
          (nativeProjectedFirstTimeDerivativeH3Extension hT tower nu tau)) :=
      (B.continuous.comp hu).clm_apply hut
    exact (hleft.add hright).congr (fun _ ↦ rfl)
  have hconst : IntervalIntegrable
      (fun _tau : ℝ ↦ nativeSharpSourceTimeJetH3Extension
        hT tower nu target) volume (target - elapsed) target :=
    intervalIntegrable_const
  have hyankIntegrable : IntervalIntegrable
      (nativeSharpSourceTimeJetH3Extension hT tower nu)
      volume (target - elapsed) target :=
    hcontinuous.intervalIntegrable _ _
  unfold nativeSharpSourceSecondClockMoment
  rw [intervalIntegral.integral_sub hconst hyankIntegrable]
  rw [intervalIntegral.integral_const, hyank]
  simp only [sub_sub_cancel]

/-! ## Local quadratic clock scaling -/

/-- **Local second-moment scaling.**  On every compact aperture strictly inside one native
restart, the genuine second clock moment is at most quadratic in elapsed time.  The returned
constant is owned by that aperture; this is not a terminal-uniform estimate. -/
theorem exists_norm_nativeSharpSourceSecondClockMoment_le_const_mul_elapsed_sq
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {target horizon : ℝ} (hhorizon : 0 ≤ horizon)
    (hbefore : horizon < target) (htarget : target < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ elapsed ∈ Icc (0 : ℝ) horizon,
      ‖nativeSharpSourceSecondClockMoment hT tower nu target elapsed‖ ≤
        C * elapsed ^ 2 := by
  let secondJet : ℝ → PeriodicVectorWeightedSobolev 2 :=
    nativeSharpSourceSecondTimeJet hT tower nu
  have hsecond : ContinuousOn secondJet (Ioo (0 : ℝ) T) :=
    continuousOn_nativeSharpSourceSecondTimeJet
      hT tower nu hnu initial hfixed hreal
  have hcompact : IsCompact (Icc (target - horizon) target) := isCompact_Icc
  have hcompactInside : Icc (target - horizon) target ⊆ Ioo (0 : ℝ) T := by
    intro tau htau
    constructor
    · have hleft : 0 < target - horizon := by linarith
      exact hleft.trans_le htau.1
    · exact htau.2.trans_lt htarget
  have hnormContinuous : ContinuousOn (fun tau ↦ ‖secondJet tau‖)
      (Icc (target - horizon) target) :=
    (hsecond.mono hcompactInside).norm
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hcompact.bddAbove_image hnormContinuous)
  have hCpoint : ∀ tau ∈ Icc (target - horizon) target,
      ‖secondJet tau‖ ≤ C := by
    intro tau htau
    exact hC ‖secondJet tau‖ ⟨tau, htau, rfl⟩
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg (secondJet target)).trans
      (hCpoint target ⟨sub_le_self target hhorizon, le_rfl⟩)
  refine ⟨C, hCnonneg, ?_⟩
  intro elapsed helapsed
  rw [nativeSharpSourceSecondClockMoment_eq_nested_secondTimeJet
    hT tower nu hnu initial hfixed hreal hhorizon helapsed hbefore htarget]
  have htimes : target - elapsed ≤ target :=
    sub_le_self target helapsed.1
  have hinner : ∀ tau ∈ Icc (target - elapsed) target,
      ‖∫ sigma in tau..target, secondJet sigma‖ ≤ C * elapsed := by
    intro tau htau
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := secondJet) (C := C) (a := tau) (b := target) (by
        intro sigma hsigma
        rw [uIoc_of_le htau.2] at hsigma
        apply hCpoint sigma
        constructor
        · have hlower : target - horizon ≤ target - elapsed := by
            linarith [helapsed.2]
          exact hlower.trans (htau.1.trans hsigma.1.le)
        · exact hsigma.2)
    have htauGap : 0 ≤ target - tau := sub_nonneg.mpr htau.2
    calc
      ‖∫ sigma in tau..target, secondJet sigma‖ ≤
          C * (target - tau) := by
        simpa [abs_of_nonneg htauGap] using hraw
      _ ≤ C * elapsed := by
        exact mul_le_mul_of_nonneg_left (by linarith [htau.1]) hCnonneg
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun tau ↦ ∫ sigma in tau..target, secondJet sigma)
    (C := C * elapsed) (a := target - elapsed) (b := target) (by
      intro tau htau
      rw [uIoc_of_le htimes] at htau
      exact hinner tau ⟨htau.1.le, htau.2⟩)
  simpa [secondJet, abs_of_nonneg helapsed.1, pow_two, mul_assoc] using houter

section Audit

#print axioms hasDerivAt_nativeProjectedFirstTimeDerivativeH3Extension
#print axioms intervalIntegral_nativeSharpSourceSecondTimeJet_eq_sub
#print axioms nativeSharpSourceSecondClockMoment_eq_nested_secondTimeJet
#print axioms nativeSharpSourceFirstClockMoment_eq_elapsed_smul_sub_secondClockMoment
#print axioms exists_norm_nativeSharpSourceSecondClockMoment_le_const_mul_elapsed_sq

end Audit


end Soma.Holonics.Millennium.NavierStokesCriticalSourceSecondClockMoment
