import ElementaryHolonics.Millennium.NavierStokesCriticalSourceTimeJetBound
import ElementaryHolonics.Millennium.NavierStokesFrozenSharpSourceBoundary

/-!
# First clock moment of the transported sharp source

**[proved-derived]**  The genuine nonlinear-source yank

`N'(t) = B(u_t(t),u(t)) + B(u(t),u_t(t))`

is integrated over the reflected clock interval `[target-elapsed,target]`.  Before any
coefficient norm, the transported source at `target-elapsed` is exactly the frozen target
source minus this first clock moment.  Integrating in elapsed time returns the existing finite
frozen heat-boundary/resolvent action minus one nested, heat-transported source-jet moment.

This is the first Taylor-reflection / time-integration-by-parts face of the actual quadratic
source on a native restart path.  The additional clock moment supplies one explicit elapsed
factor locally, but its coefficient is the genuine source time jet.  No terminal-uniform bound
for that jet, no critical endpoint estimate, and no terminal receiver are asserted.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators Interval NNReal

namespace Soma.Holonics.Millennium.NavierStokesCriticalSourceClockMoment

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalTimeReflection
open Soma.Holonics.Millennium.NavierStokesCriticalSourceTimeJet
open Soma.Holonics.Millennium.NavierStokesCriticalSourceTimeJetBound
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundary
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The reflected first source moment -/

/-- The first reflected clock moment of the exact native nonlinear-source time jet.  Its lower
boundary retains both the target address and the elapsed address. -/
def nativeSharpSourceFirstClockMoment
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (target elapsed : ℝ) : PeriodicVectorWeightedSobolev 2 :=
  ∫ tau in (target - elapsed)..target,
    nativeSharpSourceTimeJet hT tower nu tau

/-- The nested resolvent remainder: the heat clock transports the literal first source-jet
moment at each elapsed address, and only then is elapsed time integrated. -/
def nativeSharpSourceFirstClockResolventRemainder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (target horizon : ℝ) (k : SpatialFrequency) : ComplexVector :=
  ∫ elapsed in (0 : ℝ)..horizon,
    heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
      (nativeSharpSourceFirstClockMoment hT tower nu target elapsed) k

/-- On every elapsed face in the addressed clock aperture, the first source moment is exactly
the difference between the frozen target source and the reflected source. -/
theorem nativeSharpSourceFirstClockMoment_eq_sub
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {target horizon elapsed : ℝ}
    (_hhorizon : 0 ≤ horizon) (helapsed : elapsed ∈ Icc (0 : ℝ) horizon)
    (hbefore : horizon < target) (htarget : target < T) :
    nativeSharpSourceFirstClockMoment hT tower nu target elapsed =
      sharpNonlinearSource (weightedPathExtension hT base target) -
        sharpNonlinearSource
          (weightedPathExtension hT base (target - elapsed)) := by
  unfold nativeSharpSourceFirstClockMoment
  exact intervalIntegral_nativeSharpSourceTimeJet_eq_sub
    hT tower nu hnu initial hfixed hreal
    (by linarith [helapsed.2, hbefore])
    (sub_le_self target helapsed.1)
    htarget

/-- **Pointwise Taylor reflection before norms.**  Heat transport preserves the exact signed
split into the frozen target source and the reflected first source-jet moment. -/
theorem heatTransported_reflectedSharpSource_eq_frozen_sub_firstClockMoment
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {target horizon elapsed : ℝ}
    (hhorizon : 0 ≤ horizon) (helapsed : elapsed ∈ Icc (0 : ℝ) horizon)
    (hbefore : horizon < target) (htarget : target < T)
    (k : SpatialFrequency) :
    heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
        (sharpNonlinearSource
          (weightedPathExtension hT base (target - elapsed))) k =
      heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
          (sharpNonlinearSource (weightedPathExtension hT base target)) k -
        heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
          (nativeSharpSourceFirstClockMoment hT tower nu target elapsed) k := by
  rw [nativeSharpSourceFirstClockMoment_eq_sub hT tower nu hnu initial hfixed hreal
    hhorizon helapsed hbefore htarget]
  have hsub := heatTransportedH2SourceCurlCoefficient_sub
    (nu : ℝ) elapsed
    (sharpNonlinearSource (weightedPathExtension hT base target))
    (sharpNonlinearSource
      (weightedPathExtension hT base (target - elapsed))) k
  rw [hsub]
  abel

/-! ## Continuity of the exact clock populations -/

/-- The reflected first source moment is continuous in its elapsed address. -/
theorem continuous_nativeSharpSourceFirstClockMoment
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (target : ℝ) :
    Continuous (nativeSharpSourceFirstClockMoment hT tower nu target) := by
  have hjet := continuous_nativeSharpSourceTimeJet hT tower nu
  have hprimitive : Continuous (fun upper : ℝ ↦
      ∫ tau in target..upper, nativeSharpSourceTimeJet hT tower nu tau) :=
    intervalIntegral.continuous_primitive
      (fun left right ↦ hjet.intervalIntegrable left right) target
  have hreflected : Continuous (fun elapsed : ℝ ↦
      ∫ tau in target..(target - elapsed),
        nativeSharpSourceTimeJet hT tower nu tau) :=
    hprimitive.comp (continuous_const.sub continuous_id)
  unfold nativeSharpSourceFirstClockMoment
  refine hreflected.neg.congr (fun elapsed ↦ ?_)
  change -(∫ tau in target..(target - elapsed),
      nativeSharpSourceTimeJet hT tower nu tau) = _
  rw [intervalIntegral.integral_symm (target - elapsed) target]
  simp

/-- The currently owned velocity/time-jet service bounds the first clock moment without
collapsing its time interval.  This is the exact norm population exposed by the first reflection.
-/
theorem norm_nativeSharpSourceFirstClockMoment_le_velocity_timeJet_service
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (target elapsed : ℝ) (helapsed : 0 ≤ elapsed) :
    ‖nativeSharpSourceFirstClockMoment hT tower nu target elapsed‖ ≤
      ∫ tau in (target - elapsed)..target,
        2 * (23328 * periodicH3EmbeddingConstant) *
          ‖weightedPathExtension hT base tau‖ *
          ‖weightedPathExtension hT
            (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu)
            tau‖ := by
  have hvelocity : Continuous (fun tau : ℝ ↦
      weightedPathExtension hT base tau) :=
    (weightedPathExtension hT base).continuous
  have htimeJet : Continuous (fun tau : ℝ ↦
      weightedPathExtension hT
        (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu)
        tau) :=
    (weightedPathExtension hT
      (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu)).continuous
  have hservice : Continuous (fun tau : ℝ ↦
      2 * (23328 * periodicH3EmbeddingConstant) *
        ‖weightedPathExtension hT base tau‖ *
        ‖weightedPathExtension hT
          (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu)
          tau‖) :=
    ((continuous_const.mul hvelocity.norm).mul htimeJet.norm)
  unfold nativeSharpSourceFirstClockMoment
  apply intervalIntegral.norm_integral_le_of_norm_le
    (sub_le_self target helapsed)
  · exact Filter.Eventually.of_forall fun tau _ ↦
      norm_nativeSharpSourceTimeJet_le_velocity_mul_timeJet hT tower nu tau
  · exact hservice.intervalIntegrable _ _

/-- **Local first-moment scaling.**  On every fixed finite elapsed aperture, continuity of the
genuine source jet supplies a finite constant for which the reflected moment is at most linear
in elapsed time.  The constant belongs to that aperture and is not terminal-uniform. -/
theorem exists_norm_nativeSharpSourceFirstClockMoment_le_const_mul_elapsed
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (target horizon : ℝ) (hhorizon : 0 ≤ horizon) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ elapsed ∈ Icc (0 : ℝ) horizon,
      ‖nativeSharpSourceFirstClockMoment hT tower nu target elapsed‖ ≤ C * elapsed := by
  let jet : ℝ → PeriodicVectorWeightedSobolev 2 :=
    nativeSharpSourceTimeJet hT tower nu
  have hjet : Continuous jet := continuous_nativeSharpSourceTimeJet hT tower nu
  have hcompact : IsCompact (Icc (target - horizon) target) := isCompact_Icc
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hcompact.bddAbove_image hjet.norm.continuousOn)
  have hCpoint : ∀ tau ∈ Icc (target - horizon) target, ‖jet tau‖ ≤ C := by
    intro tau htau
    exact hC ‖jet tau‖ ⟨tau, htau, rfl⟩
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg (jet target)).trans
      (hCpoint target ⟨sub_le_self target hhorizon, le_rfl⟩)
  refine ⟨C, hCnonneg, ?_⟩
  intro elapsed helapsed
  have htimes : target - elapsed ≤ target := sub_le_self target helapsed.1
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := jet) (C := C) (a := target - elapsed) (b := target) (by
      intro tau htau
      rw [uIoc_of_le htimes] at htau
      apply hCpoint tau
      constructor
      · linarith [helapsed.2, htau.1]
      · exact htau.2)
  simpa only [nativeSharpSourceFirstClockMoment, jet,
    abs_of_nonneg helapsed.1, sub_sub_cancel] using hraw

/-- The heat-transported frozen source coefficient is continuous in elapsed time. -/
theorem continuous_heatTransported_frozenSharpSource
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (nu : ℝ≥0) (target : ℝ) (k : SpatialFrequency) :
    Continuous (fun elapsed : ℝ ↦
      heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
        (sharpNonlinearSource (weightedPathExtension hT base target)) k) := by
  rw [show (fun elapsed : ℝ ↦
      heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
        (sharpNonlinearSource (weightedPathExtension hT base target)) k) =
      (fun elapsed : ℝ ↦
        (heatStokesMultiplier (nu : ℝ) elapsed k : ℂ) •
          heatTransportedH2SourceCurlCoefficient (nu : ℝ) 0
            (sharpNonlinearSource (weightedPathExtension hT base target)) k) by
    funext elapsed
    exact heatTransportedH2SourceCurlCoefficient_eq_clock_smul_zero
      (nu : ℝ) elapsed
      (sharpNonlinearSource (weightedPathExtension hT base target)) k]
  have hclock : Continuous (fun elapsed : ℝ ↦
      heatStokesMultiplier (nu : ℝ) elapsed k) := by
    unfold heatStokesMultiplier
    fun_prop
  exact (Complex.continuous_ofReal.comp hclock).smul continuous_const

/-- The heat-transported first source moment is continuous in elapsed time. -/
theorem continuous_heatTransported_nativeSharpSourceFirstClockMoment
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (target : ℝ) (k : SpatialFrequency) :
    Continuous (fun elapsed : ℝ ↦
      heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
        (nativeSharpSourceFirstClockMoment hT tower nu target elapsed) k) := by
  have hmoment := continuous_nativeSharpSourceFirstClockMoment hT tower nu target
  have hclockReal : Continuous (fun elapsed : ℝ ↦
      heatStokesMultiplier (nu : ℝ) elapsed k) := by
    unfold heatStokesMultiplier
    fun_prop
  have hcoefficient : Continuous (fun elapsed : ℝ ↦
      heatTransportedH2SourceCoefficient (nu : ℝ) elapsed
        (nativeSharpSourceFirstClockMoment hT tower nu target elapsed) k) := by
    apply continuous_pi
    intro component
    have hcomponent : Continuous (fun elapsed : ℝ ↦
        nativeSharpSourceFirstClockMoment hT tower nu target elapsed component) :=
      (continuous_apply component).comp hmoment
    have heval : Continuous (fun elapsed : ℝ ↦
        nativeSharpSourceFirstClockMoment hT tower nu target elapsed component k) :=
      (lp.evalCLM ℂ (fun _ : SpatialFrequency ↦ ℂ) 2 k).continuous.comp hcomponent
    simp only [heatTransportedH2SourceCoefficient,
      weightedSobolevRawCoefficients_apply]
    exact (Complex.continuous_ofReal.comp hclockReal).mul
      (continuous_const.mul heval)
  exact (frequencyCurlMultiplierCLM k).continuous.comp hcoefficient

/-! ## Exact first transported clock-moment identity -/

/-- **First transported source clock moment.**  The elapsed integral of the reflected nonlinear
source is exactly the existing frozen heat-boundary/resolvent action minus the nested,
heat-transported genuine source-jet moment.  All spatial-frequency orientation remains signed;
no coefficient norm has occurred. -/
theorem intervalIntegral_heatTransported_reflectedSharpSource_eq_frozenBoundary_sub_firstClockRemainder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {target horizon : ℝ} (hhorizon : 0 ≤ horizon)
    (hbefore : horizon < target) (htarget : target < T)
    (k : SpatialFrequency) :
    (∫ elapsed in (0 : ℝ)..horizon,
      heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
        (sharpNonlinearSource
          (weightedPathExtension hT base (target - elapsed))) k) =
      frozenH2SourceCurlBoundaryAction (nu : ℝ) horizon
          (sharpNonlinearSource (weightedPathExtension hT base target)) k -
        nativeSharpSourceFirstClockResolventRemainder
          hT tower nu target horizon k := by
  have hfrozen : IntervalIntegrable (fun elapsed : ℝ ↦
      heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
        (sharpNonlinearSource (weightedPathExtension hT base target)) k)
      volume 0 horizon :=
    (continuous_heatTransported_frozenSharpSource hT nu target k).intervalIntegrable _ _
  have hremainder : IntervalIntegrable (fun elapsed : ℝ ↦
      heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
        (nativeSharpSourceFirstClockMoment hT tower nu target elapsed) k)
      volume 0 horizon :=
    (continuous_heatTransported_nativeSharpSourceFirstClockMoment
      hT tower nu target k).intervalIntegrable _ _
  calc
    (∫ elapsed in (0 : ℝ)..horizon,
      heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
        (sharpNonlinearSource
          (weightedPathExtension hT base (target - elapsed))) k) =
        ∫ elapsed in (0 : ℝ)..horizon,
          (heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
              (sharpNonlinearSource (weightedPathExtension hT base target)) k -
            heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
              (nativeSharpSourceFirstClockMoment hT tower nu target elapsed) k) := by
      apply intervalIntegral.integral_congr
      intro elapsed helapsed
      rw [uIcc_of_le hhorizon] at helapsed
      exact heatTransported_reflectedSharpSource_eq_frozen_sub_firstClockMoment
        hT tower nu hnu initial hfixed hreal hhorizon helapsed hbefore htarget k
    _ =
        (∫ elapsed in (0 : ℝ)..horizon,
          heatTransportedH2SourceCurlCoefficient (nu : ℝ) elapsed
            (sharpNonlinearSource (weightedPathExtension hT base target)) k) -
          nativeSharpSourceFirstClockResolventRemainder
            hT tower nu target horizon k := by
      rw [intervalIntegral.integral_sub hfrozen hremainder]
      rfl
    _ =
        frozenH2SourceCurlBoundaryAction (nu : ℝ) horizon
            (sharpNonlinearSource (weightedPathExtension hT base target)) k -
          nativeSharpSourceFirstClockResolventRemainder
            hT tower nu target horizon k := by
      rw [intervalIntegral_heatTransportedH2SourceCurlCoefficient_eq_boundaryAction
        hnu horizon
        (sharpNonlinearSource (weightedPathExtension hT base target)) k]

section Audit

#print axioms nativeSharpSourceFirstClockMoment_eq_sub
#print axioms heatTransported_reflectedSharpSource_eq_frozen_sub_firstClockMoment
#print axioms norm_nativeSharpSourceFirstClockMoment_le_velocity_timeJet_service
#print axioms exists_norm_nativeSharpSourceFirstClockMoment_le_const_mul_elapsed
#print axioms intervalIntegral_heatTransported_reflectedSharpSource_eq_frozenBoundary_sub_firstClockRemainder

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalSourceClockMoment
