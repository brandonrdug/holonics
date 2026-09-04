import ElementaryHolonics.Millennium.NavierStokesCriticalTimeReflection
import ElementaryHolonics.Millennium.NavierStokesOpenWeightedPathPassage
import ElementaryHolonics.Millennium.NavierStokesWeightedDuhamelDifference
import ElementaryHolonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap

/-!
# The exact PDE time jet of the critical nonlinear source

**[proved-derived; formal-checked]**  The coherent smooth restart tower already supplies the
genuine native `H3` derivative of its velocity path.  This module differentiates the native
Leray quadratic *before* any coefficient norm.  Its derivative is the two oriented incidences

`B(u_t, u) + B(u, u_t)`.

The Banach-valued fundamental theorem of calculus then reconstructs every strict-interior source
increment as the signed integral of that exact PDE time jet.  The final theorem identifies both
boundary sources with the actual open solution on a local restart aperture.

No norm, Dini, Carleson, terminal-uniform, or critical-vorticity estimate is asserted.  In
particular, the identity retains the exact missing current whose terminal-uniform bound would
still have to be proved.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesCriticalSourceTimeJet

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalTimeReflection
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesOpenWeightedPathPassage
open Soma.Holonics.Millennium.NavierStokesRestartSeam
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The oriented native source time jet -/

/-- The exact two-incidence Leibniz current obtained by inserting the native PDE time jet in
each input port of the Leray bilinear source.  Endpoint extension makes this a total real-time
function without changing its strict-interior reading. -/
def nativeSharpSourceTimeJet
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (t : ℝ) : PeriodicVectorWeightedSobolev 2 :=
  let velocity := weightedPathExtension hT base t
  let timeJet := weightedPathExtension hT
    (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu) t
  weightedLerayDivergenceConvolution timeJet velocity +
    weightedLerayDivergenceConvolution velocity timeJet

/-- The exact source time jet is continuous on the totalized real-time chart. -/
theorem continuous_nativeSharpSourceTimeJet
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) :
    Continuous (nativeSharpSourceTimeJet hT tower nu) := by
  let B : PeriodicVectorWeightedSobolev 3 →L[ℝ]
      PeriodicVectorWeightedSobolev 3 →L[ℝ]
        PeriodicVectorWeightedSobolev 2 :=
    weightedLerayDivergenceConvolutionContinuous.bilinearRestrictScalars ℝ
  have hu : Continuous (fun t ↦ weightedPathExtension hT base t) :=
    (weightedPathExtension hT base).continuous
  have hut : Continuous (fun t ↦ weightedPathExtension hT
      (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu) t) :=
    (weightedPathExtension hT
      (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu)).continuous
  have hleft : Continuous (fun t ↦
      B (weightedPathExtension hT
          (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu) t)
        (weightedPathExtension hT base t)) :=
    (B.continuous.comp hut).clm_apply hu
  have hright : Continuous (fun t ↦
      B (weightedPathExtension hT base t)
        (weightedPathExtension hT
          (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu) t)) :=
    (B.continuous.comp hu).clm_apply hut
  change Continuous
    ((fun t ↦ weightedLerayDivergenceConvolution
        (weightedPathExtension hT
          (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu) t)
        (weightedPathExtension hT base t)) +
      (fun t ↦ weightedLerayDivergenceConvolution
        (weightedPathExtension hT base t)
        (weightedPathExtension hT
          (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu) t)))
  simpa only [B,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    weightedLerayDivergenceConvolutionContinuous_apply] using hleft.add hright

/-- **Exact nonlinear-source PDE derivative.**  The source derivative is obtained by placing
the genuine native velocity time jet in the two ordered bilinear ports. -/
theorem CoherentWeightedSmoothPathTower.hasDerivAt_sharpNonlinearSource
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau ↦ sharpNonlinearSource (weightedPathExtension hT base tau))
      (nativeSharpSourceTimeJet hT tower nu t) t := by
  let B : PeriodicVectorWeightedSobolev 3 →L[ℝ]
      PeriodicVectorWeightedSobolev 3 →L[ℝ]
        PeriodicVectorWeightedSobolev 2 :=
    weightedLerayDivergenceConvolutionContinuous.bilinearRestrictScalars ℝ
  let jetPath :=
    CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu
  have hu :=
    CoherentWeightedSmoothPathTower.hasDerivAt_weightedPathExtension_nativeProjectedTimeDerivative
      hT tower nu hnu initial hfixed hreal ht
  have hoperator : HasDerivAt
      (fun tau ↦ B (weightedPathExtension hT base tau))
      (B (weightedPathExtension hT jetPath t)) t := by
    change HasDerivAt
      (B ∘ fun tau ↦ weightedPathExtension hT base tau)
      (B (weightedPathExtension hT jetPath t)) t
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one] using
        (B.hasFDerivAt.comp t hu.hasFDerivAt).hasDerivAt
  have hsource := hoperator.clm_apply hu
  simpa only [sharpNonlinearSource, nativeSharpSourceTimeJet, jetPath, B,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    weightedLerayDivergenceConvolutionContinuous_apply] using hsource

/-! ## Signed time reconstruction -/

/-- Every source increment strictly inside a native restart aperture is the signed Bochner
integral of the exact two-incidence PDE time jet. -/
theorem intervalIntegral_nativeSharpSourceTimeJet_eq_sub
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
        nativeSharpSourceTimeJet hT tower nu tau) =
      sharpNonlinearSource (weightedPathExtension hT base targetTime) -
        sharpNonlinearSource (weightedPathExtension hT base sourceTime) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro tau htau
    rw [uIcc_of_le htimes] at htau
    exact CoherentWeightedSmoothPathTower.hasDerivAt_sharpNonlinearSource
      hT tower nu hnu initial hfixed hreal
      ⟨hsource.trans_le htau.1, htau.2.trans_lt htarget⟩
  · exact (continuous_nativeSharpSourceTimeJet hT tower nu).intervalIntegrable _ _

/-! ## Strict-interior Dini consequence -/

/-- The source-increment Dini population attached to one native restart path.  This is kept
separate from terminal control: its horizon must lie strictly inside the one addressed native
clock. -/
def nativeSharpSourceDiniFiber
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (targetTime horizon : ℝ) : ℝ≥0∞ :=
  ∫⁻ elapsed in Ioo (0 : ℝ) horizon,
    ENNReal.ofReal
      (‖sharpNonlinearSource (weightedPathExtension hT base (targetTime - elapsed)) -
          sharpNonlinearSource (weightedPathExtension hT base targetTime)‖ / elapsed)

/-- **Unconditional local Dini finiteness.**  The continuous exact PDE source jet is bounded on
every compact interval strictly inside one native restart aperture.  Its signed FTC identity
therefore cancels the endpoint denominator.  The estimate is deliberately local: it supplies no
bound uniform in a family of restart clocks approaching an exterior terminal time. -/
theorem nativeSharpSourceDiniFiber_ne_top
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {targetTime horizon : ℝ}
    (hhorizon : 0 < horizon) (hbefore : horizon < targetTime)
    (htarget : targetTime < T) :
    nativeSharpSourceDiniFiber hT (base := base) targetTime horizon ≠ ∞ := by
  let jet : ℝ → PeriodicVectorWeightedSobolev 2 :=
    nativeSharpSourceTimeJet hT tower nu
  have hjet : Continuous jet := continuous_nativeSharpSourceTimeJet hT tower nu
  have hcompact : IsCompact (Icc (targetTime - horizon) targetTime) := isCompact_Icc
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hcompact.bddAbove_image hjet.norm.continuousOn)
  have hCpoint : ∀ tau ∈ Icc (targetTime - horizon) targetTime,
      ‖jet tau‖ ≤ C := by
    intro tau htau
    exact hC ‖jet tau‖ ⟨tau, htau, rfl⟩
  have hCnonneg : 0 ≤ C := by
    exact (norm_nonneg (jet targetTime)).trans
      (hCpoint targetTime ⟨sub_le_self _ hhorizon.le, le_rfl⟩)
  have hquotient : ∀ elapsed ∈ Ioo (0 : ℝ) horizon,
      ‖sharpNonlinearSource
            (weightedPathExtension hT base (targetTime - elapsed)) -
          sharpNonlinearSource (weightedPathExtension hT base targetTime)‖ /
          elapsed ≤ C := by
    intro elapsed helapsed
    have hsourcePos : 0 < targetTime - elapsed := by
      exact sub_pos.mpr (helapsed.2.trans hbefore)
    have hsourceTarget : targetTime - elapsed ≤ targetTime :=
      sub_le_self _ helapsed.1.le
    have hftc := intervalIntegral_nativeSharpSourceTimeJet_eq_sub
      hT tower nu hnu initial hfixed hreal hsourcePos hsourceTarget htarget
    have hbound :
        ‖∫ tau in (targetTime - elapsed)..targetTime, jet tau‖ ≤
          C * elapsed := by
      have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := jet) (C := C) (a := targetTime - elapsed) (b := targetTime) (by
          intro tau htau
          rw [uIoc_of_le hsourceTarget] at htau
          apply hCpoint tau
          constructor
          · have hlower : targetTime - horizon < targetTime - elapsed := by
              linarith [helapsed.2]
            exact hlower.le.trans htau.1.le
          · exact htau.2)
      simpa [abs_of_pos helapsed.1] using hraw
    have hincrement :
        ‖sharpNonlinearSource
              (weightedPathExtension hT base (targetTime - elapsed)) -
            sharpNonlinearSource (weightedPathExtension hT base targetTime)‖ ≤
          C * elapsed := by
      rw [← norm_neg]
      simpa only [neg_sub] using hftc.symm ▸ hbound
    exact (div_le_iff₀ helapsed.1).2 hincrement
  have hlintegral :
      nativeSharpSourceDiniFiber hT (base := base) targetTime horizon ≤
        ∫⁻ _elapsed in Ioo (0 : ℝ) horizon, ENNReal.ofReal C := by
    unfold nativeSharpSourceDiniFiber
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with elapsed helapsed
    exact ENNReal.ofReal_le_ofReal (hquotient elapsed helapsed)
  apply ne_of_lt
  exact hlintegral.trans_lt (by
    rw [setLIntegral_const]
    simp only [Real.volume_Ioo, sub_zero]
    exact ENNReal.mul_lt_top (ENNReal.ofReal_lt_top)
      (ENNReal.ofReal_lt_top))

/-! ## Actual open-solution boundary identification -/

/-- On any strict local restart subaperture, both boundary faces in the PDE source-jet FTC are
literally the sharp nonlinear sources of the actual open solution.  This is an actual-source
identity, not a comparison with a separately postulated path. -/
theorem intervalIntegral_nativeSharpSourceTimeJet_eq_openSharpSource_sub
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    {S sourceTime targetTime : ℝ}
    (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime ≤ S) :
    let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
    (∫ tau in sourceTime..targetTime,
        nativeSharpSourceTimeJet
          (openSliceNativeClock_pos solution hnu t₀).le
          carrier.tower (Real.toNNReal nu) tau) =
      sharpNonlinearSource
          (openVelocityWeightedH3State solution
            ⟨t₀.1 + targetTime, by
              constructor
              · linarith [t₀.2.1, hsource, htimes]
              · have hoverlapRemaining :
                    openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
                  unfold openSliceNativeOverlap restartCommonLifespan
                  exact min_le_left _ _
                linarith⟩) -
        sharpNonlinearSource
          (openVelocityWeightedH3State solution
            ⟨t₀.1 + sourceTime, by
              constructor
              · linarith [t₀.2.1, hsource]
              · have hoverlapRemaining :
                    openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
                  unfold openSliceNativeOverlap restartCommonLifespan
                  exact min_le_left _ _
                linarith⟩) := by
  dsimp only
  let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
  have htargetClock : targetTime < openSliceNativeClock solution hnu t₀ := by
    exact lt_of_le_of_lt htarget
      (hSoverlap.trans_le
        (openSliceNativeOverlap_le_clock solution hnu t₀))
  have hsourceS : sourceTime ≤ S := htimes.trans htarget
  have hsourceClock : sourceTime < openSliceNativeClock solution hnu t₀ :=
    lt_of_le_of_lt hsourceS
      (hSoverlap.trans_le
        (openSliceNativeOverlap_le_clock solution hnu t₀))
  have hftc := intervalIntegral_nativeSharpSourceTimeJet_eq_sub
    (openSliceNativeClock_pos solution hnu t₀).le carrier.tower
    (Real.toNNReal nu) (real_toNNReal_pos hnu)
    (openVelocityWeightedH3State solution t₀)
    carrier.fixed carrier.fourierReal hsource htimes htargetClock
  have htargetState :
      weightedPathExtension
          (openSliceNativeClock_pos solution hnu t₀).le carrier.path targetTime =
        openVelocityWeightedH3State solution
          ⟨t₀.1 + targetTime, by
            constructor
            · linarith [t₀.2.1, hsource, htimes]
            · have hoverlapRemaining :
                  openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
                unfold openSliceNativeOverlap restartCommonLifespan
                exact min_le_left _ _
              linarith⟩ := by
    rw [weightedPathExtension_of_mem
      (openSliceNativeClock_pos solution hnu t₀).le carrier.path
      ⟨hsource.le.trans htimes, htargetClock.le⟩]
    let tau : Icc (0 : ℝ) S :=
      ⟨targetTime, hsource.le.trans htimes, htarget⟩
    have hopen := actualOpenWeightedH3Path_apply
      solution hnu t₀ S hS hSoverlap tau
    change carrier.path
      ⟨targetTime, hsource.le.trans htimes,
        htarget.trans
          ((le_of_lt hSoverlap).trans
            (openSliceNativeOverlap_le_clock solution hnu t₀))⟩ = _ at hopen
    exact hopen
  have hsourceState :
      weightedPathExtension
          (openSliceNativeClock_pos solution hnu t₀).le carrier.path sourceTime =
        openVelocityWeightedH3State solution
          ⟨t₀.1 + sourceTime, by
            constructor
            · linarith [t₀.2.1, hsource]
            · have hoverlapRemaining :
                  openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
                unfold openSliceNativeOverlap restartCommonLifespan
                exact min_le_left _ _
              linarith⟩ := by
    rw [weightedPathExtension_of_mem
      (openSliceNativeClock_pos solution hnu t₀).le carrier.path
      ⟨hsource.le, hsourceClock.le⟩]
    let tau : Icc (0 : ℝ) S := ⟨sourceTime, hsource.le, hsourceS⟩
    have hopen := actualOpenWeightedH3Path_apply
      solution hnu t₀ S hS hSoverlap tau
    change carrier.path
      ⟨sourceTime, hsource.le,
        hsourceS.trans
          ((le_of_lt hSoverlap).trans
            (openSliceNativeOverlap_le_clock solution hnu t₀))⟩ = _ at hopen
    exact hopen
  simpa only [carrier, htargetState, hsourceState] using hftc

section Audit

#print axioms continuous_nativeSharpSourceTimeJet
#print axioms CoherentWeightedSmoothPathTower.hasDerivAt_sharpNonlinearSource
#print axioms intervalIntegral_nativeSharpSourceTimeJet_eq_sub
#print axioms nativeSharpSourceDiniFiber_ne_top
#print axioms intervalIntegral_nativeSharpSourceTimeJet_eq_openSharpSource_sub

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalSourceTimeJet
