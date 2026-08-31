import ElementaryHolonics.Millennium.NavierStokesCriticalSourceTimeJet

/-!
# The native source Dini fibre returns to the actual open solution

**[proved-derived; formal-checked]**  The source time-jet owner proves local Dini finiteness on
the native restart path selected by an actual strict-interior solution slice.  This module closes
the remaining return passage: on every closed subaperture of the uniqueness overlap, the native
source-increment fibre is exactly the `openSharpSourceDiniReconstructionFiber` of the literal
open solution, with the restart clock shift retained.

The resulting finiteness theorem is local to one admitted restart aperture.  It neither supplies
a bound uniform as the exterior terminal time is approached nor inhabits critical terminal
control.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesOpenSourceDiniPassage

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalSourceTimeJet
open Soma.Holonics.Millennium.NavierStokesCriticalTimeReflection
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesOpenWeightedPathPassage
open Soma.Holonics.Millennium.NavierStokesRestartSeam
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
open Soma.Holonics.Millennium.NavierStokesWeightedCommonApertureUniqueness
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture

/-! ## Exact state return on the native overlap -/

/-- Every native restart state in an admitted overlap subaperture is literally the weighted
`H3` state of the actual open solution at the shifted physical time. -/
theorem weightedPathExtension_openSliceCarrier_eq_openVelocityWeightedH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    {S relativeTime : ℝ} (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀)
    (hrelative : relativeTime ∈ Icc (0 : ℝ) S) :
    let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
    weightedPathExtension (openSliceNativeClock_pos solution hnu t₀).le
        carrier.path relativeTime =
      openVelocityWeightedH3State solution
        ⟨t₀.1 + relativeTime, by
          constructor
          · linarith [t₀.2.1, hrelative.1]
          · have hoverlapRemaining :
                openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
              unfold openSliceNativeOverlap restartCommonLifespan
              exact min_le_left _ _
            linarith [hrelative.2, hSoverlap, hoverlapRemaining]
        ⟩ := by
  dsimp only
  let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
  have hSclock : S ≤ openSliceNativeClock solution hnu t₀ :=
    (le_of_lt hSoverlap).trans
      (openSliceNativeOverlap_le_clock solution hnu t₀)
  have hrelativeClock : relativeTime ∈
      Icc (0 : ℝ) (openSliceNativeClock solution hnu t₀) :=
    ⟨hrelative.1, hrelative.2.trans hSclock⟩
  have hrelativeCarrier : relativeTime ∈
      Icc (0 : ℝ)
        (weightedRestartTimeFromCap nu
          ‖openVelocityWeightedH3State solution t₀‖) := by
    simpa only [openSliceNativeClock] using hrelativeClock
  have hSCarrier : S ≤
      weightedRestartTimeFromCap nu
        ‖openVelocityWeightedH3State solution t₀‖ := by
    simpa only [openSliceNativeClock] using hSclock
  rw [weightedPathExtension_of_mem
    (openSliceNativeClock_pos solution hnu t₀).le carrier.path hrelativeClock]
  have hactual := actualOpenWeightedH3Path_apply
    solution hnu t₀ S hS hSoverlap ⟨relativeTime, hrelative⟩
  change carrier.path ⟨relativeTime, hrelativeCarrier⟩ = _
  change
    (weightedH3PathTimeRestrict hSCarrier carrier.path)
        ⟨relativeTime, hrelative⟩ = _ at hactual
  rw [weightedH3PathTimeRestrict_apply] at hactual
  exact hactual

/-! ## Equality of the native and actual source fibres -/

/-- On an admitted restart subaperture, the native source Dini fibre is exactly the literal
actual-open-solution fibre at the clock-shifted target.  The equality is at the complete
`ENNReal` reconstruction fibre, so a possible infinite value is not discarded. -/
theorem openSharpSourceDiniReconstructionFiber_eq_native
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    {S targetTime horizon : ℝ} (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀)
    (htarget : targetTime ∈ Icc (0 : ℝ) S)
    (hhorizon : 0 < horizon) (hbefore : horizon < targetTime) :
    let absoluteTarget : ℝ := t₀.1 + targetTime
    let habsolute : absoluteTarget ∈ Ioo (0 : ℝ) T := by
      constructor
      · linarith [t₀.2.1, htarget.1]
      · have hoverlapRemaining :
            openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
          unfold openSliceNativeOverlap restartCommonLifespan
          exact min_le_left _ _
        linarith [htarget.2, hSoverlap, hoverlapRemaining]
    let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
    openSharpSourceDiniReconstructionFiber (target := absoluteTarget)
        (horizon := horizon) solution habsolute
        (by dsimp only [absoluteTarget]; linarith [t₀.2.1, hbefore]) =
      nativeSharpSourceDiniFiber
        (openSliceNativeClock_pos solution hnu t₀).le
        (base := carrier.path) targetTime horizon := by
  dsimp only
  let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
  let absoluteTarget : ℝ := t₀.1 + targetTime
  have habsolute : absoluteTarget ∈ Ioo (0 : ℝ) T := by
    constructor
    · dsimp only [absoluteTarget]
      linarith [t₀.2.1, htarget.1]
    · have hoverlapRemaining :
          openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
        unfold openSliceNativeOverlap restartCommonLifespan
        exact min_le_left _ _
      dsimp only [absoluteTarget]
      linarith [htarget.2, hSoverlap, hoverlapRemaining]
  have hhorizonAbsolute : horizon < absoluteTarget := by
    dsimp only [absoluteTarget]
    linarith [t₀.2.1, hbefore]
  unfold openSharpSourceDiniReconstructionFiber nativeSharpSourceDiniFiber
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with elapsed helapsed
  rw [openSharpSourceElapsedIncrement_eq solution habsolute
    hhorizonAbsolute helapsed]
  have hearly : targetTime - elapsed ∈ Icc (0 : ℝ) S := by
    constructor
    · linarith [helapsed.2, hbefore]
    · linarith [helapsed.1, htarget.2]
  have htargetState :=
    weightedPathExtension_openSliceCarrier_eq_openVelocityWeightedH3State
      solution hnu t₀ hS hSoverlap htarget
  have hearlyState :=
    weightedPathExtension_openSliceCarrier_eq_openVelocityWeightedH3State
      solution hnu t₀ hS hSoverlap hearly
  unfold openSharpNonlinearSourceIncrement
  have htargetState' :
      weightedPathExtension (openSliceNativeClock_pos solution hnu t₀).le
          carrier.path targetTime =
        openVelocityWeightedH3State solution ⟨absoluteTarget, habsolute⟩ := by
    simpa only [carrier, absoluteTarget] using htargetState
  have hearlyAbsolute : absoluteTarget - elapsed ∈ Ioo (0 : ℝ) T := by
    constructor
    · dsimp only [absoluteTarget]
      linarith [t₀.2.1, helapsed.2, hbefore]
    · dsimp only [absoluteTarget]
      linarith [habsolute.2, helapsed.1]
  have hearlyState' :
      weightedPathExtension (openSliceNativeClock_pos solution hnu t₀).le
          carrier.path (targetTime - elapsed) =
        openVelocityWeightedH3State solution
          ⟨absoluteTarget - elapsed, hearlyAbsolute⟩ := by
    convert hearlyState using 1 <;> dsimp only [absoluteTarget] <;> ring_nf
  rw [← htargetState', ← hearlyState']

/-! ## Unconditional local finiteness on the actual source object -/

/-- The actual open-solution source Dini fibre is finite on every clock-shifted target/horizon
which lies inside one admitted native restart subaperture.  This is the local result returned by
the genuine PDE source jet; the restart overlap remains part of the statement. -/
theorem openSharpSourceDiniReconstructionFiber_ne_top_of_nativeOverlap
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    {S targetTime horizon : ℝ} (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀)
    (htarget : targetTime ∈ Icc (0 : ℝ) S)
    (hhorizon : 0 < horizon) (hbefore : horizon < targetTime) :
    let absoluteTarget : ℝ := t₀.1 + targetTime
    let habsolute : absoluteTarget ∈ Ioo (0 : ℝ) T := by
      constructor
      · linarith [t₀.2.1, htarget.1]
      · have hoverlapRemaining :
            openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
          unfold openSliceNativeOverlap restartCommonLifespan
          exact min_le_left _ _
        linarith [htarget.2, hSoverlap, hoverlapRemaining]
    openSharpSourceDiniReconstructionFiber (target := absoluteTarget)
        (horizon := horizon) solution habsolute
        (by dsimp only [absoluteTarget]; linarith [t₀.2.1, hbefore]) ≠ ∞ := by
  dsimp only
  let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
  rw [openSharpSourceDiniReconstructionFiber_eq_native
    solution hnu t₀ hS hSoverlap htarget hhorizon hbefore]
  apply nativeSharpSourceDiniFiber_ne_top
    (openSliceNativeClock_pos solution hnu t₀).le carrier.tower
    (Real.toNNReal nu) (real_toNNReal_pos hnu)
    (openVelocityWeightedH3State solution t₀)
    carrier.fixed carrier.fourierReal hhorizon hbefore
  exact lt_of_le_of_lt htarget.2
    (hSoverlap.trans_le
      (openSliceNativeOverlap_le_clock solution hnu t₀))

section Audit

#print axioms weightedPathExtension_openSliceCarrier_eq_openVelocityWeightedH3State
#print axioms openSharpSourceDiniReconstructionFiber_eq_native
#print axioms openSharpSourceDiniReconstructionFiber_ne_top_of_nativeOverlap

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenSourceDiniPassage
