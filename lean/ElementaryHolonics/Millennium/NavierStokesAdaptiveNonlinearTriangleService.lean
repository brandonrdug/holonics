import ElementaryHolonics.Millennium.NavierStokesAdaptiveOffDiagonalMildHeatTransport
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionProjection

/-!
# Adaptive nonlinear triangle service by the reciprocal shell clock

**[proved-derived; formal-checked]**  The adaptive off-diagonal Duhamel triangle is rotated
without changing its chronology:
`a ≤ sourceTime ≤ targetTime ≤ adaptiveStart`.  Integrating the genuine heat
multiplier in target time first pays every mode by the reciprocal clock of its dyadic shell.

The result retains the actual nonlinear vorticity-mode population at every source time.  The
finite scale word is summed term by term, with no depth multiplier.  A final comparison records
the strictly coarser compact-time source envelope which remains the existing conditional
summability boundary; no terminal reconstruction conclusion is asserted.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearTriangleService

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveClockMatchedPacking
open Soma.Holonics.Millennium.NavierStokesAdaptiveOffDiagonalMildHeatTransport
open Soma.Holonics.Millennium.NavierStokesClockWeightedSpatialBandPacking
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOffDiagonalMildHeatTransport
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceChronology
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceClockBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

set_option maxHeartbeats 2400000

/-! ## A continuous causal-triangle rotation -/

/-- Fubini rotation of a continuous scalar population on the ordered triangle
`a ≤ sourceTime ≤ targetTime ≤ horizon`.  The zero-padded rectangle is only the proof
chart; both returned faces retain the exact causal triangle. -/
theorem intervalIntegral_causal_triangle_swap
    {a horizon : ℝ} (hah : a ≤ horizon) (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    (∫ targetTime in a..horizon,
      ∫ sourceTime in a..targetTime, f targetTime sourceTime) =
      ∫ sourceTime in a..horizon,
        ∫ targetTime in sourceTime..horizon, f targetTime sourceTime := by
  let padded : ℝ → ℝ → ℝ := fun targetTime sourceTime ↦
    if sourceTime ≤ targetTime then f targetTime sourceTime else 0
  have hpaddedMeasurable : Measurable (Function.uncurry padded) := by
    apply Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    · exact hf.measurable
    · exact measurable_const
  have hfRectangle : IntegrableOn (Function.uncurry f)
      (uIoc a horizon ×ˢ uIoc a horizon) := by
    exact (ContinuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc) hf.continuousOn).mono_set
        (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hpaddedRectangle : IntegrableOn (Function.uncurry padded)
      (uIoc a horizon ×ˢ uIoc a horizon) := by
    unfold IntegrableOn at hfRectangle ⊢
    apply hfRectangle.mono
    · exact hpaddedMeasurable.aestronglyMeasurable.restrict
    · filter_upwards with times
      dsimp [padded, Function.uncurry]
      split_ifs <;> simp
  have hleft (targetTime : ℝ) (htarget : targetTime ∈ Icc a horizon) :
      (∫ sourceTime in a..targetTime, f targetTime sourceTime) =
        ∫ sourceTime in a..horizon, padded targetTime sourceTime := by
    have hfSection : Continuous (f targetTime) := hf.uncurry_left targetTime
    have hpaddedLeft : IntervalIntegrable (padded targetTime) volume a targetTime := by
      exact (hfSection.intervalIntegrable a targetTime).congr fun sourceTime hsource ↦ by
        rw [uIoc_of_le htarget.1] at hsource
        simp [padded, hsource.2]
    have hpaddedRight : IntervalIntegrable (padded targetTime) volume targetTime horizon := by
      exact IntervalIntegrable.zero.congr_uIoo fun sourceTime hsource ↦ by
        rw [uIoo_of_le htarget.2] at hsource
        simp [padded, not_le.mpr hsource.1]
    have hleftEq :
        (∫ sourceTime in a..targetTime, padded targetTime sourceTime) =
          ∫ sourceTime in a..targetTime, f targetTime sourceTime := by
      apply intervalIntegral.integral_congr
      intro sourceTime hsource
      rw [uIcc_of_le htarget.1] at hsource
      simp [padded, hsource.2]
    have hrightEq :
        (∫ sourceTime in targetTime..horizon,
          padded targetTime sourceTime) = 0 := by
      rw [← intervalIntegral.integral_zero]
      apply intervalIntegral.integral_congr_ae
      filter_upwards with sourceTime hsource
      rw [uIoc_of_le htarget.2] at hsource
      simp [padded, not_le.mpr hsource.1]
    calc
      (∫ sourceTime in a..targetTime, f targetTime sourceTime) =
          ∫ sourceTime in a..targetTime, padded targetTime sourceTime := hleftEq.symm
      _ = (∫ sourceTime in a..targetTime, padded targetTime sourceTime) +
          ∫ sourceTime in targetTime..horizon,
            padded targetTime sourceTime := by rw [hrightEq, add_zero]
      _ = ∫ sourceTime in a..horizon, padded targetTime sourceTime :=
        intervalIntegral.integral_add_adjacent_intervals hpaddedLeft hpaddedRight
  have hright (sourceTime : ℝ) (hsource : sourceTime ∈ Icc a horizon) :
      (∫ targetTime in a..horizon, padded targetTime sourceTime) =
        ∫ targetTime in sourceTime..horizon, f targetTime sourceTime := by
    have hfSection : Continuous (fun targetTime ↦ f targetTime sourceTime) :=
      hf.comp (continuous_id.prodMk continuous_const)
    have hpaddedLeft : IntervalIntegrable (padded · sourceTime) volume a sourceTime := by
      exact IntervalIntegrable.zero.congr_uIoo fun targetTime htarget ↦ by
        rw [uIoo_of_le hsource.1] at htarget
        simp [padded, not_le.mpr htarget.2]
    have hpaddedRight :
        IntervalIntegrable (padded · sourceTime) volume sourceTime horizon := by
      exact (hfSection.intervalIntegrable sourceTime horizon).congr
        fun targetTime htarget ↦ by
          rw [uIoc_of_le hsource.2] at htarget
          simp [padded, htarget.1.le]
    have hleftEq :
        (∫ targetTime in a..sourceTime, padded targetTime sourceTime) = 0 := by
      rw [← intervalIntegral.integral_zero]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(Set.countable_singleton sourceTime).ae_notMem volume] with
        targetTime hne htarget
      rw [uIoc_of_le hsource.1] at htarget
      have hlt : targetTime < sourceTime := by
        exact lt_of_le_of_ne htarget.2 (by simpa only [Set.mem_singleton_iff] using hne)
      simp [padded, not_le.mpr hlt]
    have hrightEq :
        (∫ targetTime in sourceTime..horizon, padded targetTime sourceTime) =
          ∫ targetTime in sourceTime..horizon, f targetTime sourceTime := by
      apply intervalIntegral.integral_congr
      intro targetTime htarget
      rw [uIcc_of_le hsource.2] at htarget
      simp [padded, htarget.1]
    calc
      (∫ targetTime in a..horizon, padded targetTime sourceTime) =
          (∫ targetTime in a..sourceTime, padded targetTime sourceTime) +
            ∫ targetTime in sourceTime..horizon,
              padded targetTime sourceTime :=
        (intervalIntegral.integral_add_adjacent_intervals
          hpaddedLeft hpaddedRight).symm
      _ = ∫ targetTime in sourceTime..horizon,
          padded targetTime sourceTime := by rw [hleftEq, zero_add]
      _ = ∫ targetTime in sourceTime..horizon,
          f targetTime sourceTime := hrightEq
  calc
    (∫ targetTime in a..horizon,
      ∫ sourceTime in a..targetTime, f targetTime sourceTime) =
        ∫ targetTime in a..horizon,
          ∫ sourceTime in a..horizon,
            padded targetTime sourceTime := by
      apply intervalIntegral.integral_congr
      intro targetTime htarget
      rw [uIcc_of_le hah] at htarget
      exact hleft targetTime htarget
    _ = ∫ sourceTime in a..horizon,
        ∫ targetTime in a..horizon,
          padded targetTime sourceTime :=
      MeasureTheory.intervalIntegral_intervalIntegral_swap hpaddedRectangle
    _ = ∫ sourceTime in a..horizon,
        ∫ targetTime in sourceTime..horizon,
          f targetTime sourceTime := by
      apply intervalIntegral.integral_congr
      intro sourceTime hsource
      rw [uIcc_of_le hah] at hsource
      exact hright sourceTime hsource

/-! ## Target-time heat service of one actual nonlinear source face -/

private theorem intervalIntegral_targetHeatMode_le_scaleClock
    {nu sourceTime horizon : ℝ} (hnu : 0 < nu) (hsource : sourceTime ≤ horizon)
    {scale : ℕ} {frequency : SpatialFrequency}
    (hfrequency : frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1))) :
    (∫ targetTime in sourceTime..horizon,
      heatStokesMultiplier nu (targetTime - sourceTime) frequency) ≤
        dyadicParabolicClockBudget nu scale := by
  have hreflect :
      (∫ targetTime in sourceTime..horizon,
        heatStokesMultiplier nu (targetTime - sourceTime) frequency) =
      ∫ elapsed in (0 : ℝ)..(horizon - sourceTime),
        heatStokesMultiplier nu elapsed frequency := by
    simpa only [sub_self] using
      (intervalIntegral.integral_comp_sub_right
        (fun elapsed : ℝ ↦ heatStokesMultiplier nu elapsed frequency) sourceTime
        (a := sourceTime) (b := horizon))
  rw [hreflect]
  rw [Finset.mem_union] at hfrequency
  rcases hfrequency with hfrequency | hfrequency
  · exact intervalIntegral_heatStokesMultiplier_le_dyadicParabolicClockBudget
      hnu (sub_nonneg.mpr hsource) hfrequency
  · exact (intervalIntegral_heatStokesMultiplier_le_dyadicParabolicClockBudget
      hnu (sub_nonneg.mpr hsource) hfrequency).trans
        (dyadicParabolicClockBudget_succ_le hnu scale)

private theorem intervalIntegral_offDiagonalSourceMode_le_scaleClock
    {T nu a b sourceTime horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hsource : sourceTime ≤ horizon) (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1))) :
    (∫ targetTime in sourceTime..horizon,
      |dyadicHodgeBandWeight scale frequency| *
        heatStokesMultiplier nu (targetTime - sourceTime) frequency *
          ‖compactVorticityNonlinearMode
            solution ha hab hbT frequency sourceTime‖) ≤
      dyadicParabolicClockBudget nu scale *
        (|dyadicHodgeBandWeight scale frequency| *
          ‖compactVorticityNonlinearMode
            solution ha hab hbT frequency sourceTime‖) := by
  let coefficientMass := |dyadicHodgeBandWeight scale frequency| *
    ‖compactVorticityNonlinearMode solution ha hab hbT frequency sourceTime‖
  have hclock := intervalIntegral_targetHeatMode_le_scaleClock
    hnu hsource hfrequency
  have hmass : 0 ≤ coefficientMass := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  calc
    (∫ targetTime in sourceTime..horizon,
      |dyadicHodgeBandWeight scale frequency| *
        heatStokesMultiplier nu (targetTime - sourceTime) frequency *
          ‖compactVorticityNonlinearMode
            solution ha hab hbT frequency sourceTime‖) =
      coefficientMass *
        ∫ targetTime in sourceTime..horizon,
          heatStokesMultiplier nu (targetTime - sourceTime) frequency := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro targetTime _htargetTime
      dsimp [coefficientMass]
      ring
    _ ≤ coefficientMass * dyadicParabolicClockBudget nu scale :=
      mul_le_mul_of_nonneg_left hclock hmass
    _ = dyadicParabolicClockBudget nu scale *
        (|dyadicHodgeBandWeight scale frequency| *
          ‖compactVorticityNonlinearMode
            solution ha hab hbT frequency sourceTime‖) := by
      dsimp [coefficientMass]
      ring

/-- At one retained source time, target-time integration of the exact two-shell heat population
costs one reciprocal shell clock and leaves the actual unclocked vorticity-mode mass. -/
theorem intervalIntegral_offDiagonalClockedNonlinearSourceMassAt_le_scaleClock_mul_actualSourceMass
    {T nu a b sourceTime horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hsource : sourceTime ≤ horizon) (scale : ℕ) :
    (∫ targetTime in sourceTime..horizon,
      compactOffDiagonalClockedNonlinearSourceMassAt
        solution ha hab hbT scale targetTime sourceTime) ≤
      dyadicParabolicClockBudget nu scale *
        compactSmoothDyadicVorticityNonlinearSourceMassAt
          solution ha hab hbT scale sourceTime := by
  unfold compactOffDiagonalClockedNonlinearSourceMassAt
    compactSmoothDyadicVorticityNonlinearSourceMassAt
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun frequency hfrequency ↦
      intervalIntegral_offDiagonalSourceMode_le_scaleClock
        solution hnu ha hab hbT hsource scale hfrequency
  · intro frequency _hfrequency
    exact (((continuous_const.mul (by
      unfold heatStokesMultiplier
      fun_prop)).mul continuous_const).intervalIntegrable _ _)

/-! ## Exact adaptive source receiver and finite scale word -/

/-- The source-time receiver left after the target-time heat clock has been integrated exactly.
It retains the adaptive chronology, the genuine Hodge weights, and every nonlinear mode norm. -/
def compactAdaptiveReciprocalClockNonlinearSourceContribution
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) : ℝ :=
  dyadicParabolicClockBudget nu scale *
    ∫ sourceTime in a..adaptiveSmoothDyadicTerminalWindowStart a b scale,
      compactSmoothDyadicVorticityNonlinearSourceMassAt
        solution ha hab hbT scale sourceTime

/-- Exact Fubini rotation of one adaptive nonlinear Duhamel triangle. -/
theorem compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution_eq_rotatedTriangle
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution
        solution ha hab hbT scale =
      ∫ sourceTime in a..adaptiveSmoothDyadicTerminalWindowStart a b scale,
        ∫ targetTime in sourceTime..adaptiveSmoothDyadicTerminalWindowStart a b scale,
          compactOffDiagonalClockedNonlinearSourceMassAt
            solution ha hab hbT scale targetTime sourceTime := by
  unfold compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution
    compactOffDiagonalClockedNonlinearHistoryMassAt
  exact intervalIntegral_causal_triangle_swap
    (le_adaptiveSmoothDyadicTerminalWindowStart hab scale)
    (compactOffDiagonalClockedNonlinearSourceMassAt solution ha hab hbT scale)
    (continuous_uncurry_compactOffDiagonalClockedNonlinearSourceMassAt
      solution ha hab hbT scale)

/-- **Sharp reciprocal-clock service of one adaptive nonlinear triangle.** -/
theorem compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution_le_reciprocalClockSource
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution
        solution ha hab hbT scale ≤
      compactAdaptiveReciprocalClockNonlinearSourceContribution
        solution ha hab hbT scale := by
  let horizon := adaptiveSmoothDyadicTerminalWindowStart a b scale
  have hah : a ≤ horizon := le_adaptiveSmoothDyadicTerminalWindowStart hab scale
  rw [compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution_eq_rotatedTriangle]
  unfold compactAdaptiveReciprocalClockNonlinearSourceContribution
  rw [← intervalIntegral.integral_const_mul]
  have hrotatedContinuous : Continuous (fun sourceTime : ℝ ↦
      ∫ targetTime in sourceTime..horizon,
        compactOffDiagonalClockedNonlinearSourceMassAt
          solution ha hab hbT scale targetTime sourceTime) := by
    have hforward : Continuous (fun sourceTime : ℝ ↦
        ∫ targetTime in horizon..sourceTime,
          compactOffDiagonalClockedNonlinearSourceMassAt
            solution ha hab hbT scale targetTime sourceTime) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      · exact (continuous_uncurry_compactOffDiagonalClockedNonlinearSourceMassAt
          solution ha hab hbT scale).comp continuous_swap
      · exact continuous_id
    refine hforward.neg.congr ?_
    intro sourceTime
    change -(∫ targetTime in horizon..sourceTime,
        compactOffDiagonalClockedNonlinearSourceMassAt
          solution ha hab hbT scale targetTime sourceTime) = _
    rw [intervalIntegral.integral_symm sourceTime horizon, neg_neg]
  apply intervalIntegral.integral_mono_on hah
  · exact hrotatedContinuous.intervalIntegrable _ _
  · exact (continuous_const.mul
      (continuous_compactSmoothDyadicVorticityNonlinearSourceMassAt
        solution ha hab hbT scale)).intervalIntegrable _ _
  · intro sourceTime hsourceTime
    exact intervalIntegral_offDiagonalClockedNonlinearSourceMassAt_le_scaleClock_mul_actualSourceMass
      solution hnu ha hab hbT hsourceTime.2 scale

/-- Finite scale word of the exact clock-serviced nonlinear source receiver. -/
def compactAdaptiveReciprocalClockNonlinearSourcePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactAdaptiveReciprocalClockNonlinearSourceContribution
      solution ha hab hbT scale

/-- The entire finite adaptive nonlinear word is paid shell by shell.  No depth factor occurs. -/
theorem compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix_le_reciprocalClockSourcePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix
        solution ha hab hbT depth ≤
      compactAdaptiveReciprocalClockNonlinearSourcePrefix
        solution ha hab hbT depth := by
  unfold compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix
    compactAdaptiveReciprocalClockNonlinearSourcePrefix
  exact Finset.sum_le_sum fun scale _hscale ↦
    compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution_le_reciprocalClockSource
      solution hnu ha hab hbT scale

/-! ## Comparison with the existing compact-time source envelope -/

theorem compactSmoothDyadicVorticityNonlinearSourceMassAt_le_sourceEnvelope
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ)
    (hsourceTime : sourceTime ∈ Icc a b) :
    compactSmoothDyadicVorticityNonlinearSourceMassAt
        solution ha hab hbT scale sourceTime ≤
      compactSmoothDyadicVorticityNonlinearSourceEnvelope
        solution ha hab hbT scale := by
  unfold compactSmoothDyadicVorticityNonlinearSourceMassAt
    compactSmoothDyadicVorticityNonlinearSourceEnvelope
  apply Finset.sum_le_sum
  intro frequency _hfrequency
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact ContinuousMap.norm_coe_le_norm
    (compactSmoothVorticityNonlinearSourceModeFace
      solution ha hab hbT frequency)
    ⟨sourceTime, hsourceTime⟩

/-- The exact adaptive receiver is no larger than the old supremum quotient.  This is the precise
information-forgetting passage: source chronology is collapsed only on the right. -/
theorem compactAdaptiveReciprocalClockNonlinearSourceContribution_le_window_mul_clockedEnvelope
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    compactAdaptiveReciprocalClockNonlinearSourceContribution
        solution ha hab hbT scale ≤
      (adaptiveSmoothDyadicTerminalWindowStart a b scale - a) *
        (dyadicParabolicClockBudget nu scale *
          compactSmoothDyadicVorticityNonlinearSourceEnvelope
            solution ha hab hbT scale) := by
  let horizon := adaptiveSmoothDyadicTerminalWindowStart a b scale
  have hah : a ≤ horizon := le_adaptiveSmoothDyadicTerminalWindowStart hab scale
  have hhb : horizon ≤ b := adaptiveSmoothDyadicTerminalWindowStart_le hab scale
  have hbudget : 0 ≤ dyadicParabolicClockBudget nu scale := by
    unfold dyadicParabolicClockBudget
    positivity
  unfold compactAdaptiveReciprocalClockNonlinearSourceContribution
  have hintegral :
      (∫ sourceTime in a..horizon,
        compactSmoothDyadicVorticityNonlinearSourceMassAt
          solution ha hab hbT scale sourceTime) ≤
        (horizon - a) *
          compactSmoothDyadicVorticityNonlinearSourceEnvelope
            solution ha hab hbT scale := by
    calc
      (∫ sourceTime in a..horizon,
        compactSmoothDyadicVorticityNonlinearSourceMassAt
          solution ha hab hbT scale sourceTime) ≤
          ∫ _sourceTime in a..horizon,
            compactSmoothDyadicVorticityNonlinearSourceEnvelope
              solution ha hab hbT scale := by
        apply intervalIntegral.integral_mono_on hah
        · exact (continuous_compactSmoothDyadicVorticityNonlinearSourceMassAt
            solution ha hab hbT scale).intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro sourceTime hsourceTime
          exact compactSmoothDyadicVorticityNonlinearSourceMassAt_le_sourceEnvelope
            solution ha hab hbT scale ⟨hsourceTime.1, hsourceTime.2.trans hhb⟩
      _ = (horizon - a) *
          compactSmoothDyadicVorticityNonlinearSourceEnvelope
            solution ha hab hbT scale := by
        rw [intervalIntegral.integral_const]
        rfl
  calc
    dyadicParabolicClockBudget nu scale *
        (∫ sourceTime in a..horizon,
          compactSmoothDyadicVorticityNonlinearSourceMassAt
            solution ha hab hbT scale sourceTime) ≤
      dyadicParabolicClockBudget nu scale *
        ((horizon - a) *
          compactSmoothDyadicVorticityNonlinearSourceEnvelope
            solution ha hab hbT scale) :=
      mul_le_mul_of_nonneg_left hintegral hbudget
    _ = (horizon - a) *
        (dyadicParabolicClockBudget nu scale *
          compactSmoothDyadicVorticityNonlinearSourceEnvelope
            solution ha hab hbT scale) := by ring

/-- Coarser depth-free comparison with the existing finite clocked-envelope word.  The only
remaining summability obligation is the already exposed family
`clockBudget scale * sourceEnvelope scale`; the Fubini passage creates no depth loss. -/
theorem compactAdaptiveReciprocalClockNonlinearSourcePrefix_le_intervalLength_mul_clockedEnvelopePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactAdaptiveReciprocalClockNonlinearSourcePrefix
        solution ha hab hbT depth ≤
      (b - a) *
        ∑ scale ∈ Finset.range depth,
          dyadicParabolicClockBudget nu scale *
            compactSmoothDyadicVorticityNonlinearSourceEnvelope
              solution ha hab hbT scale := by
  unfold compactAdaptiveReciprocalClockNonlinearSourcePrefix
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro scale _hscale
  have hwindow := sub_le_sub_right
    (adaptiveSmoothDyadicTerminalWindowStart_le hab scale) a
  have hclocked : 0 ≤ dyadicParabolicClockBudget nu scale *
      compactSmoothDyadicVorticityNonlinearSourceEnvelope
        solution ha hab hbT scale :=
    mul_nonneg (by unfold dyadicParabolicClockBudget; positivity)
      (compactSmoothDyadicVorticityNonlinearSourceEnvelope_nonneg
        solution ha hab hbT scale)
  exact (compactAdaptiveReciprocalClockNonlinearSourceContribution_le_window_mul_clockedEnvelope
    solution hnu ha hab hbT scale).trans
      (mul_le_mul_of_nonneg_right hwindow hclocked)

/-! ## Joined adaptive decomposition with the exact remaining source receiver -/

/-- The adaptive off-diagonal reconstruction fibre is now paid by the restart shell word and the
exact reciprocal-clock nonlinear source receiver.  This is not the unweighted terminal receiver. -/
theorem compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restartPayment_add_reciprocalClockSourcePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
        solution ha hab hbT depth ≤
      nu⁻¹ * smoothRestartCoefficientPayment solution ha (hab.trans_lt hbT) +
        compactAdaptiveReciprocalClockNonlinearSourcePrefix
          solution ha hab hbT depth := by
  exact (compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restartPayment_add_nonlinearSourcePrefix
    solution hnu ha hab hbT depth).trans
      (add_le_add le_rfl
        (compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix_le_reciprocalClockSourcePrefix
          solution hnu ha hab hbT depth))

/-! ## Exact separator from the signed physical-phase receiver -/

/-- A unit receiving direction used to expose the orthogonal-output reconstruction fibre. -/
def orthogonalSeparatorReceiver : ComplexVector :=
  fun component ↦ if component = 0 then 1 else 0

/-- A nonzero unit output invisible to the preceding receiving direction. -/
def orthogonalSeparatorOutput : ComplexVector :=
  fun component ↦ if component = 1 then 1 else 0

/-- A rank-one Jacobian occurrence sending the receiver into the orthogonal output. -/
def orthogonalSeparatorJacobian : ComplexMatrix3 :=
  Matrix.of fun output input ↦ if output = 1 ∧ input = 0 then 1 else 0

@[simp]
theorem complexMatrixAction_orthogonalSeparator :
    complexMatrixAction orthogonalSeparatorJacobian orthogonalSeparatorReceiver =
      orthogonalSeparatorOutput := by
  ext component
  fin_cases component <;>
    simp [complexMatrixAction, orthogonalSeparatorJacobian,
      orthogonalSeparatorReceiver, orthogonalSeparatorOutput,
      Matrix.mulVec, dotProduct]

@[simp]
theorem complexDot_orthogonalSeparator_eq_zero :
    complexDot orthogonalSeparatorReceiver orthogonalSeparatorOutput = 0 := by
  simp [complexDot, orthogonalSeparatorReceiver, orthogonalSeparatorOutput,
    dotProduct]

@[simp]
theorem complexVectorL1_orthogonalSeparatorOutput :
    complexVectorL1 orthogonalSeparatorOutput = 1 := by
  simp [complexVectorL1, orthogonalSeparatorOutput]

/-- The orthogonal output is exactly the reconstruction fibre discarded by the scalar signed
receiver: its aligned amplitude is zero, so direction projection retains the whole output. -/
theorem receiverDirectionRemainder_orthogonalSeparator :
    receiverDirectionRemainder orthogonalSeparatorReceiver orthogonalSeparatorOutput =
      orthogonalSeparatorOutput := by
  simp [receiverDirectionRemainder, receiverAlignedAmplitude,
    complexDot, orthogonalSeparatorReceiver, orthogonalSeparatorOutput,
    dotProduct]

/-- The signed quadratic stretching receiver vanishes on a nonzero orthogonal Jacobian output.
Symmetrization does not repair the lost fibre. -/
@[simp]
theorem complexStretchingReading_orthogonalSeparator_eq_zero :
    complexStretchingReading orthogonalSeparatorReceiver
      (symmetricComplexJacobianPart orthogonalSeparatorJacobian) = 0 := by
  rw [complexStretchingReading_symmetricComplexJacobianPart]
  unfold complexStretchingReading
  rw [complexMatrixAction_orthogonalSeparator,
    complexDot_orthogonalSeparator_eq_zero]

/-- **Exact separator.** No scalar multiple of the absolute signed stretching reading can
dominate the coefficientwise absolute output population, even in one rank-one occurrence.
Consequently the physical-phase ledger cannot pay the reciprocal-clock nonlinear source word
without an additional square/absolute source receiver that restores this orthogonal fibre. -/
theorem no_scalar_signedStretching_bound_for_absoluteOrthogonalOutput (constant : ℝ) :
    ¬ complexVectorL1
        (complexMatrixAction orthogonalSeparatorJacobian orthogonalSeparatorReceiver) ≤
      constant *
        ‖complexStretchingReading orthogonalSeparatorReceiver
          (symmetricComplexJacobianPart orthogonalSeparatorJacobian)‖ := by
  simp

section Audit

#print axioms intervalIntegral_causal_triangle_swap
#print axioms intervalIntegral_offDiagonalClockedNonlinearSourceMassAt_le_scaleClock_mul_actualSourceMass
#print axioms compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution_eq_rotatedTriangle
#print axioms compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution_le_reciprocalClockSource
#print axioms compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix_le_reciprocalClockSourcePrefix
#print axioms compactSmoothDyadicVorticityNonlinearSourceMassAt_le_sourceEnvelope
#print axioms compactAdaptiveReciprocalClockNonlinearSourceContribution_le_window_mul_clockedEnvelope
#print axioms compactAdaptiveReciprocalClockNonlinearSourcePrefix_le_intervalLength_mul_clockedEnvelopePrefix
#print axioms compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restartPayment_add_reciprocalClockSourcePrefix
#print axioms receiverDirectionRemainder_orthogonalSeparator
#print axioms complexStretchingReading_orthogonalSeparator_eq_zero
#print axioms no_scalar_signedStretching_bound_for_absoluteOrthogonalOutput

end Audit

end Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearTriangleService
