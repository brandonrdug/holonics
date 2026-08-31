import ElementaryHolonics.Millennium.NavierStokesSmoothMildSourceClockBound

/-!
# Chronology-preserving smooth nonlinear mild history

**[proved-derived; formal-checked]**  This file keeps the complete source-time history which is
suppressed by the compact-time supremum receiver.  At each source time the actual complex-vector
nonlinear vorticity mode is formed first, its norm is then taken, and the finite two-shell smooth
receiver is assembled with its addressed multiplier weight.

The main estimate retains the mode-dependent heat service inside the source-time integral.  Thus
neither chronology nor the different clocks carried by distinct frequency addresses are replaced
by a time supremum.  No cross-scale summability or terminal estimate is asserted.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesSmoothMildSourceChronology

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceClockBound
open Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand

set_option maxHeartbeats 2400000

/-! ## Actual source population at one source time -/

/-- The actual two-shell nonlinear source population at one source time.  Each complex-vector mode
is retained through its full construction and is normed only at the addressed receiver. -/
def compactSmoothDyadicVorticityNonlinearSourceMassAt
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
    |dyadicHodgeBandWeight scale frequency| *
      ‖compactVorticityNonlinearMode
        solution hs hst ht frequency sourceTime‖

theorem compactSmoothDyadicVorticityNonlinearSourceMassAt_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) (sourceTime : ℝ) :
    0 ≤ compactSmoothDyadicVorticityNonlinearSourceMassAt
      solution hs hst ht scale sourceTime := by
  unfold compactSmoothDyadicVorticityNonlinearSourceMassAt
  exact Finset.sum_nonneg fun frequency _ ↦
    mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem continuous_compactSmoothDyadicVorticityNonlinearSourceMassAt
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) :
    Continuous (compactSmoothDyadicVorticityNonlinearSourceMassAt
      solution hs hst ht scale) := by
  unfold compactSmoothDyadicVorticityNonlinearSourceMassAt
  apply continuous_finsetSum
  intro frequency _hfrequency
  exact continuous_const.mul
    (continuous_compactVorticityNonlinearMode
      solution hs hst ht frequency).norm

/-! ## The modewise heat-clocked chronology -/

/-- Source-time population seen at target time `t`: every actual mode carries its own diagonal
heat clock, and the finite smooth two-shell receiver is assembled only after that clocked mode has
been normed. -/
def compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
    |dyadicHodgeBandWeight scale frequency| *
      heatStokesMultiplier nu (t - sourceTime) frequency *
        ‖compactVorticityNonlinearMode
          solution hs hst ht frequency sourceTime‖

theorem compactSmoothDyadicVorticityNonlinearClockedSourceMassAt_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (_hnu : 0 ≤ nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) {sourceTime : ℝ} (_hsourceTime : sourceTime ≤ t) :
    0 ≤ compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
      solution hs hst ht scale sourceTime := by
  unfold compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
  apply Finset.sum_nonneg
  intro frequency _hfrequency
  have hclock : 0 ≤ heatStokesMultiplier nu (t - sourceTime) frequency := by
    unfold heatStokesMultiplier
    positivity
  positivity

theorem continuous_compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) :
    Continuous (compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
      solution hs hst ht scale) := by
  unfold compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
  apply continuous_finsetSum
  intro frequency _hfrequency
  have hclock : Continuous (fun sourceTime : ℝ ↦
      heatStokesMultiplier nu (t - sourceTime) frequency) := by
    unfold heatStokesMultiplier
    exact Real.continuous_exp.comp (by fun_prop)
  exact (continuous_const.mul hclock).mul
    (continuous_compactVorticityNonlinearMode
      solution hs hst ht frequency).norm

private theorem intervalIntegral_reflected_heatStokesMultiplier_le_scaleBudget
    {nu s t : ℝ} (hnu : 0 < nu) (hst : s ≤ t)
    {scale : ℕ} {frequency : SpatialFrequency}
    (hfrequency : frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1))) :
    (∫ sourceTime in s..t,
      heatStokesMultiplier nu (t - sourceTime) frequency) ≤
        dyadicParabolicClockBudget nu scale := by
  have hreflect :
      (∫ sourceTime in s..t,
        heatStokesMultiplier nu (t - sourceTime) frequency) =
      ∫ elapsed in (0 : ℝ)..(t - s),
        heatStokesMultiplier nu elapsed frequency := by
    simpa only [sub_self] using
      (intervalIntegral.integral_comp_sub_left
        (fun elapsed : ℝ ↦ heatStokesMultiplier nu elapsed frequency) t
        (a := s) (b := t))
  rw [hreflect]
  rw [Finset.mem_union] at hfrequency
  rcases hfrequency with hfrequency | hfrequency
  · exact intervalIntegral_heatStokesMultiplier_le_dyadicParabolicClockBudget
      hnu (sub_nonneg.mpr hst) hfrequency
  · exact (intervalIntegral_heatStokesMultiplier_le_dyadicParabolicClockBudget
      hnu (sub_nonneg.mpr hst) hfrequency).trans
        (dyadicParabolicClockBudget_succ_le hnu scale)

private theorem norm_weighted_compactMildSourceIntegratedCoefficient_le_history
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (_hnu : 0 ≤ nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) (frequency : SpatialFrequency) :
    ‖(dyadicHodgeBandWeight scale frequency : ℂ) •
        compactMildSourceIntegratedCoefficient
          solution hs hst ht frequency‖ ≤
      ∫ sourceTime in s..t,
        |dyadicHodgeBandWeight scale frequency| *
          heatStokesMultiplier nu (t - sourceTime) frequency *
            ‖compactVorticityNonlinearMode
              solution hs hst ht frequency sourceTime‖ := by
  have hmode :
      ‖compactMildSourceIntegratedCoefficient
          solution hs hst ht frequency‖ ≤
        ∫ sourceTime in s..t,
          heatStokesMultiplier nu (t - sourceTime) frequency *
            ‖compactVorticityNonlinearMode
              solution hs hst ht frequency sourceTime‖ := by
    unfold compactMildSourceIntegratedCoefficient
    apply intervalIntegral.norm_integral_le_of_norm_le hst
    · filter_upwards with sourceTime hsourceTime
      unfold compactStokesTransportedVorticityNonlinearMode
      rw [norm_smul, Real.norm_eq_abs]
      have hclock :
          0 ≤ heatStokesMultiplier nu (t - sourceTime) frequency := by
        unfold heatStokesMultiplier
        positivity
      rw [abs_of_nonneg hclock]
    · apply Continuous.intervalIntegrable
      have hclock : Continuous (fun sourceTime : ℝ ↦
          heatStokesMultiplier nu (t - sourceTime) frequency) := by
        unfold heatStokesMultiplier
        exact Real.continuous_exp.comp (by fun_prop)
      exact hclock.mul
        (continuous_compactVorticityNonlinearMode
          solution hs hst ht frequency).norm
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |dyadicHodgeBandWeight scale frequency| *
        ‖compactMildSourceIntegratedCoefficient
          solution hs hst ht frequency‖ ≤
      |dyadicHodgeBandWeight scale frequency| *
        (∫ sourceTime in s..t,
          heatStokesMultiplier nu (t - sourceTime) frequency *
            ‖compactVorticityNonlinearMode
              solution hs hst ht frequency sourceTime‖) :=
      mul_le_mul_of_nonneg_left hmode (abs_nonneg _)
    _ = ∫ sourceTime in s..t,
        |dyadicHodgeBandWeight scale frequency| *
          heatStokesMultiplier nu (t - sourceTime) frequency *
            ‖compactVorticityNonlinearMode
              solution hs hst ht frequency sourceTime‖ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro sourceTime _hsourceTime
      ring

/-- **Chronology-preserving smooth mild estimate.**  The spatial supremum of one phase-bearing
smooth nonlinear Duhamel band is bounded by the source-time integral of the actual two-shell
source population with its modewise heat clocks.  The source history stays inside the integral;
no compact-time supremum is used. -/
theorem compactSmoothMildSourceIntegratedBandSpatialSup_le_integral_clockedSourceHistory
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) :
    compactSmoothMildSourceIntegratedBandSpatialSup
        solution hs hst ht scale ≤
      ∫ sourceTime in s..t,
        compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
          solution hs hst ht scale sourceTime := by
  unfold compactSmoothMildSourceIntegratedBandSpatialSup
    compactSmoothMildSourceIntegratedBand
  rw [finiteFourierSynthesis_dyadicHodgeBand_eq_twoSharpShells]
  have hright :
      0 ≤ ∫ sourceTime in s..t,
        compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
          solution hs hst ht scale sourceTime := by
    apply intervalIntegral.integral_nonneg hst
    intro sourceTime hsourceTime
    exact compactSmoothDyadicVorticityNonlinearClockedSourceMassAt_nonneg
      solution hnu hs hst ht scale hsourceTime.2
  apply (ContinuousMap.norm_le _ hright).2
  intro q
  calc
    ‖finiteFourierSynthesis
        (fun frequency ↦ (dyadicHodgeBandWeight scale frequency : ℂ) •
          compactMildSourceIntegratedCoefficient
            solution hs hst ht frequency)
        (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)) q‖ ≤
      ∑ frequency ∈
          (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
        ‖(dyadicHodgeBandWeight scale frequency : ℂ) •
          compactMildSourceIntegratedCoefficient
            solution hs hst ht frequency‖ :=
      norm_finiteFourierSynthesis_le_sum_norm _ _ q
    _ ≤ ∑ frequency ∈
          (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
        ∫ sourceTime in s..t,
          |dyadicHodgeBandWeight scale frequency| *
            heatStokesMultiplier nu (t - sourceTime) frequency *
              ‖compactVorticityNonlinearMode
                solution hs hst ht frequency sourceTime‖ := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      exact norm_weighted_compactMildSourceIntegratedCoefficient_le_history
        solution hnu hs hst ht scale frequency
    _ = ∫ sourceTime in s..t,
        compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
          solution hs hst ht scale sourceTime := by
      unfold compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
      rw [intervalIntegral.integral_finsetSum]
      intro frequency _hfrequency
      apply Continuous.intervalIntegrable
      have hclock : Continuous (fun sourceTime : ℝ ↦
          heatStokesMultiplier nu (t - sourceTime) frequency) := by
        unfold heatStokesMultiplier
        exact Real.continuous_exp.comp (by fun_prop)
      exact (continuous_const.mul hclock).mul
        (continuous_compactVorticityNonlinearMode
          solution hs hst ht frequency).norm

/-! ## Comparison with the supremum clock quotient -/

private theorem integral_weighted_clockedSourceMode_le_scaleBudget_mul_sourceSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1))) :
    (∫ sourceTime in s..t,
      |dyadicHodgeBandWeight scale frequency| *
        heatStokesMultiplier nu (t - sourceTime) frequency *
          ‖compactVorticityNonlinearMode
            solution hs hst ht frequency sourceTime‖) ≤
      dyadicParabolicClockBudget nu scale *
        (|dyadicHodgeBandWeight scale frequency| *
          compactSmoothVorticityNonlinearSourceModeSup
            solution hs hst ht frequency) := by
  let sourceSup : ℝ :=
    compactSmoothVorticityNonlinearSourceModeSup
      solution hs hst ht frequency
  have hsourceSup : 0 ≤ sourceSup :=
    compactSmoothVorticityNonlinearSourceModeSup_nonneg
      solution hs hst ht frequency
  have hhistory :
      (∫ sourceTime in s..t,
        |dyadicHodgeBandWeight scale frequency| *
          heatStokesMultiplier nu (t - sourceTime) frequency *
            ‖compactVorticityNonlinearMode
              solution hs hst ht frequency sourceTime‖) ≤
        ∫ sourceTime in s..t,
          (|dyadicHodgeBandWeight scale frequency| * sourceSup) *
            heatStokesMultiplier nu (t - sourceTime) frequency := by
    apply intervalIntegral.integral_mono_on hst
    · apply Continuous.intervalIntegrable
      have hclock : Continuous (fun sourceTime : ℝ ↦
          heatStokesMultiplier nu (t - sourceTime) frequency) := by
        unfold heatStokesMultiplier
        exact Real.continuous_exp.comp (by fun_prop)
      exact (continuous_const.mul hclock).mul
        (continuous_compactVorticityNonlinearMode
          solution hs hst ht frequency).norm
    · apply Continuous.intervalIntegrable
      have hclock : Continuous (fun sourceTime : ℝ ↦
          heatStokesMultiplier nu (t - sourceTime) frequency) := by
        unfold heatStokesMultiplier
        exact Real.continuous_exp.comp (by fun_prop)
      exact continuous_const.mul hclock
    · intro sourceTime hsourceTime
      have hsourceBound :
          ‖compactVorticityNonlinearMode
              solution hs hst ht frequency sourceTime‖ ≤ sourceSup := by
        exact ContinuousMap.norm_coe_le_norm
          (compactSmoothVorticityNonlinearSourceModeFace
            solution hs hst ht frequency)
          ⟨sourceTime, hsourceTime⟩
      have hclock :
          0 ≤ heatStokesMultiplier nu (t - sourceTime) frequency := by
        unfold heatStokesMultiplier
        positivity
      calc
        |dyadicHodgeBandWeight scale frequency| *
            heatStokesMultiplier nu (t - sourceTime) frequency *
              ‖compactVorticityNonlinearMode
                solution hs hst ht frequency sourceTime‖ ≤
          (|dyadicHodgeBandWeight scale frequency| *
            heatStokesMultiplier nu (t - sourceTime) frequency) * sourceSup :=
          mul_le_mul_of_nonneg_left hsourceBound
            (mul_nonneg (abs_nonneg _) hclock)
        _ = (|dyadicHodgeBandWeight scale frequency| * sourceSup) *
            heatStokesMultiplier nu (t - sourceTime) frequency := by ring
  have hclock :=
    intervalIntegral_reflected_heatStokesMultiplier_le_scaleBudget
      hnu hst hfrequency
  calc
    (∫ sourceTime in s..t,
      |dyadicHodgeBandWeight scale frequency| *
        heatStokesMultiplier nu (t - sourceTime) frequency *
          ‖compactVorticityNonlinearMode
            solution hs hst ht frequency sourceTime‖) ≤
      ∫ sourceTime in s..t,
        (|dyadicHodgeBandWeight scale frequency| * sourceSup) *
          heatStokesMultiplier nu (t - sourceTime) frequency := hhistory
    _ = (|dyadicHodgeBandWeight scale frequency| * sourceSup) *
        ∫ sourceTime in s..t,
          heatStokesMultiplier nu (t - sourceTime) frequency := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (|dyadicHodgeBandWeight scale frequency| * sourceSup) *
        dyadicParabolicClockBudget nu scale :=
      mul_le_mul_of_nonneg_left hclock
        (mul_nonneg (abs_nonneg _) hsourceSup)
    _ = dyadicParabolicClockBudget nu scale *
        (|dyadicHodgeBandWeight scale frequency| *
          compactSmoothVorticityNonlinearSourceModeSup
            solution hs hst ht frequency) := by
      dsimp [sourceSup]
      ring

/-- Collapsing the retained chronology to the compact-time source supremum and then paying the
modewise clocks yields exactly the earlier parabolic-clock receiver.  This comparison records the
direction in which temporal information is forgotten. -/
theorem integral_clockedSourceHistory_le_parabolicClockBudget_mul_sourceEnvelope
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) :
    (∫ sourceTime in s..t,
      compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
        solution hs hst ht scale sourceTime) ≤
      dyadicParabolicClockBudget nu scale *
        compactSmoothDyadicVorticityNonlinearSourceEnvelope
          solution hs hst ht scale := by
  unfold compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
    compactSmoothDyadicVorticityNonlinearSourceEnvelope
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro frequency hfrequency
    exact integral_weighted_clockedSourceMode_le_scaleBudget_mul_sourceSup
      solution hnu hs hst ht scale hfrequency
  · intro frequency _hfrequency
    apply Continuous.intervalIntegrable
    have hclock : Continuous (fun sourceTime : ℝ ↦
        heatStokesMultiplier nu (t - sourceTime) frequency) := by
      unfold heatStokesMultiplier
      exact Real.continuous_exp.comp (by fun_prop)
    exact (continuous_const.mul hclock).mul
      (continuous_compactVorticityNonlinearMode
        solution hs hst ht frequency).norm

section Audit

#print axioms compactSmoothDyadicVorticityNonlinearSourceMassAt_nonneg
#print axioms continuous_compactSmoothDyadicVorticityNonlinearSourceMassAt
#print axioms compactSmoothDyadicVorticityNonlinearClockedSourceMassAt_nonneg
#print axioms continuous_compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
#print axioms compactSmoothMildSourceIntegratedBandSpatialSup_le_integral_clockedSourceHistory
#print axioms integral_clockedSourceHistory_le_parabolicClockBudget_mul_sourceEnvelope

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothMildSourceChronology
