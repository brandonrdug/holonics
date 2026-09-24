import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
import ElementaryHolonics.Millennium.NavierStokesDyadicSpectralClockService

/-!
# Smooth nonlinear mild bands paid by the exact dyadic heat clock

**[proved-derived; formal-checked]**  This file keeps the actual complex-vector nonlinear
vorticity mode as a continuous source face on the addressed compact time interval.  Its norm is
taken only after that complete phase-bearing face has been formed.  The exact modal heat clock
then pays every mode in the two-shell support of one smooth Hodge band.

The resulting scale law is explicit: parabolic heat service contributes `4⁻scale`, while the
remaining source envelope is the finite population of actual smooth-band mode faces.  No
finiteness of that source population across scales is asserted.  If the literal clock-weighted
source family is summable, the corresponding smooth nonlinear mild bands are summable and their
complete sum is bounded by that source family.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesSmoothMildSourceClockBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
open Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative

set_option maxHeartbeats 2400000

/-! ## The actual phase-bearing source face -/

/-- The actual nonlinear vorticity mode, retained as one continuous complex-vector face over the
compact source-time interval. -/
def compactSmoothVorticityNonlinearSourceModeFace
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (frequency : SpatialFrequency) : C(Icc s t, ComplexVector) where
  toFun sourceTime :=
    compactVorticityNonlinearMode solution hs hst ht frequency sourceTime.1
  continuous_toFun :=
    (continuous_compactVorticityNonlinearMode solution hs hst ht frequency).comp
      continuous_subtype_val

/-- Source-time supremum of one actual phase-bearing complex-vector nonlinear mode. -/
def compactSmoothVorticityNonlinearSourceModeSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (frequency : SpatialFrequency) : ℝ :=
  ‖compactSmoothVorticityNonlinearSourceModeFace
      solution hs hst ht frequency‖

theorem compactSmoothVorticityNonlinearSourceModeSup_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (frequency : SpatialFrequency) :
    0 ≤ compactSmoothVorticityNonlinearSourceModeSup
      solution hs hst ht frequency :=
  norm_nonneg _

/-- The actual source family seen by one smooth dyadic receiver.  The complex-vector source face
is retained through its compact-time norm; only then are the finitely many addressed modes
assembled with the genuine smooth multiplier weights. -/
def compactSmoothDyadicVorticityNonlinearSourceEnvelope
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) : ℝ :=
  ∑ frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
    |dyadicHodgeBandWeight scale frequency| *
      compactSmoothVorticityNonlinearSourceModeSup
        solution hs hst ht frequency

theorem compactSmoothDyadicVorticityNonlinearSourceEnvelope_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) :
    0 ≤ compactSmoothDyadicVorticityNonlinearSourceEnvelope
      solution hs hst ht scale := by
  unfold compactSmoothDyadicVorticityNonlinearSourceEnvelope
  exact Finset.sum_nonneg fun frequency _ ↦ mul_nonneg (abs_nonneg _)
    (compactSmoothVorticityNonlinearSourceModeSup_nonneg
      solution hs hst ht frequency)

/-! ## Exact clock service on the two-shell smooth support -/

theorem dyadicParabolicClockBudget_succ_le
    {nu : ℝ} (hnu : 0 < nu) (scale : ℕ) :
    dyadicParabolicClockBudget nu (scale + 1) ≤
      dyadicParabolicClockBudget nu scale := by
  have hscaleRate : 0 < nu * (4 : ℝ) ^ scale := by positivity
  have hnextRate : 0 < nu * (4 : ℝ) ^ (scale + 1) := by positivity
  apply (inv_le_inv₀ hnextRate hscaleRate).2
  have hpow : (4 : ℝ) ^ scale ≤ (4 : ℝ) ^ (scale + 1) := by
    rw [pow_succ]
    nlinarith [show 0 ≤ (4 : ℝ) ^ scale by positivity]
  exact mul_le_mul_of_nonneg_left hpow hnu.le

/-- The public parabolic budget is exactly inverse viscosity times one reciprocal base-four step
per dyadic level. -/
theorem dyadicParabolicClockBudget_eq_viscosityInv_mul_quarterPow
    (nu : ℝ) (scale : ℕ) :
    dyadicParabolicClockBudget nu scale =
      nu⁻¹ * ((4 : ℝ)⁻¹) ^ scale := by
  simp [dyadicParabolicClockBudget, mul_inv_rev, inv_pow, mul_comm]

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

private theorem norm_weighted_compactMildSourceIntegratedCoefficient_le
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1))) :
    ‖(dyadicHodgeBandWeight scale frequency : ℂ) •
        compactMildSourceIntegratedCoefficient
          solution hs hst ht frequency‖ ≤
      dyadicParabolicClockBudget nu scale *
        (|dyadicHodgeBandWeight scale frequency| *
          compactSmoothVorticityNonlinearSourceModeSup
            solution hs hst ht frequency) := by
  let sourceSup : ℝ :=
    compactSmoothVorticityNonlinearSourceModeSup
      solution hs hst ht frequency
  have hsourceSup : 0 ≤ sourceSup := by
    exact compactSmoothVorticityNonlinearSourceModeSup_nonneg
      solution hs hst ht frequency
  have hhistory :
      ‖compactMildSourceIntegratedCoefficient
          solution hs hst ht frequency‖ ≤
        sourceSup *
          ∫ sourceTime in s..t,
            heatStokesMultiplier nu (t - sourceTime) frequency := by
    unfold compactMildSourceIntegratedCoefficient
    calc
      ‖∫ sourceTime in s..t,
          compactStokesTransportedVorticityNonlinearMode
            solution hs hst ht frequency sourceTime‖ ≤
        ∫ sourceTime in s..t,
          sourceSup * heatStokesMultiplier nu (t - sourceTime) frequency := by
        apply intervalIntegral.norm_integral_le_of_norm_le hst
        · filter_upwards with sourceTime hsourceTime
          have hsourceTimeIcc : sourceTime ∈ Icc s t :=
            ⟨hsourceTime.1.le, hsourceTime.2⟩
          have hsourceBound :
              ‖compactVorticityNonlinearMode
                  solution hs hst ht frequency sourceTime‖ ≤ sourceSup := by
            exact ContinuousMap.norm_coe_le_norm
              (compactSmoothVorticityNonlinearSourceModeFace
                solution hs hst ht frequency)
              ⟨sourceTime, hsourceTimeIcc⟩
          unfold compactStokesTransportedVorticityNonlinearMode
          rw [norm_smul, Real.norm_eq_abs]
          have hclock : 0 ≤
              heatStokesMultiplier nu (t - sourceTime) frequency := by
            unfold heatStokesMultiplier
            positivity
          rw [abs_of_nonneg hclock]
          nlinarith
        · have hcontinuous : Continuous (fun sourceTime : ℝ ↦
              sourceSup * heatStokesMultiplier nu (t - sourceTime) frequency) := by
            apply continuous_const.mul
            unfold heatStokesMultiplier
            fun_prop
          exact hcontinuous.intervalIntegrable _ _
      _ = sourceSup *
          ∫ sourceTime in s..t,
            heatStokesMultiplier nu (t - sourceTime) frequency := by
        rw [intervalIntegral.integral_const_mul]
  have hclock :=
    intervalIntegral_reflected_heatStokesMultiplier_le_scaleBudget
      hnu hst hfrequency
  have hhistoryClock :
      ‖compactMildSourceIntegratedCoefficient
          solution hs hst ht frequency‖ ≤
        sourceSup * dyadicParabolicClockBudget nu scale :=
    hhistory.trans (mul_le_mul_of_nonneg_left hclock hsourceSup)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |dyadicHodgeBandWeight scale frequency| *
        ‖compactMildSourceIntegratedCoefficient
          solution hs hst ht frequency‖ ≤
      |dyadicHodgeBandWeight scale frequency| *
        (sourceSup * dyadicParabolicClockBudget nu scale) :=
      mul_le_mul_of_nonneg_left hhistoryClock (abs_nonneg _)
    _ = dyadicParabolicClockBudget nu scale *
        (|dyadicHodgeBandWeight scale frequency| * sourceSup) := by ring

/-! ## Per-scale smooth band and complete summation consequence -/

/-- **Exact per-scale clock payment.**  One phase-bearing smooth nonlinear Duhamel band is paid
by the reciprocal parabolic clock `nu⁻¹ 4⁻scale` times the actual compact-time nonlinear source
envelope on precisely the two sharp shells supporting the smooth multiplier. -/
theorem compactSmoothMildSourceIntegratedBandSpatialSup_le_parabolicClockBudget_mul_sourceEnvelope
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (scale : ℕ) :
    compactSmoothMildSourceIntegratedBandSpatialSup
        solution hs hst ht scale ≤
      dyadicParabolicClockBudget nu scale *
        compactSmoothDyadicVorticityNonlinearSourceEnvelope
          solution hs hst ht scale := by
  unfold compactSmoothMildSourceIntegratedBandSpatialSup
    compactSmoothMildSourceIntegratedBand
  rw [finiteFourierSynthesis_dyadicHodgeBand_eq_twoSharpShells]
  apply (ContinuousMap.norm_le _ (mul_nonneg
    (by
      unfold dyadicParabolicClockBudget
      positivity)
    (compactSmoothDyadicVorticityNonlinearSourceEnvelope_nonneg
      solution hs hst ht scale))).2
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
        dyadicParabolicClockBudget nu scale *
          (|dyadicHodgeBandWeight scale frequency| *
            compactSmoothVorticityNonlinearSourceModeSup
              solution hs hst ht frequency) := by
      apply Finset.sum_le_sum
      intro frequency hfrequency
      exact norm_weighted_compactMildSourceIntegratedCoefficient_le
        solution hnu hs hst ht scale hfrequency
    _ = dyadicParabolicClockBudget nu scale *
        compactSmoothDyadicVorticityNonlinearSourceEnvelope
          solution hs hst ht scale := by
      simp [compactSmoothDyadicVorticityNonlinearSourceEnvelope,
        Finset.mul_sum]

/-- Summability of the literal clock-weighted actual source family implies summability of the
phase-bearing smooth nonlinear mild bands.  This theorem does not assert its premise. -/
theorem summable_compactSmoothMildSourceIntegratedBandSpatialSup_of_summable_clockedSourceEnvelope
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (hsource : Summable (fun scale : ℕ ↦
      dyadicParabolicClockBudget nu scale *
        compactSmoothDyadicVorticityNonlinearSourceEnvelope
          solution hs hst ht scale)) :
    Summable (compactSmoothMildSourceIntegratedBandSpatialSup
      solution hs hst ht) :=
  Summable.of_nonneg_of_le
    (compactSmoothMildSourceIntegratedBandSpatialSup_nonneg
      solution hs hst ht)
    (compactSmoothMildSourceIntegratedBandSpatialSup_le_parabolicClockBudget_mul_sourceEnvelope
      solution hnu hs hst ht) hsource

/-- Complete quantitative consequence of an actual summable clock-weighted source family. -/
theorem tsum_compactSmoothMildSourceIntegratedBandSpatialSup_le_clockedSourceEnvelope
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (hsource : Summable (fun scale : ℕ ↦
      dyadicParabolicClockBudget nu scale *
        compactSmoothDyadicVorticityNonlinearSourceEnvelope
          solution hs hst ht scale)) :
    (∑' scale : ℕ,
      compactSmoothMildSourceIntegratedBandSpatialSup
        solution hs hst ht scale) ≤
      ∑' scale : ℕ,
        dyadicParabolicClockBudget nu scale *
          compactSmoothDyadicVorticityNonlinearSourceEnvelope
            solution hs hst ht scale := by
  have hband :=
    summable_compactSmoothMildSourceIntegratedBandSpatialSup_of_summable_clockedSourceEnvelope
      solution hnu hs hst ht hsource
  exact hband.tsum_le_tsum
    (compactSmoothMildSourceIntegratedBandSpatialSup_le_parabolicClockBudget_mul_sourceEnvelope
      solution hnu hs hst ht) hsource

section Audit

#print axioms dyadicParabolicClockBudget_eq_viscosityInv_mul_quarterPow
#print axioms compactSmoothMildSourceIntegratedBandSpatialSup_le_parabolicClockBudget_mul_sourceEnvelope
#print axioms summable_compactSmoothMildSourceIntegratedBandSpatialSup_of_summable_clockedSourceEnvelope
#print axioms tsum_compactSmoothMildSourceIntegratedBandSpatialSup_le_clockedSourceEnvelope

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothMildSourceClockBound
