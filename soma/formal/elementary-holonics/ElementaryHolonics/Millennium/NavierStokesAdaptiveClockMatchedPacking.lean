import ElementaryHolonics.Millennium.NavierStokesClockWeightedCompactTimePacking

/-!
# Adaptive scale-matched terminal clocks

**[proved-derived; formal-checked]** The reciprocal shell clock can be based on the actual
compact interval rather than a privileged unit of exterior time.  Shell `j` receives the final
window of length `(b - a) * 4⁻ʲ`.  These windows lie in `[a,b]` for every ordered interval, and
the depth-uniform packing constant acquires exactly the addressed interval length `b - a`.

This removes the unit-window hypothesis from the matched diagonal construction.  It does not
estimate the earlier-history/off-diagonal reconstruction fibre and therefore asserts no terminal
control.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesAdaptiveClockMatchedPacking

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesClockWeightedCompactTimePacking
open Soma.Holonics.Millennium.NavierStokesClockWeightedSpatialBandPacking
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

set_option maxHeartbeats 2400000

/-! ## The addressed reciprocal clock -/

/-- The final shell window based on the actual compact interval length. -/
def adaptiveSmoothDyadicTerminalWindowStart
    (a b : ℝ) (scale : ℕ) : ℝ :=
  b - (b - a) * smoothDyadicReciprocalShellClock scale

theorem adaptiveSmoothDyadicTerminalWindowStart_le
    {a b : ℝ} (hab : a ≤ b) (scale : ℕ) :
    adaptiveSmoothDyadicTerminalWindowStart a b scale ≤ b := by
  unfold adaptiveSmoothDyadicTerminalWindowStart
  exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hab)
    (smoothDyadicReciprocalShellClock_pos scale).le)

theorem le_adaptiveSmoothDyadicTerminalWindowStart
    {a b : ℝ} (hab : a ≤ b) (scale : ℕ) :
    a ≤ adaptiveSmoothDyadicTerminalWindowStart a b scale := by
  unfold adaptiveSmoothDyadicTerminalWindowStart
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
  have hclock : smoothDyadicReciprocalShellClock scale ≤ 1 :=
    smoothDyadicReciprocalShellClock_le_one scale
  nlinarith

theorem adaptiveSmoothDyadicTerminalWindow_length
    (a b : ℝ) (scale : ℕ) :
    b - adaptiveSmoothDyadicTerminalWindowStart a b scale =
      (b - a) * smoothDyadicReciprocalShellClock scale := by
  unfold adaptiveSmoothDyadicTerminalWindowStart
  ring

/-! ## One-shell payment -/

/-- Shell `j`'s spatial `L¹` mass in its adaptive final reciprocal-clock window. -/
def compactOpenSmoothDyadicAdaptiveMatchedBandL1
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) : ℝ :=
  ∫ time in adaptiveSmoothDyadicTerminalWindowStart a b scale..b,
    compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale time

/-- Shell `j`'s clocked coefficient mass in the identical adaptive window. -/
def compactOpenSmoothDyadicAdaptiveMatchedBandClockMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) : ℝ :=
  ∫ time in adaptiveSmoothDyadicTerminalWindowStart a b scale..b,
    (4 : ℝ) ^ scale *
      compactOpenSmoothDyadicBandCoefficientMass
        solution ha hab hbT scale time

theorem compactOpenSmoothDyadicAdaptiveMatchedBandClockMass_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    0 ≤ compactOpenSmoothDyadicAdaptiveMatchedBandClockMass
      solution ha hab hbT scale := by
  unfold compactOpenSmoothDyadicAdaptiveMatchedBandClockMass
  exact intervalIntegral.integral_nonneg
    (adaptiveSmoothDyadicTerminalWindowStart_le hab scale) fun time _htime ↦
      mul_nonneg (by positivity)
        (openSmoothDyadicBandCoefficientMass_nonneg solution
          (compactInteriorTime ha hab hbT time) scale)

/-- The adaptive one-shell estimate.  The only new factor is the actual interval length. -/
theorem compactOpenSmoothDyadicAdaptiveMatchedBandL1_sq_le_density_mul_clockMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedBandL1
        solution ha hab hbT scale ^ 2 ≤
      ((b - a) * ((smoothDyadicBandNativeAperture scale).card : ℝ) /
          (16 : ℝ) ^ scale) *
        compactOpenSmoothDyadicAdaptiveMatchedBandClockMass
          solution ha hab hbT scale := by
  let start := adaptiveSmoothDyadicTerminalWindowStart a b scale
  let spatial := compactOpenSmoothDyadicVorticityBandSpatialSup
    solution ha hab hbT scale
  let mass := compactOpenSmoothDyadicBandCoefficientMass
    solution ha hab hbT scale
  have hstart : start ≤ b := adaptiveSmoothDyadicTerminalWindowStart_le hab scale
  have hcs : (∫ time in start..b, spatial time) ^ 2 ≤
      (b - start) * ∫ time in start..b, spatial time ^ 2 :=
    intervalIntegral_sq_integral_le_length_mul_integral_sq hstart
      (continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale)
      (fun time ↦ compactOpenSmoothDyadicVorticityBandSpatialSup_nonneg
        solution ha hab hbT scale time)
  have hspatialInt : IntervalIntegrable (fun time ↦ spatial time ^ 2) volume start b :=
    ((continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale).pow 2).intervalIntegrable _ _
  have hmassInt : IntervalIntegrable
      (fun time ↦ ((smoothDyadicBandNativeAperture scale).card : ℝ) * mass time)
      volume start b :=
    ((continuous_compactOpenSmoothDyadicBandCoefficientMass
      solution ha hab hbT scale).const_mul
        ((smoothDyadicBandNativeAperture scale).card : ℝ)).intervalIntegrable _ _
  have hmono : (∫ time in start..b, spatial time ^ 2) ≤
      ∫ time in start..b,
        ((smoothDyadicBandNativeAperture scale).card : ℝ) * mass time :=
    intervalIntegral.integral_mono_on hstart hspatialInt hmassInt
      (fun time _htime ↦
        compactOpenSmoothDyadicVorticityBandSpatialSup_sq_le_card_mul_coefficientMass
          solution ha hab hbT scale time)
  have hmono' : (∫ time in start..b, spatial time ^ 2) ≤
      ((smoothDyadicBandNativeAperture scale).card : ℝ) *
        ∫ time in start..b, mass time := by
    simpa only [intervalIntegral.integral_const_mul] using hmono
  have hlength : 0 ≤ b - start := sub_nonneg.mpr hstart
  have h4 : (0 : ℝ) < (4 : ℝ) ^ scale := by positivity
  have h16 : (16 : ℝ) ^ scale = ((4 : ℝ) ^ scale) ^ 2 := by
    rw [show (16 : ℝ) = (4 : ℝ) * 4 by norm_num, mul_pow, pow_two]
  unfold compactOpenSmoothDyadicAdaptiveMatchedBandL1
    compactOpenSmoothDyadicAdaptiveMatchedBandClockMass
  change (∫ time in start..b, spatial time) ^ 2 ≤ _
  rw [intervalIntegral.integral_const_mul]
  calc
    (∫ time in start..b, spatial time) ^ 2 ≤
        (b - start) * ∫ time in start..b, spatial time ^ 2 := hcs
    _ ≤ (b - start) *
        (((smoothDyadicBandNativeAperture scale).card : ℝ) *
          ∫ time in start..b, mass time) :=
      mul_le_mul_of_nonneg_left hmono' hlength
    _ = ((b - a) * ((smoothDyadicBandNativeAperture scale).card : ℝ) /
          (16 : ℝ) ^ scale) *
        ((4 : ℝ) ^ scale * ∫ time in start..b, mass time) := by
      rw [adaptiveSmoothDyadicTerminalWindow_length]
      dsimp [smoothDyadicReciprocalShellClock]
      rw [h16]
      field_simp [ne_of_gt h4]

/-! ## The finite adaptive diagonal word -/

def compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactOpenSmoothDyadicAdaptiveMatchedBandL1 solution ha hab hbT scale

def compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactOpenSmoothDyadicAdaptiveMatchedBandClockMass solution ha hab hbT scale

theorem compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    0 ≤ compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
      solution ha hab hbT depth := by
  unfold compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
  exact Finset.sum_nonneg fun scale _hscale ↦
    compactOpenSmoothDyadicAdaptiveMatchedBandClockMass_nonneg
      solution ha hab hbT scale

theorem compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_uniformClockMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      1024 * (b - a) *
        compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
          solution ha hab hbT depth := by
  have hraw : compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      (∑ scale ∈ Finset.range depth,
          (b - a) * ((smoothDyadicBandNativeAperture scale).card : ℝ) /
            (16 : ℝ) ^ scale) *
        compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
          solution ha hab hbT depth := by
    unfold compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
      compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro scale _hscale
      exact div_nonneg
        (mul_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)) (by positivity)
    · intro scale _hscale
      exact compactOpenSmoothDyadicAdaptiveMatchedBandClockMass_nonneg
        solution ha hab hbT scale
    · intro scale _hscale
      exact compactOpenSmoothDyadicAdaptiveMatchedBandL1_sq_le_density_mul_clockMass
        solution ha hab hbT scale
  have hdensity :
      (∑ scale ∈ Finset.range depth,
          (b - a) * ((smoothDyadicBandNativeAperture scale).card : ℝ) /
            (16 : ℝ) ^ scale) =
        (b - a) * smoothDyadicClockDensityPrefix depth := by
    unfold smoothDyadicClockDensityPrefix
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro scale _hscale
    ring
  rw [hdensity] at hraw
  calc
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      ((b - a) * smoothDyadicClockDensityPrefix depth) *
        compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
          solution ha hab hbT depth := hraw
    _ ≤ ((b - a) * 1024) *
        compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
          solution ha hab hbT depth := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (smoothDyadicClockDensityPrefix_le depth)
          (sub_nonneg.mpr hab))
        (compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix_nonneg
          solution ha hab hbT depth)
    _ = 1024 * (b - a) *
        compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
          solution ha hab hbT depth := by ring

theorem compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix_le_fullClockIntegral
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
        solution ha hab hbT depth ≤
      ∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time := by
  have hscale : ∀ scale ∈ Finset.range depth,
      compactOpenSmoothDyadicAdaptiveMatchedBandClockMass
          solution ha hab hbT scale ≤
        ∫ time in a..b, (4 : ℝ) ^ scale *
          compactOpenSmoothDyadicBandCoefficientMass
            solution ha hab hbT scale time := by
    intro scale _hscale
    unfold compactOpenSmoothDyadicAdaptiveMatchedBandClockMass
    exact intervalIntegral.integral_mono_interval
      (le_adaptiveSmoothDyadicTerminalWindowStart hab scale)
      (adaptiveSmoothDyadicTerminalWindowStart_le hab scale) le_rfl
      (ae_of_all _ fun time ↦ mul_nonneg (by positivity)
        (openSmoothDyadicBandCoefficientMass_nonneg solution
          (compactInteriorTime ha hab hbT time) scale))
      ((compactOpenSmoothDyadicBandCoefficientMass_intervalIntegrable
        solution ha hab hbT scale).const_mul ((4 : ℝ) ^ scale))
  have hsum := Finset.sum_le_sum hscale
  unfold compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
    compactOpenSmoothDyadicPrefixClockedCoefficientMass
  rw [intervalIntegral.integral_finsetSum (fun scale _hscale ↦
    (compactOpenSmoothDyadicBandCoefficientMass_intervalIntegrable
      solution ha hab hbT scale).const_mul ((4 : ℝ) ^ scale))]
  exact hsum

/-- The adaptive diagonal is paid on every ordered compact interior interval. -/
theorem openPeriodicSolutionOn_adaptiveMatchedL1Prefix_sq_le_linearBoundaryWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu) (depth : ℕ) :
    nu * compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      1024 * (b - a) * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|) := by
  have hpacking :=
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_uniformClockMass
      solution ha hab hbT depth
  have hwindow :=
    compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix_le_fullClockIntegral
      solution ha hab hbT depth
  have hledger :=
    openPeriodicSolutionOn_integral_prefixClockedCoefficientMass_le_linearBoundaryWork
      solution ha hab hbT hnu depth
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
  calc
    nu * compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      nu * (1024 * (b - a) *
        compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
          solution ha hab hbT depth) :=
      mul_le_mul_of_nonneg_left hpacking hnu.le
    _ = 1024 * (b - a) *
        (nu * compactOpenSmoothDyadicAdaptiveMatchedClockMassPrefix
          solution ha hab hbT depth) := by ring
    _ ≤ 1024 * (b - a) *
        (nu * ∫ time in a..b,
          compactOpenSmoothDyadicPrefixClockedCoefficientMass
            solution ha hab hbT depth time) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hwindow hnu.le)
        (mul_nonneg (by norm_num) hlength)
    _ ≤ 1024 * (b - a) * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|) :=
      mul_le_mul_of_nonneg_left hledger
        (mul_nonneg (by norm_num) hlength)

/-! ## Exact adaptive off-diagonal fibre -/

/-- The earlier-history cells excluded by the adaptive scale-matched diagonal. -/
def compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    ∫ time in a..adaptiveSmoothDyadicTerminalWindowStart a b scale,
      compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale time

theorem compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    0 ≤ compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
      solution ha hab hbT depth := by
  unfold compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
  exact Finset.sum_nonneg fun scale _hscale ↦
    intervalIntegral.integral_nonneg
      (le_adaptiveSmoothDyadicTerminalWindowStart hab scale)
      (fun time _htime ↦
        compactOpenSmoothDyadicVorticityBandSpatialSup_nonneg
          solution ha hab hbT scale time)

/-- The common unweighted scale--time rectangle is exactly the adaptive matched diagonal plus
its earlier-history reconstruction fibre on every ordered compact interval. -/
theorem compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_eq_adaptiveOffDiagonal_add_matched
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution ha hab hbT depth =
      compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
          solution ha hab hbT depth +
        compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
          solution ha hab hbT depth := by
  unfold compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
    compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
    compactOpenSmoothDyadicAdaptiveMatchedBandL1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro scale _hscale
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale).intervalIntegrable _ _)
    ((continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale).intervalIntegrable _ _)).symm

section Audit

#print axioms compactOpenSmoothDyadicAdaptiveMatchedBandL1_sq_le_density_mul_clockMass
#print axioms compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_uniformClockMass
#print axioms openPeriodicSolutionOn_adaptiveMatchedL1Prefix_sq_le_linearBoundaryWork
#print axioms compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_eq_adaptiveOffDiagonal_add_matched

end Audit

end Soma.Holonics.Millennium.NavierStokesAdaptiveClockMatchedPacking
