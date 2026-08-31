import ElementaryHolonics.Millennium.NavierStokesOffDiagonalMildHeatTransport
import ElementaryHolonics.Millennium.NavierStokesAdaptiveClockPhysicalPhaseLedger

/-!
# Adaptive mild heat transport of the off-diagonal scale--time fibre

**[proved-derived; formal-checked]**  The mild/heat transport is normalized to the actual
ordered compact interval.  Shell `j` is split at
`b - (b - a) * 4⁻ʲ`; no unit exterior time and no `a ≤ b - 1` hypothesis occurs.

The exact Fourier heat population is serviced by the same reciprocal parabolic shell clock,
the adaptive matched diagonal is paid by the complete physical phase ledger, and the remaining
nonlinear object is retained as an explicitly adaptive, chronology-preserving Duhamel triangle.
Recursive adaptive tiling is recorded separately and does not masquerade as closure.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesAdaptiveOffDiagonalMildHeatTransport

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveClockMatchedPacking
open Soma.Holonics.Millennium.NavierStokesAdaptiveClockPhysicalPhaseLedger
open Soma.Holonics.Millennium.NavierStokesClockWeightedCompactTimePacking
open Soma.Holonics.Millennium.NavierStokesClockWeightedPhysicalPhaseLedger
open Soma.Holonics.Millennium.NavierStokesClockWeightedSpatialBandPacking
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOffDiagonalMildHeatTransport
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceClockBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

set_option maxHeartbeats 2400000

/-! ## Adaptive causal populations -/

/-- Earlier-face heat population over shell `j`'s adaptive off-diagonal cell. -/
def compactAdaptiveOffDiagonalInitialHeatContribution
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) : ℝ :=
  ∫ targetTime in a..adaptiveSmoothDyadicTerminalWindowStart a b scale,
    compactOffDiagonalInitialHeatCoefficientMassAt
      solution ha hab hbT scale targetTime

/-- The actual nonlinear Duhamel triangle over shell `j`'s adaptive earlier-history cell. -/
def compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) : ℝ :=
  ∫ targetTime in a..adaptiveSmoothDyadicTerminalWindowStart a b scale,
    compactOffDiagonalClockedNonlinearHistoryMassAt
      solution ha hab hbT scale targetTime

theorem compactAdaptiveOffDiagonalInitialHeatContribution_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    0 ≤ compactAdaptiveOffDiagonalInitialHeatContribution
      solution ha hab hbT scale := by
  unfold compactAdaptiveOffDiagonalInitialHeatContribution
  exact intervalIntegral.integral_nonneg
    (le_adaptiveSmoothDyadicTerminalWindowStart hab scale)
    (fun targetTime _htargetTime ↦
      compactOffDiagonalInitialHeatCoefficientMassAt_nonneg
        solution ha hab hbT scale targetTime)

theorem compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    0 ≤ compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution
      solution ha hab hbT scale := by
  unfold compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution
  exact intervalIntegral.integral_nonneg
    (le_adaptiveSmoothDyadicTerminalWindowStart hab scale)
    (fun targetTime htargetTime ↦
      compactOffDiagonalClockedNonlinearHistoryMassAt_nonneg
        solution ha hab hbT scale htargetTime.1)

/-- One adaptive off-diagonal shell is transported through the actual Fourier mild identity. -/
theorem compactOpenSmoothDyadicAdaptiveOffDiagonalBandIntegral_le_initialHeat_add_nonlinearSource
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (scale : ℕ) :
    (∫ targetTime in a..adaptiveSmoothDyadicTerminalWindowStart a b scale,
      compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale targetTime) ≤
      compactAdaptiveOffDiagonalInitialHeatContribution solution ha hab hbT scale +
        compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution
          solution ha hab hbT scale := by
  let windowStart := adaptiveSmoothDyadicTerminalWindowStart a b scale
  have haw : a ≤ windowStart :=
    le_adaptiveSmoothDyadicTerminalWindowStart hab scale
  have hwb : windowStart ≤ b :=
    adaptiveSmoothDyadicTerminalWindowStart_le hab scale
  have hleft : IntervalIntegrable
      (compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale) volume a windowStart :=
    (continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale).intervalIntegrable _ _
  have hright : IntervalIntegrable (fun targetTime ↦
      compactOffDiagonalInitialHeatCoefficientMassAt
          solution ha hab hbT scale targetTime +
        compactOffDiagonalClockedNonlinearHistoryMassAt
          solution ha hab hbT scale targetTime) volume a windowStart :=
    ((continuous_compactOffDiagonalInitialHeatCoefficientMassAt
      solution ha hab hbT scale).add
      (continuous_compactOffDiagonalClockedNonlinearHistoryMassAt
        solution ha hab hbT scale)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on haw hleft hright
    (fun targetTime htargetTime ↦
      compactOpenSmoothDyadicVorticityBandSpatialSup_le_causalMildPopulations
        solution hnu ha hab hbT
          ⟨htargetTime.1, htargetTime.2.trans hwb⟩ scale)
  unfold compactAdaptiveOffDiagonalInitialHeatContribution
    compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution
  rw [← intervalIntegral.integral_add
    ((continuous_compactOffDiagonalInitialHeatCoefficientMassAt
      solution ha hab hbT scale).intervalIntegrable _ _)
    ((continuous_compactOffDiagonalClockedNonlinearHistoryMassAt
      solution ha hab hbT scale).intervalIntegrable _ _)]
  exact hmono

/-! ## Exact adaptive heat-clock service -/

private theorem adjacentDyadicFrequencyShell_disjoint (scale : ℕ) :
    Disjoint (dyadicFrequencyShell scale) (dyadicFrequencyShell (scale + 1)) := by
  rw [Finset.disjoint_left]
  intro frequency hscale hnext
  rw [mem_dyadicFrequencyShell_iff] at hscale hnext
  exact hnext.2 hscale.1

private theorem intervalIntegral_adaptiveInitialHeatMode_le_scaleClock
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1))) :
    (∫ targetTime in a..adaptiveSmoothDyadicTerminalWindowStart a b scale,
      |dyadicHodgeBandWeight scale frequency| *
        heatStokesMultiplier nu (targetTime - a) frequency *
          ‖openPeriodicVorticityFourierMode solution
            ⟨a, ha, hab.trans_lt hbT⟩ frequency‖) ≤
      dyadicParabolicClockBudget nu scale *
        complexVectorL1 (openPeriodicVorticityFourierMode solution
          ⟨a, ha, hab.trans_lt hbT⟩ frequency) := by
  let windowStart := adaptiveSmoothDyadicTerminalWindowStart a b scale
  let coefficient := openPeriodicVorticityFourierMode solution
    ⟨a, ha, hab.trans_lt hbT⟩ frequency
  have haw : a ≤ windowStart :=
    le_adaptiveSmoothDyadicTerminalWindowStart hab scale
  have hreflect :
      (∫ targetTime in a..windowStart,
        heatStokesMultiplier nu (targetTime - a) frequency) =
      ∫ elapsed in (0 : ℝ)..(windowStart - a),
        heatStokesMultiplier nu elapsed frequency := by
    simpa only [sub_self] using
      (intervalIntegral.integral_comp_sub_right
        (fun elapsed : ℝ ↦ heatStokesMultiplier nu elapsed frequency) a
        (a := a) (b := windowStart))
  have hclock :
      (∫ targetTime in a..windowStart,
        heatStokesMultiplier nu (targetTime - a) frequency) ≤
      dyadicParabolicClockBudget nu scale := by
    rw [hreflect]
    rw [Finset.mem_union] at hfrequency
    rcases hfrequency with hfrequency | hfrequency
    · exact intervalIntegral_heatStokesMultiplier_le_dyadicParabolicClockBudget
        hnu (sub_nonneg.mpr haw) hfrequency
    · exact (intervalIntegral_heatStokesMultiplier_le_dyadicParabolicClockBudget
        hnu (sub_nonneg.mpr haw) hfrequency).trans
          (dyadicParabolicClockBudget_succ_le hnu scale)
  have hweight : |dyadicHodgeBandWeight scale frequency| ≤ 1 := by
    rw [abs_of_nonneg (dyadicHodgeBandWeight_nonneg scale frequency)]
    exact dyadicHodgeBandWeight_le_one scale frequency
  have hcoefficient :
      |dyadicHodgeBandWeight scale frequency| * ‖coefficient‖ ≤
        complexVectorL1 coefficient :=
    (mul_le_of_le_one_left (norm_nonneg coefficient) hweight).trans
      (norm_complexVector_le_complexVectorL1 coefficient)
  have hbudget : 0 ≤ dyadicParabolicClockBudget nu scale := by
    unfold dyadicParabolicClockBudget
    positivity
  calc
    (∫ targetTime in a..windowStart,
      |dyadicHodgeBandWeight scale frequency| *
        heatStokesMultiplier nu (targetTime - a) frequency * ‖coefficient‖) =
      (|dyadicHodgeBandWeight scale frequency| * ‖coefficient‖) *
        (∫ targetTime in a..windowStart,
          heatStokesMultiplier nu (targetTime - a) frequency) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro targetTime _htargetTime
        ring
    _ ≤ (|dyadicHodgeBandWeight scale frequency| * ‖coefficient‖) *
        dyadicParabolicClockBudget nu scale :=
      mul_le_mul_of_nonneg_left hclock (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    _ ≤ dyadicParabolicClockBudget nu scale * complexVectorL1 coefficient := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hcoefficient hbudget

/-- The adaptive earlier-face heat orbit has the same shell clock service as the normalized
construction; shrinking the window changes no restart payment. -/
theorem compactAdaptiveOffDiagonalInitialHeatContribution_le_clockBudget_mul_restartShells
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (scale : ℕ) :
    compactAdaptiveOffDiagonalInitialHeatContribution solution ha hab hbT scale ≤
      dyadicParabolicClockBudget nu scale *
        (openPeriodicVorticityDyadicShellCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ scale +
          openPeriodicVorticityDyadicShellCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ (scale + 1)) := by
  let windowStart := adaptiveSmoothDyadicTerminalWindowStart a b scale
  unfold compactAdaptiveOffDiagonalInitialHeatContribution
    compactOffDiagonalInitialHeatCoefficientMassAt
  rw [intervalIntegral.integral_finsetSum]
  · calc
      (∑ frequency ∈ dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1),
        ∫ targetTime in a..windowStart,
          |dyadicHodgeBandWeight scale frequency| *
            heatStokesMultiplier nu (targetTime - a) frequency *
              ‖openPeriodicVorticityFourierMode solution
                ⟨a, ha, hab.trans_lt hbT⟩ frequency‖) ≤
        ∑ frequency ∈ dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1),
          dyadicParabolicClockBudget nu scale *
            complexVectorL1 (openPeriodicVorticityFourierMode solution
              ⟨a, ha, hab.trans_lt hbT⟩ frequency) := by
          apply Finset.sum_le_sum
          intro frequency hfrequency
          exact intervalIntegral_adaptiveInitialHeatMode_le_scaleClock
            solution hnu ha hab hbT scale hfrequency
      _ = dyadicParabolicClockBudget nu scale *
          (openPeriodicVorticityDyadicShellCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ scale +
            openPeriodicVorticityDyadicShellCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ (scale + 1)) := by
        unfold openPeriodicVorticityDyadicShellCoefficientMass
        rw [Finset.sum_union (adjacentDyadicFrequencyShell_disjoint scale)]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
  · intro frequency _hfrequency
    exact (((continuous_const.mul (by
      unfold heatStokesMultiplier
      fun_prop)).mul continuous_const).intervalIntegrable _ _)

/-! ## Adaptive finite scale word -/

def compactAdaptiveOffDiagonalInitialHeatContributionPrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactAdaptiveOffDiagonalInitialHeatContribution
      solution ha hab hbT scale

/-- Complete nonlinear separator for the adaptive off-diagonal finite word. -/
def compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactAdaptiveOffDiagonalScaleCriticalNonlinearSourceContribution
      solution ha hab hbT scale

theorem compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_initialHeatPrefix_add_nonlinearSourcePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
        solution ha hab hbT depth ≤
      compactAdaptiveOffDiagonalInitialHeatContributionPrefix
          solution ha hab hbT depth +
        compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix
          solution ha hab hbT depth := by
  unfold compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
    compactAdaptiveOffDiagonalInitialHeatContributionPrefix
    compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun scale _hscale ↦
    compactOpenSmoothDyadicAdaptiveOffDiagonalBandIntegral_le_initialHeat_add_nonlinearSource
      solution hnu ha hab hbT scale

/-- The exact adaptive earlier-face heat word is bounded by the retained shell-clock payment. -/
theorem compactAdaptiveOffDiagonalInitialHeatContributionPrefix_le_clockPaymentPrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactAdaptiveOffDiagonalInitialHeatContributionPrefix
        solution ha hab hbT depth ≤
      compactOffDiagonalInitialClockPaymentPrefix solution ha hab hbT depth := by
  unfold compactAdaptiveOffDiagonalInitialHeatContributionPrefix
    compactOffDiagonalInitialClockPaymentPrefix
  exact Finset.sum_le_sum fun scale _hscale ↦
    compactAdaptiveOffDiagonalInitialHeatContribution_le_clockBudget_mul_restartShells
      solution hnu ha hab hbT scale

/-- **Adaptive depth-free off-diagonal estimate.**  Every ordered compact interior interval is
admitted.  The only unclosed term is the explicitly retained adaptive nonlinear triangle. -/
theorem compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restartPayment_add_nonlinearSourcePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
        solution ha hab hbT depth ≤
      nu⁻¹ * smoothRestartCoefficientPayment solution ha (hab.trans_lt hbT) +
        compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix
          solution ha hab hbT depth := by
  have hmild :=
    compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_initialHeatPrefix_add_nonlinearSourcePrefix
      solution hnu.le ha hab hbT depth
  have hheat := compactAdaptiveOffDiagonalInitialHeatContributionPrefix_le_clockPaymentPrefix
    solution hnu ha hab hbT depth
  have hclock :=
    compactOffDiagonalInitialClockPaymentPrefix_le_viscosityInv_mul_restartPayment
      solution hnu ha hab hbT depth
  exact hmild.trans (add_le_add (hheat.trans hclock) le_rfl)

/-! ## Adaptive matched diagonal through the physical phase ledger -/

/-- The adaptive diagonal is the square-root receiver of the complete finite-radius physical
phase ledger.  The actual interval length remains explicit. -/
theorem compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_sqrt_namedPhysicalLedger
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ≤
      32 * Real.sqrt (nu⁻¹ * ((b - a) *
        compactClockWeightedPhysicalPhaseLedger
          solution ha hab hbT depth radius)) := by
  let matched := compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
    solution ha hab hbT depth
  let ledger := compactClockWeightedPhysicalPhaseLedger
    solution ha hab hbT depth radius
  have hmatched : 0 ≤ matched := by
    unfold matched compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
      compactOpenSmoothDyadicAdaptiveMatchedBandL1
    exact Finset.sum_nonneg fun scale _hscale ↦
      intervalIntegral.integral_nonneg
        (adaptiveSmoothDyadicTerminalWindowStart_le hab scale)
        (fun time _htime ↦
          compactOpenSmoothDyadicVorticityBandSpatialSup_nonneg
            solution ha hab hbT scale time)
  have hledgerNonneg : 0 ≤ ledger := by
    unfold ledger compactClockWeightedPhysicalPhaseLedger
    positivity
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
  have hledger : nu * matched ^ 2 ≤ 1024 * (b - a) * ledger := by
    exact openPeriodicSolutionOn_adaptiveMatchedL1Prefix_sq_le_namedPhysicalLedger
      solution ha hab hbT hnu depth radius
  have hscaled : matched ^ 2 ≤
      1024 * (nu⁻¹ * ((b - a) * ledger)) := by
    have hmul := mul_le_mul_of_nonneg_left hledger (inv_nonneg.mpr hnu.le)
    calc
      matched ^ 2 = nu⁻¹ * (nu * matched ^ 2) := by
        field_simp [hnu.ne']
      _ ≤ nu⁻¹ * (1024 * (b - a) * ledger) := hmul
      _ = 1024 * (nu⁻¹ * ((b - a) * ledger)) := by ring
  have hreceiver :
      0 ≤ 32 * Real.sqrt (nu⁻¹ * ((b - a) * ledger)) := by positivity
  apply (sq_le_sq₀ hmatched hreceiver).mp
  calc
    matched ^ 2 ≤ 1024 * (nu⁻¹ * ((b - a) * ledger)) := hscaled
    _ = (32 * Real.sqrt (nu⁻¹ * ((b - a) * ledger))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt]
      · norm_num
      · exact mul_nonneg (inv_nonneg.mpr hnu.le)
          (mul_nonneg hlength hledgerNonneg)

/-- **Adaptive finite rectangle mild/physical-ledger inequality.**  This is valid on every
ordered compact interior interval and contains no unit-window or depth-multiplier hypothesis. -/
theorem compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_adaptiveMildHeat_physicalLedger_add_separator
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) :
    compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution ha hab hbT depth ≤
      nu⁻¹ * smoothRestartCoefficientPayment solution ha (hab.trans_lt hbT) +
        compactAdaptiveOffDiagonalScaleCriticalNonlinearSourcePrefix
          solution ha hab hbT depth +
        32 * Real.sqrt (nu⁻¹ * ((b - a) *
          compactClockWeightedPhysicalPhaseLedger
            solution ha hab hbT depth radius)) := by
  rw [compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_eq_adaptiveOffDiagonal_add_matched]
  exact add_le_add
    (compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restartPayment_add_nonlinearSourcePrefix
      solution hnu ha hab hbT depth)
    (compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_sqrt_namedPhysicalLedger
      solution hnu ha hab hbT depth radius)

/-! ## Exact recursive-tiling warning in the adaptive chart -/

def adaptiveRecursivePantographicRemainingLength
    (a b : ℝ) (scale step : ℕ) : ℝ :=
  recursivePantographicRemainingLength (b - a) scale step

theorem tsum_adaptiveRecursivePantographicRemainingLength
    (a b : ℝ) (scale : ℕ) :
    (∑' step : ℕ, adaptiveRecursivePantographicRemainingLength a b scale step) =
      (b - a) * (4 : ℝ) ^ scale := by
  exact tsum_recursivePantographicRemainingLength (b - a) scale

/-- Recursive adaptive coverage spends the full `4^scale` multiplicity and turns the summable
diagonal density into `(b-a) * card / 4^scale`. -/
theorem tsum_adaptiveRecursivePantographicDiagonalDensity
    (a b : ℝ) (scale : ℕ) :
    (∑' step : ℕ,
      (((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale) *
        adaptiveRecursivePantographicRemainingLength a b scale step) =
      (b - a) *
        ((smoothDyadicBandNativeAperture scale).card : ℝ) / (4 : ℝ) ^ scale := by
  exact tsum_recursivePantographicDiagonalDensity (b - a) scale

/-- One further reciprocal shell-clock gain is exactly what restores the adaptive diagonal
density.  It must come from heat/source transport, not from recursive coverage. -/
theorem reciprocalClock_mul_adaptiveRecursivePantographicAccumulatedDensity
    (a b : ℝ) (scale : ℕ) :
    smoothDyadicReciprocalShellClock scale *
        ((b - a) *
          ((smoothDyadicBandNativeAperture scale).card : ℝ) / (4 : ℝ) ^ scale) =
      (b - a) *
        (((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale) := by
  exact reciprocalClock_mul_recursivePantographicAccumulatedDensity (b - a) scale

section Audit

#print axioms compactOpenSmoothDyadicAdaptiveOffDiagonalBandIntegral_le_initialHeat_add_nonlinearSource
#print axioms compactAdaptiveOffDiagonalInitialHeatContribution_le_clockBudget_mul_restartShells
#print axioms compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restartPayment_add_nonlinearSourcePrefix
#print axioms compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_le_sqrt_namedPhysicalLedger
#print axioms compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_adaptiveMildHeat_physicalLedger_add_separator
#print axioms tsum_adaptiveRecursivePantographicRemainingLength
#print axioms tsum_adaptiveRecursivePantographicDiagonalDensity
#print axioms reciprocalClock_mul_adaptiveRecursivePantographicAccumulatedDensity

end Audit

end Soma.Holonics.Millennium.NavierStokesAdaptiveOffDiagonalMildHeatTransport
