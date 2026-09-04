import ElementaryHolonics.Millennium.NavierStokesClockWeightedCompactTimePacking
import ElementaryHolonics.Millennium.NavierStokesSmoothMildSourceChronology

/-!
# Mild heat transport of the off-diagonal scale--time fibre

**[proved-derived; formal-checked]**  The earlier-history cell of shell `j`,
`[a, b - 4⁻ʲ]`, is transported through the actual Fourier mild identity.  At every target time
the direct smooth band is bounded by two explicitly caused populations:

* the earlier-face vorticity coefficients with their exact modewise heat multipliers; and
* the triangular nonlinear history `a ≤ sourceTime ≤ targetTime`, with the same exact heat
  multipliers and the actual nonlinear vorticity modes.

Time integration therefore returns an unconditional decomposition of the exact off-diagonal
fibre.  The heat orbit of the initial population is paid by the addressed reciprocal parabolic
shell clock.  Finite scale summation introduces no depth factor.

**[open]**  The remaining nonlinear object is the scale-critical triangular source population
defined below.  It is the shortest separator returned by this composition: the matched diagonal
is paid by the scale--time ledger, the earlier heat face is paid by strict-interior restart
coefficients, and no theorem here bounds the nonlinear triangular population by those two
receivers.  It is retained with source chronology, frequency addresses, smooth weights, heat
clocks, and the complete finite scale word.  No terminal conclusion is asserted.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesOffDiagonalMildHeatTransport

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesClockWeightedCompactTimePacking
open Soma.Holonics.Millennium.NavierStokesClockWeightedSpatialBandPacking
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceChronology
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceClockBound
open Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

set_option maxHeartbeats 2400000

/-! ## Causal populations over the fixed compact chart -/

/-- The exact modewise heat population emitted by the earlier face `a` and observed at a target
time.  No heat multiplier is collapsed to `1`. -/
def compactOffDiagonalInitialHeatCoefficientMassAt
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (targetTime : ℝ) : ℝ :=
  ∑ frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
    |dyadicHodgeBandWeight scale frequency| *
      heatStokesMultiplier nu (targetTime - a) frequency *
        ‖openPeriodicVorticityFourierMode solution
          ⟨a, ha, hab.trans_lt hbT⟩ frequency‖

theorem compactOffDiagonalInitialHeatCoefficientMassAt_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (targetTime : ℝ) :
    0 ≤ compactOffDiagonalInitialHeatCoefficientMassAt
      solution ha hab hbT scale targetTime := by
  unfold compactOffDiagonalInitialHeatCoefficientMassAt
  exact Finset.sum_nonneg fun frequency _hfrequency ↦ by
    have hheat : 0 ≤ heatStokesMultiplier nu (targetTime - a) frequency := by
      unfold heatStokesMultiplier
      positivity
    positivity

theorem continuous_compactOffDiagonalInitialHeatCoefficientMassAt
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    Continuous (compactOffDiagonalInitialHeatCoefficientMassAt
      solution ha hab hbT scale) := by
  unfold compactOffDiagonalInitialHeatCoefficientMassAt
  apply continuous_finsetSum
  intro frequency _hfrequency
  apply (continuous_const.mul ?_).mul continuous_const
  unfold heatStokesMultiplier
  fun_prop

/-- One target/source cell of the actual nonlinear history.  The compact clamp is fixed once on
`[a,b]`; on the causal triangle used below it is literally the open solution's nonlinear mode. -/
def compactOffDiagonalClockedNonlinearSourceMassAt
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (scale : ℕ) (targetTime sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
    |dyadicHodgeBandWeight scale frequency| *
      heatStokesMultiplier nu (targetTime - sourceTime) frequency *
        ‖compactVorticityNonlinearMode
          solution ha hab hbT frequency sourceTime‖

theorem compactOffDiagonalClockedNonlinearSourceMassAt_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (scale : ℕ) (targetTime sourceTime : ℝ) :
    0 ≤ compactOffDiagonalClockedNonlinearSourceMassAt
      solution ha hab hbT scale targetTime sourceTime := by
  unfold compactOffDiagonalClockedNonlinearSourceMassAt
  exact Finset.sum_nonneg fun frequency _hfrequency ↦ by
    have hheat : 0 ≤ heatStokesMultiplier nu (targetTime - sourceTime) frequency := by
      unfold heatStokesMultiplier
      positivity
    positivity

theorem continuous_uncurry_compactOffDiagonalClockedNonlinearSourceMassAt
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    Continuous (Function.uncurry
      (compactOffDiagonalClockedNonlinearSourceMassAt
        solution ha hab hbT scale)) := by
  unfold compactOffDiagonalClockedNonlinearSourceMassAt Function.uncurry
  apply continuous_finsetSum
  intro frequency _hfrequency
  have hheat : Continuous (fun times : ℝ × ℝ ↦
      heatStokesMultiplier nu (times.1 - times.2) frequency) := by
    unfold heatStokesMultiplier
    fun_prop
  exact (continuous_const.mul hheat).mul
    ((continuous_compactVorticityNonlinearMode
      solution ha hab hbT frequency).norm.comp continuous_snd)

/-- The complete nonlinear source history visible at one target time. -/
def compactOffDiagonalClockedNonlinearHistoryMassAt
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (scale : ℕ) (targetTime : ℝ) : ℝ :=
  ∫ sourceTime in a..targetTime,
    compactOffDiagonalClockedNonlinearSourceMassAt
      solution ha hab hbT scale targetTime sourceTime

theorem continuous_compactOffDiagonalClockedNonlinearHistoryMassAt
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    Continuous (compactOffDiagonalClockedNonlinearHistoryMassAt
      solution ha hab hbT scale) := by
  unfold compactOffDiagonalClockedNonlinearHistoryMassAt
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact continuous_uncurry_compactOffDiagonalClockedNonlinearSourceMassAt
      solution ha hab hbT scale
  · exact continuous_id

theorem compactOffDiagonalClockedNonlinearHistoryMassAt_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ)
    {targetTime : ℝ} (hat : a ≤ targetTime) :
    0 ≤ compactOffDiagonalClockedNonlinearHistoryMassAt
      solution ha hab hbT scale targetTime := by
  unfold compactOffDiagonalClockedNonlinearHistoryMassAt
  exact intervalIntegral.integral_nonneg hat fun sourceTime _hsourceTime ↦
    compactOffDiagonalClockedNonlinearSourceMassAt_nonneg
      solution ha hab hbT scale targetTime sourceTime

/-! ## Pointwise transport through the actual mild identity -/

private theorem compactSmoothInitialVorticityHeatBandSpatialSup_le_offDiagonalInitialMass
    {T nu a b targetTime : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hat : a ≤ targetTime) (htb : targetTime ≤ b) (scale : ℕ) :
    compactSmoothInitialVorticityHeatBandSpatialSup
        solution ha hat (htb.trans_lt hbT) scale ≤
      compactOffDiagonalInitialHeatCoefficientMassAt
        solution ha hab hbT scale targetTime := by
  unfold compactSmoothInitialVorticityHeatBandSpatialSup
    compactSmoothInitialVorticityHeatBand
  rw [finiteFourierSynthesis_dyadicHodgeBand_eq_twoSharpShells]
  apply (ContinuousMap.norm_le _
    (compactOffDiagonalInitialHeatCoefficientMassAt_nonneg
      solution ha hab hbT scale targetTime)).2
  intro q
  calc
    ‖finiteFourierSynthesis
        (fun frequency ↦ (dyadicHodgeBandWeight scale frequency : ℂ) •
          compactInitialVorticityHeatCoefficient
            solution ha hat (htb.trans_lt hbT) frequency)
        (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)) q‖ ≤
      ∑ frequency ∈
          (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
        ‖(dyadicHodgeBandWeight scale frequency : ℂ) •
          compactInitialVorticityHeatCoefficient
            solution ha hat (htb.trans_lt hbT) frequency‖ :=
      norm_finiteFourierSynthesis_le_sum_norm _ _ q
    _ = compactOffDiagonalInitialHeatCoefficientMassAt
        solution ha hab hbT scale targetTime := by
      unfold compactOffDiagonalInitialHeatCoefficientMassAt
        compactInitialVorticityHeatCoefficient
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have hheat : 0 ≤ heatStokesMultiplier nu (targetTime - a) frequency := by
        unfold heatStokesMultiplier
        positivity
      rw [abs_of_nonneg hheat]
      rw [mul_assoc]

private theorem compactSmoothClockedSourceMassAt_eq_offDiagonal
    {T nu a b targetTime sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hat : a ≤ targetTime) (htb : targetTime ≤ b)
    (hsource : sourceTime ∈ Icc a targetTime) (scale : ℕ) :
    compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
        solution ha hat (htb.trans_lt hbT) scale sourceTime =
      compactOffDiagonalClockedNonlinearSourceMassAt
        solution ha hab hbT scale targetTime sourceTime := by
  unfold compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
    compactOffDiagonalClockedNonlinearSourceMassAt
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  congr 1
  rw [compactVorticityNonlinearMode_eq_actual
      solution ha hat (htb.trans_lt hbT) frequency hsource,
    compactVorticityNonlinearMode_eq_actual
      solution ha hab hbT frequency ⟨hsource.1, hsource.2.trans htb⟩]

/-- **Pointwise causal mild inequality.**  On the fixed compact chart, one actual smooth band is
paid by the exact earlier heat population plus the complete modewise clocked nonlinear history. -/
theorem compactOpenSmoothDyadicVorticityBandSpatialSup_le_causalMildPopulations
    {T nu a b targetTime : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (htarget : targetTime ∈ Icc a b) (scale : ℕ) :
    compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale targetTime ≤
      compactOffDiagonalInitialHeatCoefficientMassAt
          solution ha hab hbT scale targetTime +
        compactOffDiagonalClockedNonlinearHistoryMassAt
          solution ha hab hbT scale targetTime := by
  have hmild :=
    openPeriodicSmoothDyadicVorticityBandSpatialSup_le_initialHeat_add_mildSource
      solution ha htarget.1 (htarget.2.trans_lt hbT) scale
  have hinitial :=
    compactSmoothInitialVorticityHeatBandSpatialSup_le_offDiagonalInitialMass
      solution ha hab hbT htarget.1 htarget.2 scale
  have hsource :=
    compactSmoothMildSourceIntegratedBandSpatialSup_le_integral_clockedSourceHistory
      solution hnu ha htarget.1 (htarget.2.trans_lt hbT) scale
  have hhistory :
      (∫ sourceTime in a..targetTime,
        compactSmoothDyadicVorticityNonlinearClockedSourceMassAt
          solution ha htarget.1 (htarget.2.trans_lt hbT) scale sourceTime) =
      compactOffDiagonalClockedNonlinearHistoryMassAt
        solution ha hab hbT scale targetTime := by
    unfold compactOffDiagonalClockedNonlinearHistoryMassAt
    apply intervalIntegral.integral_congr
    intro sourceTime hsourceTime
    rw [uIcc_of_le htarget.1] at hsourceTime
    exact compactSmoothClockedSourceMassAt_eq_offDiagonal
      solution ha hab hbT htarget.1 htarget.2
        ⟨hsourceTime.1, hsourceTime.2⟩ scale
  have hactual :
      compactOpenSmoothDyadicVorticityBandSpatialSup
          solution ha hab hbT scale targetTime =
        openPeriodicSmoothDyadicVorticityBandSpatialSup solution
          ⟨targetTime, ha.trans_le htarget.1, htarget.2.trans_lt hbT⟩ scale := by
    unfold compactOpenSmoothDyadicVorticityBandSpatialSup
    congr 2
    apply Subtype.ext
    exact compactInteriorTime_eq ha hab hbT htarget
  rw [hactual]
  exact hmild.trans (add_le_add hinitial (hsource.trans_eq hhistory))

/-! ## Per-shell earlier-history decomposition -/

/-- Initial heat contribution to shell `j`'s off-diagonal time cell. -/
def compactOffDiagonalInitialHeatContribution
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) : ℝ :=
  ∫ targetTime in a..smoothDyadicTerminalWindowStart b scale,
    compactOffDiagonalInitialHeatCoefficientMassAt
      solution ha hab hbT scale targetTime

/-- The minimal chronology-preserving nonlinear population separating the off-diagonal cell from
the already paid heat and clock receivers. -/
def compactOffDiagonalScaleCriticalNonlinearSourceContribution
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) : ℝ :=
  ∫ targetTime in a..smoothDyadicTerminalWindowStart b scale,
    compactOffDiagonalClockedNonlinearHistoryMassAt
      solution ha hab hbT scale targetTime

theorem compactOffDiagonalInitialHeatContribution_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (habUnit : a ≤ b - 1)
    (scale : ℕ) :
    0 ≤ compactOffDiagonalInitialHeatContribution
      solution ha hab hbT scale := by
  unfold compactOffDiagonalInitialHeatContribution
  exact intervalIntegral.integral_nonneg
    (leftEndpoint_le_smoothDyadicTerminalWindowStart habUnit scale)
    (fun targetTime _htargetTime ↦
      compactOffDiagonalInitialHeatCoefficientMassAt_nonneg
        solution ha hab hbT scale targetTime)

theorem compactOffDiagonalScaleCriticalNonlinearSourceContribution_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (habUnit : a ≤ b - 1)
    (scale : ℕ) :
    0 ≤ compactOffDiagonalScaleCriticalNonlinearSourceContribution
      solution ha hab hbT scale := by
  unfold compactOffDiagonalScaleCriticalNonlinearSourceContribution
  exact intervalIntegral.integral_nonneg
    (leftEndpoint_le_smoothDyadicTerminalWindowStart habUnit scale)
    (fun targetTime htargetTime ↦
      compactOffDiagonalClockedNonlinearHistoryMassAt_nonneg
        solution ha hab hbT scale htargetTime.1)

/-- **Unconditional one-shell off-diagonal mild transport.**  The exact earlier-history spatial
integral is bounded by its heat-transported earlier face plus its retained triangular nonlinear
source population. -/
theorem compactOpenSmoothDyadicOffDiagonalBandIntegral_le_initialHeat_add_nonlinearSource
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (habUnit : a ≤ b - 1) (scale : ℕ) :
    (∫ targetTime in a..smoothDyadicTerminalWindowStart b scale,
      compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale targetTime) ≤
      compactOffDiagonalInitialHeatContribution solution ha hab hbT scale +
        compactOffDiagonalScaleCriticalNonlinearSourceContribution
          solution ha hab hbT scale := by
  let windowStart := smoothDyadicTerminalWindowStart b scale
  have haw : a ≤ windowStart :=
    leftEndpoint_le_smoothDyadicTerminalWindowStart habUnit scale
  have hwb : windowStart ≤ b := smoothDyadicTerminalWindowStart_le b scale
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
  unfold compactOffDiagonalInitialHeatContribution
    compactOffDiagonalScaleCriticalNonlinearSourceContribution
  rw [← intervalIntegral.integral_add
    ((continuous_compactOffDiagonalInitialHeatCoefficientMassAt
      solution ha hab hbT scale).intervalIntegrable _ _)
    ((continuous_compactOffDiagonalClockedNonlinearHistoryMassAt
      solution ha hab hbT scale).intervalIntegrable _ _)]
  exact hmono

/-! ## Exact heat-clock service of the earlier face -/

private theorem adjacentDyadicFrequencyShell_disjoint (scale : ℕ) :
    Disjoint (dyadicFrequencyShell scale) (dyadicFrequencyShell (scale + 1)) := by
  rw [Finset.disjoint_left]
  intro frequency hscale hnext
  rw [mem_dyadicFrequencyShell_iff] at hscale hnext
  exact hnext.2 hscale.1

private theorem intervalIntegral_initialHeatMode_le_scaleClock
    {T nu a b windowStart : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (haw : a ≤ windowStart) (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈
      (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1))) :
    (∫ targetTime in a..windowStart,
      |dyadicHodgeBandWeight scale frequency| *
        heatStokesMultiplier nu (targetTime - a) frequency *
          ‖openPeriodicVorticityFourierMode solution
            ⟨a, ha, hab.trans_lt hbT⟩ frequency‖) ≤
      dyadicParabolicClockBudget nu scale *
        complexVectorL1 (openPeriodicVorticityFourierMode solution
          ⟨a, ha, hab.trans_lt hbT⟩ frequency) := by
  let coefficient := openPeriodicVorticityFourierMode solution
    ⟨a, ha, hab.trans_lt hbT⟩ frequency
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

/-- The exact earlier-face heat orbit of one off-diagonal shell is serviced by its reciprocal
parabolic clock and only the two actual restart shells supporting the smooth band. -/
theorem compactOffDiagonalInitialHeatContribution_le_clockBudget_mul_restartShells
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (habUnit : a ≤ b - 1) (scale : ℕ) :
    compactOffDiagonalInitialHeatContribution solution ha hab hbT scale ≤
      dyadicParabolicClockBudget nu scale *
        (openPeriodicVorticityDyadicShellCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ scale +
          openPeriodicVorticityDyadicShellCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ (scale + 1)) := by
  let windowStart := smoothDyadicTerminalWindowStart b scale
  have haw : a ≤ windowStart :=
    leftEndpoint_le_smoothDyadicTerminalWindowStart habUnit scale
  unfold compactOffDiagonalInitialHeatContribution
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
          exact intervalIntegral_initialHeatMode_le_scaleClock
            solution hnu ha hab hbT haw scale hfrequency
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

/-! ## Finite scale word and the depth-free earlier-face payment -/

/-- Exact finite initial-heat population in the off-diagonal word. -/
def compactOffDiagonalInitialHeatContributionPrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactOffDiagonalInitialHeatContribution solution ha hab hbT scale

/-- Complete finite chronology-preserving nonlinear separator. -/
def compactOffDiagonalScaleCriticalNonlinearSourcePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactOffDiagonalScaleCriticalNonlinearSourceContribution
      solution ha hab hbT scale

/-- Exact finite parabolic-clock payment requested by the earlier face. -/
def compactOffDiagonalInitialClockPaymentPrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    dyadicParabolicClockBudget nu scale *
      (openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨a, ha, hab.trans_lt hbT⟩ scale +
        openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨a, ha, hab.trans_lt hbT⟩ (scale + 1))

/-- Summing the exact per-shell mild decomposition introduces no scale-depth multiplier. -/
theorem compactOpenSmoothDyadicOffDiagonalFiber_le_initialHeatPrefix_add_nonlinearSourcePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (habUnit : a ≤ b - 1) (depth : ℕ) :
    compactOpenSmoothDyadicOffDiagonalScaleTimeReconstructionFiber
        solution ha hab hbT depth ≤
      compactOffDiagonalInitialHeatContributionPrefix solution ha hab hbT depth +
        compactOffDiagonalScaleCriticalNonlinearSourcePrefix
          solution ha hab hbT depth := by
  unfold compactOpenSmoothDyadicOffDiagonalScaleTimeReconstructionFiber
    compactOffDiagonalInitialHeatContributionPrefix
    compactOffDiagonalScaleCriticalNonlinearSourcePrefix
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun scale _hscale ↦
    compactOpenSmoothDyadicOffDiagonalBandIntegral_le_initialHeat_add_nonlinearSource
      solution hnu ha hab hbT habUnit scale

/-- Exact finite-word heat service, still retaining every shell clock before its uniform collapse. -/
theorem compactOffDiagonalInitialHeatContributionPrefix_le_clockPaymentPrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (habUnit : a ≤ b - 1) (depth : ℕ) :
    compactOffDiagonalInitialHeatContributionPrefix solution ha hab hbT depth ≤
      compactOffDiagonalInitialClockPaymentPrefix solution ha hab hbT depth := by
  unfold compactOffDiagonalInitialHeatContributionPrefix
    compactOffDiagonalInitialClockPaymentPrefix
  exact Finset.sum_le_sum fun scale _hscale ↦
    compactOffDiagonalInitialHeatContribution_le_clockBudget_mul_restartShells
      solution hnu ha hab hbT habUnit scale

/-- The earlier-face clock word has a depth-independent payment by the complete restart
coefficient population.  The exact shell clocks were used before this final receiver collapse. -/
theorem compactOffDiagonalInitialClockPaymentPrefix_le_viscosityInv_mul_restartPayment
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) :
    compactOffDiagonalInitialClockPaymentPrefix solution ha hab hbT depth ≤
      nu⁻¹ * smoothRestartCoefficientPayment solution ha (hab.trans_lt hbT) := by
  let restartMass : ℕ → ℝ := fun scale ↦
    openPeriodicVorticityDyadicShellCoefficientMass solution
        ⟨a, ha, hab.trans_lt hbT⟩ scale +
      openPeriodicVorticityDyadicShellCoefficientMass solution
        ⟨a, ha, hab.trans_lt hbT⟩ (scale + 1)
  have hmass := summable_openPeriodicVorticityDyadicShellCoefficientMass solution
    ⟨a, ha, hab.trans_lt hbT⟩
  have hrestart : Summable restartMass := by
    exact hmass.add ((summable_nat_add_iff 1).2 hmass)
  have hclock (scale : ℕ) : dyadicParabolicClockBudget nu scale ≤ nu⁻¹ := by
    rw [dyadicParabolicClockBudget_eq_viscosityInv_mul_quarterPow]
    apply mul_le_of_le_one_right (inv_nonneg.mpr hnu.le)
    simpa only [smoothDyadicReciprocalShellClock, inv_pow] using
      (smoothDyadicReciprocalShellClock_le_one scale)
  have hrestartNonneg (scale : ℕ) : 0 ≤ restartMass scale := by
    exact add_nonneg
      (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution
        ⟨a, ha, hab.trans_lt hbT⟩ scale)
      (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution
        ⟨a, ha, hab.trans_lt hbT⟩ (scale + 1))
  have hfinite :
      (∑ scale ∈ Finset.range depth,
        dyadicParabolicClockBudget nu scale * restartMass scale) ≤
      ∑ scale ∈ Finset.range depth, nu⁻¹ * restartMass scale := by
    exact Finset.sum_le_sum fun scale _hscale ↦
      mul_le_mul_of_nonneg_right (hclock scale) (hrestartNonneg scale)
  have htoTsum :
      (∑ scale ∈ Finset.range depth, nu⁻¹ * restartMass scale) ≤
      ∑' scale : ℕ, nu⁻¹ * restartMass scale := by
    exact (hrestart.mul_left nu⁻¹).sum_le_tsum (Finset.range depth)
      (fun scale _hscale ↦ mul_nonneg (inv_nonneg.mpr hnu.le) (hrestartNonneg scale))
  unfold compactOffDiagonalInitialClockPaymentPrefix
    smoothRestartCoefficientPayment
  change (∑ scale ∈ Finset.range depth,
      dyadicParabolicClockBudget nu scale * restartMass scale) ≤
    nu⁻¹ * ∑' scale : ℕ, restartMass scale
  calc
    _ ≤ ∑ scale ∈ Finset.range depth, nu⁻¹ * restartMass scale := hfinite
    _ ≤ ∑' scale : ℕ, nu⁻¹ * restartMass scale := htoTsum
    _ = nu⁻¹ * ∑' scale : ℕ, restartMass scale := hrestart.tsum_mul_left nu⁻¹

/-- **Depth-free off-diagonal estimate.**  The heat part of the actual Fourier mild identity is
closed by the restart population.  The only term not returned by that closure is the explicit
scale-critical nonlinear causal triangle. -/
theorem compactOpenSmoothDyadicOffDiagonalFiber_le_restartPayment_add_nonlinearSourcePrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (habUnit : a ≤ b - 1) (depth : ℕ) :
    compactOpenSmoothDyadicOffDiagonalScaleTimeReconstructionFiber
        solution ha hab hbT depth ≤
      nu⁻¹ * smoothRestartCoefficientPayment solution ha (hab.trans_lt hbT) +
        compactOffDiagonalScaleCriticalNonlinearSourcePrefix
          solution ha hab hbT depth := by
  have hmild :=
    compactOpenSmoothDyadicOffDiagonalFiber_le_initialHeatPrefix_add_nonlinearSourcePrefix
      solution hnu.le ha hab hbT habUnit depth
  have hheat := compactOffDiagonalInitialHeatContributionPrefix_le_clockPaymentPrefix
    solution hnu ha hab hbT habUnit depth
  have hclock :=
    compactOffDiagonalInitialClockPaymentPrefix_le_viscosityInv_mul_restartPayment
      solution hnu ha hab hbT depth
  exact hmild.trans (add_le_add (hheat.trans hclock) le_rfl)

/-! ## Join to the diagonal clock ledger -/

/-- The matched diagonal word, already separated from the earlier history, is the square-root
receiver of the exact one-copy clock ledger.  The constant is the proved uniform smooth-aperture
density constant, not a scale-depth count. -/
theorem compactOpenSmoothDyadicMatchedTerminalL1Prefix_le_sqrt_linearBoundaryClockBudget
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (habUnit : a ≤ b - 1) (depth : ℕ) :
    compactOpenSmoothDyadicMatchedTerminalL1Prefix
        solution ha hab hbT depth ≤
      32 * Real.sqrt (nu⁻¹ *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          |∫ time in a..b,
            compactOpenSmoothDyadicLinearBoundarySignedWorkRate
              solution ha hab hbT depth time|)) := by
  let matched := compactOpenSmoothDyadicMatchedTerminalL1Prefix
    solution ha hab hbT depth
  let budget := (1 / 2 : ℝ) *
      openPeriodicFullVorticityCoefficientMass solution
        ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
    |∫ time in a..b,
      compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time|
  have hmatched : 0 ≤ matched := by
    unfold matched compactOpenSmoothDyadicMatchedTerminalL1Prefix
    exact Finset.sum_nonneg fun scale _hscale ↦
      compactOpenSmoothDyadicMatchedTerminalBandL1_nonneg
        solution ha hab hbT scale
  have hbudget : 0 ≤ budget := by
    dsimp [budget]
    positivity
  have hledger : nu * matched ^ 2 ≤ 1024 * budget := by
    exact openPeriodicSolutionOn_matchedTerminalL1Prefix_sq_le_linearBoundaryWork
      solution ha hab hbT habUnit hnu depth
  have hscaled : matched ^ 2 ≤ 1024 * (nu⁻¹ * budget) := by
    have hmul := mul_le_mul_of_nonneg_left hledger (inv_nonneg.mpr hnu.le)
    calc
      matched ^ 2 = nu⁻¹ * (nu * matched ^ 2) := by
        field_simp [hnu.ne']
      _ ≤ nu⁻¹ * (1024 * budget) := hmul
      _ = 1024 * (nu⁻¹ * budget) := by ring
  have hreceiver : 0 ≤ 32 * Real.sqrt (nu⁻¹ * budget) := by positivity
  apply (sq_le_sq₀ hmatched hreceiver).mp
  calc
    matched ^ 2 ≤ 1024 * (nu⁻¹ * budget) := hscaled
    _ = (32 * Real.sqrt (nu⁻¹ * budget)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt]
      · norm_num
      · exact mul_nonneg (inv_nonneg.mpr hnu.le) hbudget

/-- **Complete finite scale--time mild/ledger inequality.**  Every part of the finite unweighted
rectangle is now assigned to its actual causal owner: earlier heat to restart coefficients,
the matched diagonal to the clock ledger, and the remaining triangular Duhamel population to the
explicit scale-critical nonlinear separator.  There is no factor depending on `depth`. -/
theorem compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_mildHeat_clockLedger_add_separator
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (habUnit : a ≤ b - 1) (depth : ℕ) :
    compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution ha hab hbT depth ≤
      nu⁻¹ * smoothRestartCoefficientPayment solution ha (hab.trans_lt hbT) +
        compactOffDiagonalScaleCriticalNonlinearSourcePrefix
          solution ha hab hbT depth +
        32 * Real.sqrt (nu⁻¹ *
          ((1 / 2 : ℝ) *
              openPeriodicFullVorticityCoefficientMass solution
                ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
            |∫ time in a..b,
              compactOpenSmoothDyadicLinearBoundarySignedWorkRate
                solution ha hab hbT depth time|)) := by
  rw [compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_eq_offDiagonal_add_matched]
  exact add_le_add
    (compactOpenSmoothDyadicOffDiagonalFiber_le_restartPayment_add_nonlinearSourcePrefix
      solution hnu ha hab hbT habUnit depth)
    (compactOpenSmoothDyadicMatchedTerminalL1Prefix_le_sqrt_linearBoundaryClockBudget
      solution hnu ha hab hbT habUnit depth)

/-! ## Recursive pantographic tiling is not a closure -/

/-- Remaining interval length after `step` recursively removes the final reciprocal-clock
fraction of the current interval. -/
def recursivePantographicRemainingLength
    (intervalLength : ℝ) (scale step : ℕ) : ℝ :=
  intervalLength * (1 - smoothDyadicReciprocalShellClock scale) ^ step

private theorem recursivePantographicContraction_norm_lt_one (scale : ℕ) :
    ‖(1 : ℝ) - smoothDyadicReciprocalShellClock scale‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · linarith [smoothDyadicReciprocalShellClock_pos scale]
  · linarith [smoothDyadicReciprocalShellClock_le_one scale]

/-- Exact cumulative remaining length of recursive terminal-fraction removal.  Although each
remaining interval converges to zero, its total multiplicity is `4^scale`. -/
theorem tsum_recursivePantographicRemainingLength
    (intervalLength : ℝ) (scale : ℕ) :
    (∑' step : ℕ,
      recursivePantographicRemainingLength intervalLength scale step) =
      intervalLength * (4 : ℝ) ^ scale := by
  have hgeometric := recursivePantographicContraction_norm_lt_one scale
  unfold recursivePantographicRemainingLength
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hgeometric]
  have hclockInverse :
      (1 - (1 - smoothDyadicReciprocalShellClock scale))⁻¹ =
        (4 : ℝ) ^ scale := by
    rw [show 1 - (1 - smoothDyadicReciprocalShellClock scale) =
      smoothDyadicReciprocalShellClock scale by ring]
    unfold smoothDyadicReciprocalShellClock
    rw [inv_inv]
  rw [hclockInverse]

/-- Exact accumulated diagonal density under recursive coverage.  The geometric tiling spends
one `4^scale` gain: `card / 16^scale` becomes `intervalLength * card / 4^scale`. -/
theorem tsum_recursivePantographicDiagonalDensity
    (intervalLength : ℝ) (scale : ℕ) :
    (∑' step : ℕ,
      (((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale) *
        recursivePantographicRemainingLength intervalLength scale step) =
      intervalLength *
        ((smoothDyadicBandNativeAperture scale).card : ℝ) / (4 : ℝ) ^ scale := by
  rw [tsum_mul_left, tsum_recursivePantographicRemainingLength]
  have h4 : (4 : ℝ) ^ scale ≠ 0 := by positivity
  have h16 : (16 : ℝ) ^ scale = ((4 : ℝ) ^ scale) ^ 2 := by
    rw [show (16 : ℝ) = 4 * 4 by norm_num, mul_pow, pow_two]
  rw [h16]
  field_simp [h4]

/-- The precise missing gain exposed by recursive tiling: multiplying its accumulated density by
one reciprocal shell clock restores the original summable diagonal density (times interval
length).  Any recursive coverage argument must obtain this gain from heat or nonlinear source
transport; the tiling itself does not supply it. -/
theorem reciprocalClock_mul_recursivePantographicAccumulatedDensity
    (intervalLength : ℝ) (scale : ℕ) :
    smoothDyadicReciprocalShellClock scale *
        (intervalLength *
          ((smoothDyadicBandNativeAperture scale).card : ℝ) / (4 : ℝ) ^ scale) =
      intervalLength *
        (((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale) := by
  unfold smoothDyadicReciprocalShellClock
  have h4 : (4 : ℝ) ^ scale ≠ 0 := by positivity
  have h16 : (16 : ℝ) ^ scale = ((4 : ℝ) ^ scale) ^ 2 := by
    rw [show (16 : ℝ) = 4 * 4 by norm_num, mul_pow, pow_two]
  rw [h16]
  field_simp [h4]

section Audit

#print axioms compactOpenSmoothDyadicVorticityBandSpatialSup_le_causalMildPopulations
#print axioms compactOpenSmoothDyadicOffDiagonalBandIntegral_le_initialHeat_add_nonlinearSource
#print axioms compactOffDiagonalInitialHeatContribution_le_clockBudget_mul_restartShells
#print axioms compactOffDiagonalInitialClockPaymentPrefix_le_viscosityInv_mul_restartPayment
#print axioms compactOpenSmoothDyadicOffDiagonalFiber_le_restartPayment_add_nonlinearSourcePrefix
#print axioms compactOpenSmoothDyadicMatchedTerminalL1Prefix_le_sqrt_linearBoundaryClockBudget
#print axioms compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_le_mildHeat_clockLedger_add_separator
#print axioms tsum_recursivePantographicRemainingLength
#print axioms tsum_recursivePantographicDiagonalDensity
#print axioms reciprocalClock_mul_recursivePantographicAccumulatedDensity

end Audit

end Soma.Holonics.Millennium.NavierStokesOffDiagonalMildHeatTransport
