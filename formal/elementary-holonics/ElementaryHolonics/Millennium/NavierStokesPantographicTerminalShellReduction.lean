import ElementaryHolonics.Millennium.NavierStokesPantographicPhaseLocalShell
import ElementaryHolonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability
import ElementaryHolonics.Millennium.NavierStokesTerminalDyadicShellPacking

/-!
# The terminal shell obstruction is the signed pantographic population

**[proved-derived; formal-checked]** Fix one earlier interior face `s`.  The heat-transported
dyadic shells are paid uniformly in every later time by the absolutely summable Fourier
coefficient population already present at `s`.  The finite swing chain, its reconstruction
residual, and the frozen boundary action remain one signed spatial population under one norm.

Consequently the actual terminal vorticity shell population is bounded by a finite constant from
the earlier face plus exactly one nonlinear pantographic shell population.  Integrability of that
single population on `(s,T)` implies integrability of the literal critical vorticity rate on the
same terminal tail.  This is a reduction, not a proof that the nonlinear population is integrable.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesPantographicTerminalShellReduction

set_option maxHeartbeats 2400000

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPantographicPhaseLocalShell
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability
open Soma.Holonics.Millennium.NavierStokesTerminalDyadicShellPacking
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-! ## Fixed-earlier-face heat payment -/

/-- Spatial supremum of one heat-transported dyadic shell from the fixed earlier face. -/
def compactInitialVorticityHeatDyadicShellSpatialSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) : ℝ :=
  ‖compactInitialVorticityHeatBand solution hs hst ht
    (dyadicFrequencyShell level)‖

theorem compactInitialVorticityHeatDyadicShellSpatialSup_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) :
    0 ≤ compactInitialVorticityHeatDyadicShellSpatialSup
      solution hs hst ht level :=
  norm_nonneg _

/-- Heat contraction leaves every later shell below the absolute coefficient mass already
present at the fixed earlier face. -/
theorem compactInitialVorticityHeatDyadicShellSpatialSup_le_restartCoefficientMass
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) :
    compactInitialVorticityHeatDyadicShellSpatialSup solution hs hst ht level ≤
      openPeriodicVorticityDyadicShellCoefficientMass solution
        ⟨s, hs, hst.trans_lt ht⟩ level := by
  unfold compactInitialVorticityHeatDyadicShellSpatialSup
    compactInitialVorticityHeatBand
    openPeriodicVorticityDyadicShellCoefficientMass
  apply (ContinuousMap.norm_le _
    (Finset.sum_nonneg fun frequency _ ↦ complexVectorL1_nonneg _)).2
  intro q
  calc
    ‖finiteFourierSynthesis
        (compactInitialVorticityHeatCoefficient solution hs hst ht)
        (dyadicFrequencyShell level) q‖ ≤
      ∑ frequency ∈ dyadicFrequencyShell level,
        ‖compactInitialVorticityHeatCoefficient solution hs hst ht frequency‖ :=
      norm_finiteFourierSynthesis_le_sum_norm _ _ _
    _ ≤ ∑ frequency ∈ dyadicFrequencyShell level,
        complexVectorL1
          (openPeriodicVorticityFourierMode solution
            ⟨s, hs, hst.trans_lt ht⟩ frequency) := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      unfold compactInitialVorticityHeatCoefficient
      rw [norm_smul]
      have hmult := heatStokesMultiplier_mem_unitInterval hnu.le
        (sub_nonneg.mpr hst) frequency
      have hnormMultiplier : ‖heatStokesMultiplier nu (t - s) frequency‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hmult.1]
        exact hmult.2
      calc
        ‖heatStokesMultiplier nu (t - s) frequency‖ *
            ‖openPeriodicVorticityFourierMode solution
              ⟨s, hs, hst.trans_lt ht⟩ frequency‖ ≤
          1 * ‖openPeriodicVorticityFourierMode solution
              ⟨s, hs, hst.trans_lt ht⟩ frequency‖ :=
          mul_le_mul_of_nonneg_right hnormMultiplier (norm_nonneg _)
        _ ≤ 1 * complexVectorL1
            (openPeriodicVorticityFourierMode solution
              ⟨s, hs, hst.trans_lt ht⟩ frequency) :=
          mul_le_mul_of_nonneg_left
            (norm_complexVector_le_complexVectorL1 _) (by norm_num)
        _ = complexVectorL1
            (openPeriodicVorticityFourierMode solution
              ⟨s, hs, hst.trans_lt ht⟩ frequency) := one_mul _

/-- Every later heat-shell population is summable, with no terminal-time hypothesis. -/
theorem summable_compactInitialVorticityHeatDyadicShellSpatialSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    Summable (compactInitialVorticityHeatDyadicShellSpatialSup
      solution hs hst ht) :=
  Summable.of_nonneg_of_le
    (compactInitialVorticityHeatDyadicShellSpatialSup_nonneg
      solution hs hst ht)
    (compactInitialVorticityHeatDyadicShellSpatialSup_le_restartCoefficientMass
      solution hnu hs hst ht)
    (summable_openPeriodicVorticityDyadicShellCoefficientMass solution
      ⟨s, hs, hst.trans_lt ht⟩)

/-- The finite service payment carried by the fixed earlier vorticity face. -/
def restartVorticityDyadicShellCoefficientMass
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hsT : s < T) : ℝ :=
  ∑' level : ℕ,
    openPeriodicVorticityDyadicShellCoefficientMass solution
      ⟨s, hs, hsT⟩ level

theorem restartVorticityDyadicShellCoefficientMass_nonneg
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hsT : s < T) :
    0 ≤ restartVorticityDyadicShellCoefficientMass solution hs hsT := by
  exact tsum_nonneg fun level ↦
    openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution
      ⟨s, hs, hsT⟩ level

/-- The entire later heat-shell population is uniformly paid by the earlier-face coefficient
mass. -/
theorem tsum_compactInitialVorticityHeatDyadicShellSpatialSup_le_restartMass
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    (∑' level : ℕ,
      compactInitialVorticityHeatDyadicShellSpatialSup
        solution hs hst ht level) ≤
      restartVorticityDyadicShellCoefficientMass solution hs (hst.trans_lt ht) := by
  exact (summable_compactInitialVorticityHeatDyadicShellSpatialSup
    solution hnu hs hst ht).tsum_le_tsum
      (compactInitialVorticityHeatDyadicShellSpatialSup_le_restartCoefficientMass
        solution hnu hs hst ht)
      (summable_openPeriodicVorticityDyadicShellCoefficientMass solution
        ⟨s, hs, hst.trans_lt ht⟩)

/-! ## The one remaining signed nonlinear population -/

/-- The recombined pantographic population is exactly the negative actual mild-source band.
Finite depth changes how the chain, residual, and frozen boundary partition the occurrence; it
does not change their signed return at the spatial receiver. -/
theorem compactPantographicIntegratedPopulationBand_eq_neg_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (modes : Finset SpatialFrequency) :
    compactPantographicIntegratedPopulationBand solution hs hst ht depth modes =
      -compactMildSourceIntegratedBand solution hs hst ht modes := by
  symm
  rw [compactMildSourceIntegratedBand_eq_neg_chain_add_residual_add_boundary
    solution hnu hs hst ht depth modes]
  simp only [neg_neg, compactPantographicIntegratedPopulationBand]

/-- One shell of the complete signed pantographic population.  Chain, residual, and frozen
boundary are deliberately not split by the receiver norm. -/
def compactPantographicDyadicShellSpatialSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (depth level : ℕ) : ℝ :=
  ‖compactPantographicIntegratedPopulationBand solution hs hst ht depth
    (dyadicFrequencyShell level)‖

theorem compactPantographicDyadicShellSpatialSup_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (depth level : ℕ) :
    0 ≤ compactPantographicDyadicShellSpatialSup
      solution hs hst ht depth level :=
  norm_nonneg _

/-- After the signed return has reached one dyadic spatial receiver, its norm is the norm of the
actual mild-source band. -/
theorem compactPantographicDyadicShellSpatialSup_eq_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth level : ℕ) :
    compactPantographicDyadicShellSpatialSup
        solution hs hst ht depth level =
      ‖compactMildSourceIntegratedBand solution hs hst ht
        (dyadicFrequencyShell level)‖ := by
  unfold compactPantographicDyadicShellSpatialSup
  rw [compactPantographicIntegratedPopulationBand_eq_neg_mildSource
    solution hnu hs hst ht depth (dyadicFrequencyShell level), norm_neg]

/-- Pantographic truncation depth only redistributes the reconstruction fibre; it cannot change
the complete signed shell receiver or manufacture terminal summability. -/
theorem compactPantographicDyadicShellSpatialSup_depth_independent
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (firstDepth secondDepth level : ℕ) :
    compactPantographicDyadicShellSpatialSup
        solution hs hst ht firstDepth level =
      compactPantographicDyadicShellSpatialSup
        solution hs hst ht secondDepth level := by
  rw [compactPantographicDyadicShellSpatialSup_eq_mildSource
      solution hnu hs hst ht firstDepth level,
    compactPantographicDyadicShellSpatialSup_eq_mildSource
      solution hnu hs hst ht secondDepth level]

/-- The signed nonlinear population is automatically summable on every strict-interior slice.
This uses its exact equality to heat minus actual vorticity, not coefficientwise absolution of
the three pantographic incidences. -/
theorem summable_compactPantographicDyadicShellSpatialSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (depth : ℕ) :
    Summable (compactPantographicDyadicShellSpatialSup
      solution hs hst ht depth) := by
  have hheat := summable_compactInitialVorticityHeatDyadicShellSpatialSup
    solution hnu hs hst ht
  have hactual := summable_openPeriodicVorticityDyadicShellSpatialSup solution
    ⟨t, hs.trans_le hst, ht⟩
  apply Summable.of_nonneg_of_le
    (compactPantographicDyadicShellSpatialSup_nonneg
      solution hs hst ht depth)
    (fun level ↦ ?_)
    (hheat.add hactual)
  have hidentity :=
    openPeriodicVorticityBandProjector_eq_initialHeat_sub_combinedPantographicPopulation
      solution hnu hs hst ht depth (dyadicFrequencyShell level)
  have hrearranged :
      compactPantographicIntegratedPopulationBand solution hs hst ht depth
          (dyadicFrequencyShell level) =
        compactInitialVorticityHeatBand solution hs hst ht
            (dyadicFrequencyShell level) -
          openPeriodicVorticityBandProjector solution
            ⟨t, hs.trans_le hst, ht⟩ (dyadicFrequencyShell level) := by
    rw [hidentity]
    abel
  unfold compactPantographicDyadicShellSpatialSup
    compactInitialVorticityHeatDyadicShellSpatialSup
    openPeriodicVorticityDyadicShellSpatialSup
  rw [hrearranged]
  exact norm_sub_le _ _

/-- Complete signed nonlinear shell population at one later time. -/
def compactPantographicDyadicShellPopulationOn
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (depth : ℕ) (t : Ioo s T) : ℝ :=
  ∑' level : ℕ,
    compactPantographicDyadicShellSpatialSup solution hs t.2.1.le t.2.2
      depth level

theorem compactPantographicDyadicShellPopulationOn_nonneg
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (depth : ℕ) (t : Ioo s T) :
    0 ≤ compactPantographicDyadicShellPopulationOn solution hs depth t := by
  exact tsum_nonneg fun level ↦
    compactPantographicDyadicShellSpatialSup_nonneg solution hs t.2.1.le
      t.2.2 depth level

/-- The complete per-time shell population is likewise independent of the finite reconstruction
depth. -/
theorem compactPantographicDyadicShellPopulationOn_depth_independent
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (firstDepth secondDepth : ℕ)
    (t : Ioo s T) :
    compactPantographicDyadicShellPopulationOn solution hs firstDepth t =
      compactPantographicDyadicShellPopulationOn solution hs secondDepth t := by
  unfold compactPantographicDyadicShellPopulationOn
  apply tsum_congr
  intro level
  exact compactPantographicDyadicShellSpatialSup_depth_independent
    solution hnu hs t.2.1.le t.2.2 firstDepth secondDepth level

/-- The actual signed shell population is bounded by the heat-shell population plus the one
complete signed nonlinear population. -/
theorem tsum_openPeriodicVorticityDyadicShellSpatialSup_le_heat_add_pantographic
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (restart : Ioo (0 : ℝ) T)
    (later : Ioo restart.1 T) (depth : ℕ) :
    (∑' level : ℕ,
      openPeriodicVorticityDyadicShellSpatialSup solution
        ⟨later.1, restart.2.1.trans later.2.1, later.2.2⟩ level) ≤
      (∑' level : ℕ,
        compactInitialVorticityHeatDyadicShellSpatialSup solution
          restart.2.1 later.2.1.le later.2.2 level) +
        compactPantographicDyadicShellPopulationOn solution
          restart.2.1 depth later := by
  have hactual := summable_openPeriodicVorticityDyadicShellSpatialSup solution
    ⟨later.1, restart.2.1.trans later.2.1, later.2.2⟩
  have hheat := summable_compactInitialVorticityHeatDyadicShellSpatialSup
    solution hnu restart.2.1 later.2.1.le later.2.2
  have hpantographic := summable_compactPantographicDyadicShellSpatialSup
    solution hnu restart.2.1 later.2.1.le later.2.2 depth
  calc
    (∑' level : ℕ,
        openPeriodicVorticityDyadicShellSpatialSup solution
          ⟨later.1, restart.2.1.trans later.2.1, later.2.2⟩ level) ≤
      ∑' level : ℕ,
        (compactInitialVorticityHeatDyadicShellSpatialSup
            solution restart.2.1 later.2.1.le later.2.2 level +
          compactPantographicDyadicShellSpatialSup
            solution restart.2.1 later.2.1.le later.2.2 depth level) :=
      hactual.tsum_le_tsum
        (fun level ↦
          openPeriodicVorticityDyadicShellSpatialSup_le_initialHeat_add_combinedPantographicPopulation
            solution hnu restart.2.1 later.2.1.le later.2.2 depth level)
        (hheat.add hpantographic)
    _ = (∑' level : ℕ,
          compactInitialVorticityHeatDyadicShellSpatialSup
            solution restart.2.1 later.2.1.le later.2.2 level) +
        compactPantographicDyadicShellPopulationOn solution restart.2.1 depth
          later := by
      rw [hheat.tsum_add hpantographic]
      rfl

/-! ## Terminal-tail reduction -/

/-- Real-time totalization of the one signed nonlinear population. -/
def compactPantographicDyadicShellPopulation
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (depth : ℕ) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo s T then
    compactPantographicDyadicShellPopulationOn solution hs depth ⟨t, ht⟩
  else 0

@[simp]
theorem compactPantographicDyadicShellPopulation_eq
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (depth : ℕ) (ht : t ∈ Ioo s T) :
    compactPantographicDyadicShellPopulation solution hs depth t =
      compactPantographicDyadicShellPopulationOn solution hs depth ⟨t, ht⟩ := by
  simp [compactPantographicDyadicShellPopulation, ht]

theorem compactPantographicDyadicShellPopulation_nonneg
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (depth : ℕ) (t : ℝ) :
    0 ≤ compactPantographicDyadicShellPopulation solution hs depth t := by
  by_cases ht : t ∈ Ioo s T
  · rw [compactPantographicDyadicShellPopulation_eq solution hs depth ht]
    exact compactPantographicDyadicShellPopulationOn_nonneg solution hs depth ⟨t, ht⟩
  · simp [compactPantographicDyadicShellPopulation, ht]

/-- Totalization does not alter the depth-independent signed receiver. -/
theorem compactPantographicDyadicShellPopulation_depth_independent
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (firstDepth secondDepth : ℕ) (t : ℝ) :
    compactPantographicDyadicShellPopulation solution hs firstDepth t =
      compactPantographicDyadicShellPopulation solution hs secondDepth t := by
  by_cases ht : t ∈ Ioo s T
  · rw [compactPantographicDyadicShellPopulation_eq solution hs firstDepth ht,
      compactPantographicDyadicShellPopulation_eq solution hs secondDepth ht]
    exact compactPantographicDyadicShellPopulationOn_depth_independent
      solution hnu hs firstDepth secondDepth ⟨t, ht⟩
  · simp [compactPantographicDyadicShellPopulation, ht]

/-! ## Divergence-safe terminal-tail packing -/

/-- The heat-shell payment can be replaced by the one finite coefficient mass carried by the
fixed earlier face. -/
theorem tsum_openPeriodicVorticityDyadicShellSpatialSup_le_restartMass_add_pantographic
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (restart : Ioo (0 : ℝ) T)
    (later : Ioo restart.1 T) (depth : ℕ) :
    (∑' level : ℕ,
      openPeriodicVorticityDyadicShellSpatialSup solution
        ⟨later.1, restart.2.1.trans later.2.1, later.2.2⟩ level) ≤
      restartVorticityDyadicShellCoefficientMass solution
          restart.2.1 restart.2.2 +
        compactPantographicDyadicShellPopulationOn solution
          restart.2.1 depth later := by
  calc
    (∑' level : ℕ,
        openPeriodicVorticityDyadicShellSpatialSup solution
          ⟨later.1, restart.2.1.trans later.2.1, later.2.2⟩ level) ≤
      (∑' level : ℕ,
        compactInitialVorticityHeatDyadicShellSpatialSup solution
          restart.2.1 later.2.1.le later.2.2 level) +
        compactPantographicDyadicShellPopulationOn solution
          restart.2.1 depth later :=
      tsum_openPeriodicVorticityDyadicShellSpatialSup_le_heat_add_pantographic
        solution hnu restart later depth
    _ ≤ restartVorticityDyadicShellCoefficientMass solution
          restart.2.1 restart.2.2 +
        compactPantographicDyadicShellPopulationOn solution
          restart.2.1 depth later := by
      have hheat :
          (∑' level : ℕ,
            compactInitialVorticityHeatDyadicShellSpatialSup solution
              restart.2.1 later.2.1.le later.2.2 level) ≤
            restartVorticityDyadicShellCoefficientMass solution
              restart.2.1 restart.2.2 := by
        simpa only using
          (tsum_compactInitialVorticityHeatDyadicShellSpatialSup_le_restartMass
            solution hnu restart.2.1 later.2.1.le later.2.2)
      exact add_le_add_left hheat _

/-- The actual shell packing restricted to the addressed terminal tail. -/
def openPeriodicVorticityTailDyadicShellPacking
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) : ℝ≥0∞ :=
  ∫⁻ t in Ioo s T,
    openPeriodicVorticityTerminalDyadicShellDensity solution t ∂volume

/-- Divergence-safe scale--time population of the one combined signed nonlinear pantographic
shell family.  A divergent population remains `∞`. -/
def compactPantographicTerminalShellPacking
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (depth : ℕ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo s T,
    ENNReal.ofReal
      (compactPantographicDyadicShellPopulation solution hs depth t) ∂volume

/-- The divergence-safe terminal packing retains reconstruction depth as lineage, but its value
is invariant because chain plus residual plus boundary is the exact mild-source return. -/
theorem compactPantographicTerminalShellPacking_depth_independent
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (firstDepth secondDepth : ℕ) :
    compactPantographicTerminalShellPacking solution hs firstDepth =
      compactPantographicTerminalShellPacking solution hs secondDepth := by
  unfold compactPantographicTerminalShellPacking
  apply congrArg (fun density : ℝ → ℝ≥0∞ ↦
    ∫⁻ t in Ioo s T, density t ∂volume)
  funext t
  exact congrArg ENNReal.ofReal
    (compactPantographicDyadicShellPopulation_depth_independent
      solution hnu hs firstDepth secondDepth t)

/-- The honest remaining terminal-tail estimate.  Measurability is retained explicitly because
finiteness of a totalized integral alone must not conceal an undefined receiver. -/
structure OpenPeriodicPantographicTerminalShellPackingReceipt
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (depth : ℕ) : Prop where
  populationAEMeasurable :
    AEMeasurable
      (fun t : ℝ ↦ ENNReal.ofReal
        (compactPantographicDyadicShellPopulation solution hs depth t))
      (volume.restrict (Ioo s T))
  packing_lt_top :
    compactPantographicTerminalShellPacking solution hs depth < ∞

/-- Pointwise on the terminal tail, the actual extended-real shell density is paid by the fixed
earlier coefficient mass and the one combined pantographic population. -/
theorem openPeriodicVorticityTerminalDyadicShellDensity_le_restart_add_pantographic
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T)
    (ht : t ∈ Ioo s T) (depth : ℕ) :
    openPeriodicVorticityTerminalDyadicShellDensity solution t ≤
      ENNReal.ofReal
          (restartVorticityDyadicShellCoefficientMass solution hs hsT) +
        ENNReal.ofReal
          (compactPantographicDyadicShellPopulation solution hs depth t) := by
  have htOpen : t ∈ Ioo (0 : ℝ) T := ⟨hs.trans ht.1, ht.2⟩
  let actualTime : Ioo (0 : ℝ) T := ⟨t, htOpen⟩
  have hsummable : Summable (fun level : ℕ ↦
      openPeriodicVorticityDyadicShellSpatialSup solution actualTime level) :=
    summable_openPeriodicVorticityDyadicShellSpatialSup solution actualTime
  have hnonneg : ∀ level : ℕ,
      0 ≤ openPeriodicVorticityDyadicShellSpatialSup solution actualTime level :=
    fun level ↦
      openPeriodicVorticityDyadicShellSpatialSup_nonneg solution actualTime level
  have hdensity :
      openPeriodicVorticityTerminalDyadicShellDensity solution t =
        ENNReal.ofReal (∑' level : ℕ,
          openPeriodicVorticityDyadicShellSpatialSup solution actualTime level) := by
    have hofReal := ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable
    simpa [openPeriodicVorticityTerminalDyadicShellDensity,
      openPeriodicVorticityDyadicShellSpatialSupRate, htOpen, actualTime] using hofReal.symm
  have hreal :=
    tsum_openPeriodicVorticityDyadicShellSpatialSup_le_restartMass_add_pantographic
      solution hnu ⟨s, hs, hsT⟩ ⟨t, ht⟩ depth
  have hreal' :
      (∑' level : ℕ,
        openPeriodicVorticityDyadicShellSpatialSup solution actualTime level) ≤
        restartVorticityDyadicShellCoefficientMass solution hs hsT +
          compactPantographicDyadicShellPopulation solution hs depth t := by
    simpa [compactPantographicDyadicShellPopulation, ht, actualTime] using hreal
  rw [hdensity]
  calc
    ENNReal.ofReal (∑' level : ℕ,
        openPeriodicVorticityDyadicShellSpatialSup solution actualTime level) ≤
      ENNReal.ofReal
        (restartVorticityDyadicShellCoefficientMass solution hs hsT +
          compactPantographicDyadicShellPopulation solution hs depth t) :=
      ENNReal.ofReal_le_ofReal hreal'
    _ = ENNReal.ofReal
          (restartVorticityDyadicShellCoefficientMass solution hs hsT) +
        ENNReal.ofReal
          (compactPantographicDyadicShellPopulation solution hs depth t) := by
      rw [ENNReal.ofReal_add
        (restartVorticityDyadicShellCoefficientMass_nonneg solution hs hsT)
        (compactPantographicDyadicShellPopulation_nonneg solution hs depth t)]

/-- A finite nonlinear pantographic scale--time population makes the complete actual shell
population finite on the same terminal tail.  The earlier heat face contributes only a finite
constant times the finite tail length. -/
theorem openPeriodicVorticityTailDyadicShellPacking_lt_top_of_pantographic
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) (depth : ℕ)
    (receipt :
      OpenPeriodicPantographicTerminalShellPackingReceipt solution hs depth) :
    openPeriodicVorticityTailDyadicShellPacking (s := s) solution < ∞ := by
  let restartPayment : ℝ≥0∞ := ENNReal.ofReal
    (restartVorticityDyadicShellCoefficientMass solution hs hsT)
  have hmajorant :
      openPeriodicVorticityTailDyadicShellPacking (s := s) solution ≤
        ∫⁻ t in Ioo s T, restartPayment +
          ENNReal.ofReal
            (compactPantographicDyadicShellPopulation solution hs depth t) ∂volume := by
    unfold openPeriodicVorticityTailDyadicShellPacking
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact openPeriodicVorticityTerminalDyadicShellDensity_le_restart_add_pantographic
      solution hnu hs hsT ht depth
  have hsplit :
      (∫⁻ t in Ioo s T, restartPayment +
        ENNReal.ofReal
          (compactPantographicDyadicShellPopulation solution hs depth t) ∂volume) =
        restartPayment * volume (Ioo s T) +
          compactPantographicTerminalShellPacking solution hs depth := by
    unfold compactPantographicTerminalShellPacking
    rw [lintegral_add_left' (μ := volume.restrict (Ioo s T)) aemeasurable_const]
    simp only [lintegral_const, Measure.restrict_apply_univ]
  have hrestart : restartPayment * volume (Ioo s T) < ∞ := by
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top
  exact lt_of_le_of_lt hmajorant (by
    rw [hsplit]
    exact ENNReal.add_lt_top.mpr ⟨hrestart, receipt.packing_lt_top⟩)

section Audit

#print axioms compactInitialVorticityHeatDyadicShellSpatialSup_le_restartCoefficientMass
#print axioms tsum_compactInitialVorticityHeatDyadicShellSpatialSup_le_restartMass
#print axioms compactPantographicIntegratedPopulationBand_eq_neg_mildSource
#print axioms compactPantographicDyadicShellSpatialSup_depth_independent
#print axioms compactPantographicTerminalShellPacking_depth_independent
#print axioms summable_compactPantographicDyadicShellSpatialSup
#print axioms tsum_openPeriodicVorticityDyadicShellSpatialSup_le_heat_add_pantographic
#print axioms openPeriodicVorticityTerminalDyadicShellDensity_le_restart_add_pantographic
#print axioms openPeriodicVorticityTailDyadicShellPacking_lt_top_of_pantographic

end Audit

end Soma.Holonics.Millennium.NavierStokesPantographicTerminalShellReduction
