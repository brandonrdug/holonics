import ElementaryHolonics.Millennium.NavierStokesPantographicTerminalShellReduction
import ElementaryHolonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking

/-!
# Exact mild reduction for the phase-bearing smooth dyadic vorticity packing

**[proved-derived; formal-checked]**  The actual smooth dyadic vorticity band is the sum of
the same smooth multiplier applied to the heat-transported restart coefficient and to the
integrated actual nonlinear vorticity source.  The identity is established coefficientwise and
lifted through finite torus synthesis before any norm is taken.

The fixed restart face has finite complete scale--time packing.  Its payment is the absolutely
summable smooth restart coefficient population already supplied by strict-interior smoothness;
heat transport is used only through its public contraction law.

After that restart face is paid, finiteness of the actual smooth terminal-tail packing is
equivalent to finiteness of the smooth nonlinear Duhamel packing.  This file adds no receipt and
asserts no bound for that remaining nonlinear population.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPantographicTerminalShellReduction
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
open Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

set_option maxHeartbeats 2400000

/-! ## Exact smooth phase-bearing mild identity -/

/-- The smooth dyadic multiplier applied to the heat-transported fixed restart face. -/
def compactSmoothInitialVorticityHeatBand
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) :
    C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (fun frequency ↦
      (dyadicHodgeBandWeight scale frequency : ℂ) •
        compactInitialVorticityHeatCoefficient solution hs hst ht frequency)
    (frequencyCube (dyadicHodgeOuterCutoff (scale + 1)))

/-- The smooth dyadic multiplier applied to the integrated actual nonlinear vorticity source. -/
def compactSmoothMildSourceIntegratedBand
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) :
    C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (fun frequency ↦
      (dyadicHodgeBandWeight scale frequency : ℂ) •
        compactMildSourceIntegratedCoefficient solution hs hst ht frequency)
    (frequencyCube (dyadicHodgeOuterCutoff (scale + 1)))

/-- **Exact phase-bearing smooth mild identity.**  The direct smooth vorticity band is its
smooth heat restart band plus its smooth integrated actual nonlinear source band. -/
theorem openPeriodicSmoothDyadicVorticityBand_eq_initialHeat_add_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) :
    openPeriodicSmoothDyadicVorticityBand solution
        ⟨t, hs.trans_le hst, ht⟩ scale =
      compactSmoothInitialVorticityHeatBand solution hs hst ht scale +
        compactSmoothMildSourceIntegratedBand solution hs hst ht scale := by
  apply ContinuousMap.ext
  intro q
  unfold openPeriodicSmoothDyadicVorticityBand
    compactSmoothInitialVorticityHeatBand
    compactSmoothMildSourceIntegratedBand finiteFourierSynthesis
  simp_rw [openPeriodicVorticityFourierMode_eq_initialHeat_add_mildSource
    solution hs hst ht]
  simp only [smul_add, Finset.sum_add_distrib, ContinuousMap.add_apply]
  rfl

/-! ## Per-scale norm comparisons -/

def compactSmoothInitialVorticityHeatBandSpatialSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) : ℝ :=
  ‖compactSmoothInitialVorticityHeatBand solution hs hst ht scale‖

def compactSmoothMildSourceIntegratedBandSpatialSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) : ℝ :=
  ‖compactSmoothMildSourceIntegratedBand solution hs hst ht scale‖

theorem compactSmoothInitialVorticityHeatBandSpatialSup_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) :
    0 ≤ compactSmoothInitialVorticityHeatBandSpatialSup
      solution hs hst ht scale := by
  unfold compactSmoothInitialVorticityHeatBandSpatialSup
  exact norm_nonneg _

theorem compactSmoothMildSourceIntegratedBandSpatialSup_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) :
    0 ≤ compactSmoothMildSourceIntegratedBandSpatialSup
      solution hs hst ht scale := by
  unfold compactSmoothMildSourceIntegratedBandSpatialSup
  exact norm_nonneg _

theorem openPeriodicSmoothDyadicVorticityBandSpatialSup_le_initialHeat_add_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) :
    openPeriodicSmoothDyadicVorticityBandSpatialSup solution
        ⟨t, hs.trans_le hst, ht⟩ scale ≤
      compactSmoothInitialVorticityHeatBandSpatialSup solution hs hst ht scale +
        compactSmoothMildSourceIntegratedBandSpatialSup solution hs hst ht scale := by
  unfold openPeriodicSmoothDyadicVorticityBandSpatialSup
    compactSmoothInitialVorticityHeatBandSpatialSup
    compactSmoothMildSourceIntegratedBandSpatialSup
  rw [openPeriodicSmoothDyadicVorticityBand_eq_initialHeat_add_mildSource
    solution hs hst ht scale]
  exact norm_add_le _ _

theorem compactSmoothMildSourceIntegratedBandSpatialSup_le_actual_add_initialHeat
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) :
    compactSmoothMildSourceIntegratedBandSpatialSup solution hs hst ht scale ≤
      openPeriodicSmoothDyadicVorticityBandSpatialSup solution
          ⟨t, hs.trans_le hst, ht⟩ scale +
        compactSmoothInitialVorticityHeatBandSpatialSup solution hs hst ht scale := by
  have hidentity :=
    openPeriodicSmoothDyadicVorticityBand_eq_initialHeat_add_mildSource
      solution hs hst ht scale
  have hrearranged :
      compactSmoothMildSourceIntegratedBand solution hs hst ht scale =
        openPeriodicSmoothDyadicVorticityBand solution
            ⟨t, hs.trans_le hst, ht⟩ scale -
          compactSmoothInitialVorticityHeatBand solution hs hst ht scale := by
    rw [hidentity]
    abel
  unfold compactSmoothMildSourceIntegratedBandSpatialSup
    openPeriodicSmoothDyadicVorticityBandSpatialSup
    compactSmoothInitialVorticityHeatBandSpatialSup
  rw [hrearranged]
  exact norm_sub_le _ _

/-! ## The finite fixed-restart payment -/

private theorem adjacentDyadicFrequencyShell_disjoint (scale : ℕ) :
    Disjoint (dyadicFrequencyShell scale) (dyadicFrequencyShell (scale + 1)) := by
  rw [Finset.disjoint_left]
  intro frequency hfirst hsecond
  rw [mem_dyadicFrequencyShell_iff] at hfirst hsecond
  exact hsecond.2 hfirst.1

/-- One smooth restart band is paid by the two adjacent sharp coefficient shells on the fixed
restart slice. -/
theorem compactSmoothInitialVorticityHeatBandSpatialSup_le_adjacentRestartCoefficientMass
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (scale : ℕ) :
    compactSmoothInitialVorticityHeatBandSpatialSup solution hs hst ht scale ≤
      openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hst.trans_lt ht⟩ scale +
        openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hst.trans_lt ht⟩ (scale + 1) := by
  unfold compactSmoothInitialVorticityHeatBandSpatialSup
    compactSmoothInitialVorticityHeatBand
  rw [finiteFourierSynthesis_dyadicHodgeBand_eq_twoSharpShells]
  apply (ContinuousMap.norm_le _ (add_nonneg
    (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution
      ⟨s, hs, hst.trans_lt ht⟩ scale)
    (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution
      ⟨s, hs, hst.trans_lt ht⟩ (scale + 1)))).2
  intro q
  calc
    ‖finiteFourierSynthesis
        (fun frequency ↦ (dyadicHodgeBandWeight scale frequency : ℂ) •
          compactInitialVorticityHeatCoefficient solution hs hst ht frequency)
        (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)) q‖ ≤
      ∑ frequency ∈
          (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
        ‖(dyadicHodgeBandWeight scale frequency : ℂ) •
          compactInitialVorticityHeatCoefficient solution hs hst ht frequency‖ :=
      norm_finiteFourierSynthesis_le_sum_norm _ _ q
    _ ≤ ∑ frequency ∈
          (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
        complexVectorL1 (openPeriodicVorticityFourierMode solution
          ⟨s, hs, hst.trans_lt ht⟩ frequency) := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      rw [norm_smul]
      have hweight : ‖(dyadicHodgeBandWeight scale frequency : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real]
        exact abs_dyadicHodgeBandWeight_le_one scale frequency
      have hheat := heatStokesMultiplier_mem_unitInterval hnu.le
        (sub_nonneg.mpr hst) frequency
      have hheatNorm :
          ‖heatStokesMultiplier nu (t - s) frequency‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hheat.1]
        exact hheat.2
      unfold compactInitialVorticityHeatCoefficient
      rw [norm_smul]
      calc
        ‖(dyadicHodgeBandWeight scale frequency : ℂ)‖ *
            (‖heatStokesMultiplier nu (t - s) frequency‖ *
              ‖openPeriodicVorticityFourierMode solution
                ⟨s, hs, hst.trans_lt ht⟩ frequency‖) ≤
          1 * (1 * ‖openPeriodicVorticityFourierMode solution
                ⟨s, hs, hst.trans_lt ht⟩ frequency‖) := by
            gcongr
        _ ≤ complexVectorL1 (openPeriodicVorticityFourierMode solution
              ⟨s, hs, hst.trans_lt ht⟩ frequency) := by
          simpa using norm_complexVector_le_complexVectorL1
            (openPeriodicVorticityFourierMode solution
              ⟨s, hs, hst.trans_lt ht⟩ frequency)
    _ = openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hst.trans_lt ht⟩ scale +
        openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hst.trans_lt ht⟩ (scale + 1) := by
      rw [Finset.sum_union (adjacentDyadicFrequencyShell_disjoint scale)]
      rfl

theorem summable_compactSmoothInitialVorticityHeatBandSpatialSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    Summable (compactSmoothInitialVorticityHeatBandSpatialSup
      solution hs hst ht) := by
  have hmass := summable_openPeriodicVorticityDyadicShellCoefficientMass solution
    ⟨s, hs, hst.trans_lt ht⟩
  have hmajorant : Summable (fun scale : ℕ ↦
      openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hst.trans_lt ht⟩ scale +
        openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hst.trans_lt ht⟩ (scale + 1)) :=
    hmass.add ((summable_nat_add_iff 1).2 hmass)
  exact Summable.of_nonneg_of_le
    (compactSmoothInitialVorticityHeatBandSpatialSup_nonneg solution hs hst ht)
    (compactSmoothInitialVorticityHeatBandSpatialSup_le_adjacentRestartCoefficientMass
      solution hnu hs hst ht) hmajorant

/-- Fixed finite restart payment for all later smooth scales. -/
def smoothRestartCoefficientPayment
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hsT : s < T) : ℝ :=
  ∑' scale : ℕ,
    (openPeriodicVorticityDyadicShellCoefficientMass solution
        ⟨s, hs, hsT⟩ scale +
      openPeriodicVorticityDyadicShellCoefficientMass solution
        ⟨s, hs, hsT⟩ (scale + 1))

theorem smoothRestartCoefficientPayment_nonneg
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hsT : s < T) :
    0 ≤ smoothRestartCoefficientPayment solution hs hsT := by
  unfold smoothRestartCoefficientPayment
  exact tsum_nonneg fun scale ↦ add_nonneg
    (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution
      ⟨s, hs, hsT⟩ scale)
    (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution
      ⟨s, hs, hsT⟩ (scale + 1))

theorem tsum_compactSmoothInitialVorticityHeatBandSpatialSup_le_restartPayment
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    (∑' scale : ℕ,
      compactSmoothInitialVorticityHeatBandSpatialSup
        solution hs hst ht scale) ≤
      smoothRestartCoefficientPayment solution hs (hst.trans_lt ht) := by
  have hrestart := summable_compactSmoothInitialVorticityHeatBandSpatialSup
    solution hnu hs hst ht
  have hmass := summable_openPeriodicVorticityDyadicShellCoefficientMass solution
    ⟨s, hs, hst.trans_lt ht⟩
  have hmajorant : Summable (fun scale : ℕ ↦
      openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hst.trans_lt ht⟩ scale +
        openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hst.trans_lt ht⟩ (scale + 1)) :=
    hmass.add ((summable_nat_add_iff 1).2 hmass)
  exact hrestart.tsum_le_tsum
    (compactSmoothInitialVorticityHeatBandSpatialSup_le_adjacentRestartCoefficientMass
      solution hnu hs hst ht) hmajorant

/-! ## Complete scale populations at one tail time -/

def compactSmoothInitialVorticityHeatPopulationOn
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (later : Ioo s T) : ℝ :=
  ∑' scale : ℕ,
    compactSmoothInitialVorticityHeatBandSpatialSup solution hs
      later.2.1.le later.2.2 scale

def compactSmoothMildSourcePopulationOn
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (later : Ioo s T) : ℝ :=
  ∑' scale : ℕ,
    compactSmoothMildSourceIntegratedBandSpatialSup solution hs
      later.2.1.le later.2.2 scale

theorem summable_compactSmoothMildSourceIntegratedBandSpatialSup
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    Summable (compactSmoothMildSourceIntegratedBandSpatialSup
      solution hs hst ht) := by
  have hactual := summable_openPeriodicSmoothDyadicVorticityBandSpatialSup solution
    ⟨t, hs.trans_le hst, ht⟩
  have hrestart := summable_compactSmoothInitialVorticityHeatBandSpatialSup
    solution hnu hs hst ht
  exact Summable.of_nonneg_of_le
    (compactSmoothMildSourceIntegratedBandSpatialSup_nonneg solution hs hst ht)
    (compactSmoothMildSourceIntegratedBandSpatialSup_le_actual_add_initialHeat
      solution hs hst ht) (hactual.add hrestart)

theorem tsum_actualSmoothBands_le_restart_add_mildSource
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (later : Ioo s T) :
    (∑' scale : ℕ,
      openPeriodicSmoothDyadicVorticityBandSpatialSup solution
        ⟨later.1, hs.trans later.2.1, later.2.2⟩ scale) ≤
      compactSmoothInitialVorticityHeatPopulationOn solution hs later +
        compactSmoothMildSourcePopulationOn solution hs later := by
  have hactual := summable_openPeriodicSmoothDyadicVorticityBandSpatialSup solution
    ⟨later.1, hs.trans later.2.1, later.2.2⟩
  have hrestart := summable_compactSmoothInitialVorticityHeatBandSpatialSup
    solution hnu hs later.2.1.le later.2.2
  have hsource := summable_compactSmoothMildSourceIntegratedBandSpatialSup
    solution hnu hs later.2.1.le later.2.2
  calc
    (∑' scale : ℕ,
        openPeriodicSmoothDyadicVorticityBandSpatialSup solution
          ⟨later.1, hs.trans later.2.1, later.2.2⟩ scale) ≤
      ∑' scale : ℕ,
        (compactSmoothInitialVorticityHeatBandSpatialSup solution hs
            later.2.1.le later.2.2 scale +
          compactSmoothMildSourceIntegratedBandSpatialSup solution hs
            later.2.1.le later.2.2 scale) :=
      hactual.tsum_le_tsum
        (openPeriodicSmoothDyadicVorticityBandSpatialSup_le_initialHeat_add_mildSource
          solution hs later.2.1.le later.2.2)
        (hrestart.add hsource)
    _ = compactSmoothInitialVorticityHeatPopulationOn solution hs later +
        compactSmoothMildSourcePopulationOn solution hs later := by
      rw [hrestart.tsum_add hsource]
      rfl

theorem tsum_mildSourceSmoothBands_le_actual_add_restart
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (later : Ioo s T) :
    compactSmoothMildSourcePopulationOn solution hs later ≤
      (∑' scale : ℕ,
        openPeriodicSmoothDyadicVorticityBandSpatialSup solution
          ⟨later.1, hs.trans later.2.1, later.2.2⟩ scale) +
        compactSmoothInitialVorticityHeatPopulationOn solution hs later := by
  have hsource := summable_compactSmoothMildSourceIntegratedBandSpatialSup
    solution hnu hs later.2.1.le later.2.2
  have hactual := summable_openPeriodicSmoothDyadicVorticityBandSpatialSup solution
    ⟨later.1, hs.trans later.2.1, later.2.2⟩
  have hrestart := summable_compactSmoothInitialVorticityHeatBandSpatialSup
    solution hnu hs later.2.1.le later.2.2
  calc
    compactSmoothMildSourcePopulationOn solution hs later =
        ∑' scale : ℕ,
          compactSmoothMildSourceIntegratedBandSpatialSup solution hs
            later.2.1.le later.2.2 scale := rfl
    _ ≤ ∑' scale : ℕ,
        (openPeriodicSmoothDyadicVorticityBandSpatialSup solution
            ⟨later.1, hs.trans later.2.1, later.2.2⟩ scale +
          compactSmoothInitialVorticityHeatBandSpatialSup solution hs
            later.2.1.le later.2.2 scale) :=
      hsource.tsum_le_tsum
        (compactSmoothMildSourceIntegratedBandSpatialSup_le_actual_add_initialHeat
          solution hs later.2.1.le later.2.2)
        (hactual.add hrestart)
    _ = (∑' scale : ℕ,
          openPeriodicSmoothDyadicVorticityBandSpatialSup solution
            ⟨later.1, hs.trans later.2.1, later.2.2⟩ scale) +
        compactSmoothInitialVorticityHeatPopulationOn solution hs later := by
      rw [hactual.tsum_add hrestart]
      rfl

/-! ## Real-time densities and terminal-tail packings -/

def compactSmoothInitialVorticityHeatPopulation
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo s T then
    compactSmoothInitialVorticityHeatPopulationOn solution hs ⟨t, ht⟩
  else 0

def compactSmoothMildSourcePopulation
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo s T then
    compactSmoothMildSourcePopulationOn solution hs ⟨t, ht⟩
  else 0

def compactSmoothInitialVorticityHeatDensity
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (compactSmoothInitialVorticityHeatPopulation solution hs t)

def compactSmoothMildSourceDensity
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (compactSmoothMildSourcePopulation solution hs t)

def compactSmoothInitialVorticityHeatTerminalPacking
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) : ℝ≥0∞ :=
  ∫⁻ t in Ioo s T, compactSmoothInitialVorticityHeatDensity solution hs t ∂volume

/-- The exact remaining nonlinear Duhamel scale--time population in the smooth dyadic chart. -/
def compactSmoothMildSourceTerminalPacking
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) : ℝ≥0∞ :=
  ∫⁻ t in Ioo s T, compactSmoothMildSourceDensity solution hs t ∂volume

def openPeriodicVorticityTailSmoothDyadicPacking
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) : ℝ≥0∞ :=
  ∫⁻ t in Ioo s T,
    openPeriodicVorticityTerminalSmoothDyadicDensity solution t ∂volume

theorem compactSmoothInitialVorticityHeatPopulation_le_restartPayment
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) (t : ℝ) :
    compactSmoothInitialVorticityHeatPopulation solution hs t ≤
      smoothRestartCoefficientPayment solution hs hsT := by
  by_cases ht : t ∈ Ioo s T
  · simp only [compactSmoothInitialVorticityHeatPopulation, ht, dite_true]
    unfold compactSmoothInitialVorticityHeatPopulationOn
    simpa only using
      (tsum_compactSmoothInitialVorticityHeatBandSpatialSup_le_restartPayment
        solution hnu hs ht.1.le ht.2)
  · simp only [compactSmoothInitialVorticityHeatPopulation, ht, dite_false]
    exact smoothRestartCoefficientPayment_nonneg solution hs hsT

theorem compactSmoothInitialVorticityHeatTerminalPacking_le
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) :
    compactSmoothInitialVorticityHeatTerminalPacking solution hs ≤
      ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) *
        volume (Ioo s T) := by
  unfold compactSmoothInitialVorticityHeatTerminalPacking
    compactSmoothInitialVorticityHeatDensity
  calc
    (∫⁻ t in Ioo s T,
        ENNReal.ofReal
          (compactSmoothInitialVorticityHeatPopulation solution hs t) ∂volume) ≤
      ∫⁻ _t in Ioo s T,
        ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) ∂volume := by
      apply lintegral_mono
      intro t
      exact ENNReal.ofReal_le_ofReal
        (compactSmoothInitialVorticityHeatPopulation_le_restartPayment
          solution hnu hs hsT t)
    _ = ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) *
        volume (Ioo s T) := by
      simp only [lintegral_const, Measure.restrict_apply_univ]

theorem compactSmoothInitialVorticityHeatTerminalPacking_lt_top
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) :
    compactSmoothInitialVorticityHeatTerminalPacking solution hs < ∞ := by
  exact lt_of_le_of_lt
    (compactSmoothInitialVorticityHeatTerminalPacking_le solution hnu hs hsT)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top)

/-! ## Exact two-sided finiteness reduction -/

theorem openPeriodicVorticityTerminalSmoothDyadicDensity_eq_ofReal_tsum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    openPeriodicVorticityTerminalSmoothDyadicDensity solution t =
      ENNReal.ofReal (∑' scale : ℕ,
        openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale) := by
  have hsummable :=
    summable_openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩
  have hnonneg : ∀ scale : ℕ,
      0 ≤ openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale :=
    openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg solution ⟨t, ht⟩
  have hofReal := ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable
  simpa [openPeriodicVorticityTerminalSmoothDyadicDensity,
    openPeriodicSmoothDyadicVorticityBandSpatialSupRate, ht] using hofReal.symm

theorem openPeriodicVorticityTerminalSmoothDyadicDensity_le_restart_add_mildSource
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (ht : t ∈ Ioo s T) :
    openPeriodicVorticityTerminalSmoothDyadicDensity solution t ≤
      compactSmoothInitialVorticityHeatDensity solution hs t +
        compactSmoothMildSourceDensity solution hs t := by
  let later : Ioo s T := ⟨t, ht⟩
  let actualTime : Ioo (0 : ℝ) T := ⟨t, hs.trans ht.1, ht.2⟩
  have hreal := tsum_actualSmoothBands_le_restart_add_mildSource
    solution hnu hs later
  have hrestartNonneg :
      0 ≤ compactSmoothInitialVorticityHeatPopulationOn solution hs later :=
    tsum_nonneg fun scale ↦
      compactSmoothInitialVorticityHeatBandSpatialSup_nonneg solution hs
        later.2.1.le later.2.2 scale
  have hsourceNonneg :
      0 ≤ compactSmoothMildSourcePopulationOn solution hs later :=
    tsum_nonneg fun scale ↦
      compactSmoothMildSourceIntegratedBandSpatialSup_nonneg solution hs
        later.2.1.le later.2.2 scale
  rw [openPeriodicVorticityTerminalSmoothDyadicDensity_eq_ofReal_tsum
    solution ⟨hs.trans ht.1, ht.2⟩]
  unfold compactSmoothInitialVorticityHeatDensity compactSmoothMildSourceDensity
  simp only [compactSmoothInitialVorticityHeatPopulation,
    compactSmoothMildSourcePopulation, ht, dite_true]
  rw [← ENNReal.ofReal_add hrestartNonneg hsourceNonneg]
  exact ENNReal.ofReal_le_ofReal (by simpa [later, actualTime] using hreal)

theorem compactSmoothMildSourceDensity_le_actual_add_restart
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (ht : t ∈ Ioo s T) :
    compactSmoothMildSourceDensity solution hs t ≤
      openPeriodicVorticityTerminalSmoothDyadicDensity solution t +
        compactSmoothInitialVorticityHeatDensity solution hs t := by
  let later : Ioo s T := ⟨t, ht⟩
  let actualTime : Ioo (0 : ℝ) T := ⟨t, hs.trans ht.1, ht.2⟩
  have hreal := tsum_mildSourceSmoothBands_le_actual_add_restart
    solution hnu hs later
  have hactualNonneg : 0 ≤ ∑' scale : ℕ,
      openPeriodicSmoothDyadicVorticityBandSpatialSup solution actualTime scale :=
    tsum_nonneg fun scale ↦
      openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg solution actualTime scale
  have hrestartNonneg :
      0 ≤ compactSmoothInitialVorticityHeatPopulationOn solution hs later :=
    tsum_nonneg fun scale ↦
      compactSmoothInitialVorticityHeatBandSpatialSup_nonneg solution hs
        later.2.1.le later.2.2 scale
  unfold compactSmoothMildSourceDensity compactSmoothInitialVorticityHeatDensity
  simp only [compactSmoothMildSourcePopulation,
    compactSmoothInitialVorticityHeatPopulation, ht, dite_true]
  rw [openPeriodicVorticityTerminalSmoothDyadicDensity_eq_ofReal_tsum
    solution ⟨hs.trans ht.1, ht.2⟩]
  rw [← ENNReal.ofReal_add hactualNonneg hrestartNonneg]
  exact ENNReal.ofReal_le_ofReal (by simpa [later, actualTime] using hreal)

theorem openPeriodicVorticityTailSmoothDyadicPacking_le_restart_add_mildSource
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) :
    openPeriodicVorticityTailSmoothDyadicPacking (s := s) solution ≤
      ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) *
          volume (Ioo s T) +
        compactSmoothMildSourceTerminalPacking solution hs := by
  have hmajorant :
      openPeriodicVorticityTailSmoothDyadicPacking (s := s) solution ≤
        ∫⁻ t in Ioo s T,
          ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) +
            compactSmoothMildSourceDensity solution hs t ∂volume := by
    unfold openPeriodicVorticityTailSmoothDyadicPacking
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hrestart :
        compactSmoothInitialVorticityHeatDensity solution hs t ≤
          ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) := by
      unfold compactSmoothInitialVorticityHeatDensity
      exact ENNReal.ofReal_le_ofReal
        (compactSmoothInitialVorticityHeatPopulation_le_restartPayment
          solution hnu hs hsT t)
    exact (openPeriodicVorticityTerminalSmoothDyadicDensity_le_restart_add_mildSource
      solution hnu hs ht).trans (add_le_add hrestart le_rfl)
  calc
    openPeriodicVorticityTailSmoothDyadicPacking (s := s) solution ≤
        ∫⁻ t in Ioo s T,
          ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) +
            compactSmoothMildSourceDensity solution hs t ∂volume := hmajorant
    _ = ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) *
          volume (Ioo s T) +
        compactSmoothMildSourceTerminalPacking solution hs := by
      unfold compactSmoothMildSourceTerminalPacking
      rw [lintegral_add_left' (μ := volume.restrict (Ioo s T))
        aemeasurable_const]
      simp only [lintegral_const, Measure.restrict_apply_univ]

theorem compactSmoothMildSourceTerminalPacking_le_actual_add_restart
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) :
    compactSmoothMildSourceTerminalPacking solution hs ≤
      openPeriodicVorticityTailSmoothDyadicPacking (s := s) solution +
        ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) *
          volume (Ioo s T) := by
  have hmajorant :
      compactSmoothMildSourceTerminalPacking solution hs ≤
        ∫⁻ t in Ioo s T,
          openPeriodicVorticityTerminalSmoothDyadicDensity solution t +
            ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) ∂volume := by
    unfold compactSmoothMildSourceTerminalPacking
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hrestart :
        compactSmoothInitialVorticityHeatDensity solution hs t ≤
          ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) := by
      unfold compactSmoothInitialVorticityHeatDensity
      exact ENNReal.ofReal_le_ofReal
        (compactSmoothInitialVorticityHeatPopulation_le_restartPayment
          solution hnu hs hsT t)
    exact (compactSmoothMildSourceDensity_le_actual_add_restart
      solution hnu hs ht).trans (add_le_add le_rfl hrestart)
  calc
    compactSmoothMildSourceTerminalPacking solution hs ≤
        ∫⁻ t in Ioo s T,
          openPeriodicVorticityTerminalSmoothDyadicDensity solution t +
            ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) ∂volume :=
      hmajorant
    _ = openPeriodicVorticityTailSmoothDyadicPacking (s := s) solution +
        ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) *
          volume (Ioo s T) := by
      unfold openPeriodicVorticityTailSmoothDyadicPacking
      rw [lintegral_add_right'
        (fun t : ℝ ↦ openPeriodicVorticityTerminalSmoothDyadicDensity solution t)
        (aemeasurable_const : AEMeasurable
          (fun _ : ℝ ↦ ENNReal.ofReal
            (smoothRestartCoefficientPayment solution hs hsT))
          (volume.restrict (Ioo s T)))]
      simp only [lintegral_const, Measure.restrict_apply_univ]

/-- **Two-sided smooth terminal-tail reduction.**  The fixed heat restart face is finite, so the
actual smooth dyadic packing and the smooth nonlinear Duhamel packing have identical finiteness
content. -/
theorem compactSmoothMildSourceTerminalPacking_lt_top_iff_actual
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) :
    compactSmoothMildSourceTerminalPacking solution hs < ∞ ↔
      openPeriodicVorticityTailSmoothDyadicPacking (s := s) solution < ∞ := by
  have hrestart :
      ENNReal.ofReal (smoothRestartCoefficientPayment solution hs hsT) *
          volume (Ioo s T) < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top
  constructor
  · intro hsource
    exact lt_of_le_of_lt
      (openPeriodicVorticityTailSmoothDyadicPacking_le_restart_add_mildSource
        solution hnu hs hsT)
      (ENNReal.add_lt_top.mpr ⟨hrestart, hsource⟩)
  · intro hactual
    exact lt_of_le_of_lt
      (compactSmoothMildSourceTerminalPacking_le_actual_add_restart
        solution hnu hs hsT)
      (ENNReal.add_lt_top.mpr ⟨hactual, hrestart⟩)

section Audit

#print axioms openPeriodicSmoothDyadicVorticityBand_eq_initialHeat_add_mildSource
#print axioms compactSmoothInitialVorticityHeatTerminalPacking_lt_top
#print axioms openPeriodicVorticityTailSmoothDyadicPacking_le_restart_add_mildSource
#print axioms compactSmoothMildSourceTerminalPacking_le_actual_add_restart
#print axioms compactSmoothMildSourceTerminalPacking_lt_top_iff_actual

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
