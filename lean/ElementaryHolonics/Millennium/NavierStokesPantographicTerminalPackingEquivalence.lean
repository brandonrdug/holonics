import ElementaryHolonics.Millennium.NavierStokesPantographicMildSourcePacking

/-!
# Equivalence of pantographic and actual terminal shell packing

**[proved-derived; formal-checked]**  Once the fixed restart heat face has been paid, the
terminal packing of the complete signed pantographic return has exactly the same finiteness
content as the terminal packing of the actual dyadic vorticity shells.  The reverse comparison
proved here uses the exact mild identity before taking the shell norm:

`mild source = actual vorticity - restart heat`.

Together with the already checked forward comparison, this proves a two-sided finiteness
equivalence.  It rules out finite pantographic truncation depth as a source of regularization:
the depth retains reconstruction lineage, while the unresolved estimate remains the actual
scale-critical terminal PDE population.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Soma.Holonics.Millennium.NavierStokesPantographicTerminalPackingEquivalence

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPantographicMildSourcePacking
open Soma.Holonics.Millennium.NavierStokesPantographicTerminalShellReduction
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesTerminalDyadicShellPacking
open Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand

set_option maxHeartbeats 2400000

/-! ## Reverse shell comparison -/

/-- One actual nonlinear mild-source shell is paid by the corresponding actual vorticity shell
and the fixed earlier heat shell.  The rearrangement is performed before the norm. -/
theorem compactMildSourceDyadicShellSpatialSup_le_actual_add_initialHeat
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) :
    compactMildSourceDyadicShellSpatialSup solution hs hst ht level ≤
      openPeriodicVorticityDyadicShellSpatialSup solution
          ⟨t, hs.trans_le hst, ht⟩ level +
        compactInitialVorticityHeatDyadicShellSpatialSup
          solution hs hst ht level := by
  have hidentity :=
    openPeriodicVorticityBandProjector_eq_initialHeat_add_mildSource
      solution hs hst ht (dyadicFrequencyShell level)
  have hrearranged :
      compactMildSourceIntegratedBand solution hs hst ht
          (dyadicFrequencyShell level) =
        openPeriodicVorticityBandProjector solution
            ⟨t, hs.trans_le hst, ht⟩ (dyadicFrequencyShell level) -
          compactInitialVorticityHeatBand solution hs hst ht
            (dyadicFrequencyShell level) := by
    rw [hidentity]
    abel
  unfold compactMildSourceDyadicShellSpatialSup
    openPeriodicVorticityDyadicShellSpatialSup
    compactInitialVorticityHeatDyadicShellSpatialSup
  rw [hrearranged]
  exact norm_sub_le _ _

/-- At one strict terminal-tail time, the complete nonlinear mild-source shell population is
bounded by the actual shell population plus the fixed restart heat payment. -/
theorem compactMildSourceDyadicShellPopulationOn_le_actual_add_restartMass
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) (later : Ioo s T) :
    compactMildSourceDyadicShellPopulationOn solution hs later ≤
      (∑' level : ℕ,
        openPeriodicVorticityDyadicShellSpatialSup solution
          ⟨later.1, hs.trans later.2.1, later.2.2⟩ level) +
        restartVorticityDyadicShellCoefficientMass solution hs hsT := by
  have hactual := summable_openPeriodicVorticityDyadicShellSpatialSup solution
    ⟨later.1, hs.trans later.2.1, later.2.2⟩
  have hheat := summable_compactInitialVorticityHeatDyadicShellSpatialSup
    solution hnu hs later.2.1.le later.2.2
  have hsource : Summable (fun level : ℕ ↦
      compactMildSourceDyadicShellSpatialSup solution hs
        later.2.1.le later.2.2 level) := by
    apply Summable.of_nonneg_of_le
      (fun level ↦ norm_nonneg _)
      (fun level ↦
        compactMildSourceDyadicShellSpatialSup_le_actual_add_initialHeat
          solution hs later.2.1.le later.2.2 level)
      (hactual.add hheat)
  calc
    compactMildSourceDyadicShellPopulationOn solution hs later =
        ∑' level : ℕ,
          compactMildSourceDyadicShellSpatialSup solution hs
            later.2.1.le later.2.2 level := rfl
    _ ≤ ∑' level : ℕ,
        (openPeriodicVorticityDyadicShellSpatialSup solution
            ⟨later.1, hs.trans later.2.1, later.2.2⟩ level +
          compactInitialVorticityHeatDyadicShellSpatialSup solution hs
            later.2.1.le later.2.2 level) :=
      hsource.tsum_le_tsum
        (fun level ↦
          compactMildSourceDyadicShellSpatialSup_le_actual_add_initialHeat
            solution hs later.2.1.le later.2.2 level)
        (hactual.add hheat)
    _ = (∑' level : ℕ,
          openPeriodicVorticityDyadicShellSpatialSup solution
            ⟨later.1, hs.trans later.2.1, later.2.2⟩ level) +
        (∑' level : ℕ,
          compactInitialVorticityHeatDyadicShellSpatialSup solution hs
            later.2.1.le later.2.2 level) := by
      rw [hactual.tsum_add hheat]
    _ ≤ (∑' level : ℕ,
          openPeriodicVorticityDyadicShellSpatialSup solution
            ⟨later.1, hs.trans later.2.1, later.2.2⟩ level) +
        restartVorticityDyadicShellCoefficientMass solution hs hsT := by
      apply add_le_add le_rfl
      simpa only using
        (tsum_compactInitialVorticityHeatDyadicShellSpatialSup_le_restartMass
          solution hnu hs later.2.1.le later.2.2)

/-- Interior actual density is the `ENNReal.ofReal` image of its finite real shell sum. -/
theorem openPeriodicVorticityTerminalDyadicShellDensity_eq_ofReal_tsum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    openPeriodicVorticityTerminalDyadicShellDensity solution t =
      ENNReal.ofReal (∑' level : ℕ,
        openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level) := by
  have hsummable :=
    summable_openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩
  have hnonneg : ∀ level : ℕ,
      0 ≤ openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level :=
    fun level ↦ openPeriodicVorticityDyadicShellSpatialSup_nonneg solution ⟨t, ht⟩ level
  have hofReal := ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable
  simpa [openPeriodicVorticityTerminalDyadicShellDensity,
    openPeriodicVorticityDyadicShellSpatialSupRate, ht] using hofReal.symm

/-- Pointwise on the terminal tail, the actual nonlinear mild-source density is paid by the
actual vorticity shell density and the fixed restart coefficient mass. -/
theorem compactMildSourceDyadicShellDensity_le_actual_add_restart
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) (ht : t ∈ Ioo s T) :
    ENNReal.ofReal (compactMildSourceDyadicShellPopulation solution hs t) ≤
      openPeriodicVorticityTerminalDyadicShellDensity solution t +
        ENNReal.ofReal
          (restartVorticityDyadicShellCoefficientMass solution hs hsT) := by
  let later : Ioo s T := ⟨t, ht⟩
  let actualTime : Ioo (0 : ℝ) T := ⟨t, hs.trans ht.1, ht.2⟩
  have hreal :=
    compactMildSourceDyadicShellPopulationOn_le_actual_add_restartMass
      solution hnu hs hsT later
  have hreal' :
      compactMildSourceDyadicShellPopulation solution hs t ≤
        (∑' level : ℕ,
          openPeriodicVorticityDyadicShellSpatialSup solution actualTime level) +
          restartVorticityDyadicShellCoefficientMass solution hs hsT := by
    simpa [compactMildSourceDyadicShellPopulation, ht, later, actualTime] using hreal
  calc
    ENNReal.ofReal (compactMildSourceDyadicShellPopulation solution hs t) ≤
        ENNReal.ofReal
          ((∑' level : ℕ,
            openPeriodicVorticityDyadicShellSpatialSup solution actualTime level) +
            restartVorticityDyadicShellCoefficientMass solution hs hsT) :=
      ENNReal.ofReal_le_ofReal hreal'
    _ = ENNReal.ofReal
          (∑' level : ℕ,
            openPeriodicVorticityDyadicShellSpatialSup solution actualTime level) +
        ENNReal.ofReal
          (restartVorticityDyadicShellCoefficientMass solution hs hsT) := by
      rw [ENNReal.ofReal_add
        (tsum_nonneg fun level ↦
          openPeriodicVorticityDyadicShellSpatialSup_nonneg
            solution actualTime level)
        (restartVorticityDyadicShellCoefficientMass_nonneg solution hs hsT)]
    _ = openPeriodicVorticityTerminalDyadicShellDensity solution t +
        ENNReal.ofReal
          (restartVorticityDyadicShellCoefficientMass solution hs hsT) := by
      rw [openPeriodicVorticityTerminalDyadicShellDensity_eq_ofReal_tsum
        solution ⟨hs.trans ht.1, ht.2⟩]

/-! ## Two-sided spacetime finiteness -/

/-- Actual terminal packing controls the nonlinear mild-source packing.  The only extra term is
the fixed restart coefficient mass multiplied by the finite terminal-tail length. -/
theorem compactMildSourceTerminalShellPacking_le_actual_add_restart
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) :
    compactMildSourceTerminalShellPacking solution hs ≤
      openPeriodicVorticityTailDyadicShellPacking (s := s) solution +
        ENNReal.ofReal
            (restartVorticityDyadicShellCoefficientMass solution hs hsT) *
          volume (Ioo s T) := by
  have hmajorant :
      compactMildSourceTerminalShellPacking solution hs ≤
        ∫⁻ t in Ioo s T,
          openPeriodicVorticityTerminalDyadicShellDensity solution t +
            ENNReal.ofReal
              (restartVorticityDyadicShellCoefficientMass solution hs hsT) ∂volume := by
    unfold compactMildSourceTerminalShellPacking
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact compactMildSourceDyadicShellDensity_le_actual_add_restart
      solution hnu hs hsT ht
  calc
    compactMildSourceTerminalShellPacking solution hs ≤
        ∫⁻ t in Ioo s T,
          openPeriodicVorticityTerminalDyadicShellDensity solution t +
            ENNReal.ofReal
              (restartVorticityDyadicShellCoefficientMass solution hs hsT) ∂volume :=
      hmajorant
    _ = openPeriodicVorticityTailDyadicShellPacking (s := s) solution +
        ENNReal.ofReal
            (restartVorticityDyadicShellCoefficientMass solution hs hsT) *
          volume (Ioo s T) := by
      unfold openPeriodicVorticityTailDyadicShellPacking
      rw [lintegral_add_right'
        (fun t : ℝ ↦ openPeriodicVorticityTerminalDyadicShellDensity solution t)
        (aemeasurable_const :
          AEMeasurable
            (fun _ : ℝ ↦ ENNReal.ofReal
              (restartVorticityDyadicShellCoefficientMass solution hs hsT))
            (volume.restrict (Ioo s T)))]
      simp only [lintegral_const, Measure.restrict_apply_univ]

/-- Finiteness of the actual terminal shell packing therefore forces finiteness of the signed
nonlinear mild-source packing. -/
theorem compactMildSourceTerminalShellPacking_lt_top_of_actual
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T)
    (hactual :
      openPeriodicVorticityTailDyadicShellPacking (s := s) solution < ∞) :
    compactMildSourceTerminalShellPacking solution hs < ∞ := by
  apply lt_of_le_of_lt
    (compactMildSourceTerminalShellPacking_le_actual_add_restart
      solution hnu hs hsT)
  apply ENNReal.add_lt_top.mpr
  refine ⟨hactual, ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top⟩

/-- The already checked forward estimate needs only packing finiteness; measurability of the
pantographic presentation is not used in this direct scalar comparison. -/
theorem openPeriodicVorticityTailDyadicShellPacking_lt_top_of_packing_lt_top
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) (depth : ℕ)
    (hpantographic : compactPantographicTerminalShellPacking solution hs depth < ∞) :
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
  have hrestart : restartPayment * volume (Ioo s T) < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top
  exact lt_of_le_of_lt hmajorant (by
    rw [hsplit]
    exact ENNReal.add_lt_top.mpr ⟨hrestart, hpantographic⟩)

/-- **Two-sided terminal equivalence.**  At every positive restart, finite pantographic packing,
finite signed mild-source packing, and finite actual terminal dyadic-vorticity packing have the
same truth value. -/
theorem compactPantographicTerminalShellPacking_lt_top_iff_actual
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) (depth : ℕ) :
    compactPantographicTerminalShellPacking solution hs depth < ∞ ↔
      openPeriodicVorticityTailDyadicShellPacking (s := s) solution < ∞ := by
  constructor
  · exact openPeriodicVorticityTailDyadicShellPacking_lt_top_of_packing_lt_top
      solution hnu hs hsT depth
  · intro hactual
    rw [compactPantographicTerminalShellPacking_eq_mildSource
      solution hnu hs depth]
    exact compactMildSourceTerminalShellPacking_lt_top_of_actual
      solution hnu hs hsT hactual

section Audit

#print axioms compactMildSourceDyadicShellSpatialSup_le_actual_add_initialHeat
#print axioms compactMildSourceDyadicShellPopulationOn_le_actual_add_restartMass
#print axioms compactMildSourceTerminalShellPacking_le_actual_add_restart
#print axioms compactPantographicTerminalShellPacking_lt_top_iff_actual

end Audit

end Soma.Holonics.Millennium.NavierStokesPantographicTerminalPackingEquivalence
