import ElementaryHolonics.Millennium.NavierStokesCriticalEnergySquareSeparator

/-!
# Phase-aligned shell separation at the critical vorticity receiver

**[proved-derived; formal-checked]**  The critical continuation route consumes the spatial
supremum of vorticity, rather than absolute Fourier coefficient mass as such.  Retaining signed
complex coefficients before reconstruction therefore cannot by itself remove the shell loss:
one admissible phase population can align at one spatial receiver.

This module reconstructs the complete finite shell section on the genuine spatial torus.  At the
zero chart every torus character is one, so the constant unit section has point value `R^3`.
Its energy-critical negative-half square norm is only `R`, and even the stronger square norm paid
after the frozen boundary is only `R^2`.  Consequently neither square receiver controls the
spatial supremum with a scale-independent coefficient.  The separator acts before any absolute
coefficient quotient and hence identifies phase-local cancellation, not merely delayed use of the
triangle inequality, as a genuinely additional terminal obligation.

This is a receiver firing section, not a Navier--Stokes blow-up construction and not terminal
control.  It does not assert that arbitrary shell sections are solution time slices.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesCriticalPhaseAlignmentSeparator

open Soma.Holonics.Millennium.NavierStokesCriticalEnergySquareSeparator
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-! ## Complete phase-bearing reconstruction -/

/-- The complete shell section reconstructed on the genuine three-torus.  No coefficient norm is
taken before the characters meet at the spatial receiver. -/
def criticalEnergyShellFourierSynthesis
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    C(SpatialTorus, ℂ) where
  toFun q := ∑ occurrence,
    UnitAddTorus.mFourier (criticalEnergyShellFrequency level occurrence) q •
      carrier occurrence
  continuous_toFun := by fun_prop

@[simp]
theorem criticalEnergyShellFourierSynthesis_apply
    {level : ℕ} (carrier : CriticalEnergyShellSection level)
    (q : SpatialTorus) :
    criticalEnergyShellFourierSynthesis carrier q =
      ∑ occurrence,
        UnitAddTorus.mFourier (criticalEnergyShellFrequency level occurrence) q •
          carrier occurrence :=
  rfl

/-- At the zero torus chart, every frequency character is one.  This is the exact phase-alignment
face, not an absolute-value estimate. -/
theorem criticalEnergyShellFourierSynthesis_zero
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    criticalEnergyShellFourierSynthesis carrier 0 = ∑ occurrence, carrier occurrence := by
  simp [criticalEnergyShellFourierSynthesis, UnitAddTorus.mFourier]

/-- The spatial-supremum receiver of the reconstructed signed shell population. -/
def criticalEnergyShellSpatialSup
    {level : ℕ} (carrier : CriticalEnergyShellSection level) : ℝ :=
  ‖criticalEnergyShellFourierSynthesis carrier‖

/-- The phase-bearing spatial receiver is bounded by absolute coefficient mass, but is not
defined through that quotient. -/
theorem criticalEnergyShellSpatialSup_le_absoluteMass
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    criticalEnergyShellSpatialSup carrier ≤
      criticalEnergyShellAbsoluteMass carrier := by
  unfold criticalEnergyShellSpatialSup
  apply (ContinuousMap.norm_le _
    (Finset.sum_nonneg fun occurrence _hoccurrence ↦ norm_nonneg (carrier occurrence))).2
  intro q
  unfold criticalEnergyShellFourierSynthesis
  calc
    ‖∑ occurrence,
        UnitAddTorus.mFourier (criticalEnergyShellFrequency level occurrence) q •
          carrier occurrence‖ ≤
        ∑ occurrence,
          ‖UnitAddTorus.mFourier (criticalEnergyShellFrequency level occurrence) q •
            carrier occurrence‖ := norm_sum_le _ _
    _ = ∑ occurrence, ‖carrier occurrence‖ := by
      apply Finset.sum_congr rfl
      intro occurrence _hoccurrence
      rw [norm_smul]
      simp [UnitAddTorus.mFourier, norm_prod, Circle.norm_coe]

/-- One spatial point already sees the coherent sum of the signed coefficient section. -/
theorem norm_sum_le_criticalEnergyShellSpatialSup
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    ‖∑ occurrence, carrier occurrence‖ ≤
      criticalEnergyShellSpatialSup carrier := by
  rw [← criticalEnergyShellFourierSynthesis_zero carrier]
  exact (criticalEnergyShellFourierSynthesis carrier).norm_coe_le_norm 0

/-! ## The exact aligned firing section -/

/-- The coherent unit section attains its complete `R^3` population at the spatial receiver. -/
theorem unitCriticalEnergyShellSection_spatialSup (level : ℕ) :
    criticalEnergyShellSpatialSup (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) ^ 3 := by
  apply le_antisymm
  · exact (criticalEnergyShellSpatialSup_le_absoluteMass _).trans_eq
      (unitCriticalEnergyShellSection_absoluteMass level)
  · calc
      (criticalEnergyShellRadius level : ℝ) ^ 3 =
          ‖∑ occurrence : CriticalEnergyShellOccurrence level,
            unitCriticalEnergyShellSection level occurrence‖ := by
        simp [unitCriticalEnergyShellSection]
        ring
      _ ≤ criticalEnergyShellSpatialSup (unitCriticalEnergyShellSection level) :=
        norm_sum_le_criticalEnergyShellSpatialSup
          (unitCriticalEnergyShellSection level)

/-- At the actual spatial-supremum receiver the energy-critical square face loses exactly `R^2`
on the coherent shell. -/
theorem unitCriticalEnergyShellSection_spatialSup_sharp_ratio (level : ℕ) :
    criticalEnergyShellSpatialSup (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) ^ 2 *
        criticalEnergyShellSquareNorm (unitCriticalEnergyShellSection level) := by
  rw [unitCriticalEnergyShellSection_spatialSup,
    unitCriticalEnergyShellSection_squareNorm]
  norm_cast

/-- Even after the frozen boundary pays one derivative, coherent phase alignment leaves one full
uncancelled shell radius at the spatial-supremum receiver. -/
theorem unitCriticalEnergyShellSection_spatialSup_energyPaidSharpRatio (level : ℕ) :
    criticalEnergyShellSpatialSup (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) *
        energyPaidFrozenShellSquareNorm (unitCriticalEnergyShellSection level) := by
  rw [unitCriticalEnergyShellSection_spatialSup,
    unitCriticalEnergyShellSection_energyPaidFrozenSquareNorm]
  ring

/-- Every proposed scale-independent energy-critical square coefficient is defeated directly at
one spatial point, before any absolute coefficient mass is formed. -/
theorem exists_shell_separating_squareNorm_from_spatialSup (coefficient : ℝ) :
    ∃ level : ℕ,
      coefficient *
          criticalEnergyShellSquareNorm (unitCriticalEnergyShellSection level) <
        criticalEnergyShellSpatialSup (unitCriticalEnergyShellSection level) := by
  obtain ⟨level, hlevel⟩ :=
    exists_shell_separating_squareNorm_from_absoluteMass coefficient
  refine ⟨level, ?_⟩
  simpa [unitCriticalEnergyShellSection_spatialSup,
    unitCriticalEnergyShellSection_absoluteMass] using hlevel

theorem no_uniform_spatialSup_factorization_through_energyCriticalSquare :
    ¬ ∃ coefficient : ℝ, ∀ (level : ℕ)
        (carrier : CriticalEnergyShellSection level),
      criticalEnergyShellSpatialSup carrier ≤
        coefficient * criticalEnergyShellSquareNorm carrier := by
  rintro ⟨coefficient, hcoefficient⟩
  obtain ⟨level, hseparate⟩ :=
    exists_shell_separating_squareNorm_from_spatialSup coefficient
  exact (not_lt_of_ge
    (hcoefficient level (unitCriticalEnergyShellSection level))) hseparate

/-- The stronger frozen square face also fails at the signed spatial receiver, with exactly one
unpaid shell power. -/
theorem exists_shell_separating_energyPaidFrozenSquareNorm_from_spatialSup
    (coefficient : ℝ) :
    ∃ level : ℕ,
      coefficient *
          energyPaidFrozenShellSquareNorm (unitCriticalEnergyShellSection level) <
        criticalEnergyShellSpatialSup (unitCriticalEnergyShellSection level) := by
  obtain ⟨level, hlevel⟩ :=
    exists_shell_separating_energyPaidFrozenSquareNorm_from_absoluteMass coefficient
  refine ⟨level, ?_⟩
  simpa [unitCriticalEnergyShellSection_spatialSup,
    unitCriticalEnergyShellSection_absoluteMass] using hlevel

theorem no_uniform_spatialSup_factorization_through_energyPaidFrozenSquare :
    ¬ ∃ coefficient : ℝ, ∀ (level : ℕ)
        (carrier : CriticalEnergyShellSection level),
      criticalEnergyShellSpatialSup carrier ≤
        coefficient * energyPaidFrozenShellSquareNorm carrier := by
  rintro ⟨coefficient, hcoefficient⟩
  obtain ⟨level, hseparate⟩ :=
    exists_shell_separating_energyPaidFrozenSquareNorm_from_spatialSup coefficient
  exact (not_lt_of_ge
    (hcoefficient level (unitCriticalEnergyShellSection level))) hseparate

/-! ## Unit-clock terminal work -/

/-- Hold one reconstructed shell section over a unit causal clock and integrate its spatial
receiver.  This isolates the spatial obstruction from any endpoint singularity or clock
rescaling. -/
def criticalEnergyShellUnitClockTerminalWork
    {level : ℕ} (carrier : CriticalEnergyShellSection level) : ℝ :=
  ∫ _time : ℝ in (0 : ℝ)..1, criticalEnergyShellSpatialSup carrier

@[simp]
theorem criticalEnergyShellUnitClockTerminalWork_eq_spatialSup
    {level : ℕ} (carrier : CriticalEnergyShellSection level) :
    criticalEnergyShellUnitClockTerminalWork carrier =
      criticalEnergyShellSpatialSup carrier := by
  simp [criticalEnergyShellUnitClockTerminalWork]

/-- On the coherent shell, unit-clock `L¹_t L∞_x` work retains the same exact `R^3` firing
population.  Time integration alone supplies no cancellation. -/
theorem unitCriticalEnergyShellSection_unitClockTerminalWork (level : ℕ) :
    criticalEnergyShellUnitClockTerminalWork
        (unitCriticalEnergyShellSection level) =
      (criticalEnergyShellRadius level : ℝ) ^ 3 := by
  rw [criticalEnergyShellUnitClockTerminalWork_eq_spatialSup,
    unitCriticalEnergyShellSection_spatialSup]

/-- Even on a nonsingular unit clock there is no scale-independent passage from the
energy-critical square coordinate to the terminal vorticity-work receiver. -/
theorem no_uniform_unitClockTerminalWork_factorization_through_energyCriticalSquare :
    ¬ ∃ coefficient : ℝ, ∀ (level : ℕ)
        (carrier : CriticalEnergyShellSection level),
      criticalEnergyShellUnitClockTerminalWork carrier ≤
        coefficient * criticalEnergyShellSquareNorm carrier := by
  simpa only [criticalEnergyShellUnitClockTerminalWork_eq_spatialSup] using
    no_uniform_spatialSup_factorization_through_energyCriticalSquare

/-- The same unit-clock firing persists after the frozen square receiver pays one derivative. -/
theorem no_uniform_unitClockTerminalWork_factorization_through_energyPaidFrozenSquare :
    ¬ ∃ coefficient : ℝ, ∀ (level : ℕ)
        (carrier : CriticalEnergyShellSection level),
      criticalEnergyShellUnitClockTerminalWork carrier ≤
        coefficient * energyPaidFrozenShellSquareNorm carrier := by
  simpa only [criticalEnergyShellUnitClockTerminalWork_eq_spatialSup] using
    no_uniform_spatialSup_factorization_through_energyPaidFrozenSquare

section Audit

#print axioms criticalEnergyShellFourierSynthesis_zero
#print axioms criticalEnergyShellSpatialSup_le_absoluteMass
#print axioms norm_sum_le_criticalEnergyShellSpatialSup
#print axioms unitCriticalEnergyShellSection_spatialSup
#print axioms unitCriticalEnergyShellSection_spatialSup_sharp_ratio
#print axioms unitCriticalEnergyShellSection_spatialSup_energyPaidSharpRatio
#print axioms no_uniform_spatialSup_factorization_through_energyCriticalSquare
#print axioms no_uniform_spatialSup_factorization_through_energyPaidFrozenSquare
#print axioms criticalEnergyShellUnitClockTerminalWork_eq_spatialSup
#print axioms unitCriticalEnergyShellSection_unitClockTerminalWork
#print axioms no_uniform_unitClockTerminalWork_factorization_through_energyCriticalSquare
#print axioms no_uniform_unitClockTerminalWork_factorization_through_energyPaidFrozenSquare

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalPhaseAlignmentSeparator
