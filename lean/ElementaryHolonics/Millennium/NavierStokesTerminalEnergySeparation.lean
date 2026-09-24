import ElementaryHolonics.Millennium.NavierStokesWeightedSobolevHilbert
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Kinetic energy does not control the terminal derivative receiver

**[counterexample; formal-checked]** A single addressed Fourier occurrence has the same exact
order-zero mass at every frequency, while its order-two Sobolev mass escapes every proposed
uniform constant.  Thus the remaining terminal vorticity-derivative estimate cannot be obtained
from kinetic energy alone.  A successful passage must retain additional scale-sensitive
testimony, such as viscous dissipation or an oriented direction-coherence law.
-/

noncomputable section

open scoped ENNReal BigOperators Matrix

namespace Soma.Holonics.Millennium.NavierStokesTerminalEnergySeparation

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- The axial frequency occurrence carrying natural magnitude `n`. -/
def axialFrequency (n : ℕ) : SpatialFrequency :=
  ![(n : ℤ), 0, 0]

@[simp]
theorem frequencySquared_axialFrequency (n : ℕ) :
    frequencySquared (axialFrequency n) = (n : ℝ) ^ 2 := by
  simp [frequencySquared, axialFrequency, Fin.sum_univ_succ]

@[simp]
theorem torusStokesEigenvalue_axialFrequency (n : ℕ) :
    torusStokesEigenvalue (axialFrequency n) =
      (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 := by
  simp [torusStokesEigenvalue]

/-- One exact complex Fourier occurrence, with no unrecorded surrounding population. -/
def singleFrequencyPopulation (k : SpatialFrequency) : PeriodicFourierL2 :=
  lp.single 2 k (1 : ℂ)

@[simp]
theorem singleFrequencyPopulation_apply_self (k : SpatialFrequency) :
    singleFrequencyPopulation k k = 1 := by
  exact lp.single_apply_self 2 k 1

theorem singleFrequencyPopulation_apply_ne
    (k j : SpatialFrequency) (hjk : j ≠ k) :
    singleFrequencyPopulation k j = 0 := by
  exact lp.single_apply_ne 2 k 1 hjk

/-- The complete squared Sobolev receiver of a Fourier coefficient population. -/
def sobolevMass (order : ℕ) (coeff : PeriodicFourierL2) : ℝ :=
  ∑' k : SpatialFrequency, periodicSobolevWeight order k * ‖coeff k‖ ^ 2

/-- A singleton population is admissible at every finite Sobolev order. -/
theorem singleFrequencyPopulation_hasPeriodicSobolevCoefficients
    (order : ℕ) (k : SpatialFrequency) :
    HasPeriodicSobolevCoefficients order (singleFrequencyPopulation k) := by
  unfold HasPeriodicSobolevCoefficients
  apply summable_of_ne_finset_zero (s := {k})
  intro j hj
  have hjk : j ≠ k := by simpa using hj
  rw [singleFrequencyPopulation_apply_ne k j hjk]
  simp

/-- The singleton's complete Sobolev mass is exactly the weight at its retained address. -/
theorem sobolevMass_singleFrequencyPopulation
    (order : ℕ) (k : SpatialFrequency) :
    sobolevMass order (singleFrequencyPopulation k) =
      periodicSobolevWeight order k := by
  unfold sobolevMass
  rw [tsum_eq_single k]
  · simp [singleFrequencyPopulation_apply_self]
  · intro j hj
    rw [singleFrequencyPopulation_apply_ne k j hj]
    simp

/-- Every single-frequency population has exact order-zero mass one. -/
@[simp]
theorem sobolevMass_zero_singleFrequencyPopulation (k : SpatialFrequency) :
    sobolevMass 0 (singleFrequencyPopulation k) = 1 := by
  rw [sobolevMass_singleFrequencyPopulation]
  simp [periodicSobolevWeight]

/-- The order-two receiver of the axial occurrence retains the exact squared Stokes scale. -/
@[simp]
theorem sobolevMass_two_singleFrequencyPopulation_axial (n : ℕ) :
    sobolevMass 2 (singleFrequencyPopulation (axialFrequency n)) =
      (1 + (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2) ^ 2 := by
  rw [sobolevMass_singleFrequencyPopulation]
  simp [periodicSobolevWeight]

/-- The derivative-bearing mass dominates the natural frequency index exactly. -/
theorem natCast_le_sobolevMass_two_singleFrequencyPopulation_axial (n : ℕ) :
    (n : ℝ) ≤ sobolevMass 2 (singleFrequencyPopulation (axialFrequency n)) := by
  rw [sobolevMass_two_singleFrequencyPopulation_axial]
  have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
    have hthree : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [sq_nonneg (2 * Real.pi - 1)]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnSq : (n : ℝ) ≤ (n : ℝ) ^ 2 + 1 := by nlinarith
  have hscale : (n : ℝ) ^ 2 ≤ (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  nlinarith [sq_nonneg ((2 * Real.pi) ^ 2 * (n : ℝ) ^ 2)]

/-- **[counterexample; formal-checked]** Every proposed order-zero-to-order-two bound is
separated by one exact axial Fourier occurrence. -/
theorem exists_singleFrequencyPopulation_separating_energy_from_orderTwo
    (C : ℝ) :
    ∃ n : ℕ,
      C * sobolevMass 0 (singleFrequencyPopulation (axialFrequency n)) <
        sobolevMass 2 (singleFrequencyPopulation (axialFrequency n)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  rw [sobolevMass_zero_singleFrequencyPopulation]
  simpa using hn.trans_le
    (natCast_le_sobolevMass_two_singleFrequencyPopulation_axial n)

/-- There is no scalar constant through which kinetic Fourier mass can reconstruct the complete
order-two mass of every smooth single-mode population. -/
theorem no_uniform_energy_bound_for_orderTwo_singleFrequencyPopulations :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      sobolevMass 2 (singleFrequencyPopulation (axialFrequency n)) ≤
        C * sobolevMass 0 (singleFrequencyPopulation (axialFrequency n)) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ :=
    exists_singleFrequencyPopulation_separating_energy_from_orderTwo C
  exact (not_lt_of_ge (hC n)) hn

section Audit

#print axioms frequencySquared_axialFrequency
#print axioms torusStokesEigenvalue_axialFrequency
#print axioms singleFrequencyPopulation_hasPeriodicSobolevCoefficients
#print axioms sobolevMass_singleFrequencyPopulation
#print axioms sobolevMass_zero_singleFrequencyPopulation
#print axioms sobolevMass_two_singleFrequencyPopulation_axial
#print axioms natCast_le_sobolevMass_two_singleFrequencyPopulation_axial
#print axioms exists_singleFrequencyPopulation_separating_energy_from_orderTwo
#print axioms no_uniform_energy_bound_for_orderTwo_singleFrequencyPopulations

end Audit

end Soma.Holonics.Millennium.NavierStokesTerminalEnergySeparation
