import ElementaryHolonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner

/-!
# Temporal payment boundary for the adaptive nonlinear-source square owner

**[proved-derived; formal-checked]**  The adaptive square owner is paid on every compact
interior interval by the time integral of the squared native `H3` norm.  Thus its temporal face is
exactly an `L1` current of a square, equivalently the squared `L2_t H3_x` current; it is not a
time-jet norm.

This file tests whether lower unconditional energy/enstrophy currents can pay that face.  One
single Fourier occurrence is observed through a clock aperture whose duration is the reciprocal
of its order-two Sobolev mass.  On that aperture the integrated order-two mass is exactly one,
the integrated order-one mass is at most one, and the order-zero endpoint mass is exactly one.
Nevertheless, the required integrated order-three mass is exactly the unbounded order-one mass.

The result is a scaling separator, not a Navier--Stokes solution or a blow-up construction.  It
shows that even granting a uniformly paid order-two spacetime current in addition to kinetic
energy and the energy-law order-one current does not close the square owner's terminal-uniform
fibre.  The next missing dissipative current is the order-three spatial square mass itself (the
viscous current belonging to an order-two energy), or a constitutive estimate that genuinely
controls it.
-/

noncomputable section

open MeasureTheory

namespace Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceTemporalPayment

open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTerminalEnergySeparation
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The exact reciprocal order-two clock aperture -/

/-- The time aperture which spends one unit of integrated order-two singleton mass. -/
def enstrophyDissipationClockAperture (n : ℕ) : ℝ :=
  (sobolevMass 2 (singleFrequencyPopulation (axialFrequency n)))⁻¹

/-- The constant Sobolev square current observed through the reciprocal order-two aperture. -/
def enstrophyDissipationClockPayment (order n : ℕ) : ℝ :=
  ∫ _time in (0 : ℝ)..enstrophyDissipationClockAperture n,
    sobolevMass order (singleFrequencyPopulation (axialFrequency n))

/-- Every reciprocal order-two clock aperture has positive duration. -/
theorem enstrophyDissipationClockAperture_pos (n : ℕ) :
    0 < enstrophyDissipationClockAperture n := by
  unfold enstrophyDissipationClockAperture
  apply inv_pos.mpr
  rw [sobolevMass_singleFrequencyPopulation]
  exact periodicSobolevWeight_pos 2 (axialFrequency n)

/-- On a singleton, order two is the square of order one. -/
theorem sobolevMass_two_singleFrequencyPopulation_eq_one_sq
    (frequency : SpatialFrequency) :
    sobolevMass 2 (singleFrequencyPopulation frequency) =
      sobolevMass 1 (singleFrequencyPopulation frequency) ^ 2 := by
  rw [sobolevMass_singleFrequencyPopulation,
    sobolevMass_singleFrequencyPopulation]
  unfold periodicSobolevWeight
  ring

/-- The clock aperture pays exactly one unit of integrated order-two mass. -/
@[simp]
theorem enstrophyDissipationClockPayment_two (n : ℕ) :
    enstrophyDissipationClockPayment 2 n = 1 := by
  have hmass : sobolevMass 2
      (singleFrequencyPopulation (axialFrequency n)) ≠ 0 := by
    rw [sobolevMass_singleFrequencyPopulation]
    exact (periodicSobolevWeight_pos 2 (axialFrequency n)).ne'
  rw [enstrophyDissipationClockPayment,
    intervalIntegral.integral_const,
    enstrophyDissipationClockAperture, sub_zero]
  simpa [smul_eq_mul] using
    (inv_mul_cancel₀ hmass)

/-- The integrated order-three mass across the same aperture is exactly the remaining order-one
scale factor. -/
@[simp]
theorem enstrophyDissipationClockPayment_three (n : ℕ) :
    enstrophyDissipationClockPayment 3 n =
      sobolevMass 1 (singleFrequencyPopulation (axialFrequency n)) := by
  have hone : sobolevMass 1
      (singleFrequencyPopulation (axialFrequency n)) ≠ 0 := by
    rw [sobolevMass_singleFrequencyPopulation]
    exact (periodicSobolevWeight_pos 1 (axialFrequency n)).ne'
  rw [enstrophyDissipationClockPayment,
    intervalIntegral.integral_const,
    enstrophyDissipationClockAperture,
    sobolevMass_three_singleFrequencyPopulation_eq_one_mul_two]
  rw [sub_zero]
  simp only [smul_eq_mul]
  field_simp

/-- The integrated order-one current is the reciprocal order-one mass. -/
@[simp]
theorem enstrophyDissipationClockPayment_one (n : ℕ) :
    enstrophyDissipationClockPayment 1 n =
      (sobolevMass 1 (singleFrequencyPopulation (axialFrequency n)))⁻¹ := by
  have hone : sobolevMass 1
      (singleFrequencyPopulation (axialFrequency n)) ≠ 0 := by
    rw [sobolevMass_singleFrequencyPopulation]
    exact (periodicSobolevWeight_pos 1 (axialFrequency n)).ne'
  rw [enstrophyDissipationClockPayment,
    intervalIntegral.integral_const,
    enstrophyDissipationClockAperture,
    sobolevMass_two_singleFrequencyPopulation_eq_one_sq]
  rw [sub_zero]
  simp only [smul_eq_mul]
  field_simp

/-- The energy-law order-one spacetime current remains at most one on the reciprocal order-two
clock aperture. -/
theorem enstrophyDissipationClockPayment_one_le_one (n : ℕ) :
    enstrophyDissipationClockPayment 1 n ≤ 1 := by
  rw [enstrophyDissipationClockPayment_one]
  rw [sobolevMass_singleFrequencyPopulation]
  exact inv_le_one_of_one_le₀
    (one_le_periodicSobolevWeight 1 (axialFrequency n))

/-! ## The mixed lower-current budget and its exact separation -/

/-- Kinetic endpoint mass plus the integrated order-one and order-two currents.  This is stronger
than the unconditional energy-law testimony because it grants a uniformly paid order-two current.
-/
def energyEnstrophyDissipationClockBudget (n : ℕ) : ℝ :=
  sobolevMass 0 (singleFrequencyPopulation (axialFrequency n)) +
    enstrophyDissipationClockPayment 1 n +
      enstrophyDissipationClockPayment 2 n

/-- The mixed lower-current budget is uniformly bounded by three. -/
theorem energyEnstrophyDissipationClockBudget_le_three (n : ℕ) :
    energyEnstrophyDissipationClockBudget n ≤ 3 := by
  unfold energyEnstrophyDissipationClockBudget
  rw [sobolevMass_zero_singleFrequencyPopulation,
    enstrophyDissipationClockPayment_two]
  linarith [enstrophyDissipationClockPayment_one_le_one n]

/-- The mixed lower-current budget is strictly positive. -/
theorem energyEnstrophyDissipationClockBudget_pos (n : ℕ) :
    0 < energyEnstrophyDissipationClockBudget n := by
  unfold energyEnstrophyDissipationClockBudget
  rw [sobolevMass_zero_singleFrequencyPopulation,
    enstrophyDissipationClockPayment_one,
    enstrophyDissipationClockPayment_two]
  have hone : 0 < sobolevMass 1
      (singleFrequencyPopulation (axialFrequency n)) := by
    rw [sobolevMass_singleFrequencyPopulation]
    exact periodicSobolevWeight_pos 1 (axialFrequency n)
  positivity

/-- The order-one singleton mass is unbounded without reopening the trigonometric scale formula.
The already-owned order-two lower bound and the exact square identity suffice. -/
theorem exists_axial_orderOne_mass_gt (C : ℝ) (hC : 0 ≤ C) :
    ∃ n : ℕ, C < sobolevMass 1
      (singleFrequencyPopulation (axialFrequency n)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2)
  have hscale :=
    natCast_le_sobolevMass_two_singleFrequencyPopulation_axial n
  rw [sobolevMass_two_singleFrequencyPopulation_eq_one_sq] at hscale
  have hone : 0 < sobolevMass 1
      (singleFrequencyPopulation (axialFrequency n)) := by
    rw [sobolevMass_singleFrequencyPopulation]
    exact periodicSobolevWeight_pos 1 (axialFrequency n)
  refine ⟨n, ?_⟩
  nlinarith

/-- Every nonnegative proposed multiplier is separated by a clocked singleton whose endpoint
energy and integrated order-one/order-two currents remain uniformly bounded. -/
theorem exists_clocked_singleFrequencyPopulation_separating_mixed_lower_currents
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ n : ℕ,
      C * energyEnstrophyDissipationClockBudget n <
        enstrophyDissipationClockPayment 3 n := by
  obtain ⟨n, hn⟩ := exists_axial_orderOne_mass_gt (3 * C) (by positivity)
  refine ⟨n, ?_⟩
  calc
    C * energyEnstrophyDissipationClockBudget n ≤ C * 3 :=
      mul_le_mul_of_nonneg_left
        (energyEnstrophyDissipationClockBudget_le_three n) hC
    _ = 3 * C := by ring
    _ < sobolevMass 1 (singleFrequencyPopulation (axialFrequency n)) := hn
    _ = enstrophyDissipationClockPayment 3 n :=
      (enstrophyDissipationClockPayment_three n).symm

/-- **[counterexample; formal-checked]** No constant pays the required clocked `H3` square
current from kinetic endpoint mass plus integrated order-one and order-two currents.  This is a
strictly stronger temporal separator than the pointwise order-one-to-order-three test: the time
aperture contracts so that the entire order-two spacetime mass is exactly one. -/
theorem no_uniform_mixed_lower_current_bound_for_clocked_orderThree :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      enstrophyDissipationClockPayment 3 n ≤
        C * energyEnstrophyDissipationClockBudget n := by
  rintro ⟨C, hC⟩
  have hCnonneg : 0 ≤ C := by
    by_contra hnot
    have hCneg : C < 0 := lt_of_not_ge hnot
    have hright : C * energyEnstrophyDissipationClockBudget 0 < 0 :=
      mul_neg_of_neg_of_pos hCneg
        (energyEnstrophyDissipationClockBudget_pos 0)
    have hleft : 0 < enstrophyDissipationClockPayment 3 0 := by
      rw [enstrophyDissipationClockPayment_three,
        sobolevMass_singleFrequencyPopulation]
      exact periodicSobolevWeight_pos 1 (axialFrequency 0)
    linarith [hC 0]
  obtain ⟨n, hn⟩ :=
    exists_clocked_singleFrequencyPopulation_separating_mixed_lower_currents C hCnonneg
  exact (not_lt_of_ge (hC n)) hn

/-! ## Audit -/

section Audit

#print axioms enstrophyDissipationClockPayment_two
#print axioms enstrophyDissipationClockPayment_three
#print axioms enstrophyDissipationClockPayment_one
#print axioms energyEnstrophyDissipationClockBudget_le_three
#print axioms exists_axial_orderOne_mass_gt
#print axioms exists_clocked_singleFrequencyPopulation_separating_mixed_lower_currents
#print axioms no_uniform_mixed_lower_current_bound_for_clocked_orderThree

end Audit

end Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceTemporalPayment
