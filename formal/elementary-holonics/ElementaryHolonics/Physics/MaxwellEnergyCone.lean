import ElementaryHolonics.Millennium.HolonicMaxwellPropagation
import Mathlib

/-!
# Maxwell energy cone in a normalized finite field chart

This is the algebraic `Fin 3` electromagnetic field chart for arbitrary local field values.
Positive constitutive coefficients define the normalized fields. The polynomial energy bound
applies to standing, mixed and propagating configurations in that chart.
-/

namespace Soma.Holonics.Physics.MaxwellEnergyCone

noncomputable section

open scoped BigOperators

abbrev Field := Fin 3 → ℝ

def energyDensity (X Y : Field) : ℝ :=
  ((∑ i, X i ^ 2) + ∑ i, Y i ^ 2) / 2

def cross (X Y : Field) : Field :=
  ![X 1 * Y 2 - X 2 * Y 1,
    X 2 * Y 0 - X 0 * Y 2,
    X 0 * Y 1 - X 1 * Y 0]

def flux (c : ℝ) (X Y : Field) : Field := c • cross X Y

theorem cross_norm_identity (X Y : Field) :
    ∑ i, (cross X Y i) ^ 2 =
      (∑ i, X i ^ 2) * (∑ i, Y i ^ 2) - (∑ i, X i * Y i) ^ 2 := by
  simp [cross, Fin.sum_univ_succ]
  ring

theorem energy_cone_identity (c : ℝ) (X Y : Field) :
    c ^ 2 * (energyDensity X Y) ^ 2 - ∑ i, (flux c X Y i) ^ 2 =
      c ^ 2 * (((∑ i, X i ^ 2) - ∑ i, Y i ^ 2) ^ 2 / 4 +
        (∑ i, X i * Y i) ^ 2) := by
  rw [show (∑ i, (flux c X Y i) ^ 2) = c ^ 2 * ∑ i, (cross X Y i) ^ 2 by
    simp only [flux, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum]]
  rw [cross_norm_identity]
  unfold energyDensity
  ring

theorem energy_cone_nonnegative (c : ℝ) (X Y : Field) (hc : 0 ≤ c) :
    0 ≤ c ^ 2 * (energyDensity X Y) ^ 2 - ∑ i, (flux c X Y i) ^ 2 := by
  rw [energy_cone_identity]
  positivity

theorem flux_speed_bound (c : ℝ) (X Y : Field) (hc : 0 ≤ c) :
    Real.sqrt (∑ i, (flux c X Y i) ^ 2) ≤ c * energyDensity X Y := by
  have hu : 0 ≤ energyDensity X Y := by
    unfold energyDensity
    positivity
  have hcu : 0 ≤ c * energyDensity X Y := mul_nonneg hc hu
  have hflux : 0 ≤ ∑ i, (flux c X Y i) ^ 2 := by positivity
  have hsq : (Real.sqrt (∑ i, (flux c X Y i) ^ 2)) ^ 2 ≤
      (c * energyDensity X Y) ^ 2 := by
    rw [Real.sq_sqrt hflux]
    nlinarith [energy_cone_nonnegative c X Y hc]
  nlinarith [Real.sqrt_nonneg (∑ i, (flux c X Y i) ^ 2)]

theorem flux_zero_for_parallel (c : ℝ) (X : Field) (a : ℝ) (hc : 0 ≤ c) :
    flux c X (a • X) = 0 := by
  funext i
  fin_cases i <;> dsimp [flux, cross] <;> ring

end
end Soma.Holonics.Physics.MaxwellEnergyCone
