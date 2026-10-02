import HolonicsResearch.Geometry.CyclicGrover.GroverGraphChart
import HolonicsResearch.Geometry.CyclicGrover.CyclicGraphValuation

/-! Refs #62. The consumer concerns the actual incidence-defined graph operator
at every level, not a desired determinant expression. Integral coefficients;
the rational Grover normalization is joined through the degree-two certificate. -/
namespace Holonics.Epime.GroverTower
open Matrix Polynomial

def count (n : ℕ) : ℕ := 3^(n+1)
def chart (n : ℕ) : ℕ := count n - 2
abbrev Dart (n : ℕ) := GroverCycle.Dart (chart n)
def operator (n : ℕ) : Matrix (Dart n) (Dart n) ℤ := GroverCycle.grover (chart n)

theorem count_ge_three (n : ℕ) : 3 ≤ count n := by
  have h := Nat.one_le_pow n 3 (by decide : 0 < 3)
  dsimp [count]
  rw [pow_succ]
  omega

theorem chart_size (n : ℕ) : chart n + 2 = count n := by
  have := count_ge_three n
  dsimp [chart]
  omega

theorem chart_positive (n : ℕ) : 1 ≤ chart n := by
  have := count_ge_three n
  dsimp [chart]
  omega

theorem actual_characteristic_polynomial (n : ℕ) :
    (operator n).charpoly = ((X : ℤ[X])^(count n)-1)^2 := by
  change (GroverCycle.grover (chart n) : Matrix (Dart n) (Dart n) ℤ).charpoly = _
  rw [GroverCycle.grover_charpoly, chart_size]

theorem actual_determinant (n : ℕ) :
    (Matrix.scalar (Dart n) (4:ℤ) - operator n).det = ((4:ℤ)^(count n)-1)^2 := by
  change (Matrix.scalar (Dart n) (4:ℤ) - GroverCycle.grover (chart n)).det = _
  rw [GroverCycle.grover_determinant, chart_size]

theorem actual_determinant_nat (n : ℕ) :
    (Matrix.scalar (Dart n) (4:ℤ) - operator n).det = (((4^(count n)-1)^2 : ℕ):ℤ) := by
  rw [actual_determinant]
  have hp : 1 ≤ (4:ℕ)^(count n) := Nat.one_le_pow _ _ (by decide)
  simp only [Nat.cast_pow, Int.natCast_sub hp, Nat.cast_one, Nat.cast_ofNat]

theorem actual_valuation (n : ℕ) :
    padicValInt 3 ((Matrix.scalar (Dart n) (4:ℤ) - operator n).det) = 2*(n+2) := by
  rw [actual_determinant_nat, padicValInt.of_nat]
  simpa [count, Holonics.Foundation.CyclicGraphValuation.vertexCount] using Holonics.Foundation.CyclicGraphValuation.valuation_expression n

theorem actual_non_eigenvalue (n : ℕ) :
    (Matrix.scalar (Dart n) (4:ℤ) - operator n).det ≠ 0 := by
  rw [actual_determinant_nat]
  exact Int.natCast_ne_zero.mpr (Holonics.Foundation.CyclicGraphValuation.expression_nonzero n)

theorem rational_operator_receipt (n : ℕ) :
    (Int.castRingHom ℚ).mapMatrix (operator n) = GroverCycle.rationalGrover (chart n) :=
  GroverCycle.integral_matches_rational (chart n) (chart_positive n)

end Holonics.Epime.GroverTower

#print axioms Holonics.Epime.GroverTower.actual_determinant
#print axioms Holonics.Epime.GroverTower.actual_valuation
#print axioms Holonics.Epime.GroverTower.actual_non_eigenvalue
