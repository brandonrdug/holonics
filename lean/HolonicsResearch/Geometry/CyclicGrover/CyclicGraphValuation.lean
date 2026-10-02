import Mathlib.NumberTheory.Multiplicity
import Lean.Elab.Tactic.Omega

/-!
Refs #62. Adachi--Mizuno--Tateno, Iwasawa theory for weighted graphs,
arXiv:2412.01612, newly found reference (not a recovered historical B submission).
This proves the valuation of the proposed determinant EXPRESSION for all levels.
It does not assume that expression is the determinant of the constructed operator:
the v2 TowerOperator consumer proves that join for every level.
-/

namespace Holonics.Foundation.CyclicGraphValuation
instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def vertexCount (n : ℕ) : ℕ := 3 ^ (n + 1)

theorem half_valuation (n : ℕ) :
    padicValNat 3 (4 ^ vertexCount n - 1) = n + 2 := by
  have h := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
    (by decide : Odd 3) (by decide : 1 < 4) (by decide : 3 ∣ 4 - 1)
    (by decide : ¬ 3 ∣ 4) (by simp [vertexCount] : vertexCount n ≠ 0)
  have h' : padicValNat 3 (4 ^ vertexCount n - 1) = 1 + (n + 1) := by
    simpa [vertexCount, padicValNat.prime_pow, padicValNat_self] using h
  omega

theorem valuation_expression (n : ℕ) :
    padicValNat 3 ((4 ^ vertexCount n - 1) ^ 2) = 2 * (n + 2) := by
  rw [padicValNat.pow, half_valuation]

theorem expression_nonzero (n : ℕ) : (4 ^ vertexCount n - 1) ^ 2 ≠ 0 := by
  have hn : vertexCount n ≠ 0 := by simp [vertexCount]
  have h : 1 < 4 ^ vertexCount n := one_lt_pow₀ (by decide) hn
  exact pow_ne_zero _ (Nat.sub_ne_zero_of_lt h)

end Holonics.Foundation.CyclicGraphValuation

#print axioms Holonics.Foundation.CyclicGraphValuation.valuation_expression
