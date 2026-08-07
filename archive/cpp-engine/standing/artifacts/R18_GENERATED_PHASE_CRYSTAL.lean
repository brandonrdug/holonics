import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace Soma.Holonics.R18

theorem generated_diagonal_return (m n k : Nat) :
    (k % m = 0 ∧ k % n = 0) ↔ Nat.lcm m n ∣ k := by
  simp only [← Nat.dvd_iff_mod_eq_zero, Nat.lcm_dvd_iff]

theorem generated_coprime_diagonal_return (m n k : Nat) (h : Nat.Coprime m n) :
    (k % m = 0 ∧ k % n = 0) ↔ m * n ∣ k := by
  rw [generated_diagonal_return, h.lcm_eq_mul]

theorem generated_cell_population_product (first second : Finset Nat) :
    (first ×ˢ second).card = first.card * second.card := by
  exact Finset.card_product first second

def gaussStep112 (n : ℕ) : ℚ :=
  (((n : ℚ) + 1) * ((n : ℚ) + 1)) /
    (((n : ℚ) + 2) * ((n : ℚ) + 1))

theorem generated_gauss_112_transport (n : ℕ) :
    (1 / ((n : ℚ) + 1)) * gaussStep112 n = 1 / ((n : ℚ) + 2) := by
  simp only [gaussStep112]
  have h1 : (n : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n : ℚ) + 2 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (n + 1)
  field_simp

end Soma.Holonics.R18

#check Soma.Holonics.R18.generated_coprime_diagonal_return
