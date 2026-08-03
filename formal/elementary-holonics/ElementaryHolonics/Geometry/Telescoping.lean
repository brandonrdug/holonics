import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Abel

/-!
# Exact finite transport identities

These are exact algebraic statements.
-/

open scoped BigOperators

namespace Soma.Holonics

theorem finite_telescoping {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (n : ℕ) :
    (∑ k ∈ Finset.range n, (f (k + 1) - f k)) = f n - f 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      abel

theorem closed_path_exact_sum_zero {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (n : ℕ) (hclosed : f n = f 0) :
    (∑ k ∈ Finset.range n, (f (k + 1) - f k)) = 0 := by
  rw [finite_telescoping, hclosed, sub_self]

theorem finite_geometric_remainder {R : Type*} [CommRing R]
    (r : R) (n : ℕ) :
    (∑ k ∈ Finset.range n, r ^ k) * (1 - r) = 1 - r ^ n := by
  exact geom_sum_mul_neg r n

end Soma.Holonics
