import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Pair resonance: locks, mediants and the modular address of a pair

[definition] Two rationally related phases either lock or wind without closing. This owner states
the elementary address and period laws: neighbouring locks have determinant one, their mediant
neighbours both, and every ratio strictly between them costs at least the mediant's period. A
unimodular word recharts the pair's two windings without changing their intersection number.
Independent coprime phases form a torus on which the single diagonal step visits every joint phase.
The contact-power lock criteria live with the pair contact in
`Transport/HelicalPairInteraction`; the broader Farey address theory remains in
`Millennium/Farey`.

[established-bounded; formal-checked] Scope: integer and rational arithmetic, `ZMod` and 2×2
integer matrices. The rotation number of a driven pair, its mode-locking plateaus and any
analytic staircase are outside this module. No `axiom`, no `sorry`, no `native_decide`.
-/

open scoped BigOperators Matrix
open Matrix

namespace Holonics.Geometry.PairResonance

/-! ## 1. Neighbouring locks, the mediant and its cost -/

/-- [proved-derived; formal-checked] **The mediant of two neighbouring locks neighbours both.** -/
theorem mediant_neighbours_both (p q p' q' : ℤ) (hadj : p' * q - p * q' = 1) :
    (p + p') * q - p * (q + q') = 1 ∧ p' * (q + q') - (p + p') * q' = 1 := by
  constructor <;> linear_combination hadj

/-- [proved-derived; formal-checked] The mediant lies strictly between, in cross-multiplied
form so that no division is introduced. -/
theorem mediant_lies_between (p q p' q' : ℤ) (hlt : p * q' < p' * q) :
    p * (q + q') < (p + p') * q ∧ (p + p') * q' < p' * (q + q') := by
  constructor <;> nlinarith

/-- [proved-derived; formal-checked] **Every ratio strictly between two neighbouring locks costs
at least the mediant's period.** The mediant is the cheapest lock in the gap, which is why a
tolerance selects a finite address. -/
theorem between_neighbours_costs_at_least_the_mediant (p q p' q' a b : ℤ)
    (hq : 0 < q) (hq' : 0 < q') (hadj : p' * q - p * q' = 1)
    (hleft : p * b < a * q) (hright : a * q' < p' * b) : q + q' ≤ b := by
  have hx : 1 ≤ a * q - p * b := by omega
  have hy : 1 ≤ p' * b - a * q' := by omega
  have hb : b = q * (p' * b - a * q') + q' * (a * q - p * b) := by
    linear_combination (-b) * hadj
  nlinarith [mul_le_mul_of_nonneg_left hy hq.le, mul_le_mul_of_nonneg_left hx hq'.le]

/-- [proved-derived; formal-checked] Neighbouring locks are exactly the unimodular pairs in their
integer determinant chart. -/
theorem neighbours_iff_unimodular (p q p' q' : ℤ) :
    p' * q - p * q' = 1 ↔ (!![p', p; q', q]).det = 1 := by
  simp [Matrix.det_fin_two]

/-! ## 2. A unimodular word recharts the pair's windings -/

/-- [proved-derived; formal-checked] A unimodular integer word is invertible over the integers:
it is a change of basis of the pair's winding lattice, not a loss of resolution. -/
theorem unimodular_rechart_is_invertible (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = 1) :
    M * M.adjugate = 1 ∧ M.adjugate * M = 1 := by
  constructor
  · rw [Matrix.mul_adjugate, hM, one_smul]
  · rw [Matrix.adjugate_mul, hM, one_smul]

/-- [proved-derived; formal-checked] **A unimodular rechart conserves the intersection number**
of any two winding classes. -/
theorem unimodular_rechart_conserves_intersection (M N : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.det = 1) : (M * N).det = N.det := by
  rw [Matrix.det_mul, hM, one_mul]

/-! ## 3. Independent coprime phases form a torus with one diagonal winding -/

/-- [proved-derived; formal-checked] **The diagonal step visits every joint phase of two coprime
circles.** Independent moduli admit a toroidal chart, and the single act-and-advance step `+1`
is its diagonal winding. -/
theorem diagonal_step_generates_the_coprime_torus {m n : ℕ} [NeZero m] [NeZero n]
    (h : Nat.Coprime m n) (x : ZMod m × ZMod n) :
    ∃ k : ℕ, x = k • ((1, 1) : ZMod m × ZMod n) := by
  let e := ZMod.chineseRemainder h
  refine ⟨(e.symm x).val, ?_⟩
  have hval : ((e.symm x).val : ZMod (m * n)) = e.symm x := ZMod.natCast_zmod_val _
  have h1 : e 1 = ((1, 1) : ZMod m × ZMod n) := map_one e
  calc x = e (e.symm x) := (e.apply_symm_apply x).symm
    _ = e (((e.symm x).val : ZMod (m * n))) := by rw [hval]
    _ = e ((e.symm x).val • (1 : ZMod (m * n))) := by rw [nsmul_one]
    _ = (e.symm x).val • e 1 := map_nsmul e _ _
    _ = (e.symm x).val • ((1, 1) : ZMod m × ZMod n) := by rw [h1]

end Holonics.Geometry.PairResonance
