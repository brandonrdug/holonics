import ElementaryHolonics.Transport.HelicalPairInteraction
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Pair resonance: locks, mediants and the modular address of a pair

[definition] Two phases coupled by a contact either lock at a rational rate ratio or wind
without closing. A lock is a direction in the pair's parameter plane; on a dissipative face it
is exactly the zero-power kernel of `HelicalPairInteraction`. Two locks are neighbours exactly
when their determinant is one, their mediant is a neighbour of both, and every ratio strictly
between two neighbours costs at least the mediant's period. This file proves those elementary
determinant and period statements; the broader Farey address theory remains in `Millennium/Farey`.
A unimodular word recharts the pair's two windings without changing their intersection number.
Independent coprime phases form a torus on which the single diagonal step visits every joint phase.

[established-bounded; formal-checked] Scope: integer and rational arithmetic, `ZMod` and 2×2
integer matrices. The rotation number of a driven pair, its mode-locking plateaus and any
analytic staircase are outside this module. No `axiom`, no `sorry`, no `native_decide`.
-/

open scoped BigOperators Matrix
open Matrix

namespace Soma.Holonics.Geometry.PairResonance

open Soma.Holonics.Geometry.ScrewGeometry
open Soma.Holonics.Transport.HolonicInteraction
open Soma.Holonics.Transport.HelicalPairInteraction

/-! ## 1. A lock is the zero-power direction -/

/-- [proved-derived; formal-checked] **A rational lock dissipates nothing.** On a dissipative
face of positive weight, advancing the first object at rate `q` and the second at rate `p`
reads zero power exactly when `q v_a = p v_b`. -/
theorem lock_iff_zero_power {w : ℚ} (hw : 0 < w) (va vb : Vec) (D : Matrix (Fin 3) (Fin 3) ℚ)
    (hdefinite : ∀ x : Vec, x ⬝ᵥ (D *ᵥ x) = 0 → x = 0) (p q : ℤ) :
    quad (faceForm w (pairSlip va vb) D) ![(q : ℚ), (p : ℚ)] = 0
      ↔ (q : ℚ) • va = (p : ℚ) • vb := by
  simpa using pair_face_power_eq_zero_iff hw va vb D hdefinite ![(q : ℚ), (p : ℚ)]

/-- [proved-derived; formal-checked] A lock is a whole line of rates: every multiple of a
zero-power rate is a zero-power rate. -/
theorem lock_is_a_line (w : ℚ) (va vb : Vec) (D : Matrix (Fin 3) (Fin 3) ℚ) (u : Fin 2 → ℚ)
    (hzero : quad (faceForm w (pairSlip va vb) D) u = 0) (k : ℚ) :
    quad (faceForm w (pairSlip va vb) D) (k • u) = 0 := by
  rw [quad_smul, hzero, mul_zero]

/-! ## 2. Neighbouring locks, the mediant and its cost -/

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

/-! ## 3. A unimodular word recharts the pair's windings -/

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

/-! ## 4. Independent coprime phases form a torus with one diagonal winding -/

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

end Soma.Holonics.Geometry.PairResonance
