import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Two reflections make the dihedral group; a mirror is never a turn

The record `research/records/2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`
(§11 and §13(h)) owes the dihedral group by two reflections to #410. `Mathematics/BaseAction`
proves it inside `DihedralGroup n` (`two_reflections`, `two_reflections_generate`); this file proves
the rest of the box.

[proved-standard; formal-checked] What is proved.

1. **Two involutions in any group make the dihedral group** (`dihedralHom`,
   `two_involutions_dihedral`, `card_two_involutions`). For involutions `a ≠ b`, both `≠ 1`, the
   map `r i ↦ (ab)ⁱ`, `sr i ↦ a(ab)ⁱ` is an injective homomorphism from
   `DihedralGroup (orderOf (ab))` onto the subgroup they generate. So that subgroup has `2n`
   elements when `ab` has order `n` (`(ab)ⁿ = 1`, a finite turn), and is the infinite dihedral group
   when `ab` has infinite order, as the helix's step does.
2. **A mirror is never conjugate to a turn** (`det_turnMat`, `det_mirrorMat`,
   `mirror_not_conj_turn`). In the plane, a turn `[[a, −b], [b, a]]` with `a² + b² = 1` has
   determinant `1` and a mirror `[[c, s], [s, −c]]` with `c² + s² = 1` has determinant `−1`; a
   conjugation keeps the determinant, so no conjugation carries one to the other.
3. **The mirrors are conjugate to each other by turns** (`mirror_conj_by_turn`,
   `turnMat_mul_inverse`, `mirror_conj_by_turn_complex`). Conjugating the mirror `[[1, 0], [0, −1]]`
   by the turn `(a, b)` gives the mirror `(a² − b², 2ab)`, the doubled turn; on `ℂ`,
   `v · conj(conj v · z) = v² · conj z`, which is `R_ψ = Rot(ψ/2) R_0 Rot(−ψ/2)` with the angle kept as
   the exact unit `v`.

Consumers: the atlas row `motion.two-reflections-dihedral`.
-/

namespace Holonics.Geometry.TwoReflections

section Involutions

variable {G : Type*} [Group G]

/-- The turn part: `i ↦ tⁱ` on `ZMod (orderOf t)`, read through an integer representative. -/
noncomputable def turnPow (t : G) (i : ZMod (orderOf t)) : G := t ^ (i.cast : ℤ)

/-- [proved-standard; formal-checked] `turnPow` agrees with the integer power. -/
theorem turnPow_intCast (t : G) (k : ℤ) : turnPow t (k : ZMod (orderOf t)) = t ^ k := by
  rw [turnPow, zpow_eq_zpow_iff_modEq, ← ZMod.intCast_eq_intCast_iff, ZMod.intCast_zmod_cast]

/-- The candidate map from `DihedralGroup (orderOf (a b))` to `G`. -/
noncomputable def dihedralToGroup (a b : G) : DihedralGroup (orderOf (a * b)) → G
  | .r i => turnPow (a * b) i
  | .sr i => a * turnPow (a * b) i

/-- [proved-standard; formal-checked] An involution `a` turns `(ab)ᵏ` back to `(ab)⁻ᵏ`. -/
theorem conj_pow_of_involutions {a b : G} (ha : a * a = 1) (hb : b * b = 1) (k : ℤ) :
    a * (a * b) ^ k * a = (a * b) ^ (-k) := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, ha', hb', ← mul_assoc, ha, one_mul]
  calc a * (a * b) ^ k * a = a * (a * b) ^ k * a⁻¹ := by rw [ha']
    _ = (a * (a * b) * a⁻¹) ^ k := (conj_zpow).symm
    _ = (a * b) ^ (-k) := by rw [hconj, inv_zpow']

/-- [proved-standard; formal-checked] **The dihedral homomorphism of two involutions.** -/
noncomputable def dihedralHom {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    DihedralGroup (orderOf (a * b)) →* G where
  toFun := dihedralToGroup a b
  map_one' := by
    show turnPow (a * b) 0 = 1
    rw [show (0 : ZMod (orderOf (a * b))) = ((0 : ℤ) : ZMod _) by simp, turnPow_intCast,
      zpow_zero]
  map_mul' := by
    -- `a` carries `tᵏ` past itself as `t⁻ᵏ`.
    have key : ∀ k : ℤ, (a * b) ^ k * a = a * (a * b) ^ (-k) := fun k => by
      rw [← conj_pow_of_involutions ha hb k]
      simp only [← mul_assoc, ha, one_mul]
    rintro (i | i) (j | j) <;>
      obtain ⟨x, rfl⟩ := ZMod.intCast_surjective i <;>
      obtain ⟨y, rfl⟩ := ZMod.intCast_surjective j <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr, dihedralToGroup, ← Int.cast_add, ← Int.cast_sub,
        turnPow_intCast] <;>
      try simp only [mul_assoc]
    · rw [zpow_add]
    · -- tˣ · a tʸ = a t^(y − x)
      calc a * (a * b) ^ (y - x) = a * ((a * b) ^ (-x) * (a * b) ^ y) := by
            rw [← zpow_add, neg_add_eq_sub]
        _ = (a * b) ^ x * (a * (a * b) ^ y) := by rw [← mul_assoc, ← key, mul_assoc]
    · rw [zpow_add]
    · -- a tˣ · a tʸ = t^(y − x)
      calc (a * b) ^ (y - x) = (a * b) ^ (-x) * (a * b) ^ y := by rw [← zpow_add, neg_add_eq_sub]
        _ = a * (a * ((a * b) ^ (-x) * (a * b) ^ y)) := by rw [← mul_assoc a a, ha, one_mul]
        _ = a * ((a * b) ^ x * (a * (a * b) ^ y)) := by
            rw [← mul_assoc a ((a * b) ^ (-x)), ← key, mul_assoc]

/-- [proved-standard; formal-checked] **Two involutions make the dihedral group.** For
involutions `a ≠ b`, both `≠ 1`, the homomorphism is injective and its image is `⟨a, b⟩`. -/
theorem two_involutions_dihedral {a b : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) :
    Function.Injective (dihedralHom ha hb) ∧
      (dihedralHom ha hb).range = Subgroup.closure ({a, b} : Set G) := by
  set t := a * b with ht
  -- `a` is not a power of `t`: otherwise `a` commutes with `t`, so `t² = 1`, and then `a = b` or
  -- `b = 1`.
  have hnot : ∀ k : ℤ, a ≠ t ^ k := by
    intro k hk
    have hcomm : a * t * a = t := by
      have hta : t * a = a * t := by
        rw [hk]
        exact (Commute.self_zpow t k).eq
      rw [mul_assoc, hta, ← mul_assoc, ha, one_mul]
    have hinv := conj_pow_of_involutions ha hb 1
    rw [zpow_one, ← ht, hcomm] at hinv
    -- `t = t⁻¹`, so `t * t = 1`
    have htt : t * t = 1 := by
      rw [zpow_neg, zpow_one] at hinv
      exact mul_eq_one_iff_eq_inv.mpr hinv
    by_cases h1 : t = 1
    · apply hab
      have : a * b = 1 := h1
      calc a = a * (b * b) := by rw [hb, mul_one]
        _ = (a * b) * b := by group
        _ = b := by rw [this, one_mul]
    · -- `t` has order 2, so its powers are `1` and `t`; `a ≠ 1` forces `a = t = a b`, so `b = 1`
      apply hb1
      have hk' : a = 1 ∨ a = t := by
        rcases Int.emod_two_eq_zero_or_one k with h0 | h0
        · left
          rw [hk, ← Int.mul_ediv_add_emod k 2, h0, add_zero, zpow_mul, zpow_two, htt, one_zpow]
        · right
          rw [hk, ← Int.mul_ediv_add_emod k 2, h0, zpow_add, zpow_mul, zpow_two, htt, one_zpow,
            one_mul, zpow_one]
      rcases hk' with h | h
      · exact absurd h ha1
      · calc b = a⁻¹ * (a * b) := by group
          _ = a⁻¹ * a := by rw [← ht, ← h]
          _ = 1 := inv_mul_cancel a
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) hij <;>
      obtain ⟨x, rfl⟩ := ZMod.intCast_surjective i <;>
      obtain ⟨y, rfl⟩ := ZMod.intCast_surjective j <;>
      simp only [dihedralHom, MonoidHom.coe_mk, OneHom.coe_mk, dihedralToGroup,
        turnPow_intCast] at hij
    · congr 1
      rw [ZMod.intCast_eq_intCast_iff, ← zpow_eq_zpow_iff_modEq]
      exact hij
    · rw [← ht] at hij
      exact absurd (by rw [zpow_sub, hij, mul_inv_cancel_right] : a = t ^ (x - y)) (hnot _)
    · rw [← ht] at hij
      exact absurd (by rw [zpow_sub, ← hij, mul_inv_cancel_right] : a = t ^ (y - x)) (hnot _)
    · congr 1
      rw [ZMod.intCast_eq_intCast_iff, ← zpow_eq_zpow_iff_modEq]
      exact mul_left_cancel hij
  · apply le_antisymm
    · rintro g ⟨d, rfl⟩
      rcases d with i | i <;> obtain ⟨x, rfl⟩ := ZMod.intCast_surjective i <;>
        simp only [dihedralHom, MonoidHom.coe_mk, OneHom.coe_mk, dihedralToGroup,
          turnPow_intCast]
      · exact Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))) x
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))) x)
    · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨⟨.sr 0, ?_⟩, ⟨.sr 1, ?_⟩⟩
      · simp only [dihedralHom, MonoidHom.coe_mk, OneHom.coe_mk, dihedralToGroup]
        rw [show (0 : ZMod (orderOf (a * b))) = ((0 : ℤ) : ZMod _) by simp, turnPow_intCast,
          zpow_zero, mul_one]
      · simp only [dihedralHom, MonoidHom.coe_mk, OneHom.coe_mk, dihedralToGroup]
        rw [show (1 : ZMod (orderOf (a * b))) = ((1 : ℤ) : ZMod _) by simp, turnPow_intCast,
          zpow_one, ← mul_assoc, ha, one_mul]

/-- [proved-standard; formal-checked] **`⟨a, b⟩` has `2·orderOf(ab)` elements** (`0`, by
`Nat.card`'s convention, when it is infinite). -/
theorem card_two_involutions {a b : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 2 * orderOf (a * b) := by
  obtain ⟨hinj, hrange⟩ := two_involutions_dihedral ha hb ha1 hb1 hab
  rw [← hrange, ← DihedralGroup.nat_card]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Involutions

section Plane

variable {R : Type*} [CommRing R]

/-- The turn `(a, b)`: `[[a, −b], [b, a]]`. -/
def turnMat (a b : R) : Matrix (Fin 2) (Fin 2) R := !![a, -b; b, a]

/-- The mirror `(c, s)`: `[[c, s], [s, −c]]`. -/
def mirrorMat (c s : R) : Matrix (Fin 2) (Fin 2) R := !![c, s; s, -c]

/-- [proved-standard; formal-checked] A turn's determinant is `a² + b²`. -/
theorem det_turnMat (a b : R) : (turnMat a b).det = a ^ 2 + b ^ 2 := by
  simp [turnMat, Matrix.det_fin_two]
  ring

/-- [proved-standard; formal-checked] A mirror's determinant is `−(c² + s²)`. -/
theorem det_mirrorMat (c s : R) : (mirrorMat c s).det = -(c ^ 2 + s ^ 2) := by
  simp [mirrorMat, Matrix.det_fin_two]
  ring

/-- [proved-standard; formal-checked] **A mirror is never conjugate to a turn.** -/
theorem mirror_not_conj_turn (h2 : (2 : R) ≠ 0) {a b c s : R} (hab : a ^ 2 + b ^ 2 = 1)
    (hcs : c ^ 2 + s ^ 2 = 1) (P : Matrix (Fin 2) (Fin 2) R) (hP : IsUnit P) :
    P * mirrorMat c s * P⁻¹ ≠ turnMat a b := by
  intro h
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_conj hP, det_mirrorMat, det_turnMat, hab, hcs] at hdet
  apply h2
  linear_combination -hdet

/-- [proved-standard; formal-checked] The turn `(a, −b)` undoes the turn `(a, b)` on the unit
circle. -/
theorem turnMat_mul_inverse {a b : R} (hab : a ^ 2 + b ^ 2 = 1) :
    turnMat a b * turnMat a (-b) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [turnMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hab | linear_combination

/-- [proved-standard; formal-checked] **The mirrors are conjugate by turns:** the turn `(a, b)`
carries the mirror `(1, 0)` to the mirror `(a² − b², 2ab)`. -/
theorem mirror_conj_by_turn (a b : R) :
    turnMat a b * mirrorMat 1 0 * turnMat a (-b) = mirrorMat (a ^ 2 - b ^ 2) (2 * a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [turnMat, mirrorMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

open ComplexConjugate in
/-- [proved-standard; formal-checked] On `ℂ`: `v · conj(conj v · z) = v² · conj z`, so the mirror
`z ↦ v² conj z` is the turn by `v` of the mirror `z ↦ conj z`. -/
theorem mirror_conj_by_turn_complex (v z : ℂ) : v * conj (conj v * z) = v ^ 2 * conj z := by
  simp only [map_mul, Complex.conj_conj]
  ring

end Plane

end Holonics.Geometry.TwoReflections
