import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The egg's modular face: the Legendre `j` and the square lattice

[definition] `research/records/2026-09-27_EGG_PACKING_THE_MOIRE_OF_TWO_HELICES_IS_A_TORUS_KNOT_AND_THE_TREFOIL_IS_THE_HALF_TURN_WITH_THE_THIRD_TURN.md`
and the September 27 probability derivation (§5). The Hügelschäffer egg with semi-axis `a` and
displacement `w` carries the Legendre parameter `λ = ((a − w)/(a + w))²`; with `β = w/a` it is
`λ(β) = ((1 − β)/(1 + β))²` (`eggLambda`). The modular invariant of the Legendre curve
`y² = x(x − 1)(x − λ)` is

`j(λ) = 256 (1 − λ + λ²)³ / (λ² (1 − λ)²)` (`legendreJ`).

[proved-derived; formal-checked] What is proved, over any field for `j` and over `ℝ` for the egg.

1. **`j` forgets the labelling of the three finite branch points.** It is invariant under the six
   anharmonic images `λ, 1 − λ, 1/λ, 1/(1 − λ), (λ − 1)/λ, λ/(λ − 1)` (`legendreJ_anharmonic`):
   the half-turn `λ ↦ 1 − λ` and the inversion `λ ↦ 1/λ` generate the cross-ratio action of the
   permutations of the branch points.
2. **The square lattice.** `j − 1728 = 64 (λ + 1)² (λ − 2)² (2λ − 1)² / (λ² (1 − λ)²)`
   (`legendreJ_sub_1728`), so `j = 1728` exactly on the orbit `{−1, 1/2, 2}`, and
   `j(1/2) = 1728` (`legendreJ_half`).
3. **The egg reaches it at one displacement** (`egg_j_of_legendre_lambda`): for `0 < β < 1`,
   `λ(β) = 1/2` exactly when `β² − 6β + 1 = 0`, exactly when `β = 3 − 2√2`; there the egg's
   Legendre curve has `j = 1728`. The irrational displacement is carried as its constraint
   identity `β² − 6β + 1 = 0`, and `√2` as the root of `x² = 2`.

[open] The hypergeometric charts (`K(√λ) = (π/2) ₂F₁(½, ½; 1; λ)` and the Schwarz map of the
`(½, ⅓, 0)` triangle whose inverse is `1728/j`) and the identification of the monodromy with
`PSL(2, ℤ)` are not stated here; they remain named analytic obligations in #62.
-/

namespace Holonics.Geometry.EggModular

section Field

variable {K : Type*} [Field K]

/-- [definition] **The modular invariant of the Legendre curve** `y² = x(x − 1)(x − λ)`. -/
def legendreJ (l : K) : K :=
  256 * (1 - l + l ^ 2) ^ 3 / (l ^ 2 * (1 - l) ^ 2)

/-- [proved-derived; formal-checked] **`j` is invariant under the six anharmonic images.** -/
theorem legendreJ_anharmonic {l : K} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    legendreJ (1 - l) = legendreJ l ∧ legendreJ l⁻¹ = legendreJ l ∧
      legendreJ (1 - l)⁻¹ = legendreJ l ∧ legendreJ ((l - 1) / l) = legendreJ l ∧
        legendreJ (l / (l - 1)) = legendreJ l := by
  have h1' : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : l - 1 ≠ 0 := sub_ne_zero.mpr h1
  have e2 : 1 - l⁻¹ = (l - 1) / l := by field_simp
  have e3 : 1 - (1 - l)⁻¹ = -l / (1 - l) := by field_simp; ring
  have e4 : 1 - (l - 1) / l = 1 / l := by field_simp; ring
  have e5 : 1 - l / (l - 1) = -1 / (l - 1) := by field_simp; ring
  unfold legendreJ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sub_sub_cancel]
    ring
  · rw [e2]
    field_simp
    ring
  · rw [e3]
    field_simp
    ring
  · rw [e4]
    field_simp
    ring
  · rw [e5]
    field_simp
    ring

/-- [proved-derived; formal-checked] **The distance from the square lattice is a square.** -/
theorem legendreJ_sub_1728 {l : K} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    legendreJ l - 1728 =
      64 * (l + 1) ^ 2 * (l - 2) ^ 2 * (2 * l - 1) ^ 2 / (l ^ 2 * (1 - l) ^ 2) := by
  have h1' : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold legendreJ
  field_simp
  ring

end Field

/-- [proved-derived; formal-checked] **`j(1/2) = 1728`**, the square lattice. -/
theorem legendreJ_half : legendreJ (1 / 2 : ℚ) = 1728 := by
  norm_num [legendreJ]

/-- [definition] **The egg's Legendre parameter** at displacement ratio `β = w/a`. -/
noncomputable def eggLambda (β : ℝ) : ℝ := ((1 - β) / (1 + β)) ^ 2

/-- [proved-derived; formal-checked] **`egg_j_of_legendre_lambda`.** For `0 < β < 1` the egg's
Legendre parameter is `1/2` exactly when `β² − 6β + 1 = 0`, exactly when `β = 3 − 2√2`; there its
`j` is `1728`. -/
theorem egg_j_of_legendre_lambda {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (eggLambda β = 1 / 2 ↔ β ^ 2 - 6 * β + 1 = 0) ∧
      (β ^ 2 - 6 * β + 1 = 0 ↔ β = 3 - 2 * Real.sqrt 2) ∧
      (eggLambda β = 1 / 2 → legendreJ (eggLambda β) = 1728) := by
  have hpos : 1 + β ≠ 0 := by linarith
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hquad : eggLambda β = 1 / 2 ↔ β ^ 2 - 6 * β + 1 = 0 := by
    unfold eggLambda
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hpos) two_ne_zero]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  refine ⟨hquad, ?_, fun h => ?_⟩
  · constructor
    · intro h
      have hprod : (β - (3 - 2 * Real.sqrt 2)) * (β - (3 + 2 * Real.sqrt 2)) = 0 := by
        linear_combination h - 4 * hs
      rcases mul_eq_zero.mp hprod with h1 | h1
      · linarith
      · exfalso
        nlinarith
    · intro h
      rw [h]
      linear_combination 4 * hs
  · rw [h]
    norm_num [legendreJ]

end Holonics.Geometry.EggModular

section Audit
open Holonics.Geometry.EggModular
#print axioms legendreJ_anharmonic
#print axioms legendreJ_sub_1728
#print axioms legendreJ_half
#print axioms egg_j_of_legendre_lambda
end Audit
