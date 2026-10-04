import Holonics.HNN.ChartResidual

/-!
# HNN.MovedChart: the chart re-founded at the moved prior

[definition] #62, owed by #317 (`hnn::constitution::SolvedChart::moved`; the record
`research/records/2026-10-04_THE_RECEIVING_PRIOR_IS_CARRIED_BESIDE_ITS_GRAM_AND_MOVES_TO_THE_CODES_CELL.md`
§3).
When the located prior moves from `s = 2^k` to `s′ = 2^(k′)`, the law's Gram keeps its
readings' statistic and moves its diagonal with the prior, `H′ = H + (s′ − s) I`; the chart is
re-founded at the new scale and warm-started at `x X̂`, `x = s/s′ = 2^(k − k′)`, the same `x` by
which `HNN/PriorMove` rebases the at-map pair (the exit down `k ↦ k + 1` is `x = ½`). It is then
refined and certified against `H′` as a deposit's chart is (`SolvedChart::settled`), and the
certified chart is near the exact inverse by `ChartResidual.inverse_chart_deviation_left`.

```text
moved Gram     H′ = H + (s′ − s) I ,   H′ − s′ I = H − s I = G           (the statistic unchanged)
warm start     1 − x X̂ H′ = (1 − X̂ H) + (1 − x) X̂ G ,   x = s/s′
               ‖1 − x X̂ H′‖∞ ≤ δ + (1 − x) ‖X̂ G‖∞      (x ≤ 1, ‖1 − X̂ H‖∞ ≤ δ)
exact chart    Y H = 1  ⇒  1 − x Y H′ = (1 − x) Y G
off support    X̂ = s⁻¹ , H = s on a row  ⇒  x X̂ is exact there:  (1 − x X̂ H′)_ii = 0
unscaled       1 − X̂ H′ = (1 − X̂ H) + (1 − x⁻¹) s X̂ ;  off support (1 − X̂ H′)_ii = 1 − x⁻¹
lattice        X̂_ij ∈ 2^(−a) ℤ, k ≤ k′  ⇒  x X̂_ij ∈ 2^(−(a + k′ − k)) ℤ
```

[proved-derived; formal-checked] What is proved.

1. **The moved Gram keeps the statistic** (`moved_gram_statistic`).
2. **The warm start's residual** (`moved_residual`, `moved_residual_le`). Against the moved Gram the
   scaled chart's residual is the chart's own plus `(1 − x)` times `X̂ G`, exactly. So for a move up
   (`x ≤ 1`) its certificate is at most the chart's plus `(1 − x) ‖X̂ G‖∞`. At the exact
   inverse the residual is `(1 − x) Y G` (`moved_exact_residual`): what remains is the part of the
   Gram the prior does not carry, scaled by the move.
3. **Off the support the scaled chart is exact** (`moved_off_support`), and **the unscaled chart is
   not** (`unmoved_residual`, `unmoved_off_support`, `unmoved_not_contracting`): there the previous
   chart leaves `1 − x⁻¹` on the diagonal, whose certificate is at least `1` at `x ≤ ½`, outside the
   contraction the refinement needs. This is why the Rust scales the warm start.
4. **The lattice** (`moved_lattice`). For a move up the scaled chart lies on a lattice `k′ − k`
   levels finer, the Rust's `exponent ≥ self.exponent + finer`.

[open] The refinement's convergence from the warm start is not a theorem here: the Rust
(`settled`) restarts once from the scaled identity when the warm start does not contract, and
refuses the move when `δ_ℓ` is not reached. For a move down (`x = 2`) `moved_residual` gives
`(1 − X̂ H) − X̂ G`, which no bound here keeps below `1`. The Rust warm-starts the Gram's support
block only, off it the founded `2^(−k′) I`; the identities hold on any square block. No `sorry`, no
`axiom`, no `native_decide`.
-/

namespace Holonics.HNN.MovedChart

open Matrix
open Holonics.HNN.LatticeWord (rowNorm rowNorm_nonneg row_sum_le_rowNorm rowNorm_le
  rowNorm_add_le)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] **The moved Gram** (`SolvedChart::moved`'s `gram`): the diagonal moved from the
prior `s` to `s′`, the readings' statistic unchanged. -/
def movedGram (H : Matrix n n ℚ) (s s' : ℚ) : Matrix n n ℚ := H + (s' - s) • (1 : Matrix n n ℚ)

omit [Fintype n] in
/-- [proved-derived; formal-checked] **The moved Gram keeps the statistic**:
`H′ − s′ I = H − s I`. -/
theorem moved_gram_statistic (H : Matrix n n ℚ) (s s' : ℚ) :
    movedGram H s s' - s' • (1 : Matrix n n ℚ) = H - s • (1 : Matrix n n ℚ) := by
  simp only [movedGram, sub_smul]
  abel

/-- [proved-derived; formal-checked] **The warm start's residual against the moved Gram.** With
`G = H − s I` and `x = s/s′`, `1 − x X̂ H′ = (1 − X̂ H) + (1 − x) X̂ G`. -/
theorem moved_residual (H X : Matrix n n ℚ) {s s' : ℚ} (hs' : s' ≠ 0) :
    1 - ((s / s') • X) * movedGram H s s' =
      (1 - X * H) + (1 - s / s') • (X * (H - s • (1 : Matrix n n ℚ))) := by
  have hsx : s = s' * (s / s') := by field_simp
  generalize s / s' = x at hsx ⊢
  subst hsx
  simp only [movedGram, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_sub]
  module

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] A nonnegative scalar scales the row norm. -/
theorem rowNorm_smul_le {c : ℚ} (hc : 0 ≤ c) (A : Matrix n n ℚ) :
    rowNorm (c • A) ≤ c * rowNorm A :=
  rowNorm_le (mul_nonneg hc (rowNorm_nonneg A)) fun i => by
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (row_sum_le_rowNorm A i) hc

/-- [proved-derived; formal-checked] **The warm start's certificate.** For a move up
(`x ≤ 1`), `‖1 − x X̂ H′‖∞ ≤ δ + (1 − x) ‖X̂ G‖∞` when `‖1 − X̂ H‖∞ ≤ δ`. -/
theorem moved_residual_le (H X : Matrix n n ℚ) {s s' δ : ℚ} (hs' : s' ≠ 0)
    (hx1 : s / s' ≤ 1) (hδ : rowNorm (1 - X * H) ≤ δ) :
    rowNorm (1 - ((s / s') • X) * movedGram H s s') ≤
      δ + (1 - s / s') * rowNorm (X * (H - s • (1 : Matrix n n ℚ))) := by
  rw [moved_residual H X hs']
  exact (rowNorm_add_le _ _).trans (add_le_add hδ (rowNorm_smul_le (sub_nonneg.mpr hx1) _))

/-- [proved-derived; formal-checked] **At the exact inverse** the scaled chart's residual is the
part of the Gram the prior does not carry, scaled by the move:
`Y H = 1 ⇒ 1 − x Y H′ = (1 − x) Y G`. -/
theorem moved_exact_residual (H Y : Matrix n n ℚ) {s s' : ℚ} (hs' : s' ≠ 0) (hY : Y * H = 1) :
    1 - ((s / s') • Y) * movedGram H s s' =
      (1 - s / s') • (Y * (H - s • (1 : Matrix n n ℚ))) := by
  rw [moved_residual H Y hs', hY, sub_self, zero_add]

/-- [proved-derived; formal-checked] **Off the support the scaled chart is exact**: on a row where
the chart is `s⁻¹` and the Gram is `s` (the founded chart `2^(−k) I` off the Gram's support), the
residual of `x X̂` against `H′` vanishes. -/
theorem moved_off_support (H X : Matrix n n ℚ) {s s' : ℚ} (hs : s ≠ 0) (hs' : s' ≠ 0) (i : n)
    (hX : ∀ j, X i j = if i = j then s⁻¹ else 0) (hH : ∀ j, H i j = if i = j then s else 0)
    (j : n) : (1 - ((s / s') • X) * movedGram H s s') i j = 0 := by
  rw [moved_residual H X hs']
  have hrow : ∀ (A : Matrix n n ℚ), (X * A) i j = s⁻¹ * A i j := fun A => by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hX i, if_pos rfl]
    · intro b _ hb; rw [hX b, if_neg (Ne.symm hb), zero_mul]
    · simp
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hrow, hH,
    Matrix.one_apply]
  split_ifs <;> field_simp <;> ring

/-- [proved-derived; formal-checked] **The unscaled chart against the moved Gram**:
`1 − X̂ H′ = (1 − X̂ H) + (1 − x⁻¹) s X̂`. -/
theorem unmoved_residual (H X : Matrix n n ℚ) {s s' : ℚ} (hs : s ≠ 0) :
    1 - X * movedGram H s s' = (1 - X * H) + (1 - (s / s')⁻¹) • (s • X) := by
  have hx : (1 - (s / s')⁻¹) * s = -(s' - s) := by rw [inv_div]; field_simp; ring
  simp only [movedGram, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, smul_smul, hx, neg_smul]
  abel

/-- [proved-derived; formal-checked] Off the support the unscaled chart leaves `1 − x⁻¹` on the
diagonal. -/
theorem unmoved_off_support (H X : Matrix n n ℚ) {s s' : ℚ} (hs : s ≠ 0) (i : n)
    (hX : ∀ j, X i j = if i = j then s⁻¹ else 0) (hH : ∀ j, H i j = if i = j then s else 0) :
    (1 - X * movedGram H s s') i i = 1 - (s / s')⁻¹ := by
  rw [unmoved_residual H X hs]
  have hXH : (X * H) i i = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hX i, hH i, if_pos rfl, if_pos rfl, inv_mul_cancel₀ hs]
    · intro b _ hb; rw [hX b, if_neg (Ne.symm hb), zero_mul]
    · simp
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq, hXH, Matrix.smul_apply,
    Matrix.smul_apply, hX i, if_pos rfl, smul_eq_mul, smul_eq_mul, mul_inv_cancel₀ hs]
  ring

/-- [proved-derived; formal-checked] **The unscaled chart does not contract** for a move up by at
least one level: off the support its certificate is at least `1` at `0 < x ≤ ½`. -/
theorem unmoved_not_contracting (H X : Matrix n n ℚ) {s s' : ℚ} (hs : s ≠ 0) (i : n)
    (hX : ∀ j, X i j = if i = j then s⁻¹ else 0) (hH : ∀ j, H i j = if i = j then s else 0)
    (hx0 : 0 < s / s') (hx : s / s' ≤ 1 / 2) :
    1 ≤ rowNorm (1 - X * movedGram H s s') := by
  have hdiag := unmoved_off_support H X (s' := s') hs i hX hH
  have hge : 1 ≤ |(1 - X * movedGram H s s') i i| := by
    rw [hdiag]
    have h2 : 2 ≤ (s / s')⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hx0]; simpa using hx
    rw [abs_of_nonpos (by linarith)]
    linarith
  refine hge.trans ((Finset.single_le_sum (fun j _ => abs_nonneg _) (Finset.mem_univ i)).trans
    (row_sum_le_rowNorm _ i))

/-- [proved-derived; formal-checked] **The lattice** (`exponent ≥ self.exponent + finer`). For a
move up `k ≤ k′`, an entry on `2^(−a) ℤ` scaled by `x = 2^(k − k′)` lies on
`2^(−(a + k′ − k)) ℤ`. -/
theorem moved_lattice {k k' a : ℕ} (hk : k ≤ k') (m : ℤ) :
    (2 : ℚ) ^ k / 2 ^ k' * (m / 2 ^ a) = m / 2 ^ (a + (k' - k)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add, pow_add]
  field_simp

end Holonics.HNN.MovedChart

#print axioms Holonics.HNN.MovedChart.moved_gram_statistic
#print axioms Holonics.HNN.MovedChart.moved_residual
#print axioms Holonics.HNN.MovedChart.moved_residual_le
#print axioms Holonics.HNN.MovedChart.moved_exact_residual
#print axioms Holonics.HNN.MovedChart.moved_off_support
#print axioms Holonics.HNN.MovedChart.unmoved_residual
#print axioms Holonics.HNN.MovedChart.unmoved_off_support
#print axioms Holonics.HNN.MovedChart.unmoved_not_contracting
#print axioms Holonics.HNN.MovedChart.moved_lattice
