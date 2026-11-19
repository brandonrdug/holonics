import Mathlib

/-!
# A reading's leverage as a series over the pivots: `h = Σ_k Γ_k² / (Δ_(k−1) Δ_k)`

`HNN/ReadingLeverage` proves the split of a reading in a pivot chart of an encounter Gram, its bound, its value in
range, the bordered corner `−Δ h` (`det_bordered_corner`) and the prequential identities. #410's box also asks for the
corner as the series the fraction-free elimination reads it by: with `Δ_k` the pivots (the leading minors of the pivot
block, `Δ_0 = 1`) and `Γ_k` the border entry at the `k`-th pivot (the leading `k × k` minor with its last column
replaced by the reading), `h = Σ_k Γ_k² / (Δ_(k−1) Δ_k)`, so `−corner = Δ_r h` is a sum of the reading's shares at the
pivots (record
`2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT`,
§§9 and 10; atlas `contact.reading-leverage`).

[proved-derived; formal-checked] What is proved, over ℝ, for a symmetric array `G` (a Gram read on its first `r`
cells: the pivot block in its order) and a reading `v`, whose leading minors `Δ_k = det G_k` are nonzero for `k ≤ r`
(the positive definite case, `delta_pos_of_posDef`).

1. **One more pivot** (`delta_succ`, `gamma_eq`, `lev_succ`): with `A = G_k`, `g` the next column, `s` its Schur
   complement `G_kk − gᵀ A⁻¹ g` and `t = v_k − gᵀ A⁻¹ v`, the next minor is `Δ_(k+1) = Δ_k s`, the border entry is
   `Γ_k = Δ_k t`, and the leverage grows by `t² / s`: `h_(k+1) = h_k + t² / s`.
2. **The series** (`lev_eq_series`): `h_r = Σ_(k<r) Γ_k² / (Δ_k Δ_(k+1))` (indices from `0`, so `Δ_0 = 1` is the
   empty minor), each term the reading's share at one pivot.
3. **The corner** (`corner_eq_series`): `Δ_r h_r = Δ_r Σ_k Γ_k² / (Δ_k Δ_(k+1))`, the undivided pair the elimination
   carries; every term is a ratio of integers when `G` and `v` are.

The computational object is the helical pair interaction's encounter Gram: the cells a contact has met, read as a Gram,
and a new reading's leverage against it. Of the winding guide's six general objects this touches faces and placement
(the pivot chart); the helix, the pair, the cell holonomy, the tube and the tower thread stay attached.

What stands beside it: `HNN/ReadingLeverage` (the chart, the bound, `det_bordered_corner`, the prequential identities).
The identification of an elimination that passes zero pivots with the leading minors of the pivot block is the
elimination's own and is not stated here, and neither is the error `σ²(1 + h)`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ReadingLeverageSeries

open Matrix Finset

/-! ## 0. The leading blocks -/

/-- [definition] The leading `k × k` block of an array. -/
def lead (G : ℕ → ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => G i j

/-- [definition] The first `k` entries of a reading. -/
def leadVec (v : ℕ → ℝ) (k : ℕ) : Fin k → ℝ := fun i => v i

/-- [definition] The pivot `Δ_k`, the leading minor. -/
noncomputable def delta (G : ℕ → ℕ → ℝ) (k : ℕ) : ℝ := (lead G k).det

/-- [definition] The border entry at the pivot `k + 1`: the leading minor of size `k + 1` with its last column replaced
by the reading. -/
noncomputable def gamma (G : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (k : ℕ) : ℝ :=
  ((lead G (k + 1)).updateCol (Fin.last k) (leadVec v (k + 1))).det

/-- [definition] The leverage of the reading's first `k` entries against the leading block. -/
noncomputable def lev (G : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (k : ℕ) : ℝ :=
  leadVec v k ⬝ᵥ ((lead G k)⁻¹ *ᵥ leadVec v k)

/-! ## 1. A bordered determinant -/

/-- A matrix bordered by one column, one row and a corner has determinant `det A · (d − wᵀ A⁻¹ u)`. -/
theorem det_border {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) (hA : IsUnit A.det)
    (u w : m → ℝ) (d : ℝ) :
    (fromBlocks A (replicateCol (Fin 1) u) (replicateRow (Fin 1) w) (Matrix.of fun _ _ => d)).det =
      A.det * (d - w ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have := A.invertibleOfIsUnitDet hA
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 1
  rw [det_unique]
  simp only [Matrix.sub_apply, of_apply, Matrix.mul_apply, replicateRow_apply, replicateCol_apply, dotProduct,
    mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- The block of size `k + 1`, read through `Fin k ⊕ Fin 1`. -/
theorem lead_succ (G : ℕ → ℕ → ℝ) (k : ℕ) :
    (lead G (k + 1)).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (lead G k) (replicateCol (Fin 1) fun i : Fin k => G i k)
        (replicateRow (Fin 1) fun j : Fin k => G k j) (Matrix.of fun _ _ => G k k) := by
  ext (i | i) (j | j) <;> simp [lead, Fin.val_eq_zero]

/-- The bordered block of size `k + 1`, read through `Fin k ⊕ Fin 1`. -/
theorem border_succ (G : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (k : ℕ) :
    ((lead G (k + 1)).updateCol (Fin.last k) (leadVec v (k + 1))).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (lead G k) (replicateCol (Fin 1) (leadVec v k))
        (replicateRow (Fin 1) fun j : Fin k => G k j) (Matrix.of fun _ _ => v k) := by
  ext (i | i) (j | j)
  · simp [lead, Fin.ext_iff, j.isLt.ne]
  · simp [lead, leadVec, updateCol_apply, Fin.ext_iff, Fin.val_eq_zero]
  · simp [lead, Fin.ext_iff, Fin.val_eq_zero, j.isLt.ne]
  · simp [lead, leadVec, updateCol_apply, Fin.ext_iff, Fin.val_eq_zero]

/-! ## 2. One more pivot -/

section Step

variable (G : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (k : ℕ)

/-- [definition] The next column `g`. -/
def col (j : Fin k) : ℝ := G j k

/-- [definition] The Schur complement of the next pivot, `s = G_kk − gᵀ A⁻¹ g`. -/
noncomputable def schur : ℝ := G k k - col G k ⬝ᵥ ((lead G k)⁻¹ *ᵥ col G k)

/-- [definition] The reading's new part, `t = v_k − gᵀ A⁻¹ v`. -/
noncomputable def fresh : ℝ := v k - col G k ⬝ᵥ ((lead G k)⁻¹ *ᵥ leadVec v k)

variable {G}

/-- **The next minor**: `Δ_(k+1) = Δ_k s`. -/
theorem delta_succ (hsym : ∀ i j, G i j = G j i) (hk : delta G k ≠ 0) :
    delta G (k + 1) = delta G k * schur G k := by
  rw [delta, ← det_submatrix_equiv_self finSumFinEquiv, lead_succ, det_border _ (isUnit_iff_ne_zero.2 hk)]
  simp only [delta, schur]
  congr 3
  funext j
  exact hsym _ _

/-- **The border entry**: `Γ_k = Δ_k t`. -/
theorem gamma_eq (hsym : ∀ i j, G i j = G j i) (hk : delta G k ≠ 0) :
    gamma G v k = delta G k * fresh G v k := by
  rw [gamma, ← det_submatrix_equiv_self finSumFinEquiv, border_succ, det_border _ (isUnit_iff_ne_zero.2 hk)]
  simp only [delta, fresh]
  congr 3
  funext j
  exact hsym _ _

theorem lead_symm (hsym : ∀ i j, G i j = G j i) : (lead G k)ᵀ = lead G k := by
  ext i j
  simp [lead, hsym]

theorem dotProduct_inv_comm (hsym : ∀ i j, G i j = G j i) (a b : Fin k → ℝ) :
    a ⬝ᵥ ((lead G k)⁻¹ *ᵥ b) = b ⬝ᵥ ((lead G k)⁻¹ *ᵥ a) := by
  have hT : ((lead G k)⁻¹)ᵀ = (lead G k)⁻¹ := by rw [transpose_nonsing_inv, lead_symm k hsym]
  rw [dotProduct_mulVec, ← hT, vecMul_transpose, hT, dotProduct_comm]

/-- **The leverage grows by `t² / s`** at each pivot. -/
theorem lev_succ (hsym : ∀ i j, G i j = G j i) (hk : delta G k ≠ 0) (hs : schur G k ≠ 0) :
    lev G v (k + 1) = lev G v k + fresh G v k ^ 2 / schur G k := by
  set A := lead G k
  set g := col G k
  set τ := fresh G v k / schur G k with hτ
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 hk
  have hM : IsUnit (lead G (k + 1)).det := by
    have := delta_succ k hsym hk
    exact isUnit_iff_ne_zero.2 (by rw [← delta, this]; exact mul_ne_zero hk hs)
  have hτs : τ * schur G k = fresh G v k := by rw [hτ]; field_simp
  set z : Fin (k + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) (A⁻¹ *ᵥ (leadVec v k - τ • g)) τ with hz
  have hsolve : lead G (k + 1) *ᵥ z = leadVec v (k + 1) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [mulVec, dotProduct, Fin.sum_univ_castSucc]
      simp only [hz, Fin.snoc_castSucc, Fin.snoc_last]
      have hrow : ∀ j : Fin k, lead G (k + 1) (Fin.last k) (Fin.castSucc j) = g j := fun j => by
        simp [lead, g, col, hsym]
      simp only [hrow]
      have hlast : lead G (k + 1) (Fin.last k) (Fin.last k) = G k k := by simp [lead]
      rw [hlast]
      have hdot : ∑ j : Fin k, g j * (A⁻¹ *ᵥ (leadVec v k - τ • g)) j =
          g ⬝ᵥ (A⁻¹ *ᵥ leadVec v k) - τ * (g ⬝ᵥ (A⁻¹ *ᵥ g)) := by
        rw [← dotProduct, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [hdot]
      have hfresh : fresh G v k = v k - g ⬝ᵥ (A⁻¹ *ᵥ leadVec v k) := rfl
      have hschur : schur G k = G k k - g ⬝ᵥ (A⁻¹ *ᵥ g) := rfl
      simp only [leadVec, Fin.val_last]
      linear_combination hτs + hfresh - τ * hschur
    · rw [mulVec, dotProduct, Fin.sum_univ_castSucc]
      simp only [hz, Fin.snoc_castSucc, Fin.snoc_last]
      have hblock : ∀ j : Fin k, lead G (k + 1) (Fin.castSucc i) (Fin.castSucc j) = A i j := fun j => by
        simp [A, lead]
      simp only [hblock]
      have hinv : ∑ j : Fin k, A i j * (A⁻¹ *ᵥ (leadVec v k - τ • g)) j = leadVec v k i - τ * g i := by
        rw [← dotProduct, ← mulVec, mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
        simp
      rw [hinv]
      simp [lead, leadVec, g, col]
      ring
  have hz' : (lead G (k + 1))⁻¹ *ᵥ leadVec v (k + 1) = z := by
    rw [← hsolve, mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec]
  rw [lev, hz', dotProduct, Fin.sum_univ_castSucc]
  simp only [hz, Fin.snoc_castSucc, Fin.snoc_last]
  have hv : ∀ j : Fin k, leadVec v (k + 1) (Fin.castSucc j) = leadVec v k j := fun j => rfl
  simp only [hv]
  rw [← dotProduct, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    dotProduct_inv_comm k hsym (leadVec v k) g]
  have hfresh : fresh G v k = v k - g ⬝ᵥ (A⁻¹ *ᵥ leadVec v k) := rfl
  have hlastv : leadVec v (k + 1) (Fin.last k) = v k := by simp [leadVec]
  rw [hlastv, lev]
  rw [hτ]
  field_simp
  rw [hfresh]
  ring

end Step

/-! ## 3. The series -/

variable {G : ℕ → ℕ → ℝ} (v : ℕ → ℝ)

theorem delta_zero (G : ℕ → ℕ → ℝ) : delta G 0 = 1 := det_isEmpty

theorem lev_zero (G : ℕ → ℕ → ℝ) : lev G v 0 = 0 := by simp [lev, dotProduct]

/-- **The leverage is a series over the pivots**: `h_r = Σ_(k<r) Γ_k² / (Δ_k Δ_(k+1))`. -/
theorem lev_eq_series (hsym : ∀ i j, G i j = G j i) {r : ℕ} (hΔ : ∀ k ≤ r, delta G k ≠ 0) :
    lev G v r = ∑ k ∈ range r, gamma G v k ^ 2 / (delta G k * delta G (k + 1)) := by
  induction r with
  | zero => simp [lev_zero]
  | succ r ih =>
    have hr : delta G r ≠ 0 := hΔ r (Nat.le_succ r)
    have hr1 : delta G (r + 1) ≠ 0 := hΔ (r + 1) le_rfl
    have hs : schur G r ≠ 0 := by
      intro h0
      rw [delta_succ r hsym hr, h0, mul_zero] at hr1
      exact hr1 rfl
    rw [lev_succ v r hsym hr hs, ih (fun k hk => hΔ k (hk.trans (Nat.le_succ r))), sum_range_succ,
      gamma_eq v r hsym hr, delta_succ r hsym hr]
    congr 1
    field_simp

/-- **The corner**: the bordered block `[[G_r, v], [vᵀ, 0]]` has determinant `−Δ_r Σ_k Γ_k² / (Δ_k Δ_(k+1))`, the
undivided pair the fraction-free elimination carries. -/
theorem corner_eq_series (hsym : ∀ i j, G i j = G j i) {r : ℕ} (hΔ : ∀ k ≤ r, delta G k ≠ 0) :
    (fromBlocks (lead G r) (replicateCol (Fin 1) (leadVec v r)) (replicateRow (Fin 1) (leadVec v r))
      (Matrix.of fun _ _ => (0 : ℝ))).det =
      -(delta G r * ∑ k ∈ range r, gamma G v k ^ 2 / (delta G k * delta G (k + 1))) := by
  rw [det_border _ (isUnit_iff_ne_zero.2 (hΔ r le_rfl)), ← lev, lev_eq_series v hsym hΔ, delta]
  ring

/-- With a positive definite Gram on the first `r` cells, every pivot is positive. -/
theorem delta_pos_of_posDef {r : ℕ} (hG : (lead G r).PosDef) {k : ℕ} (hk : k ≤ r) : 0 < delta G k := by
  have h := hG.submatrix (e := Fin.castLE hk) (Fin.castLE_injective hk)
  have heq : (lead G r).submatrix (Fin.castLE hk) (Fin.castLE hk) = lead G k := by
    ext i j
    simp [lead]
  rw [heq] at h
  exact h.det_pos

end Holonics.HNN.ReadingLeverageSeries
