import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# What a contact cannot bridge is its effective tension

The record `research/records/2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT.md`
(§§1, 5, 6, 8 and 10) keeps, over the cells `t` of a section with declared weights `w_t ≥ 0`, the
joint moments of a block's face `f̄_t` and the comparison's covector `t_t` arriving at its output,

`H = Σ w f̄f̄ᵀ`, `B = Σ w t f̄ᵀ`, `T = Σ w t tᵀ`,

and reads what the block's material cannot produce from its present face as the Schur complement
`S = T − B H⁺ Bᵀ`. #410 owes its laws; this file proves them. A family of vectors read at the cells
is a matrix whose columns are the cells (`A : Matrix n ι ℝ`), and `moment A Z w = A diag(w) Zᵀ` is
`Σ_t w_t a_t z_tᵀ` (`moment_eq_sum`).

[proved-standard; formal-checked] What is proved.

1. **The normal law closes through any generalized inverse.** A face Gram is positive semidefinite
   (`posSemidef_moment`) and a direction it does not see is not seen by any weighted cell
   (`diagonal_mul_transpose_mul_eq_zero`), so for every `G` with `H G H = H` (`IsGInv`) every cross
   moment satisfies `Z G H = Z` (`moment_mul_ginv_mul`); in particular `W = B G` solves the normal
   law `W H = B`. Such a `G` exists: `pinv` diagonalizes `H` and inverts its nonzero eigenvalues,
   and it satisfies the four Penrose equations (`pinv_isGInv`, `pinv_mul_mul_pinv`,
   `isHermitian_mul_pinv`, `isHermitian_pinv_mul`), so it is the Moore–Penrose `H⁺`.
2. **The tension is the least residual, and the remainder is orthogonal to every face.** With
   `S = T − B G Bᵀ` (`tension`), the remainder `r_t = t_t − B G f̄_t` has `Σ w r f̄ᵀ = 0`
   (`remainder_orthogonal`); for every material `W` the residual Gram `Σ w (t − W f̄)(t − W f̄)ᵀ` is
   `S + (W − BG) H (W − BG)ᵀ` (`residual_eq_tension_add`), so `S ≤ residual W` in the Loewner order
   (`tension_le_residual`), with equality at the bridge `W = B G` (`residual_bridge`); `S ⪰ 0`
   (`posSemidef_tension`) and `S` does not depend on the choice of `G` (`tension_eq_of_isGInv`).
   This extends `Objects/Membrane.interior_elimination` from an invertible interior block to a
   positive semidefinite face Gram.
3. **The tension is frame-free.** A face that is a linear read of another leaves at least the
   other's tension (`tension_le_of_factor`), so an invertible rebase `f̄ ↦ P f̄` leaves `S`
   unchanged (`tension_rebase`).
4. **Reading a face beside it removes exactly `M Q⁺ Mᵀ`** (`tension_fromRows`): with
   `K = Σ w t cᵀ`, `L = Σ w f̄ cᵀ`, `C = Σ w c cᵀ`, `M = K − B G L` and `Q = C − Lᵀ G L`, the
   tension of the joint face `(f̄, c)` is `S − M G_Q Mᵀ` for every generalized inverse `G_Q` of
   `Q` (the quotient formula, by partial regression). A face `Wᵀ c` read from a pool removes
   `M W (Wᵀ Q W)⁺ Wᵀ Mᵀ` (`tension_fromRows_pool`).
5. **The context ceiling** (`tension_context`, `tension_context_le`). For a finite context `p` of
   each cell, with counts `n_p`, covector sums `τ_p` and face sums `φ_p`, the tension after reading
   every function of the context beside the face is the within-context tension
   `T_w − B_w G_w B_wᵀ`, `X_w = X − Σ_p sums_p sums_pᵀ / n_p` (`within`, `within_eq_sum`), and
   no pool of that context leaves less.
6. **The first-person ratio** (`ratio_turn`, `turn_moves_real_face`,
   `hasFDerivAt_half_sq_log_ratio`). `R = y_T / y_H` is unchanged when the readout row turns by a
   unit, while the real face it reads can move; and the gradient of `½ |log R|²` in `y_H` is
   `−log R / conj(y_H)` (the real Fréchet derivative is the real inner product with it).
7. **Commonality in the moment chart** (`det_ratio`, `det_one_sub_eq_prod_roots`): for invertible
   `S₀`, `det S / det S₀ = det(I − S₀⁻¹(S₀ − S))`, and that determinant is the product of
   `1 − ρ_k²` over the eigenvalues `ρ_k²` of `S₀⁻¹(S₀ − S)` (the roots of its characteristic
   polynomial over `ℂ`, with multiplicity).
8. **The alignment code** (`alignment_code`, `alignment_code_unit`): sending each strand given the
   other by a coupling `c` and its unmatched cells costs
   `L(H|T) + L(T|H) = L(H) + L(T) − Σ_c (ℓ_H + ℓ_T) + 2 L(c)`, and at one unit per cell with
   `L(c) = 0` it is `|H| + |T| − 2|c|`, the lock's `F*` at a longest coupling.

Not proved here: that the best rank-`k` face read from a pool removes the sum of the `k` leading
generalized eigenvalues of `(Mᵀ M, Q)` (a Ky Fan maximum principle, not in Mathlib); the record's
worked numbers stay checked by its receipts.

The computational object is the helical pair interaction: the face and the covector meet at a pair
contact, and the tension is what that contact leaves unresolved. Of the winding guide's six general
objects this touches faces and placement (the face Gram and its rebase) and the tower thread (the
covector a level carries back); the helix, the pair, the cell holonomy and the tube stay attached.

Consumers: the atlas rows `contact.effective-tension`, `contact.tension-founds-face`,
`contact.pool-founding`, `contact.context-table-ceiling`, `contact.closure-channels`,
`ratio.first-person-ratio` and `code.lock-friction-alignment-code`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

open Matrix
open scoped MatrixOrder

namespace Holonics.HNN.EffectiveTension

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n o m k : Type*}

/-! ## 1. Moments and the normal law -/

/-- [definition] The weighted moment `Σ_t w_t a_t z_tᵀ` of two families read at the same cells. -/
def moment (A : Matrix n ι ℝ) (Z : Matrix o ι ℝ) (w : ι → ℝ) : Matrix n o ℝ :=
  A * diagonal w * Zᵀ

theorem moment_eq_sum (A : Matrix n ι ℝ) (Z : Matrix o ι ℝ) (w : ι → ℝ) :
    moment A Z w = ∑ t, w t • vecMulVec (fun i => A i t) (fun j => Z j t) := by
  ext i j
  rw [moment, mul_apply]
  simp_rw [mul_diagonal]
  simp only [transpose_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem moment_transpose (A : Matrix n ι ℝ) (Z : Matrix o ι ℝ) (w : ι → ℝ) :
    (moment A Z w)ᵀ = moment Z A w := by
  simp [moment, transpose_mul, Matrix.mul_assoc]

theorem moment_sub_left (A A' : Matrix n ι ℝ) (Z : Matrix o ι ℝ) (w : ι → ℝ) :
    moment (A - A') Z w = moment A Z w - moment A' Z w := by
  simp [moment, Matrix.sub_mul]

theorem moment_sub_right (A : Matrix n ι ℝ) (Z Z' : Matrix o ι ℝ) (w : ι → ℝ) :
    moment A (Z - Z') w = moment A Z w - moment A Z' w := by
  simp [moment, Matrix.mul_sub, transpose_sub]

theorem moment_mul_left [Fintype n] (E : Matrix m n ℝ) (A : Matrix n ι ℝ) (Z : Matrix o ι ℝ)
    (w : ι → ℝ) :
    moment (E * A) Z w = E * moment A Z w := by
  simp [moment, Matrix.mul_assoc]

theorem moment_mul_right [Fintype o] (A : Matrix n ι ℝ) (E : Matrix m o ℝ) (Z : Matrix o ι ℝ)
    (w : ι → ℝ) :
    moment A (E * Z) w = moment A Z w * Eᵀ := by
  simp [moment, transpose_mul, Matrix.mul_assoc]

/-- [proved-standard; formal-checked] A weighted Gram is positive semidefinite. -/
theorem posSemidef_moment [Fintype n] (A : Matrix n ι ℝ) {w : ι → ℝ} (hw : ∀ t, 0 ≤ w t) :
    (moment A A w).PosSemidef := by
  have hD : (diagonal w).PosSemidef := posSemidef_diagonal_iff.mpr hw
  simpa [moment, conjTranspose_eq_transpose_of_trivial] using hD.mul_mul_conjTranspose_same A

private theorem mul_apply_eq_mulVec {p q : Type*} [Fintype q] (M : Matrix p q ℝ)
    (Z : Matrix q k ℝ) (i : p) (j : k) : (M * Z) i j = (M *ᵥ fun r => Z r j) i := rfl

/-- [proved-standard; formal-checked] A direction the Gram does not see is seen by no weighted cell:
`H v = 0` gives `diag(w) Aᵀ v = 0`. -/
theorem diagonal_mul_transpose_mulVec_eq_zero [Fintype n] (A : Matrix n ι ℝ) {w : ι → ℝ}
    (hw : ∀ t, 0 ≤ w t)
    {v : n → ℝ} (hv : moment A A w *ᵥ v = 0) : diagonal w *ᵥ (Aᵀ *ᵥ v) = 0 := by
  have hD : (diagonal w).PosSemidef := posSemidef_diagonal_iff.mpr hw
  rw [← hD.dotProduct_mulVec_zero_iff, star_trivial]
  have h : (Aᵀ *ᵥ v) ⬝ᵥ diagonal w *ᵥ (Aᵀ *ᵥ v) = v ⬝ᵥ moment A A w *ᵥ v := by
    rw [moment, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec v A, mulVec_transpose]
  rw [h, hv, dotProduct_zero]

theorem diagonal_mul_transpose_mul_eq_zero [Fintype n] (A : Matrix n ι ℝ) {w : ι → ℝ}
    (hw : ∀ t, 0 ≤ w t)
    {Z : Matrix n k ℝ} (hZ : moment A A w * Z = 0) : diagonal w * Aᵀ * Z = 0 := by
  ext i j
  have hcol : moment A A w *ᵥ (fun r => Z r j) = 0 := by
    funext r
    rw [← mul_apply_eq_mulVec, hZ]
    rfl
  rw [mul_apply_eq_mulVec, ← mulVec_mulVec, diagonal_mul_transpose_mulVec_eq_zero A hw hcol]
  rfl

/-- [definition] `G` is a generalized inverse of `H`: `H G H = H`. -/
def IsGInv [Fintype n] (H G : Matrix n n ℝ) : Prop := H * G * H = H

/-- [proved-standard; formal-checked] **The normal law closes.** For a generalized inverse `G` of
the face Gram, every cross moment `Z = Σ w z f̄ᵀ` satisfies `Z G H = Z`. -/
theorem moment_mul_ginv_mul [Fintype n] [DecidableEq n] (Z : Matrix o ι ℝ) (A : Matrix n ι ℝ)
    {w : ι → ℝ} (hw : ∀ t, 0 ≤ w t) {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) :
    moment Z A w * G * moment A A w = moment Z A w := by
  have hker : diagonal w * Aᵀ * (1 - G * moment A A w) = 0 := by
    apply diagonal_mul_transpose_mul_eq_zero A hw
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hG, sub_self]
  have h : moment Z A w - moment Z A w * G * moment A A w =
      Z * (diagonal w * Aᵀ * (1 - G * moment A A w)) := by
    simp only [moment, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  rw [hker, Matrix.mul_zero, sub_eq_zero] at h
  exact h.symm

/-! ## 2. A generalized inverse exists: the Moore–Penrose inverse -/

section Pinv

variable [Fintype n] [DecidableEq n]

open Unitary in
private theorem conj_diag_mul (U : unitary (Matrix n n ℝ)) (d e : n → ℝ) :
    conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal d) *
        conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal e) =
      conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal (d * e)) := by
  rw [← map_mul, diagonal_mul_diagonal]
  rfl

open Unitary in
private theorem isHermitian_conj_diag (U : unitary (Matrix n n ℝ)) (d : n → ℝ) :
    (conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal d)).IsHermitian := by
  rw [IsHermitian, ← star_eq_conjTranspose, ← map_star, star_eq_conjTranspose,
    diagonal_conjTranspose, star_trivial]

omit [Fintype n] [DecidableEq n] in
private theorem mul_inv_mul_self (d : n → ℝ) : d * d⁻¹ * d = d := by
  funext i
  by_cases h : d i = 0 <;> simp [h]

omit [Fintype n] [DecidableEq n] in
private theorem inv_mul_inv_self (d : n → ℝ) : d⁻¹ * d * d⁻¹ = d⁻¹ := by
  funext i
  by_cases h : d i = 0 <;> simp [h]

open Unitary in
private theorem pinv_laws_of_eq {H : Matrix n n ℝ} (U : unitary (Matrix n n ℝ)) (d : n → ℝ)
    (h : H = conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal d)) :
    IsGInv H (conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal d⁻¹)) ∧
      conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal d⁻¹) * H *
          conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal d⁻¹) =
        conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal d⁻¹) ∧
      (H * conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal d⁻¹)).IsHermitian ∧
      (conjStarAlgAut ℝ (Matrix n n ℝ) U (diagonal d⁻¹) * H).IsHermitian := by
  subst h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsGInv, conj_diag_mul, conj_diag_mul, mul_inv_mul_self]
  · rw [conj_diag_mul, conj_diag_mul, inv_mul_inv_self]
  · rw [conj_diag_mul]
    exact isHermitian_conj_diag U _
  · rw [conj_diag_mul]
    exact isHermitian_conj_diag U _

variable {H : Matrix n n ℝ} (hH : H.IsHermitian)

/-- [definition] The Moore–Penrose inverse of a symmetric matrix: diagonalize and invert the nonzero
eigenvalues (`0⁻¹ = 0`). -/
def pinv : Matrix n n ℝ :=
  Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hH.eigenvectorUnitary
    (diagonal (RCLike.ofReal ∘ hH.eigenvalues)⁻¹)

/-- [proved-standard; formal-checked] `H H⁺ H = H`. -/
theorem pinv_isGInv : IsGInv H (pinv hH) :=
  (pinv_laws_of_eq _ _ hH.spectral_theorem).1

/-- [proved-standard; formal-checked] `H⁺ H H⁺ = H⁺`. -/
theorem pinv_mul_mul_pinv : pinv hH * H * pinv hH = pinv hH :=
  (pinv_laws_of_eq _ _ hH.spectral_theorem).2.1

/-- [proved-standard; formal-checked] `H H⁺` is symmetric. -/
theorem isHermitian_mul_pinv : (H * pinv hH).IsHermitian :=
  (pinv_laws_of_eq _ _ hH.spectral_theorem).2.2.1

/-- [proved-standard; formal-checked] `H⁺ H` is symmetric. -/
theorem isHermitian_pinv_mul : (pinv hH * H).IsHermitian :=
  (pinv_laws_of_eq _ _ hH.spectral_theorem).2.2.2

end Pinv

theorem isHermitian_moment (A : Matrix n ι ℝ) (w : ι → ℝ) : (moment A A w).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, moment_transpose]

/-- [proved-standard; formal-checked] Every face Gram has a generalized inverse. -/
theorem exists_isGInv [Fintype n] [DecidableEq n] (A : Matrix n ι ℝ) (w : ι → ℝ) : ∃ G, IsGInv
    (moment A A w) G :=
  ⟨pinv (isHermitian_moment A w), pinv_isGInv _⟩

/-! ## 3. The tension is the least residual -/

/-- [definition] The effective tension `S = T − B G Bᵀ` of the covector `Y` on the face `A`. -/
def tension [Fintype n] (A : Matrix n ι ℝ) (Y : Matrix o ι ℝ) (w : ι → ℝ) (G : Matrix n n ℝ) :
    Matrix o o ℝ :=
  moment Y Y w - moment Y A w * G * moment A Y w

/-- [definition] The residual Gram `Σ w (t − W f̄)(t − W f̄)ᵀ` of a material `W`. -/
def residual [Fintype n] (A : Matrix n ι ℝ) (Y : Matrix o ι ℝ) (w : ι → ℝ) (W : Matrix o n ℝ) :
    Matrix o o ℝ :=
  moment (Y - W * A) (Y - W * A) w

variable {w : ι → ℝ}

/-- [proved-standard; formal-checked] **The remainder is orthogonal to every face:**
`Σ w (t − B G f̄) f̄ᵀ = 0`. -/
theorem remainder_orthogonal [Fintype n] [DecidableEq n] [Fintype o] (A : Matrix n ι ℝ)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) :
    moment (Y - moment Y A w * G * A) A w = 0 := by
  rw [moment_sub_left, moment_mul_left, moment_mul_ginv_mul Y A hw hG, sub_self]

/-- A remainder orthogonal to the face splits every residual. -/
theorem moment_sub_mul_self [Fintype n] (A : Matrix n ι ℝ) (R : Matrix o ι ℝ) (E : Matrix o n ℝ)
    (hR : moment R A w = 0) :
    moment (R - E * A) (R - E * A) w = moment R R w + E * moment A A w * Eᵀ := by
  have hR' : moment A R w = 0 := by rw [← moment_transpose, hR, transpose_zero]
  rw [moment_sub_left, moment_sub_right, moment_sub_right, moment_mul_right, moment_mul_left,
    moment_mul_left, moment_mul_right, hR, hR', Matrix.zero_mul, Matrix.mul_zero, zero_sub,
    sub_zero, Matrix.mul_assoc]
  abel

/-- [proved-standard; formal-checked] The remainder's Gram is the tension. -/
theorem moment_remainder [Fintype n] [DecidableEq n] [Fintype o] (A : Matrix n ι ℝ)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) :
    moment (Y - moment Y A w * G * A) (Y - moment Y A w * G * A) w = tension A Y w G := by
  rw [moment_sub_right (Y - moment Y A w * G * A), moment_mul_right,
    remainder_orthogonal A Y hw hG, Matrix.zero_mul, sub_zero, moment_sub_left, moment_mul_left,
    tension]

/-- [proved-standard; formal-checked] **Completing the square:** the residual of every material `W`
is the tension plus `(W − BG) H (W − BG)ᵀ`. -/
theorem residual_eq_tension_add [Fintype n] [DecidableEq n] [Fintype o] (A : Matrix n ι ℝ)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) (W : Matrix o n ℝ) :
    residual A Y w W = tension A Y w G +
      (W - moment Y A w * G) * moment A A w * (W - moment Y A w * G)ᵀ := by
  have hsplit : Y - W * A = (Y - moment Y A w * G * A) - (W - moment Y A w * G) * A := by
    rw [Matrix.sub_mul]; abel
  rw [residual, hsplit, moment_sub_mul_self A _ _ (remainder_orthogonal A Y hw hG),
    moment_remainder A Y hw hG]

/-- [proved-standard; formal-checked] **The tension is the least residual** in the Loewner order. -/
theorem tension_le_residual [Fintype n] [DecidableEq n] [Fintype o] (A : Matrix n ι ℝ)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) (W : Matrix o n ℝ) :
    tension A Y w G ≤ residual A Y w W := by
  rw [le_iff, residual_eq_tension_add A Y hw hG W, add_sub_cancel_left]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    (posSemidef_moment A hw).mul_mul_conjTranspose_same (W - moment Y A w * G)

/-- [proved-standard; formal-checked] The bridge `W = B G` attains it. -/
theorem residual_bridge [Fintype n] [DecidableEq n] [Fintype o] (A : Matrix n ι ℝ)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) :
    residual A Y w (moment Y A w * G) = tension A Y w G :=
  moment_remainder A Y hw hG

/-- [proved-standard; formal-checked] `S ⪰ 0`. -/
theorem posSemidef_tension [Fintype n] [DecidableEq n] [Fintype o] (A : Matrix n ι ℝ)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) : (tension A Y w G).PosSemidef := by
  rw [← residual_bridge A Y hw hG]
  exact posSemidef_moment _ hw

/-- [proved-standard; formal-checked] `S` does not depend on the generalized inverse. -/
theorem tension_eq_of_isGInv [Fintype n] [DecidableEq n] [Fintype o] (A : Matrix n ι ℝ)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {G G' : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) (hG' : IsGInv (moment A A w) G') :
    tension A Y w G = tension A Y w G' :=
  le_antisymm (residual_bridge A Y hw hG' ▸ tension_le_residual A Y hw hG _)
    (residual_bridge A Y hw hG ▸ tension_le_residual A Y hw hG' _)

/-! ## 4. The tension is frame-free -/

/-- [proved-standard; formal-checked] A face that is a linear read of another leaves at least the
other's tension. -/
theorem tension_le_of_factor [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype o] (A₁ : Matrix n ι ℝ) (A₂ : Matrix m ι ℝ) (Φ : Matrix m n ℝ)
    (hΦ : A₂ = Φ * A₁) (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t) {G₁ : Matrix n n ℝ}
    {G₂ : Matrix m m ℝ} (hG₁ : IsGInv (moment A₁ A₁ w) G₁) (hG₂ : IsGInv (moment A₂ A₂ w) G₂) :
    tension A₁ Y w G₁ ≤ tension A₂ Y w G₂ := by
  calc tension A₁ Y w G₁ ≤ residual A₁ Y w (moment Y A₂ w * G₂ * Φ) :=
        tension_le_residual A₁ Y hw hG₁ _
    _ = residual A₂ Y w (moment Y A₂ w * G₂) := by rw [residual, residual, hΦ, Matrix.mul_assoc]
    _ = tension A₂ Y w G₂ := residual_bridge A₂ Y hw hG₂

/-- [proved-standard; formal-checked] **An invertible rebase of the face leaves `S` unchanged.** -/
theorem tension_rebase [Fintype n] [DecidableEq n] [Fintype o] (A : Matrix n ι ℝ)
    (P : Matrix n n ℝ) (hP : IsUnit P.det)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t) {G G' : Matrix n n ℝ}
    (hG : IsGInv (moment A A w) G) (hG' : IsGInv (moment (P * A) (P * A) w) G') :
    tension (P * A) Y w G' = tension A Y w G :=
  le_antisymm
    (tension_le_of_factor (P * A) A P⁻¹ (by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hP,
      Matrix.one_mul]) Y hw hG' hG)
    (tension_le_of_factor A (P * A) P rfl Y hw hG hG')

/-! ## 5. Reading a face beside it: the quotient formula -/

/-- [definition] `M = K − B G L`: the remainder's cross moment with the new face's residual. -/
def crossRemainder [Fintype n] (A : Matrix n ι ℝ) (Cf : Matrix m ι ℝ) (Y : Matrix o ι ℝ)
    (w : ι → ℝ) (G : Matrix n n ℝ) : Matrix o m ℝ :=
  moment Y Cf w - moment Y A w * G * moment A Cf w

/-- [definition] `Q = C − Lᵀ G L`: the new face's residual Gram. -/
def faceRemainder [Fintype n] (A : Matrix n ι ℝ) (Cf : Matrix m ι ℝ) (w : ι → ℝ)
    (G : Matrix n n ℝ) : Matrix m m ℝ :=
  moment Cf Cf w - moment Cf A w * G * moment A Cf w

/-- [proved-standard; formal-checked] **The quotient formula.** Reading `c` beside the face `f̄`
leaves the tension `S − M G_Q Mᵀ`, for every generalized inverse of the joint Gram and of `Q`. -/
theorem tension_fromRows [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype o] (A : Matrix n ι ℝ) (Cf : Matrix m ι ℝ) (Y : Matrix o ι ℝ)
    (hw : ∀ t, 0 ≤ w t) {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G)
    {GQ : Matrix m m ℝ} (hGQ : IsGInv (faceRemainder A Cf w G) GQ)
    {G' : Matrix (n ⊕ m) (n ⊕ m) ℝ} (hG' : IsGInv (moment (fromRows A Cf) (fromRows A Cf) w) G') :
    tension (fromRows A Cf) Y w G' =
      tension A Y w G - crossRemainder A Cf Y w G * GQ * (crossRemainder A Cf Y w G)ᵀ := by
  -- the covector and the new face, each with its regression on the face removed
  set Yr := Y - moment Y A w * G * A with hYr
  set Cr := Cf - moment Cf A w * G * A with hCr
  have hYA : moment Yr A w = 0 := remainder_orthogonal A Y hw hG
  have hCA : moment Cr A w = 0 := remainder_orthogonal A Cf hw hG
  have hYC : moment Yr Cr w = crossRemainder A Cf Y w G := by
    rw [hCr, moment_sub_right, moment_mul_right, hYA, Matrix.zero_mul, sub_zero, hYr,
      moment_sub_left, moment_mul_left, crossRemainder]
  have hCC : moment Cr Cr w = faceRemainder A Cf w G := by
    rw [moment_sub_right Cr, moment_mul_right, hCA, Matrix.zero_mul, sub_zero, hCr,
      moment_sub_left, moment_mul_left, faceRemainder]
  have hGQ' : IsGInv (moment Cr Cr w) GQ := hCC ▸ hGQ
  have hS : tension Cr Yr w GQ =
      tension A Y w G - crossRemainder A Cf Y w G * GQ * (crossRemainder A Cf Y w G)ᵀ := by
    rw [tension, moment_remainder A Y hw hG, hYC, ← moment_transpose Yr Cr, hYC]
  rw [← hS]
  -- every joint material is a material on the residualized face plus a material on the face
  have hjoint : ∀ W₁ : Matrix o n ℝ, ∀ W₂ : Matrix o m ℝ,
      residual (fromRows A Cf) Y w (fromCols W₁ W₂) = residual Cr Yr w W₂ +
        (W₁ - moment Y A w * G + W₂ * (moment Cf A w * G)) * moment A A w *
          (W₁ - moment Y A w * G + W₂ * (moment Cf A w * G))ᵀ := by
    intro W₁ W₂
    have hsplit : Y - fromCols W₁ W₂ * fromRows A Cf =
        (Yr - W₂ * Cr) - (W₁ - moment Y A w * G + W₂ * (moment Cf A w * G)) * A := by
      rw [fromCols_mul_fromRows, hYr, hCr]
      simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    have hRA : moment (Yr - W₂ * Cr) A w = 0 := by
      rw [moment_sub_left, moment_mul_left, hYA, hCA, Matrix.mul_zero, sub_zero]
    rw [residual, hsplit, moment_sub_mul_self A _ _ hRA, residual]
  apply le_antisymm
  · -- the joint tension is at most the residualized optimum
    calc tension (fromRows A Cf) Y w G'
        ≤ residual (fromRows A Cf) Y w
            (fromCols (moment Y A w * G - moment Yr Cr w * GQ * (moment Cf A w * G))
              (moment Yr Cr w * GQ)) := tension_le_residual _ Y hw hG' _
      _ = residual Cr Yr w (moment Yr Cr w * GQ) := by
          rw [hjoint, show moment Y A w * G - moment Yr Cr w * GQ * (moment Cf A w * G) -
              moment Y A w * G + moment Yr Cr w * GQ * (moment Cf A w * G) = 0 by abel,
            Matrix.zero_mul, Matrix.zero_mul, add_zero]
      _ = tension Cr Yr w GQ := residual_bridge Cr Yr hw hGQ'
  · -- and at least it: every joint residual dominates a residualized residual
    rw [← residual_bridge (fromRows A Cf) Y hw hG',
      ← fromCols_toCols (moment Y (fromRows A Cf) w * G'),
      hjoint]
    refine le_trans
      (tension_le_residual Cr Yr hw hGQ' (moment Y (fromRows A Cf) w * G').toCols₂) ?_
    rw [le_iff, add_sub_cancel_left]
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (posSemidef_moment A hw).mul_mul_conjTranspose_same
        ((moment Y (fromRows A Cf) w * G').toCols₁ - moment Y A w * G +
          (moment Y (fromRows A Cf) w * G').toCols₂ * (moment Cf A w * G))

/-- [proved-standard; formal-checked] **A face read from a pool.** The face `Wᵀ c` removes
`M W (Wᵀ Q W)⁺ Wᵀ Mᵀ`. -/
theorem tension_fromRows_pool [Fintype n] [DecidableEq n] [Fintype m] [Fintype k]
    [DecidableEq k] [Fintype o] (A : Matrix n ι ℝ) (Cp : Matrix m ι ℝ) (W : Matrix m k ℝ)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t) {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G)
    {GQ : Matrix k k ℝ} (hGQ : IsGInv (Wᵀ * faceRemainder A Cp w G * W) GQ)
    {G' : Matrix (n ⊕ k) (n ⊕ k) ℝ}
    (hG' : IsGInv (moment (fromRows A (Wᵀ * Cp)) (fromRows A (Wᵀ * Cp)) w) G') :
    tension (fromRows A (Wᵀ * Cp)) Y w G' =
      tension A Y w G - crossRemainder A Cp Y w G * W * GQ * (crossRemainder A Cp Y w G * W)ᵀ := by
  have hQ : faceRemainder A (Wᵀ * Cp) w G = Wᵀ * faceRemainder A Cp w G * W := by
    simp only [faceRemainder, moment_mul_left, moment_mul_right, transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hM : crossRemainder A (Wᵀ * Cp) Y w G = crossRemainder A Cp Y w G * W := by
    simp only [crossRemainder, moment_mul_right, transpose_transpose, Matrix.sub_mul,
      Matrix.mul_assoc]
  rw [tension_fromRows A (Wᵀ * Cp) Y hw hG (hQ ▸ hGQ) hG', hM]

/-! ## 6. The context ceiling -/

section Context

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (ctx : ι → κ)

/-- [definition] The indicator faces of a finite context: every function of the context is a linear
read of them. -/
def indicator : Matrix κ ι ℝ := fun p t => if ctx t = p then 1 else 0

/-- [definition] The weighted count `n_p` of each context. -/
def count (w : ι → ℝ) (p : κ) : ℝ := ∑ t, if ctx t = p then w t else 0

omit [Fintype κ] in
theorem moment_indicator (w : ι → ℝ) : moment (indicator ctx) (indicator ctx) w =
    diagonal (count ctx w) := by
  ext p q
  rw [moment, mul_apply]
  simp_rw [mul_diagonal]
  simp only [transpose_apply, indicator, diagonal_apply, count]
  split_ifs with h
  · subst h
    exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
  · exact Finset.sum_eq_zero fun t _ => by split_ifs with h1 h2 <;> simp_all

omit [Fintype κ] in
theorem moment_indicator_right (A : Matrix n ι ℝ) (w : ι → ℝ) :
    moment A (indicator ctx) w = of fun i p => ∑ t, if ctx t = p then w t * A i t else 0 := by
  ext i p
  rw [moment, mul_apply]
  simp_rw [mul_diagonal]
  simp only [transpose_apply, indicator, of_apply]
  exact Finset.sum_congr rfl fun t _ => by split_ifs <;> ring

omit [Fintype κ] in
theorem moment_indicator_left (Z : Matrix o ι ℝ) (w : ι → ℝ) :
    moment (indicator ctx) Z w = of fun p j => ∑ t, if ctx t = p then w t * Z j t else 0 := by
  rw [← moment_transpose, moment_indicator_right]
  rfl

theorem isGInv_indicator (w : ι → ℝ) :
    IsGInv (moment (indicator ctx) (indicator ctx) w) (diagonal (count ctx w)⁻¹) := by
  rw [IsGInv, moment_indicator, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases h : count ctx w p = 0 <;> simp [h]

/-- [definition] The within-context moment `X_w = X − Σ_p sums_p sums_pᵀ / n_p`. -/
def within (A : Matrix n ι ℝ) (Z : Matrix o ι ℝ) (w : ι → ℝ) : Matrix n o ℝ :=
  moment A Z w - moment A (indicator ctx) w * diagonal (count ctx w)⁻¹ * moment (indicator ctx) Z w

/-- [proved-standard; formal-checked] The within-context moment read from the context table:
`X_w = X − Σ_p (sums_p)(sums_p)ᵀ / n_p`, with `sums_p` the weighted sums over the context. -/
theorem within_eq_sum (A : Matrix n ι ℝ) (Z : Matrix o ι ℝ) (w : ι → ℝ) :
    within ctx A Z w = moment A Z w - ∑ p, (count ctx w p)⁻¹ •
      vecMulVec (fun i => ∑ t, if ctx t = p then w t * A i t else 0)
        (fun j => ∑ t, if ctx t = p then w t * Z j t else 0) := by
  rw [within, moment_indicator_right, moment_indicator_left]
  congr 1
  ext i j
  rw [mul_apply]
  simp_rw [mul_diagonal]
  simp only [of_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    Pi.inv_apply]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- [proved-standard; formal-checked] **The context ceiling.** The tension after reading every
function of the context beside the face is the within-context tension `T_w − B_w G_w B_wᵀ`. -/
theorem tension_context [Fintype n] [DecidableEq n] [Fintype o] (A : Matrix n ι ℝ)
    (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {Gw : Matrix n n ℝ} (hGw : IsGInv (within ctx A A w) Gw)
    {G' : Matrix (κ ⊕ n) (κ ⊕ n) ℝ}
    (hG' : IsGInv (moment (fromRows (indicator ctx) A) (fromRows (indicator ctx) A) w) G') :
    tension (fromRows (indicator ctx) A) Y w G' =
      within ctx Y Y w - within ctx Y A w * Gw * within ctx A Y w := by
  have hW : within ctx A Y w = (within ctx Y A w)ᵀ := by
    simp only [within, transpose_sub, transpose_mul, moment_transpose, diagonal_transpose,
      Matrix.mul_assoc]
  rw [tension_fromRows (indicator ctx) A Y hw (isGInv_indicator ctx w) hGw hG', hW]
  rfl

/-- [proved-standard; formal-checked] **No pool of the context leaves less**: for every pool `Φ` of
functions of the context, the face `(f̄, Φ · indicator)` leaves at least the ceiling. -/
theorem tension_context_le [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype o] (A : Matrix n ι ℝ) (Φ : Matrix m κ ℝ) (Y : Matrix o ι ℝ)
    (hw : ∀ t, 0 ≤ w t) {G' : Matrix (κ ⊕ n) (κ ⊕ n) ℝ}
    (hG' : IsGInv (moment (fromRows (indicator ctx) A) (fromRows (indicator ctx) A) w) G')
    {G'' : Matrix (n ⊕ m) (n ⊕ m) ℝ}
    (hG'' : IsGInv (moment (fromRows A (Φ * indicator ctx)) (fromRows A (Φ * indicator ctx)) w)
      G'') :
    tension (fromRows (indicator ctx) A) Y w G' ≤
      tension (fromRows A (Φ * indicator ctx)) Y w G'' :=
  tension_le_of_factor _ _ (fromBlocks 0 1 Φ 0) (by
    rw [fromBlocks_mul_fromRows]; simp) Y hw hG' hG''

end Context

/-! ## 7. The first-person ratio -/

/-- [proved-standard; formal-checked] `R = y_T / y_H` is unchanged by a unit turn of the
readout row. -/
theorem ratio_turn [Fintype n] (C hT hH : n → ℂ) (α : ℝ) :
    ((Complex.exp (α * Complex.I) • C) ⬝ᵥ hT) / ((Complex.exp (α * Complex.I) • C) ⬝ᵥ hH) =
      (C ⬝ᵥ hT) / (C ⬝ᵥ hH) := by
  rw [smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/-- [proved-standard; formal-checked] A unit turn can move the real face the row reads. -/
theorem turn_moves_real_face {y : ℂ} (hy : y ≠ 0) :
    ∃ α : ℝ, (Complex.exp (α * Complex.I) * y).re ≠ y.re := by
  by_cases h : y.re = 0
  · refine ⟨Real.pi / 2, ?_⟩
    have him : y.im ≠ 0 := fun him => hy (Complex.ext h him)
    rw [show ((Real.pi / 2 : ℝ) : ℂ) * Complex.I = (Real.pi / 2 : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two, h, him]
  · refine ⟨Real.pi, ?_⟩
    rw [Complex.exp_pi_mul_I]
    simp only [neg_mul, one_mul, Complex.neg_re]
    intro h'
    exact h (by linarith)

open scoped RealInnerProductSpace ComplexConjugate in
/-- [proved-standard; formal-checked] **The gradient of `½ |log R|²` in `y_H` is
`−log R / conj(y_H)`:** its real Fréchet derivative at `y_H` is the real inner product with it. -/
theorem hasFDerivAt_half_sq_log_ratio {yT z : ℂ} (hz : z ≠ 0)
    (hR : yT / z ∈ Complex.slitPlane) :
    HasFDerivAt (fun ζ : ℂ => (1 / 2 : ℝ) * ‖Complex.log (yT / ζ)‖ ^ 2)
      (innerSL ℝ (-Complex.log (yT / z) / conj z)) z := by
  have hyT : yT ≠ 0 := by
    intro h
    exact Complex.slitPlane_ne_zero hR (by rw [h, zero_div])
  have h1 : HasDerivAt (fun ζ : ℂ => yT / ζ) (yT * -(z ^ 2)⁻¹) z := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hz).const_mul yT
  have h2 := h1.clog hR
  have hd : yT * -(z ^ 2)⁻¹ / (yT / z) = -z⁻¹ := by field_simp
  rw [hd] at h2
  have h3 := (hasStrictFDerivAt_norm_sq (Complex.log (yT / z))).hasFDerivAt.comp z
    (h2.hasFDerivAt.restrictScalars ℝ)
  refine (h3.const_mul (1 / 2 : ℝ)).congr_fderiv (ContinuousLinearMap.ext fun δ => ?_)
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, smul_eq_mul]
  rw [Complex.inner, Complex.inner, map_div₀, map_neg, Complex.conj_conj]
  rw [show δ * (-(starRingEnd ℂ) (Complex.log (yT / z)) / z) =
    δ * -z⁻¹ * (starRingEnd ℂ) (Complex.log (yT / z)) by ring]
  simp
  ring

/-! ## 8. Commonality in the moment chart -/

/-- [proved-standard; formal-checked] `det S / det S₀ = det(I − S₀⁻¹(S₀ − S))` for invertible `S₀`.
-/
theorem det_ratio [Fintype o] [DecidableEq o] (S S₀ : Matrix o o ℝ) (h : IsUnit S₀.det) :
    S.det / S₀.det = (1 - S₀⁻¹ * (S₀ - S)).det := by
  have hS : S = S₀ * (1 - S₀⁻¹ * (S₀ - S)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ h, Matrix.one_mul,
      sub_sub_cancel]
  rw [div_eq_iff h.ne_zero, mul_comm]
  conv_lhs => rw [hS]
  rw [det_mul]

/-- [proved-standard; formal-checked] `det(I − N)` is the product of `1 − ρ²` over the eigenvalues
`ρ²` of `N` (the roots of its characteristic polynomial over `ℂ`, with multiplicity). -/
theorem det_one_sub_eq_prod_roots [Fintype o] [DecidableEq o] (N : Matrix o o ℝ) :
    ((1 - N).det : ℂ) =
      ((N.map (algebraMap ℝ ℂ)).charpoly.roots.map (fun μ => 1 - μ)).prod := by
  have hsplit := IsAlgClosed.splits (N.map (algebraMap ℝ ℂ)).charpoly
  rw [← hsplit.eval_eq_prod_roots_of_monic (charpoly_monic _) 1, eval_charpoly]
  have h : scalar o (1 : ℂ) - N.map (algebraMap ℝ ℂ) = (algebraMap ℝ ℂ).mapMatrix (1 - N) := by
    rw [map_sub, map_one, map_one]
    rfl
  rw [h, ← RingHom.map_det]
  rfl

/-! ## 9. The alignment code -/

section Alignment

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- [definition] A strand's code under a per-cell code `ℓ`. -/
def strandCode (ℓ : α → ℝ) : ℝ := ∑ i, ℓ i

/-- [definition] The code of a strand sent given the other by a coupling whose cells on this strand
are `c₁`: its unmatched cells plus the coupling's own description `Lc`. -/
def givenCode (ℓ : α → ℝ) (c₁ : Finset α) (Lc : ℝ) : ℝ := ∑ i ∈ Finset.univ \ c₁, ℓ i + Lc

theorem givenCode_eq (ℓ : α → ℝ) (c₁ : Finset α) (Lc : ℝ) :
    givenCode ℓ c₁ Lc = strandCode ℓ - ∑ i ∈ c₁, ℓ i + Lc := by
  rw [givenCode, strandCode, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]

/-- [proved-standard; formal-checked] **The alignment code.** For a coupling `c` (a set of pairs,
injective on each strand), `L(H|T) + L(T|H) = L(H) + L(T) − Σ_c (ℓ_H + ℓ_T) + 2 L(c)`. -/
theorem alignment_code (ℓH : α → ℝ) (ℓT : β → ℝ) (c : Finset (α × β))
    (h₁ : Set.InjOn Prod.fst (c : Set (α × β))) (h₂ : Set.InjOn Prod.snd (c : Set (α × β)))
    (Lc : ℝ) :
    givenCode ℓH (c.image Prod.fst) Lc + givenCode ℓT (c.image Prod.snd) Lc =
      strandCode ℓH + strandCode ℓT - ∑ x ∈ c, (ℓH x.1 + ℓT x.2) + 2 * Lc := by
  rw [givenCode_eq, givenCode_eq, Finset.sum_image (fun x hx y hy => h₁ hx hy),
    Finset.sum_image (fun x hx y hy => h₂ hx hy), Finset.sum_add_distrib]
  ring

/-- [proved-standard; formal-checked] At one unit per cell with `L(c) = 0` it is
`|H| + |T| − 2|c|`, the lock's `F* = |H| + |T| − 2λ` at a longest coupling. -/
theorem alignment_code_unit (c : Finset (α × β))
    (h₁ : Set.InjOn Prod.fst (c : Set (α × β))) (h₂ : Set.InjOn Prod.snd (c : Set (α × β))) :
    givenCode (fun _ => (1 : ℝ)) (c.image Prod.fst) 0 +
        givenCode (fun _ => (1 : ℝ)) (c.image Prod.snd) 0 =
      Fintype.card α + Fintype.card β - 2 * c.card := by
  rw [alignment_code _ _ c h₁ h₂]
  simp [strandCode]
  ring

end Alignment

end Holonics.HNN.EffectiveTension

end
