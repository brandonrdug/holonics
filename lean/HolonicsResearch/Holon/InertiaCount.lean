import Mathlib
import HolonicsResearch.Holon.Inertia
import HolonicsResearch.Landmarks.RegularGraphNormForm
import HolonicsResearch.Zeta.FiniteWeilCriterion

/-!
# The negative squares count the modes that left the half

The record of November 18
(`research/records/2026-11-18_THE_HALF_IS_THE_POSITIVITY_OF_THE_REVERSALS_OWN_FORM_…`)
reads two forms built from a move and its reversal: the norm form of a regular complex (§4) and
Weil's form of a finite family with a reversal (§6). Lean held their positivity criteria
(`Landmarks/RegularGraphNormForm:normForm_pos_iff`, `Zeta/FiniteWeilCriterion:weil_nonneg_iff`). The
record's counts (§4.4, §6.2) were derived by hand: the negative squares of the norm form number the
modes with `λ² > 4q`, and the negative squares of Weil's form number the exchanged pairs. This file
states and proves both counts with the tree's own indices, `Holon/Inertia`'s `posIndex` and
`negIndex` (the largest dimension of a subspace on which the form is positive, or negative).

[from training] Sylvester's law of inertia (1852): a real symmetric form has a positive index and a
negative index that no invertible change of basis moves. The tree proves the invariance
(`Inertia.posIndex_congr`, `Inertia.negIndex_congr`); what was missing is the value on a diagonal.

[proved-derived; formal-checked] What is proved.

1. **Two bounds by a linear map** (`posIndex_le_card_of_ker_nonpos`, `card_le_posIndex_of_pos`),
   over any linearly ordered field. If a linear map to `t` coordinates has the form nonpositive on
   its kernel, then `n₊ ≤ |t|`; if a linear map from `t` coordinates has the form positive on every
   nonzero image, then `|t| ≤ n₊`. Every count below is these two bounds with a chosen pair of maps.
2. **Sylvester for a diagonal** (`posIndex_diagonal`, `negIndex_diagonal`), over any linearly
   ordered field: `n₊(diag d) = #{i | 0 < d i}` and `n₋(diag d) = #{i | d i < 0}`.
3. **Congruence to a diagonal gives the index** (`posIndex_of_congr_diagonal`,
   `negIndex_of_congr_diagonal`): if `Pᵀ A P = diag d` with `P` invertible, the indices of `A` are
   those counts.
4. **The regular complex's norm form** (`normMatrix`, `quad_normMatrix`,
   `quad_normMatrix_eq_normForm`, `orthogonal_diag`, `bothHalves_congr`, `shear_congr`,
   `normMatrix_congr_diagonal`, `negIndex_normMatrix`, `posIndex_normMatrix`,
   `index_add_null_normMatrix`). For a real symmetric `A` on `V` with eigenvalues `λ_i` and a real
   `q`, the matrix `K = [[q, A/2], [A/2, 1]]` on `V ⊕ V` has quadratic form
   `q‖a‖² + ⟨a, A b⟩ + ‖b‖²`, the tree's `normForm`. It is congruent to
   `diag(q − λ_i²/4) ⊕ 1`, by the orthogonal eigenvector chart on both halves and then the shear
   that completes the square `q a² + λ a b + b² = (b + λ a/2)² + (q − λ²/4) a²`. So
   `n₋(K) = #{i | 4q < λ_i²}`, `n₊(K) = |V| + #{i | λ_i² < 4q}`, and the modes with `λ_i² = 4q` are
   in neither: `n₊ + n₋ + #{i | λ_i² = 4q} = 2|V|`.
5. **The corollaries the record states** (`negIndex_normMatrix_eq_zero_iff`,
   `one_le_negIndex_normMatrix_of_trivial`): `K` has no negative square if and only if every mode
   has `λ_i² ≤ 4q`, and a mode at `λ = q + 1` with `q ≠ 1` (the trivial mode of a complex with
   `q + 1` contacts a cell) is one negative square, since `(q + 1)² − 4q = (q − 1)²`.
6. **Weil's form on real tests** (`weilMatrix`, `weilMatrix_isSymm`, `quad_weilMatrix`,
   `weil_ofReal`, `negIndex_weilMatrix_of_reps`, `posIndex_weilMatrix_of_reps`,
   `two_mul_negIndex_weilMatrix`, `two_mul_posIndex_weilMatrix`, `negIndex_weilMatrix_eq_zero_iff`).
   For a finite family with a reversal `σ` (an involution) and positive weights `m` that `σ` keeps,
   the matrix `H i j = m i` at `j = σ i` and `0` elsewhere is symmetric, with quadratic form
   `Σ m_i f_i f_(σ i)`, the real reading of `FiniteWeilCriterion.weil`. With one representative
   chosen from each exchanged pair, `n₋(H)` is the number of representatives and `n₊(H)` is the
   number of fixed places plus the number of representatives. Without a choice:
   `2·n₋(H) = #{i | σ i ≠ i}` and `2·n₊(H) = 2·#{i | σ i = i} + #{i | σ i ≠ i}`. So `n₋(H) = 0`
   if and only if `σ` fixes every place: the criterion, now as the vanishing of a count.

The computational object is the helical pair interaction read through a form that its move and its
reversal build. Of the winding guide's six general objects this touches the pair (a place and its
reflection, a cell `[[q, λ/2], [λ/2, 1]]`) and faces and placement (a congruence is a placement of
the form); the helix, the cell holonomy, the tube and the tower thread stay attached.

What this does not state. Nothing here says which complexes are tempered or which families are
fixed by their reversal: the counts are of whatever spectrum or reversal is given. The norm form's
count is over all of `V ⊕ V`, the trivial mode included, and is not restricted to the lifted
nontrivial part of the dart space (the record's ruler reads that restriction). Weil's form is
counted on real tests of a finite family; the Hermitian form on complex tests has the same counts
(a complex test is two real ones) and that step is not written here. No statement is made about an
unending family, where a count of negative squares needs its own convergence.

Consumers: the record's §4.4 and §6.2, and the atlas rows that cite them.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Holon.InertiaCount

open Matrix Module Holonics.Holon.Inertia

/-! ## 1. Two bounds by a linear map -/

section Bounds

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n t : Type*} [Fintype n] [Fintype t]

/-- [proved-derived; formal-checked] **An upper bound.** If the form of `A` is nonpositive on the
kernel of a linear map to `t` coordinates, then `n₊(A) ≤ |t|`: the map is injective on every
subspace on which `A` is positive. -/
theorem posIndex_le_card_of_ker_nonpos (A : Matrix n n K) (g : (n → K) →ₗ[K] (t → K))
    (h : ∀ w, g w = 0 → w ⬝ᵥ (A *ᵥ w) ≤ 0) : posIndex A ≤ Fintype.card t := by
  refine posIndex_le fun W hW => ?_
  have hinj : Function.Injective (g.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hpos := hW w w.2 fun h0 => hne (Submodule.coe_eq_zero.mp h0)
    exact absurd (h w hw) (not_le.mpr hpos)
  calc finrank K W ≤ finrank K (t → K) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card t := Module.finrank_fintype_fun_eq_card K

/-- [proved-derived; formal-checked] **A lower bound.** If a linear map from `t` coordinates has
the form of `A` positive on every nonzero image, then `|t| ≤ n₊(A)`: the map is injective and its
range is a subspace on which `A` is positive. -/
theorem card_le_posIndex_of_pos (A : Matrix n n K) (e : (t → K) →ₗ[K] (n → K))
    (h : ∀ x, x ≠ 0 → 0 < e x ⬝ᵥ (A *ᵥ e x)) : Fintype.card t ≤ posIndex A := by
  have hinj : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have hpos := h x hne
    rw [hx, mulVec_zero, dotProduct_zero] at hpos
    exact lt_irrefl _ hpos
  have hpos : PosOn A (LinearMap.range e) := by
    intro y hy hne
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact h x fun hx => hne (by rw [hx, map_zero])
  calc Fintype.card t = finrank K (t → K) := (Module.finrank_fintype_fun_eq_card K).symm
    _ = finrank K (LinearMap.range e) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ posIndex A := le_posIndex hpos

end Bounds

/-! ### Extension by zero -/

section Extend

variable {K : Type*} [Field K] {n : Type*}

/-- [definition] Extension by zero from the coordinates where `p` holds. -/
def extendZero (p : n → Prop) [DecidablePred p] : ({i // p i} → K) →ₗ[K] (n → K) where
  toFun f i := if h : p i then f ⟨i, h⟩ else 0
  map_add' f g := by
    funext i
    by_cases h : p i <;> simp [h]
  map_smul' c f := by
    funext i
    by_cases h : p i <;> simp [h]

theorem extendZero_of_pos (p : n → Prop) [DecidablePred p] (f : {i // p i} → K) {i : n}
    (h : p i) : extendZero p f i = f ⟨i, h⟩ := by
  simp [extendZero, h]

theorem extendZero_of_neg (p : n → Prop) [DecidablePred p] (f : {i // p i} → K) {i : n}
    (h : ¬p i) : extendZero p f i = 0 := by
  simp [extendZero, h]

end Extend

/-! ## 2. Sylvester for a diagonal -/

section Diagonal

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] The quadratic form of a diagonal. -/
theorem quad_diagonal (d w : n → K) :
    w ⬝ᵥ (diagonal d *ᵥ w) = ∑ i, d i * (w i * w i) := by
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- [proved-derived; formal-checked] **Sylvester for a diagonal, positive index**: the positive
index of `diag d` is the count of its positive entries. -/
theorem posIndex_diagonal (d : n → K) :
    posIndex (diagonal d) = (Finset.univ.filter fun i => 0 < d i).card := by
  rw [← Fintype.card_subtype]
  refine le_antisymm ?_ ?_
  · refine posIndex_le_card_of_ker_nonpos _
      (LinearMap.funLeft K K (Subtype.val : {i // 0 < d i} → n)) ?_
    intro w hw
    rw [quad_diagonal]
    refine Finset.sum_nonpos fun i _ => ?_
    by_cases hi : 0 < d i
    · have hwi : w i = 0 := by
        have := congrFun hw ⟨i, hi⟩
        simpa [LinearMap.funLeft_apply] using this
      simp [hwi]
    · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hi) (mul_self_nonneg _)
  · refine card_le_posIndex_of_pos _ (extendZero (fun i => 0 < d i)) ?_
    intro x hx
    rw [quad_diagonal]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun i _ => ?_) ⟨j.1, Finset.mem_univ _, ?_⟩
    · by_cases hi : 0 < d i
      · exact mul_nonneg hi.le (mul_self_nonneg _)
      · rw [extendZero_of_neg (fun i => 0 < d i) x hi]
        simp
    · rw [extendZero_of_pos (fun i => 0 < d i) x j.2]
      exact mul_pos j.2 (mul_self_pos.mpr hj)

/-- [proved-derived; formal-checked] **Sylvester for a diagonal, negative index**: the negative
index of `diag d` is the count of its negative entries. -/
theorem negIndex_diagonal (d : n → K) :
    negIndex (diagonal d) = (Finset.univ.filter fun i => d i < 0).card := by
  have h : -(diagonal d) = diagonal fun i => -d i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [negIndex, h, posIndex_diagonal]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  exact neg_pos

/-- [proved-derived; formal-checked] **Congruence to a diagonal gives the positive index.** -/
theorem posIndex_of_congr_diagonal (A : Matrix n n K) {P : Matrix n n K} (hP : IsUnit P.det)
    {d : n → K} (h : Pᵀ * A * P = diagonal d) :
    posIndex A = (Finset.univ.filter fun i => 0 < d i).card := by
  rw [← posIndex_congr A hP, h, posIndex_diagonal]

/-- [proved-derived; formal-checked] **Congruence to a diagonal gives the negative index.** -/
theorem negIndex_of_congr_diagonal (A : Matrix n n K) {P : Matrix n n K} (hP : IsUnit P.det)
    {d : n → K} (h : Pᵀ * A * P = diagonal d) :
    negIndex A = (Finset.univ.filter fun i => d i < 0).card := by
  rw [← negIndex_congr A hP, h, negIndex_diagonal]

end Diagonal

/-! ## 3. The regular complex's norm form -/

section NormForm

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- [definition] The norm form of a regular complex as a matrix on `V ⊕ V`:
`[[q, A/2], [A/2, 1]]`. -/
def normMatrix (A : Matrix V V ℝ) (q : ℝ) : Matrix (V ⊕ V) (V ⊕ V) ℝ :=
  fromBlocks (q • 1) ((1 / 2 : ℝ) • A) ((1 / 2 : ℝ) • A) 1

omit [Fintype V] [DecidableEq V] in
/-- A real Hermitian matrix is symmetric. -/
theorem isSymm_of_isHermitian {A : Matrix V V ℝ} (hA : A.IsHermitian) : A.IsSymm := by
  have h : Aᴴ = A := hA
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- [proved-derived; formal-checked] The quadratic form of `normMatrix`:
`q‖a‖² + ⟨a, A b⟩ + ‖b‖²`. -/
theorem quad_normMatrix {A : Matrix V V ℝ} (hA : A.IsHermitian) (q : ℝ) (a b : V → ℝ) :
    Sum.elim a b ⬝ᵥ (normMatrix A q *ᵥ Sum.elim a b)
      = q * (a ⬝ᵥ a) + a ⬝ᵥ (A *ᵥ b) + b ⬝ᵥ b := by
  have hsymm : b ⬝ᵥ (A *ᵥ a) = a ⬝ᵥ (A *ᵥ b) := by
    rw [Holonics.Landmarks.RegularGraphNormForm.dot_mulVec_symm (isSymm_of_isHermitian hA) b a,
      dotProduct_comm]
  rw [normMatrix, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_add, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul, hsymm]
  ring

/-- [proved-derived; formal-checked] The matrix reads the tree's `normForm`. -/
theorem quad_normMatrix_eq_normForm {A : Matrix V V ℝ} (hA : A.IsHermitian) (q : ℝ)
    (x : (V → ℝ) × (V → ℝ)) :
    Sum.elim x.1 x.2 ⬝ᵥ (normMatrix A q *ᵥ Sum.elim x.1 x.2)
      = Holonics.Landmarks.RegularGraphNormForm.normForm A q x := by
  rw [quad_normMatrix hA]
  rfl

/-- [proved-standard; formal-checked] The spectral theorem for a real symmetric matrix as a
congruence: an orthogonal `U` with `Uᵀ A U = diag λ`. -/
theorem orthogonal_diag {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix V V ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ Uᵀ * A * U = diagonal hA.eigenvalues := by
  refine ⟨(hA.eigenvectorUnitary : Matrix V V ℝ), ?_, ?_, ?_⟩
  · have h := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  · have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  · have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
    rw [h]
    congr 1

/-- [definition] One chart `U` applied to both halves of `V ⊕ V`. -/
def bothHalves (U : Matrix V V ℝ) : Matrix (V ⊕ V) (V ⊕ V) ℝ := fromBlocks U 0 0 U

/-- [definition] The shear `(a, b) ↦ (a, b − D a / 2)` that completes the square. -/
def shear (D : Matrix V V ℝ) : Matrix (V ⊕ V) (V ⊕ V) ℝ :=
  fromBlocks 1 0 (-(1 / 2 : ℝ) • D) 1

theorem isUnit_det_bothHalves {U : Matrix V V ℝ} (hU : U * Uᵀ = 1) :
    IsUnit (bothHalves U).det := by
  refine isUnit_det_of_right_inverse (B := bothHalves Uᵀ) ?_
  simp only [bothHalves, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, hU, fromBlocks_one]

theorem isUnit_det_shear (D : Matrix V V ℝ) : IsUnit (shear D).det := by
  refine isUnit_det_of_right_inverse (B := shear (-D)) ?_
  simp [shear, fromBlocks_multiply]

/-- [proved-derived; formal-checked] **A chart on both halves moves the norm form of `A` to the
norm form of `Uᵀ A U`**, for `UᵀU = 1`. -/
theorem bothHalves_congr (A : Matrix V V ℝ) (q : ℝ) {U : Matrix V V ℝ} (hU : Uᵀ * U = 1) :
    (bothHalves U)ᵀ * normMatrix A q * bothHalves U = normMatrix (Uᵀ * A * U) q := by
  have e11 : Uᵀ * (q • (1 : Matrix V V ℝ)) * U = q • 1 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
  have e12 : Uᵀ * ((1 / 2 : ℝ) • A) * U = (1 / 2 : ℝ) • (Uᵀ * A * U) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have e22 : Uᵀ * (1 : Matrix V V ℝ) * U = 1 := by rw [Matrix.mul_one, hU]
  simp only [bothHalves, normMatrix, fromBlocks_transpose, transpose_zero, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e11, e12, e22]

/-- [proved-derived; formal-checked] **Completing the square.** On a diagonal `A = diag d` the
shear takes the norm form to `diag(q − d²/4) ⊕ 1`:
`q a² + d a b + b² = (b + d a / 2)² + (q − d²/4) a²` in every cell. -/
theorem shear_congr (d : V → ℝ) (q : ℝ) :
    (shear (diagonal d))ᵀ * normMatrix (diagonal d) q * shear (diagonal d)
      = diagonal (Sum.elim (fun i => q - d i ^ 2 / 4) (fun _ => (1 : ℝ))) := by
  rw [← fromBlocks_diagonal]
  simp only [shear, normMatrix, fromBlocks_transpose, transpose_zero, transpose_one,
    transpose_smul, diagonal_transpose, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, Matrix.mul_one, Matrix.one_mul]
  congr 1
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [diagonal_mul_diagonal]
      ring
    · simp [diagonal_mul_diagonal, hij]
  · ext i j
    simp
  · ext i j
    simp

/-- [proved-derived; formal-checked] **The norm form is congruent to `diag(q − λ²/4) ⊕ 1`.** First
the orthogonal eigenvector chart on both halves, then the shear that completes the square. -/
theorem normMatrix_congr_diagonal {A : Matrix V V ℝ} (hA : A.IsHermitian) (q : ℝ) :
    ∃ P : Matrix (V ⊕ V) (V ⊕ V) ℝ, IsUnit P.det ∧
      Pᵀ * normMatrix A q * P
        = diagonal (Sum.elim (fun i => q - hA.eigenvalues i ^ 2 / 4) (fun _ => (1 : ℝ))) := by
  obtain ⟨U, hU1, hU2, hUA⟩ := orthogonal_diag hA
  refine ⟨bothHalves U * shear (diagonal hA.eigenvalues), ?_, ?_⟩
  · rw [det_mul]
    exact (isUnit_det_bothHalves hU2).mul (isUnit_det_shear _)
  · rw [transpose_mul]
    calc (shear (diagonal hA.eigenvalues))ᵀ * (bothHalves U)ᵀ * normMatrix A q
          * (bothHalves U * shear (diagonal hA.eigenvalues))
        = (shear (diagonal hA.eigenvalues))ᵀ
          * ((bothHalves U)ᵀ * normMatrix A q * bothHalves U)
          * shear (diagonal hA.eigenvalues) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [bothHalves_congr A q hU1, hUA, shear_congr]

/-- [proved-derived; formal-checked] **The index of the norm form.** Its negative squares number
the modes with `λ² > 4q`. -/
theorem negIndex_normMatrix {A : Matrix V V ℝ} (hA : A.IsHermitian) (q : ℝ) :
    negIndex (normMatrix A q)
      = (Finset.univ.filter fun i => 4 * q < hA.eigenvalues i ^ 2).card := by
  obtain ⟨P, hP, h⟩ := normMatrix_congr_diagonal hA q
  rw [negIndex_of_congr_diagonal _ hP h, Finset.card_filter, Fintype.sum_sum_type,
    Finset.card_filter]
  have hiff : ∀ i : V, (q - hA.eigenvalues i ^ 2 / 4 < 0) ↔ (4 * q < hA.eigenvalues i ^ 2) :=
    fun i => by constructor <;> intro h' <;> linarith
  simp only [Sum.elim_inl, Sum.elim_inr, hiff, not_lt.mpr (zero_le_one' ℝ), if_false,
    Finset.sum_const_zero, add_zero]

/-- [proved-derived; formal-checked] **The positive index of the norm form**: `|V|` from the second
half, and one for each mode with `λ² < 4q`. -/
theorem posIndex_normMatrix {A : Matrix V V ℝ} (hA : A.IsHermitian) (q : ℝ) :
    posIndex (normMatrix A q)
      = Fintype.card V + (Finset.univ.filter fun i => hA.eigenvalues i ^ 2 < 4 * q).card := by
  obtain ⟨P, hP, h⟩ := normMatrix_congr_diagonal hA q
  rw [posIndex_of_congr_diagonal _ hP h, Finset.card_filter, Fintype.sum_sum_type,
    Finset.card_filter]
  have hiff : ∀ i : V, (0 < q - hA.eigenvalues i ^ 2 / 4) ↔ (hA.eigenvalues i ^ 2 < 4 * q) :=
    fun i => by constructor <;> intro h' <;> linarith
  simp only [Sum.elim_inl, Sum.elim_inr, hiff, zero_lt_one' ℝ, if_true, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one]
  ring

/-- [proved-derived; formal-checked] **The null count.** The modes with `λ² = 4q` are in neither
index: `n₊ + n₋ + #{λ² = 4q} = 2|V|`. -/
theorem index_add_null_normMatrix {A : Matrix V V ℝ} (hA : A.IsHermitian) (q : ℝ) :
    posIndex (normMatrix A q) + negIndex (normMatrix A q)
        + (Finset.univ.filter fun i => hA.eigenvalues i ^ 2 = 4 * q).card
      = 2 * Fintype.card V := by
  rw [posIndex_normMatrix hA, negIndex_normMatrix hA]
  have key : (Finset.univ.filter fun i => hA.eigenvalues i ^ 2 < 4 * q).card
      + (Finset.univ.filter fun i => 4 * q < hA.eigenvalues i ^ 2).card
      + (Finset.univ.filter fun i => hA.eigenvalues i ^ 2 = 4 * q).card = Fintype.card V := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.card_univ, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases lt_trichotomy (hA.eigenvalues i ^ 2) (4 * q) with h | h | h
    · simp [h, h.not_gt, h.ne]
    · simp [h]
    · simp [h, h.not_gt, h.ne']
  omega

/-- [proved-derived; formal-checked] **No negative square exactly when every mode is at or inside
the half.** -/
theorem negIndex_normMatrix_eq_zero_iff {A : Matrix V V ℝ} (hA : A.IsHermitian) (q : ℝ) :
    negIndex (normMatrix A q) = 0 ↔ ∀ i, hA.eigenvalues i ^ 2 ≤ 4 * q := by
  rw [negIndex_normMatrix hA, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i
    exact not_lt.mp (h (Finset.mem_univ i))
  · intro h i _
    exact not_lt.mpr (h i)

/-- [proved-derived; formal-checked] **The trivial mode is a negative square.** A mode at
`λ = q + 1` with `q ≠ 1` has `λ² − 4q = (q − 1)² > 0`. -/
theorem one_le_negIndex_normMatrix_of_trivial {A : Matrix V V ℝ} (hA : A.IsHermitian) {q : ℝ}
    (hq : q ≠ 1) {i₀ : V} (h : hA.eigenvalues i₀ = q + 1) : 1 ≤ negIndex (normMatrix A q) := by
  rw [negIndex_normMatrix hA]
  refine Finset.card_pos.mpr ⟨i₀, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [h]
  have hpos : 0 < (q - 1) ^ 2 := by
    have : q - 1 ≠ 0 := sub_ne_zero.mpr hq
    positivity
  nlinarith [hpos]

end NormForm

/-! ## 4. Weil's form on real tests -/

section Weil

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [definition] Weil's form of a finite family with reversal `σ` and weights `m`, as a matrix:
`H i j = m i` at `j = σ i`. -/
def weilMatrix (m : ι → ℝ) (σ : ι → ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j => if j = σ i then m i else 0

omit [Fintype ι] in
/-- [proved-derived; formal-checked] The matrix is symmetric when `σ` is an involution that keeps
the weights. -/
theorem weilMatrix_isSymm {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i)
    (hmσ : ∀ i, m (σ i) = m i) : (weilMatrix m σ).IsSymm := by
  ext i j
  simp only [weilMatrix, transpose_apply, of_apply]
  by_cases h : j = σ i
  · subst h
    simp [hσ, hmσ]
  · have h' : ¬i = σ j := fun h' => h (by rw [h', hσ])
    rw [if_neg h, if_neg h']

/-- [proved-derived; formal-checked] The quadratic form of `weilMatrix`: `Σ m_i f_i f_(σ i)`. -/
theorem quad_weilMatrix (m : ι → ℝ) (σ : ι → ι) (f : ι → ℝ) :
    f ⬝ᵥ (weilMatrix m σ *ᵥ f) = ∑ i, m i * f i * f (σ i) := by
  simp only [dotProduct, mulVec, weilMatrix, of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (σ i)]
  · rw [if_pos rfl]
    ring
  · intro j _ hj
    rw [if_neg hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- [proved-derived; formal-checked] On a real test the complex form of
`Zeta/FiniteWeilCriterion` is this matrix's quadratic form. -/
theorem weil_ofReal (m : ι → ℝ) (σ : ι → ι) (f : ι → ℝ) :
    Holonics.Zeta.FiniteWeilCriterion.weil m σ (fun i => (f i : ℂ))
      = ((f ⬝ᵥ (weilMatrix m σ *ᵥ f) : ℝ) : ℂ) := by
  rw [quad_weilMatrix, Holonics.Zeta.FiniteWeilCriterion.weil]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_ofReal]

/-- The quadratic form on a test that the reversal keeps: `Σ m_i f_i²`. -/
theorem quad_weilMatrix_of_symm (m : ι → ℝ) (σ : ι → ι) {f : ι → ℝ}
    (hf : ∀ i, f (σ i) = f i) : f ⬝ᵥ (weilMatrix m σ *ᵥ f) = ∑ i, m i * (f i * f i) := by
  rw [quad_weilMatrix]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf i]
  ring

/-- The quadratic form on a test that the reversal negates: `−Σ m_i f_i²`. -/
theorem quad_weilMatrix_of_antisymm (m : ι → ℝ) (σ : ι → ι) {f : ι → ℝ}
    (hf : ∀ i, f (σ i) = -f i) : f ⬝ᵥ (weilMatrix m σ *ᵥ f) = -∑ i, m i * (f i * f i) := by
  rw [quad_weilMatrix, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf i]
  ring

omit [DecidableEq ι] in
theorem quad_neg (A : Matrix ι ι ℝ) (w : ι → ℝ) : w ⬝ᵥ ((-A) *ᵥ w) = -(w ⬝ᵥ (A *ᵥ w)) := by
  rw [neg_mulVec, dotProduct_neg]

/-- [proved-derived; formal-checked] **The negative index of Weil's form, with representatives.**
If `r` picks one place from each exchanged pair, the negative squares number the representatives.
-/
theorem negIndex_weilMatrix_of_reps {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i)
    (hm : ∀ i, 0 < m i) (r : ι → Prop) [DecidablePred r]
    (hr : ∀ i, σ i ≠ i → (r i ↔ ¬r (σ i))) (hrm : ∀ i, r i → σ i ≠ i) :
    negIndex (weilMatrix m σ) = Fintype.card {i // r i} := by
  refine le_antisymm ?_ ?_
  · -- upper bound: the differences `f i − f (σ i)` at the representatives
    refine posIndex_le_card_of_ker_nonpos _
      (LinearMap.funLeft ℝ ℝ (fun i : {i // r i} => (i : ι))
        - LinearMap.funLeft ℝ ℝ (fun i : {i // r i} => σ i)) ?_
    intro w hw
    have hwr : ∀ i, r i → w (σ i) = w i := by
      intro i hi
      have := congrFun hw ⟨i, hi⟩
      simp only [LinearMap.sub_apply, LinearMap.funLeft_apply, Pi.sub_apply, Pi.zero_apply] at this
      linarith
    have hsym : ∀ i, w (σ i) = w i := by
      intro i
      by_cases hfix : σ i = i
      · rw [hfix]
      · by_cases hi : r i
        · exact hwr i hi
        · have hsi : r (σ i) := by
            by_contra hns
            exact hi ((hr i hfix).mpr hns)
          have := hwr (σ i) hsi
          rw [hσ] at this
          exact this.symm
    rw [quad_neg, quad_weilMatrix_of_symm m σ hsym, neg_nonpos]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (mul_self_nonneg _)
  · -- lower bound: the tests `x_i` at a representative and `−x_i` at its reflection
    let e : ({i // r i} → ℝ) →ₗ[ℝ] (ι → ℝ) :=
      extendZero r - (LinearMap.funLeft ℝ ℝ σ).comp (extendZero r)
    refine card_le_posIndex_of_pos _ e ?_
    intro x hx
    set f : ι → ℝ := e x with hf
    have hfi : ∀ i, f i = extendZero r x i - extendZero r x (σ i) := fun i => rfl
    have hanti : ∀ i, f (σ i) = -f i := by
      intro i
      rw [hfi, hfi, hσ]
      ring
    rw [quad_neg, quad_weilMatrix_of_antisymm m σ hanti, neg_neg]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hm i).le (mul_self_nonneg _))
      ⟨j.1, Finset.mem_univ _, ?_⟩
    have hsj : ¬r (σ j.1) := (hr j.1 (hrm j.1 j.2)).mp j.2
    have hfj : f j.1 = x j := by
      rw [hfi, extendZero_of_pos r x j.2, extendZero_of_neg r x hsj, sub_zero]
    rw [hfj]
    exact mul_pos (hm _) (mul_self_pos.mpr hj)

/-- [proved-derived; formal-checked] **The positive index of Weil's form, with representatives**:
the fixed places and one for each exchanged pair. -/
theorem posIndex_weilMatrix_of_reps {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i)
    (hm : ∀ i, 0 < m i) (r : ι → Prop) [DecidablePred r]
    (hr : ∀ i, σ i ≠ i → (r i ↔ ¬r (σ i))) (hrm : ∀ i, r i → σ i ≠ i) :
    posIndex (weilMatrix m σ) = Fintype.card {i // σ i = i ∨ r i} := by
  refine le_antisymm ?_ ?_
  · -- upper bound: the sums `f i + f (σ i)` at the fixed places and the representatives
    refine posIndex_le_card_of_ker_nonpos _
      (LinearMap.funLeft ℝ ℝ (fun i : {i // σ i = i ∨ r i} => (i : ι))
        + LinearMap.funLeft ℝ ℝ (fun i : {i // σ i = i ∨ r i} => σ i)) ?_
    intro w hw
    have hwt : ∀ i, (σ i = i ∨ r i) → w (σ i) = -w i := by
      intro i hi
      have := congrFun hw ⟨i, hi⟩
      simp only [LinearMap.add_apply, LinearMap.funLeft_apply, Pi.add_apply, Pi.zero_apply] at this
      linarith
    have hanti : ∀ i, w (σ i) = -w i := by
      intro i
      by_cases hi : σ i = i ∨ r i
      · exact hwt i hi
      · have hfix : σ i ≠ i := fun h => hi (Or.inl h)
        have hri : ¬r i := fun h => hi (Or.inr h)
        have hsi : r (σ i) := by
          by_contra hns
          exact hri ((hr i hfix).mpr hns)
        have := hwt (σ i) (Or.inr hsi)
        rw [hσ] at this
        linarith
    rw [quad_weilMatrix_of_antisymm m σ hanti, neg_nonpos]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (mul_self_nonneg _)
  · -- lower bound: the tests kept by the reversal
    let e : ({i // σ i = i ∨ r i} → ℝ) →ₗ[ℝ] (ι → ℝ) :=
      extendZero (fun i => σ i = i ∨ r i)
        + (LinearMap.funLeft ℝ ℝ σ).comp (extendZero (fun i => σ i = i ∨ r i))
    refine card_le_posIndex_of_pos _ e ?_
    intro x hx
    set f : ι → ℝ := e x with hf
    have hfi : ∀ i, f i = extendZero (fun i => σ i = i ∨ r i) x i
        + extendZero (fun i => σ i = i ∨ r i) x (σ i) := fun i => rfl
    have hsym : ∀ i, f (σ i) = f i := by
      intro i
      rw [hfi, hfi, hσ]
      ring
    rw [quad_weilMatrix_of_symm m σ hsym]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hm i).le (mul_self_nonneg _))
      ⟨j.1, Finset.mem_univ _, ?_⟩
    have hfj : f j.1 ≠ 0 := by
      rw [hfi, extendZero_of_pos _ x j.2]
      rcases j.2 with hfix | hrj
      · have hmem : σ (σ j.1) = σ j.1 ∨ r (σ j.1) := Or.inl (by rw [hfix, hfix])
        rw [extendZero_of_pos _ x hmem]
        have hsub : (⟨σ j.1, hmem⟩ : {i // σ i = i ∨ r i}) = j := Subtype.ext hfix
        rw [hsub]
        intro h0
        apply hj
        simp only [Pi.zero_apply]
        linarith
      · have hmoved : σ j.1 ≠ j.1 := hrm j.1 hrj
        have hsj : ¬r (σ j.1) := (hr j.1 hmoved).mp hrj
        have hnot : ¬(σ (σ j.1) = σ j.1 ∨ r (σ j.1)) := by
          rintro (h | h)
          · rw [hσ] at h
            exact hmoved h.symm
          · exact hsj h
        rw [extendZero_of_neg _ x hnot, add_zero]
        exact hj
    exact mul_pos (hm _) (mul_self_pos.mpr hfj)

/-- The exchanged places come in pairs: under a linear order, half of them have `i < σ i`. -/
theorem two_mul_card_lt [LinearOrder ι] {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i) :
    2 * (Finset.univ.filter fun i => i < σ i).card
      = (Finset.univ.filter fun i => σ i ≠ i).card := by
  have hswap : (Finset.univ.filter fun i => σ i < i).card
      = (Finset.univ.filter fun i => i < σ i).card := by
    refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hσ]
      exact hi.2
    · intro i _ j _ hij
      have := congrArg σ hij
      rwa [hσ, hσ] at this
    · intro j hj
      rw [Finset.mem_filter] at hj
      refine ⟨σ j, ?_, hσ j⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hσ]
      exact hj.2
  have hsplit : (Finset.univ.filter fun i => σ i ≠ i).card
      = (Finset.univ.filter fun i => i < σ i).card
        + (Finset.univ.filter fun i => σ i < i).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases lt_trichotomy i (σ i) with h | h | h
    · simp [h, h.not_gt, h.ne']
    · simp [← h]
    · simp [h, h.not_gt, h.ne]
  rw [hsplit, hswap]
  ring

/-- [proved-derived; formal-checked] **The negative squares of Weil's form number the exchanged
pairs**: `2·n₋ = #{i | σ i ≠ i}`. -/
theorem two_mul_negIndex_weilMatrix {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i)
    (hm : ∀ i, 0 < m i) :
    2 * negIndex (weilMatrix m σ) = (Finset.univ.filter fun i => σ i ≠ i).card := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hr : ∀ i, σ i ≠ i → (i < σ i ↔ ¬σ i < σ (σ i)) := by
    intro i hne
    rw [hσ]
    constructor
    · intro h
      exact h.not_gt
    · intro h
      exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
  have hrm : ∀ i, i < σ i → σ i ≠ i := fun i h => h.ne'
  rw [negIndex_weilMatrix_of_reps hσ hm (fun i => i < σ i) hr hrm, Fintype.card_subtype,
    two_mul_card_lt hσ]

/-- [proved-derived; formal-checked] **The positive index of Weil's form**:
`2·n₊ = 2·#{i | σ i = i} + #{i | σ i ≠ i}`. -/
theorem two_mul_posIndex_weilMatrix {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i)
    (hm : ∀ i, 0 < m i) :
    2 * posIndex (weilMatrix m σ)
      = 2 * (Finset.univ.filter fun i => σ i = i).card
        + (Finset.univ.filter fun i => σ i ≠ i).card := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hr : ∀ i, σ i ≠ i → (i < σ i ↔ ¬σ i < σ (σ i)) := by
    intro i hne
    rw [hσ]
    constructor
    · intro h
      exact h.not_gt
    · intro h
      exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
  have hrm : ∀ i, i < σ i → σ i ≠ i := fun i h => h.ne'
  have hsplit : (Finset.univ.filter fun i => σ i = i ∨ i < σ i).card
      = (Finset.univ.filter fun i => σ i = i).card
        + (Finset.univ.filter fun i => i < σ i).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hfix : σ i = i
    · simp [hfix]
    · by_cases hlt : i < σ i
      · simp [hfix, hlt]
      · simp [hfix, hlt]
  rw [posIndex_weilMatrix_of_reps hσ hm (fun i => i < σ i) hr hrm, Fintype.card_subtype, hsplit,
    mul_add, two_mul_card_lt hσ]

/-- [proved-derived; formal-checked] **No negative square exactly when the reversal fixes every
place.** -/
theorem negIndex_weilMatrix_eq_zero_iff {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i)
    (hm : ∀ i, 0 < m i) : negIndex (weilMatrix m σ) = 0 ↔ ∀ i, σ i = i := by
  have h := two_mul_negIndex_weilMatrix hσ hm
  constructor
  · intro h0 i
    rw [h0, mul_zero] at h
    have hempty := Finset.card_eq_zero.mp h.symm
    by_contra hne
    have : i ∈ (Finset.univ.filter fun i => σ i ≠ i) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hne⟩
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty i)
  · intro hfix
    have hempty : (Finset.univ.filter fun i => σ i ≠ i) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _
      exact not_not.mpr (hfix i)
    rw [hempty, Finset.card_empty] at h
    omega

end Weil

section Audit

#print axioms posIndex_le_card_of_ker_nonpos
#print axioms card_le_posIndex_of_pos
#print axioms posIndex_diagonal
#print axioms negIndex_diagonal
#print axioms posIndex_of_congr_diagonal
#print axioms negIndex_of_congr_diagonal
#print axioms quad_normMatrix
#print axioms quad_normMatrix_eq_normForm
#print axioms orthogonal_diag
#print axioms bothHalves_congr
#print axioms shear_congr
#print axioms normMatrix_congr_diagonal
#print axioms negIndex_normMatrix
#print axioms posIndex_normMatrix
#print axioms index_add_null_normMatrix
#print axioms negIndex_normMatrix_eq_zero_iff
#print axioms one_le_negIndex_normMatrix_of_trivial
#print axioms weilMatrix_isSymm
#print axioms quad_weilMatrix
#print axioms weil_ofReal
#print axioms negIndex_weilMatrix_of_reps
#print axioms posIndex_weilMatrix_of_reps
#print axioms two_mul_negIndex_weilMatrix
#print axioms two_mul_posIndex_weilMatrix
#print axioms negIndex_weilMatrix_eq_zero_iff

end Audit

end Holonics.Holon.InertiaCount
