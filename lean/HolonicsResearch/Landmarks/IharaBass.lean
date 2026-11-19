import Mathlib

/-!
# Ihara–Bass: the dart operator's determinant is the cell operator's, for every finite complex

The tree held Ihara's theorem as a cited law (`trace.ihara-zeta`) with one formal instance, the
tetrahedron (`Geometry/GraphTrace`).  This owner proves the determinant identity itself, for every
finite multigraph and over every commutative ring, by Bass's block-matrix argument, which divides
by nothing.

**The model.**  Cells `V` and contacts `E` are finite types and `a b : E → V` give each contact its
two ends.  Loops (`a e = b e`) and parallel contacts are allowed.  A dart is an oriented contact,
an element of `E ⊕ E`: `inl e` runs from `a e` to `b e` and `inr e` from `b e` to `a e`, and the
reversal is `Sum.swap`, an involution with no fixed dart.

* [definition] `src`, `tgt` (a dart's start and end), `startMatrix` `S` and `endMatrix` `T`
  (the incidences `V × darts`), `reversal` `J` (the reversal's permutation matrix), `hashimoto` `B`
  (the non-backtracking dart operator, `B d f = 1` when `f` leaves the cell `d` enters and `f` is
  not `d` reversed), `adjacency` `A = S Tᵀ` and `degree` `D = S Sᵀ`.
* [proved-derived; formal-checked] the readings of those products: `adjacency_apply` (the count
  of darts from `v` to `w`), `degree_apply` (diagonal, the count of darts leaving `v`),
  `degree_eq_end` (`S Sᵀ = T Tᵀ`), `adjacency_transpose` (`A` is symmetric).
* [proved-derived; formal-checked] the reversal's laws: `reversal_mul_reversal` (`J J = 1`),
  `reversal_transpose`, `reversal_mul_endMatrix_transpose` (`J Tᵀ = Sᵀ`),
  `reversal_mul_startMatrix_transpose` (`J Sᵀ = Tᵀ`), `startMatrix_mul_reversal` (`S J = T`),
  `endMatrix_mul_reversal` (`T J = S`), and
  `endMatrix_transpose_mul_startMatrix` (`Tᵀ S = B + J`: the darts that leave where `d` enters are
  the non-backtracking continuations and the one reversal).
* [proved-derived; formal-checked] `det_one_add_smul_reversal`:
  `det (1 + u J) = (1 − u²)^|E|`, because the reversal has no fixed dart.
* [proved-derived; formal-checked] `bass_block_identity`: on `V ⊕ darts`,
  `[[1, 0], [Tᵀ, 1]] · [[(1 − u²), u S], [0, 1 − u B]] =
   [[1 − u A + u² (D − 1), u S], [0, 1 + u J]] · [[1, 0], [Tᵀ − u Sᵀ, 1]]`.
* [proved-derived; formal-checked] **`ihara_bass`**:
  `(1 − u²)^|V| · det (1 − u B) = det (1 − u A + u² (D − 1)) · (1 − u²)^|E|`,
  for every `u` in every commutative ring.
* [proved-derived; formal-checked] its forms: `ihara_bass_regular` (every cell with `q + 1` darts:
  the right determinant is `det ((1 + q u²) − u A)`); `ihara_bass_charpolyRev` (in `R[X]` at
  `u = X`, with Mathlib's reversed characteristic polynomial `det (1 − X B)` on the left);
  `ihara_bass_cancel` and `ihara_bass_cancel'` (in a domain with `u² ≠ 1` the common power of
  `1 − u²` is cancelled, on either side of `|V| ≤ |E|`); `det_hashimoto_eq_zero_iff` (in a domain
  with `u² ≠ 1`, `u` is a zero of the dart determinant if and only if it is one of the cell
  determinant) and `det_hashimoto_eq_zero_iff_regular` (the regular case: if and only if
  `det ((1 + q u²) − u A) = 0`).
* [proved-derived; formal-checked] supporting statements: `degree_eq_smul_one_of_regular`
  (`D = (q + 1)` when every cell has `q + 1` darts) and `startMatrix_map`, `endMatrix_map`,
  `hashimoto_map`, `adjacency_map`, `degree_map` (every ring map carries each operator to the same
  operator over the target ring, which is how the polynomial form is read from `ihara_bass`).

**What this does not state.**  The Euler product over primitive closed walks,
`det (1 − u B) = ∏ (1 − u^len P)`, is the dynamical side of `trace.ihara-zeta`, stated coefficient by
coefficient in `Landmarks/IharaEulerProduct`; this owner is the determinant side alone.  No spectral statement is made: that a regular
complex's nontrivial zeros stand on `|u| = q^(−1/2)` when every other mode of `A` has `λ² ≤ 4q`
needs the spectral theorem for `A` and the quadratic cell, which are other owners'.  The
`m − n` of the classical statement appears as the two powers on the two sides, so no connectivity
and no sign of `|E| − |V|` is assumed.

Every theorem is discharged and none depends on `sorryAx`.
-/

open Matrix

namespace Holonics.Landmarks.IharaBass

/-! ## Darts -/

section Darts

variable {V E : Type*}

/-- [definition] The cell a dart leaves: `inl e` leaves `a e`, `inr e` leaves `b e`. -/
def src (a b : E → V) : E ⊕ E → V := Sum.elim a b

/-- [definition] The cell a dart enters: `inl e` enters `b e`, `inr e` enters `a e`. -/
def tgt (a b : E → V) : E ⊕ E → V := Sum.elim b a

variable (a b : E → V)

@[simp] theorem src_inl (e : E) : src a b (Sum.inl e) = a e := rfl
@[simp] theorem src_inr (e : E) : src a b (Sum.inr e) = b e := rfl
@[simp] theorem tgt_inl (e : E) : tgt a b (Sum.inl e) = b e := rfl
@[simp] theorem tgt_inr (e : E) : tgt a b (Sum.inr e) = a e := rfl

/-- [proved-derived; formal-checked] A reversed dart leaves where the dart enters. -/
@[simp] theorem src_swap (d : E ⊕ E) : src a b d.swap = tgt a b d := by
  cases d <;> rfl

/-- [proved-derived; formal-checked] A reversed dart enters where the dart leaves. -/
@[simp] theorem tgt_swap (d : E ⊕ E) : tgt a b d.swap = src a b d := by
  cases d <;> rfl

/-- [proved-derived; formal-checked] The reversal has no fixed dart. -/
theorem swap_ne_self (d : E ⊕ E) : d.swap ≠ d := by
  cases d <;> simp

/-- [proved-derived; formal-checked] `d` is `f` reversed if and only if `f` is `d` reversed. -/
theorem eq_swap_comm (d f : E ⊕ E) : d = f.swap ↔ f = d.swap :=
  ⟨fun h => by rw [h, Sum.swap_swap], fun h => by rw [h, Sum.swap_swap]⟩

end Darts

/-! ## The operators -/

section Operators

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable (R : Type*) [CommRing R] (a b : E → V)

/-- [definition] The start incidence `S`: `S v d = 1` when the dart `d` leaves the cell `v`. -/
def startMatrix : Matrix V (E ⊕ E) R :=
  Matrix.of fun v d => if src a b d = v then 1 else 0

/-- [definition] The end incidence `T`: `T v d = 1` when the dart `d` enters the cell `v`. -/
def endMatrix : Matrix V (E ⊕ E) R :=
  Matrix.of fun v d => if tgt a b d = v then 1 else 0

/-- [definition] The reversal `J`: the permutation matrix of `Sum.swap` on darts. -/
def reversal (E : Type*) [DecidableEq E] : Matrix (E ⊕ E) (E ⊕ E) R :=
  Matrix.of fun d f => if f = d.swap then 1 else 0

/-- [definition] The non-backtracking dart operator `B` (Hashimoto's): `B d f = 1` when `f` leaves
the cell that `d` enters and `f` is not `d` reversed. -/
def hashimoto : Matrix (E ⊕ E) (E ⊕ E) R :=
  Matrix.of fun d f => if tgt a b d = src a b f ∧ f ≠ d.swap then 1 else 0

omit [DecidableEq E] in
@[simp] theorem startMatrix_apply (v : V) (d : E ⊕ E) :
    startMatrix R a b v d = if src a b d = v then 1 else 0 := rfl

omit [DecidableEq E] in
@[simp] theorem endMatrix_apply (v : V) (d : E ⊕ E) :
    endMatrix R a b v d = if tgt a b d = v then 1 else 0 := rfl

@[simp] theorem reversal_apply (d f : E ⊕ E) :
    reversal R E d f = if f = d.swap then 1 else 0 := rfl

@[simp] theorem hashimoto_apply (d f : E ⊕ E) :
    hashimoto R a b d f = if tgt a b d = src a b f ∧ f ≠ d.swap then 1 else 0 := rfl

/-- [proved-derived; formal-checked] `Jᵀ = J`. -/
theorem reversal_transpose : (reversal R E)ᵀ = reversal R E := by
  ext d f
  simp only [Matrix.transpose_apply, reversal_apply, eq_swap_comm d f]

end Operators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (R : Type*) [CommRing R] (a b : E → V)

/-- [definition] The cell operator `A = S Tᵀ`: `A v w` counts the darts from `v` to `w`. -/
def adjacency : Matrix V V R := startMatrix R a b * (endMatrix R a b)ᵀ

/-- [definition] The degree operator `D = S Sᵀ`: diagonal, counting the darts that leave a cell. -/
def degree : Matrix V V R := startMatrix R a b * (startMatrix R a b)ᵀ

/-! ## The reversal's laws -/

omit [Fintype V] [DecidableEq V] in
/-- [proved-derived; formal-checked] `J J = 1`: the reversal is an involution. -/
theorem reversal_mul_reversal : reversal R E * reversal R E = 1 := by
  ext d f
  simp only [Matrix.mul_apply, reversal_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ d.swap]
  simp only [Finset.mem_univ, if_true, Sum.swap_swap]
  by_cases h : d = f
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `J Tᵀ = Sᵀ`. -/
theorem reversal_mul_endMatrix_transpose :
    reversal R E * (endMatrix R a b)ᵀ = (startMatrix R a b)ᵀ := by
  ext d v
  simp only [Matrix.mul_apply, reversal_apply, Matrix.transpose_apply, endMatrix_apply,
    startMatrix_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ d.swap]
  simp only [Finset.mem_univ, if_true, tgt_swap]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `J Sᵀ = Tᵀ`. -/
theorem reversal_mul_startMatrix_transpose :
    reversal R E * (startMatrix R a b)ᵀ = (endMatrix R a b)ᵀ := by
  ext d v
  simp only [Matrix.mul_apply, reversal_apply, Matrix.transpose_apply, endMatrix_apply,
    startMatrix_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ d.swap]
  simp only [Finset.mem_univ, if_true, src_swap]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `S J = T`. -/
theorem startMatrix_mul_reversal : startMatrix R a b * reversal R E = endMatrix R a b := by
  have h := congrArg Matrix.transpose (reversal_mul_startMatrix_transpose R a b)
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
    reversal_transpose] at h

omit [Fintype V] in
/-- [proved-derived; formal-checked] `T J = S`. -/
theorem endMatrix_mul_reversal : endMatrix R a b * reversal R E = startMatrix R a b := by
  have h := congrArg Matrix.transpose (reversal_mul_endMatrix_transpose R a b)
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
    reversal_transpose] at h

omit [Fintype E] in
/-- [proved-derived; formal-checked] `Tᵀ S = B + J`: the darts leaving the cell that `d` enters are
its non-backtracking continuations and its one reversal. -/
theorem endMatrix_transpose_mul_startMatrix :
    (endMatrix R a b)ᵀ * startMatrix R a b = hashimoto R a b + reversal R E := by
  ext d f
  simp only [Matrix.mul_apply, Matrix.transpose_apply, endMatrix_apply, startMatrix_apply,
    Matrix.add_apply, hashimoto_apply, reversal_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ (tgt a b d)]
  simp only [Finset.mem_univ, if_true]
  by_cases hf : f = d.swap
  · have hs : src a b f = tgt a b d := by rw [hf, src_swap]
    rw [if_pos hs, if_neg (fun h => h.2 hf), if_pos hf, zero_add]
  · by_cases ht : tgt a b d = src a b f
    · rw [if_pos ht.symm, if_pos ⟨ht, hf⟩, if_neg hf, add_zero]
    · rw [if_neg (fun h => ht h.symm), if_neg (fun h => ht h.1), if_neg hf, add_zero]

/-! ## The products' readings -/

omit [Fintype V] in
/-- [proved-derived; formal-checked] `S Sᵀ = T Tᵀ`: a cell's darts out are as many as its darts in. -/
theorem degree_eq_end : degree R a b = endMatrix R a b * (endMatrix R a b)ᵀ := by
  have hS : (startMatrix R a b)ᵀ = reversal R E * (endMatrix R a b)ᵀ :=
    (reversal_mul_endMatrix_transpose R a b).symm
  have hT : startMatrix R a b = endMatrix R a b * reversal R E :=
    (endMatrix_mul_reversal R a b).symm
  calc degree R a b
      = (endMatrix R a b * reversal R E) * (reversal R E * (endMatrix R a b)ᵀ) := by
        rw [degree, ← hS, ← hT]
    _ = endMatrix R a b * ((reversal R E * reversal R E) * (endMatrix R a b)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = endMatrix R a b * (endMatrix R a b)ᵀ := by
        rw [reversal_mul_reversal, Matrix.one_mul]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `Aᵀ = A`: the cell operator is symmetric. -/
theorem adjacency_transpose : (adjacency R a b)ᵀ = adjacency R a b := by
  have hS : (startMatrix R a b)ᵀ = reversal R E * (endMatrix R a b)ᵀ :=
    (reversal_mul_endMatrix_transpose R a b).symm
  calc (adjacency R a b)ᵀ
      = endMatrix R a b * (startMatrix R a b)ᵀ := by
        rw [adjacency, Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = (endMatrix R a b * reversal R E) * (endMatrix R a b)ᵀ := by
        rw [hS, Matrix.mul_assoc]
    _ = adjacency R a b := by rw [endMatrix_mul_reversal, adjacency]

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] `A v w` is the count of darts from `v` to `w`. -/
theorem adjacency_apply (v w : V) :
    adjacency R a b v w =
      ((Finset.univ.filter fun d : E ⊕ E => src a b d = v ∧ tgt a b d = w).card : R) := by
  simp only [adjacency, Matrix.mul_apply, Matrix.transpose_apply, startMatrix_apply,
    endMatrix_apply, ite_mul, one_mul, zero_mul, ← ite_and]
  rw [Finset.sum_boole]

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] `D` is diagonal and `D v v` is the count of darts leaving `v`. -/
theorem degree_apply (v w : V) :
    degree R a b v w =
      if v = w then ((Finset.univ.filter fun d : E ⊕ E => src a b d = v).card : R) else 0 := by
  simp only [degree, Matrix.mul_apply, Matrix.transpose_apply, startMatrix_apply, ite_mul,
    one_mul, zero_mul, ← ite_and]
  by_cases h : v = w
  · subst h
    simp only [and_self, if_true]
    rw [Finset.sum_boole]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (h1.symm.trans h2)

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] On a complex whose every cell has `q + 1` darts, `D = (q + 1)`. -/
theorem degree_eq_smul_one_of_regular {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1) :
    degree R a b = ((q : R) + 1) • (1 : Matrix V V R) := by
  ext v w
  rw [degree_apply, Matrix.smul_apply, Matrix.one_apply, hreg v]
  by_cases h : v = w
  · rw [if_pos h, if_pos h, smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  · rw [if_neg h, if_neg h, smul_zero]

/-! ## The reversal's determinant -/

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- [proved-derived; formal-checked] In the two halves of the darts, `1 + u J` is the block matrix
`[[1, u], [u, 1]]`. -/
theorem one_add_smul_reversal (u : R) :
    (1 : Matrix (E ⊕ E) (E ⊕ E) R) + u • reversal R E =
      Matrix.fromBlocks 1 (u • (1 : Matrix E E R)) (u • (1 : Matrix E E R)) 1 := by
  ext (i | i) (j | j)
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply, eq_comm]
  · simp [Matrix.one_apply, eq_comm]
  · simp [Matrix.one_apply]

omit [Fintype V] [DecidableEq V] in
/-- [proved-derived; formal-checked] `det (1 + u J) = (1 − u²)^|E|`: each contact's two darts make
one `2 × 2` block `[[1, u], [u, 1]]`, because the reversal fixes no dart. -/
theorem det_one_add_smul_reversal (u : R) :
    ((1 : Matrix (E ⊕ E) (E ⊕ E) R) + u • reversal R E).det = (1 - u ^ 2) ^ Fintype.card E := by
  rw [one_add_smul_reversal, Matrix.det_fromBlocks_one₁₁]
  have h : (1 : Matrix E E R) - u • (1 : Matrix E E R) * u • (1 : Matrix E E R) =
      (1 - u ^ 2) • (1 : Matrix E E R) := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, sub_smul, one_smul, pow_two]
  rw [h, Matrix.det_smul, Matrix.det_one, mul_one]

/-! ## Bass's block identity and the determinant formula -/

/-- [proved-derived; formal-checked] Bass's block identity on `V ⊕ darts`.  It divides by nothing,
so it holds over every commutative ring. -/
theorem bass_block_identity (u : R) :
    Matrix.fromBlocks (1 : Matrix V V R) 0 (endMatrix R a b)ᵀ 1 *
        Matrix.fromBlocks ((1 - u ^ 2) • (1 : Matrix V V R)) (u • startMatrix R a b) 0
          (1 - u • hashimoto R a b) =
      Matrix.fromBlocks (1 - u • adjacency R a b + u ^ 2 • (degree R a b - 1))
          (u • startMatrix R a b) 0 (1 + u • reversal R E) *
        Matrix.fromBlocks 1 0 ((endMatrix R a b)ᵀ - u • (startMatrix R a b)ᵀ) 1 := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  · -- the cells' block: `(1 − u²) = 1 − u A + u² (D − 1) + u S (Tᵀ − u Sᵀ)`
    simp only [Matrix.mul_one, Matrix.zero_mul, add_zero, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, adjacency, degree]
    module
  · -- the upper right block: `u S` on both sides
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add]
  · -- the lower left block: `Tᵀ (1 − u²) = (1 + u J)(Tᵀ − u Sᵀ)`
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
      zero_add, Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
      reversal_mul_endMatrix_transpose, reversal_mul_startMatrix_transpose]
    module
  · -- the darts' block: `Tᵀ (u S) + 1 − u B = 1 + u J`
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, zero_add,
      Matrix.mul_smul, endMatrix_transpose_mul_startMatrix]
    module

/-- [proved-derived; formal-checked] **Ihara–Bass.**  For every finite multigraph (loops and
parallel contacts allowed) and every `u` in every commutative ring,
`(1 − u²)^|V| · det (1 − u B) = det (1 − u A + u² (D − 1)) · (1 − u²)^|E|`. -/
theorem ihara_bass (u : R) :
    (1 - u ^ 2) ^ Fintype.card V * (1 - u • hashimoto R a b).det =
      (1 - u • adjacency R a b + u ^ 2 • (degree R a b - 1)).det *
        (1 - u ^ 2) ^ Fintype.card E := by
  have h := congrArg Matrix.det (bass_block_identity R a b u)
  simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_smul, one_mul, mul_one, det_one_add_smul_reversal] at h
  exact h

/-- [proved-derived; formal-checked] The regular case: when every cell has `q + 1` darts,
`(1 − u²)^|V| · det (1 − u B) = det ((1 + q u²) − u A) · (1 − u²)^|E|`. -/
theorem ihara_bass_regular {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1) (u : R) :
    (1 - u ^ 2) ^ Fintype.card V * (1 - u • hashimoto R a b).det =
      ((1 + (q : R) * u ^ 2) • (1 : Matrix V V R) - u • adjacency R a b).det *
        (1 - u ^ 2) ^ Fintype.card E := by
  rw [ihara_bass, degree_eq_smul_one_of_regular R a b hreg]
  congr 2
  module

/-! ## In a domain: cancelling the common power, and the zeros -/

/-- [proved-derived; formal-checked] In a domain with `u² ≠ 1` and `|V| ≤ |E|`,
`det (1 − u B) = (1 − u²)^(|E| − |V|) · det (1 − u A + u² (D − 1))`. -/
theorem ihara_bass_cancel [IsDomain R] {u : R} (hu : u ^ 2 ≠ 1)
    (hVE : Fintype.card V ≤ Fintype.card E) :
    (1 - u • hashimoto R a b).det =
      (1 - u ^ 2) ^ (Fintype.card E - Fintype.card V) *
        (1 - u • adjacency R a b + u ^ 2 • (degree R a b - 1)).det := by
  have hne : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h := ihara_bass R a b u
  refine mul_left_cancel₀ (pow_ne_zero (Fintype.card V) hne) ?_
  rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hVE, mul_comm]

/-- [proved-derived; formal-checked] In a domain with `u² ≠ 1` and `|E| ≤ |V|` (a forest's side),
`(1 − u²)^(|V| − |E|) · det (1 − u B) = det (1 − u A + u² (D − 1))`. -/
theorem ihara_bass_cancel' [IsDomain R] {u : R} (hu : u ^ 2 ≠ 1)
    (hEV : Fintype.card E ≤ Fintype.card V) :
    (1 - u ^ 2) ^ (Fintype.card V - Fintype.card E) * (1 - u • hashimoto R a b).det =
      (1 - u • adjacency R a b + u ^ 2 • (degree R a b - 1)).det := by
  have hne : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h := ihara_bass R a b u
  refine mul_right_cancel₀ (pow_ne_zero (Fintype.card E) hne) ?_
  rw [← h, mul_right_comm, ← pow_add, Nat.sub_add_cancel hEV]

/-- [proved-derived; formal-checked] In a domain, away from `u² = 1`, the dart determinant and the
cell determinant vanish together: the zeros of `det (1 − u B)` other than `u = ±1` are those of
`det (1 − u A + u² (D − 1))`. -/
theorem det_hashimoto_eq_zero_iff [IsDomain R] {u : R} (hu : u ^ 2 ≠ 1) :
    (1 - u • hashimoto R a b).det = 0 ↔
      (1 - u • adjacency R a b + u ^ 2 • (degree R a b - 1)).det = 0 := by
  have hne : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h := ihara_bass R a b u
  constructor
  · intro h0
    rw [h0, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right (pow_ne_zero _ hne)
  · intro h0
    rw [h0, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hne)

/-- [proved-derived; formal-checked] The regular case of the zeros: with `q + 1` darts at every
cell and `u² ≠ 1` in a domain, `det (1 − u B) = 0` if and only if `det ((1 + q u²) − u A) = 0`. -/
theorem det_hashimoto_eq_zero_iff_regular [IsDomain R] {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1) {u : R}
    (hu : u ^ 2 ≠ 1) :
    (1 - u • hashimoto R a b).det = 0 ↔
      ((1 + (q : R) * u ^ 2) • (1 : Matrix V V R) - u • adjacency R a b).det = 0 := by
  have hne : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h := ihara_bass_regular R a b hreg u
  constructor
  · intro h0
    rw [h0, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right (pow_ne_zero _ hne)
  · intro h0
    rw [h0, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hne)

/-! ## Change of ring, and the polynomial form -/

section Map

variable {R} {R' : Type*} [CommRing R'] (f : R →+* R')

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- [proved-derived; formal-checked] The start incidence is carried by every ring map. -/
theorem startMatrix_map : (startMatrix R a b).map f = startMatrix R' a b := by
  ext v d
  simp only [Matrix.map_apply, startMatrix_apply, apply_ite f, map_one, map_zero]

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- [proved-derived; formal-checked] The end incidence is carried by every ring map. -/
theorem endMatrix_map : (endMatrix R a b).map f = endMatrix R' a b := by
  ext v d
  simp only [Matrix.map_apply, endMatrix_apply, apply_ite f, map_one, map_zero]

omit [Fintype V] [Fintype E] in
/-- [proved-derived; formal-checked] The dart operator is carried by every ring map. -/
theorem hashimoto_map : (hashimoto R a b).map f = hashimoto R' a b := by
  ext d e
  simp only [Matrix.map_apply, hashimoto_apply, apply_ite f, map_one, map_zero]

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] The cell operator is carried by every ring map. -/
theorem adjacency_map : (adjacency R a b).map f = adjacency R' a b := by
  rw [adjacency, Matrix.map_mul, Matrix.transpose_map, startMatrix_map, endMatrix_map, adjacency]

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] The degree operator is carried by every ring map. -/
theorem degree_map : (degree R a b).map f = degree R' a b := by
  rw [degree, Matrix.map_mul, Matrix.transpose_map, startMatrix_map, degree]

end Map

open Polynomial in
/-- [proved-derived; formal-checked] The polynomial form.  With Mathlib's reversed characteristic
polynomial `charpolyRev B = det (1 − X B)`, the reciprocal of the complex's zeta as a transfer
determinant,
`(1 − X²)^|V| · charpolyRev B = det (1 − X A + X² (D − 1)) · (1 − X²)^|E|` in `R[X]`. -/
theorem ihara_bass_charpolyRev :
    (1 - (X : R[X]) ^ 2) ^ Fintype.card V * (hashimoto R a b).charpolyRev =
      (1 - (X : R[X]) • (adjacency R a b).map C +
            (X : R[X]) ^ 2 • ((degree R a b).map C - 1)).det *
        (1 - (X : R[X]) ^ 2) ^ Fintype.card E := by
  rw [Matrix.charpolyRev, hashimoto_map, adjacency_map, degree_map]
  exact ihara_bass R[X] a b X

section Audit

#print axioms reversal_mul_reversal
#print axioms endMatrix_transpose_mul_startMatrix
#print axioms det_one_add_smul_reversal
#print axioms bass_block_identity
#print axioms ihara_bass
#print axioms ihara_bass_regular
#print axioms ihara_bass_cancel
#print axioms ihara_bass_cancel'
#print axioms det_hashimoto_eq_zero_iff
#print axioms det_hashimoto_eq_zero_iff_regular
#print axioms ihara_bass_charpolyRev

end Audit

end Holonics.Landmarks.IharaBass
