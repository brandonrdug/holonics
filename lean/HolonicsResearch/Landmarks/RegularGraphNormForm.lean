import Mathlib

/-!
# The norm form of a finite complex with `q + 1` contacts a cell

[definition] A finite complex whose every cell has `q + 1` contacts is read here on pairs of cell
functions `x = (a, b)`. With `A` the symmetric adjacency of the cells, three objects stand on such
pairs:

* the **move** `move A q (a, b) = (−b, q·a + A b)`, the non-backtracking step of the contacts read
  on the two lifts of a cell function (Part B proves that reading);
* the **area form** `area (a, b) (a′, b′) = a·b′ − b·a′`, the reversal's pairing;
* the **norm form** `normForm A q (a, b) = q·(a·a) + a·(A b) + b·b`.

[proved-derived; formal-checked] What is proved.

1. The move scales the area form by `q` (`area_move`); this is the functional equation's face and
   uses only the symmetry of `A`.
2. The norm form is the area form of a state against its own image, `normForm x = area x (move x)`
   (`normForm_eq_area`), so it is the reversal's own form and no pairing is supplied from outside.
   The move scales it by `q` (`normForm_move`, `normForm_iterate`): a similitude, for every `A`.
3. Completing the square, `normForm (a, b) = |b + ½ A a|² + (q·|a|² − ¼·|A a|²)`
   (`normForm_eq_square_add`). On an `A`-invariant submodule `U` the norm form is positive on
   `U × U` away from zero if and only if `|A a|² < 4q·|a|²` for every nonzero `a ∈ U`
   (`normForm_pos_iff`): the certificate is positive on, and only on, the part of the complex whose
   modes stand strictly inside the widest gap, `λ² < 4q`.
4. The half from the certificate: a complex eigenvector of the move whose real and imaginary parts
   lie in `U`, with the norm form positive on `U × U`, has an eigenvalue `α` with `|α|² = q`
   (`normSq_eq_of_normForm_pos`; with item 3, `normSq_eq_of_tempered`). The proof uses only the
   similitude and the positivity: `H(x) = normForm (re x) + normForm (im x)` is multiplied by `q`
   under the move and by `|α|²` under multiplication by `α`.
5. The cell: a root `α` of `α² − l·α + q = 0` with real `l`, `q` and `l² ≤ 4q` has `|α|² = q`
   (`cell_normSq_of_le`, `cell_normSq_of_lt`), and when `4q < l²` with `0 < q` the cell has a real
   root with `r² > q` and one with `r² < q` (`cell_real_roots_of_gt`): a turn on one side and a
   boost on the other.
6. The eigen correspondence: a complex eigenvector `(a, b) ≠ 0` of the move with eigenvalue `α`
   has `a ≠ 0`, `b = −α·a` and `α·(A a) = (α² + q)·a` (`eigen_correspondence`).
7. Part B, the lift. For a finite multigraph given by its edges' two ends (loops and repeated
   edges allowed), with darts `E ⊕ E`, reversal `Sum.swap` and the non-backtracking dart operator
   `B`, the adjacency is symmetric (`adjacency_isSymm`) and, when every cell is the source of
   `q + 1` darts, `B *ᵥ lift x = lift (move A q x)` for the lift
   `lift (a, b) e = a (src e) + b (tgt e)` (`nonBacktracking_lift`).
8. On the mean of a complex whose cells all have row sum `q + 1` the norm form takes a negative
   value when `1 < q` (`normForm_const_neg`): the count is a boost and carries no certificate.

[interpretation] The reading. The modes of the move over a cell mode `λ` are the roots of
`α² − λα + q`, the cell of the junction-and-delay record of November 15. The norm form restricted
to that mode is the norm of the quadratic algebra `ℝ[α]/(α² − λα + q)`: definite when the algebra
is `ℂ` (a turn), indefinite when it is `ℝ × ℝ` (a boost). A complex is tempered on `U` if and only if
its own reversal form is positive there.

**What this does not state.** Nothing here is a statement about the zeta function of the
integers. The determinant formula joining `B` to `A` is the sibling module `Landmarks/IharaBass`
and is not used. That every mode of `B` outside the lifts is `±1` is not proved here. The count of
negative squares of the norm form (one for each mode with `λ² > 4q`) was read by a host ruler and
is not formalized; only the positivity criterion of item 3 is.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Holonics.Landmarks.RegularGraphNormForm

open Matrix

/-! ## Part A: the move, the area form and the norm form -/

section Real

variable {V : Type*} [Fintype V]

/-- [definition] A state: a pair of cell functions. -/
abbrev State (V : Type*) := (V → ℝ) × (V → ℝ)

/-- [definition] The move `(a, b) ↦ (−b, q·a + A b)`. -/
def move (A : Matrix V V ℝ) (q : ℝ) (x : State V) : State V :=
  (-x.2, q • x.1 + A *ᵥ x.2)

/-- [definition] The area form `a·b′ − b·a′`, the reversal's pairing. -/
def area (x y : State V) : ℝ := x.1 ⬝ᵥ y.2 - x.2 ⬝ᵥ y.1

/-- [definition] The norm form `q·(a·a) + a·(A b) + b·b`. -/
def normForm (A : Matrix V V ℝ) (q : ℝ) (x : State V) : ℝ :=
  q * (x.1 ⬝ᵥ x.1) + x.1 ⬝ᵥ (A *ᵥ x.2) + x.2 ⬝ᵥ x.2

/-- [proved-derived; formal-checked] A symmetric `A` moves across the dot product. -/
theorem dot_mulVec_symm {A : Matrix V V ℝ} (hA : A.IsSymm) (a b : V → ℝ) :
    a ⬝ᵥ (A *ᵥ b) = (A *ᵥ a) ⬝ᵥ b := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq]

theorem dot_self_nonneg (v : V → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem dot_self_pos {v : V → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  rcases (dot_self_nonneg v).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hv
    funext i
    have hsum : ∑ i, v i * v i = 0 := h.symm
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (v i))).mp hsum i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hi

/-- [proved-derived; formal-checked] The move scales the area form by `q`. -/
theorem area_move {A : Matrix V V ℝ} (hA : A.IsSymm) (q : ℝ) (x y : State V) :
    area (move A q x) (move A q y) = q * area x y := by
  have h := dot_mulVec_symm hA x.2 y.2
  simp only [area, move, dotProduct_add, add_dotProduct, neg_dotProduct, dotProduct_neg,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  linear_combination (-1 : ℝ) * h

/-- [proved-derived; formal-checked] The norm form is the area of a state against its image. -/
theorem normForm_eq_area (A : Matrix V V ℝ) (q : ℝ) (x : State V) :
    normForm A q x = area x (move A q x) := by
  simp only [area, move, normForm, dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] The move is a similitude of the norm form, of ratio `q`. -/
theorem normForm_move {A : Matrix V V ℝ} (hA : A.IsSymm) (q : ℝ) (x : State V) :
    normForm A q (move A q x) = q * normForm A q x := by
  have h1 : x.2 ⬝ᵥ (A *ᵥ x.1) = x.1 ⬝ᵥ (A *ᵥ x.2) := by
    rw [dot_mulVec_symm hA, dotProduct_comm]
  have h2 : x.2 ⬝ᵥ (A *ᵥ (A *ᵥ x.2)) = (A *ᵥ x.2) ⬝ᵥ (A *ᵥ x.2) := dot_mulVec_symm hA _ _
  have h3 : (A *ᵥ x.2) ⬝ᵥ x.1 = x.1 ⬝ᵥ (A *ᵥ x.2) := dotProduct_comm _ _
  simp only [normForm, move, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    neg_dotProduct, dotProduct_neg, smul_dotProduct, dotProduct_smul, smul_eq_mul, neg_neg]
  linear_combination (-q) * h1 - h2 + q * h3

/-- [proved-derived; formal-checked] After `n` moves the norm form has been scaled by `qⁿ`. -/
theorem normForm_iterate {A : Matrix V V ℝ} (hA : A.IsSymm) (q : ℝ) (n : ℕ) (x : State V) :
    normForm A q ((move A q)^[n] x) = q ^ n * normForm A q x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', normForm_move hA, ih]
    ring

/-- [proved-derived; formal-checked] Completing the square. -/
theorem normForm_eq_square_add {A : Matrix V V ℝ} (hA : A.IsSymm) (q : ℝ) (a b : V → ℝ) :
    normForm A q (a, b) =
      (b + (1 / 2 : ℝ) • (A *ᵥ a)) ⬝ᵥ (b + (1 / 2 : ℝ) • (A *ᵥ a)) +
        (q * (a ⬝ᵥ a) - (1 / 4 : ℝ) * ((A *ᵥ a) ⬝ᵥ (A *ᵥ a))) := by
  have h1 : b ⬝ᵥ (A *ᵥ a) = a ⬝ᵥ (A *ᵥ b) := by
    rw [dot_mulVec_symm hA, dotProduct_comm]
  have h2 : (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (A *ᵥ b) := (dot_mulVec_symm hA a b).symm
  simp only [normForm, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  linear_combination (-(1 / 2 : ℝ)) * h1 - (1 / 2 : ℝ) * h2

/-- [proved-derived; formal-checked] The positivity criterion: on an `A`-invariant submodule the
norm form is positive away from zero if and only if `|A a|² < 4q·|a|²` there. -/
theorem normForm_pos_iff {A : Matrix V V ℝ} (hA : A.IsSymm) (q : ℝ)
    (U : Submodule ℝ (V → ℝ)) (hU : ∀ a ∈ U, A *ᵥ a ∈ U) :
    (∀ a ∈ U, ∀ b ∈ U, (a ≠ 0 ∨ b ≠ 0) → 0 < normForm A q (a, b)) ↔
      (∀ a ∈ U, a ≠ 0 → (A *ᵥ a) ⬝ᵥ (A *ᵥ a) < 4 * q * (a ⬝ᵥ a)) := by
  constructor
  · intro h a ha ha0
    have hb : (-(1 / 2 : ℝ)) • (A *ᵥ a) ∈ U := U.smul_mem _ (hU a ha)
    have hpos := h a ha _ hb (Or.inl ha0)
    rw [normForm_eq_square_add hA] at hpos
    have hz : (-(1 / 2 : ℝ)) • (A *ᵥ a) + (1 / 2 : ℝ) • (A *ᵥ a) = 0 := by
      rw [← add_smul]; norm_num
    rw [hz, dotProduct_zero] at hpos
    linarith
  · intro h a ha b _ hab
    rw [normForm_eq_square_add hA]
    have hsq := dot_self_nonneg (b + (1 / 2 : ℝ) • (A *ᵥ a))
    by_cases ha0 : a = 0
    · subst ha0
      have hb0 : b ≠ 0 := by
        rcases hab with h0 | h0
        · exact absurd rfl h0
        · exact h0
      have hbpos := dot_self_pos hb0
      simp only [mulVec_zero, smul_zero, add_zero, dotProduct_zero, mul_zero, sub_zero]
      exact hbpos
    · have := h a ha ha0
      linarith

end Real

/-! ## The cell -/

/-- [proved-derived; formal-checked] A root of the cell `α² − l·α + q` with `l² ≤ 4q` has
`|α|² = q`. -/
theorem cell_normSq_of_le {l q : ℝ} {α : ℂ} (h : α ^ 2 - (l : ℂ) * α + (q : ℂ) = 0)
    (hl : l ^ 2 ≤ 4 * q) : Complex.normSq α = q := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.zero_re,
    Complex.zero_im, zero_mul, sub_zero, add_zero] at hre him
  rw [Complex.normSq_apply]
  by_cases hy : α.im = 0
  · rw [hy] at hre
    have hsq : (2 * α.re - l) ^ 2 = l ^ 2 - 4 * q := by linear_combination 4 * hre
    have hzero : (2 * α.re - l) ^ 2 = 0 := le_antisymm (by rw [hsq]; linarith) (sq_nonneg _)
    have hx : 2 * α.re - l = 0 := by simpa using hzero
    rw [hy]
    nlinarith
  · have hprod : α.im * (2 * α.re - l) = 0 := by linear_combination him
    have hx : 2 * α.re - l = 0 := by
      rcases mul_eq_zero.mp hprod with h0 | h0
      · exact absurd h0 hy
      · exact h0
    have hxl : α.re = l / 2 := by linarith
    rw [hxl] at hre
    rw [hxl]
    linarith

/-- [proved-derived; formal-checked] The strict form of the cell's half. -/
theorem cell_normSq_of_lt {l q : ℝ} {α : ℂ} (h : α ^ 2 - (l : ℂ) * α + (q : ℂ) = 0)
    (hl : l ^ 2 < 4 * q) : Complex.normSq α = q :=
  cell_normSq_of_le h hl.le

/-- [proved-derived; formal-checked] Outside the gap the cell is a boost: it has a real root with
`r² > q` and a real root with `r² < q`. -/
theorem cell_real_roots_of_gt {l q : ℝ} (hq : 0 < q) (hl : 4 * q < l ^ 2) :
    (∃ r : ℝ, r ^ 2 - l * r + q = 0 ∧ q < r ^ 2) ∧
      (∃ r : ℝ, r ^ 2 - l * r + q = 0 ∧ r ^ 2 < q) := by
  have hd : 0 < l ^ 2 - 4 * q := by linarith
  set d := Real.sqrt (l ^ 2 - 4 * q) with hd_def
  have hdsq : d ^ 2 = l ^ 2 - 4 * q := Real.sq_sqrt hd.le
  have hdpos : 0 < d := Real.sqrt_pos.mpr hd
  have hr1 : ((l + d) / 2) ^ 2 - l * ((l + d) / 2) + q = 0 := by nlinarith
  have hr2 : ((l - d) / 2) ^ 2 - l * ((l - d) / 2) + q = 0 := by nlinarith
  have hprod : ((l + d) / 2) * ((l - d) / 2) = q := by nlinarith
  have hsum : ((l + d) / 2) ^ 2 + ((l - d) / 2) ^ 2 = l ^ 2 - 2 * q := by nlinarith
  by_cases hbig : q < ((l + d) / 2) ^ 2
  · refine ⟨⟨_, hr1, hbig⟩, ⟨_, hr2, ?_⟩⟩
    have hp2 : ((l + d) / 2) ^ 2 * ((l - d) / 2) ^ 2 = q ^ 2 := by
      rw [← mul_pow, hprod]
    by_contra hcon
    have hcon' := not_lt.mp hcon
    nlinarith
  · have hbig := not_lt.mp hbig
    have hbig2 : q < ((l - d) / 2) ^ 2 := by linarith
    refine ⟨⟨_, hr2, hbig2⟩, ⟨_, hr1, ?_⟩⟩
    have hp2 : ((l + d) / 2) ^ 2 * ((l - d) / 2) ^ 2 = q ^ 2 := by
      rw [← mul_pow, hprod]
    by_contra hcon
    have hcon' := not_lt.mp hcon
    have heq : ((l + d) / 2) ^ 2 = q := le_antisymm hbig hcon'
    rw [heq] at hp2
    nlinarith

/-! ## The count is a boost -/

section Mean

variable {V : Type*} [Fintype V]

/-- [proved-derived; formal-checked] On the mean of a complex whose cells have row sum `q + 1`
the norm form takes a negative value when `1 < q`: the count carries no certificate. -/
theorem normForm_const_neg [Nonempty V] {A : Matrix V V ℝ} {q : ℝ} (hq : 1 < q)
    (hA1 : A *ᵥ (fun _ => (1 : ℝ)) = (q + 1) • (fun _ => (1 : ℝ))) :
    normForm A q ((fun _ => (1 : ℝ)), (-((q + 1) / 2)) • (fun _ => (1 : ℝ))) < 0 := by
  have hN : (0 : ℝ) < (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) := by
    apply dot_self_pos
    intro h
    have := congrFun h (Classical.arbitrary V)
    simp at this
  simp only [normForm, mulVec_smul, hA1, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  nlinarith [sq_nonneg (q - 1), mul_pos hN (mul_pos (sub_pos.mpr hq) (sub_pos.mpr hq))]

end Mean

/-! ## The half from the certificate: complex states -/

section Complex

variable {V : Type*} [Fintype V]

/-- [definition] A complex state: a pair of complex cell functions. -/
abbrev StateC (V : Type*) := (V → ℂ) × (V → ℂ)

/-- [definition] The move on complex states, with the real `A` read in `ℂ`. -/
def moveC (A : Matrix V V ℝ) (q : ℝ) (x : StateC V) : StateC V :=
  (-x.2, (q : ℂ) • x.1 + (A.map Complex.ofReal) *ᵥ x.2)

/-- [definition] The real part of a complex state. -/
def rePart (x : StateC V) : State V := (fun v => (x.1 v).re, fun v => (x.2 v).re)

/-- [definition] The imaginary part of a complex state. -/
def imPart (x : StateC V) : State V := (fun v => (x.1 v).im, fun v => (x.2 v).im)

theorem re_map_mulVec (A : Matrix V V ℝ) (b : V → ℂ) (v : V) :
    ((A.map Complex.ofReal *ᵥ b) v).re = (A *ᵥ fun w => (b w).re) v := by
  simp [mulVec, dotProduct, Complex.re_sum]

theorem im_map_mulVec (A : Matrix V V ℝ) (b : V → ℂ) (v : V) :
    ((A.map Complex.ofReal *ᵥ b) v).im = (A *ᵥ fun w => (b w).im) v := by
  simp [mulVec, dotProduct, Complex.im_sum]

theorem rePart_moveC (A : Matrix V V ℝ) (q : ℝ) (x : StateC V) :
    rePart (moveC A q x) = move A q (rePart x) := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · simp [rePart, moveC, move]
  · simp [rePart, moveC, move, re_map_mulVec]

theorem imPart_moveC (A : Matrix V V ℝ) (q : ℝ) (x : StateC V) :
    imPart (moveC A q x) = move A q (imPart x) := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · simp [imPart, moveC, move]
  · simp [imPart, moveC, move, im_map_mulVec]

omit [Fintype V] in
theorem rePart_smul (α : ℂ) (x : StateC V) :
    rePart (α • x) = α.re • rePart x - α.im • imPart x := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_) <;>
    simp [rePart, imPart, Complex.mul_re]

omit [Fintype V] in
theorem imPart_smul (α : ℂ) (x : StateC V) :
    imPart (α • x) = α.im • rePart x + α.re • imPart x := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_) <;>
    simp [rePart, imPart, Complex.mul_im, add_comm]

/-- [proved-derived; formal-checked] A real quadratic form on the two parts of a complex state:
turning the pair `(u, w)` by `s + i t` multiplies the sum of the two norm forms by `s² + t²`. -/
theorem normForm_rotate (A : Matrix V V ℝ) (q s t : ℝ) (u w : State V) :
    normForm A q (s • u - t • w) + normForm A q (t • u + s • w) =
      (s ^ 2 + t ^ 2) * (normForm A q u + normForm A q w) := by
  simp only [normForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, mulVec_sub, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- [definition] The norm form read on a complex state: the sum over its two parts. -/
def hermitianNorm (A : Matrix V V ℝ) (q : ℝ) (x : StateC V) : ℝ :=
  normForm A q (rePart x) + normForm A q (imPart x)

/-- [proved-derived; formal-checked] The complex move scales the complex reading by `q`. -/
theorem hermitianNorm_moveC {A : Matrix V V ℝ} (hA : A.IsSymm) (q : ℝ) (x : StateC V) :
    hermitianNorm A q (moveC A q x) = q * hermitianNorm A q x := by
  simp only [hermitianNorm, rePart_moveC, imPart_moveC, normForm_move hA]
  ring

/-- [proved-derived; formal-checked] Multiplication by `α` scales the complex reading by `|α|²`. -/
theorem hermitianNorm_smul (A : Matrix V V ℝ) (q : ℝ) (α : ℂ) (x : StateC V) :
    hermitianNorm A q (α • x) = Complex.normSq α * hermitianNorm A q x := by
  simp only [hermitianNorm, rePart_smul, imPart_smul]
  rw [normForm_rotate, Complex.normSq_apply]
  ring

theorem normForm_zero (A : Matrix V V ℝ) (q : ℝ) : normForm A q (0, 0) = 0 := by
  simp [normForm]

/-- [proved-derived; formal-checked] **The half from the certificate.** If the norm form is
positive on `U × U` away from zero, a nonzero complex eigenvector of the move whose real and
imaginary parts lie in `U` has an eigenvalue of squared modulus `q`. -/
theorem normSq_eq_of_normForm_pos {A : Matrix V V ℝ} (hA : A.IsSymm) (q : ℝ)
    (U : Submodule ℝ (V → ℝ))
    (hpos : ∀ a ∈ U, ∀ b ∈ U, (a ≠ 0 ∨ b ≠ 0) → 0 < normForm A q (a, b))
    {x : StateC V} (hx : x ≠ 0)
    (hre : (rePart x).1 ∈ U ∧ (rePart x).2 ∈ U) (him : (imPart x).1 ∈ U ∧ (imPart x).2 ∈ U)
    {α : ℂ} (h : moveC A q x = α • x) : Complex.normSq α = q := by
  have hnonneg : ∀ y : State V, y.1 ∈ U → y.2 ∈ U → 0 ≤ normForm A q y := by
    intro y h1 h2
    by_cases hy : y.1 ≠ 0 ∨ y.2 ≠ 0
    · exact (hpos y.1 h1 y.2 h2 hy).le
    · have hy1 : y.1 = 0 := by_contra fun h0 => hy (Or.inl h0)
      have hy2 : y.2 = 0 := by_contra fun h0 => hy (Or.inr h0)
      have hy0 : y = (0, 0) := Prod.ext hy1 hy2
      rw [hy0, normForm_zero]
  have hparts : (rePart x ≠ (0, 0)) ∨ (imPart x ≠ (0, 0)) := by
    by_contra hcon
    have h1 : rePart x = (0, 0) := by_contra fun h0 => hcon (Or.inl h0)
    have h2 : imPart x = (0, 0) := by_contra fun h0 => hcon (Or.inr h0)
    apply hx
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · apply Complex.ext
      · exact congrFun (congrArg Prod.fst h1) v
      · exact congrFun (congrArg Prod.fst h2) v
    · apply Complex.ext
      · exact congrFun (congrArg Prod.snd h1) v
      · exact congrFun (congrArg Prod.snd h2) v
  have hstrict : ∀ y : State V, y.1 ∈ U → y.2 ∈ U → y ≠ (0, 0) → 0 < normForm A q y := by
    intro y h1 h2 hy
    apply hpos y.1 h1 y.2 h2
    by_contra hcon
    apply hy
    have hy1 : y.1 = 0 := by_contra fun h0 => hcon (Or.inl h0)
    have hy2 : y.2 = 0 := by_contra fun h0 => hcon (Or.inr h0)
    exact Prod.ext hy1 hy2
  have hH : 0 < hermitianNorm A q x := by
    have hr := hnonneg (rePart x) hre.1 hre.2
    have hi := hnonneg (imPart x) him.1 him.2
    rcases hparts with hp | hp
    · have := hstrict (rePart x) hre.1 hre.2 hp
      simp only [hermitianNorm]
      linarith
    · have := hstrict (imPart x) him.1 him.2 hp
      simp only [hermitianNorm]
      linarith
  have hboth : q * hermitianNorm A q x = Complex.normSq α * hermitianNorm A q x := by
    rw [← hermitianNorm_moveC hA, h, hermitianNorm_smul]
  exact (mul_right_cancel₀ hH.ne' hboth).symm

/-- [proved-derived; formal-checked] The half on the tempered part: where `|A a|² < 4q·|a|²` on an
`A`-invariant `U`, every mode of the move carried by `U` has squared modulus `q`. -/
theorem normSq_eq_of_tempered {A : Matrix V V ℝ} (hA : A.IsSymm) (q : ℝ)
    (U : Submodule ℝ (V → ℝ)) (hU : ∀ a ∈ U, A *ᵥ a ∈ U)
    (htemp : ∀ a ∈ U, a ≠ 0 → (A *ᵥ a) ⬝ᵥ (A *ᵥ a) < 4 * q * (a ⬝ᵥ a))
    {x : StateC V} (hx : x ≠ 0)
    (hre : (rePart x).1 ∈ U ∧ (rePart x).2 ∈ U) (him : (imPart x).1 ∈ U ∧ (imPart x).2 ∈ U)
    {α : ℂ} (h : moveC A q x = α • x) : Complex.normSq α = q :=
  normSq_eq_of_normForm_pos hA q U ((normForm_pos_iff hA q U hU).mpr htemp) hx hre him h

/-- [proved-derived; formal-checked] The eigen correspondence: a mode of the move is a mode of
`A` read through the cell `α² − λα + q`, with `λ = α + q/α`. -/
theorem eigen_correspondence (A : Matrix V V ℝ) (q : ℝ) {x : StateC V} (hx : x ≠ 0) {α : ℂ}
    (h : moveC A q x = α • x) :
    x.1 ≠ 0 ∧ x.2 = -(α • x.1) ∧
      α • ((A.map Complex.ofReal) *ᵥ x.1) = (α ^ 2 + (q : ℂ)) • x.1 := by
  have h1 : -x.2 = α • x.1 := congrArg Prod.fst h
  have h2 : (q : ℂ) • x.1 + (A.map Complex.ofReal) *ᵥ x.2 = α • x.2 := congrArg Prod.snd h
  have hb : x.2 = -(α • x.1) := by rw [← h1, neg_neg]
  refine ⟨?_, hb, ?_⟩
  · intro ha
    apply hx
    refine Prod.ext ha ?_
    rw [hb, ha]
    simp
  · rw [hb] at h2
    funext v
    have hv := congrFun h2 v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_neg, mulVec_smul,
      Pi.neg_apply] at hv
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (-1 : ℂ) * hv

end Complex

/-! ## Part B: the lift from cells to darts -/

section Lift

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- [definition] The source of a dart: an edge with ends `a e`, `b e` carries the dart
`inl e` from `a e` to `b e` and its reversal `inr e`. -/
def src (a b : E → V) : E ⊕ E → V := Sum.elim a b

/-- [definition] The target of a dart. -/
def tgt (a b : E → V) : E ⊕ E → V := Sum.elim b a

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
@[simp] theorem src_swap (a b : E → V) (e : E ⊕ E) : src a b e.swap = tgt a b e := by
  cases e <;> rfl

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
@[simp] theorem tgt_swap (a b : E → V) (e : E ⊕ E) : tgt a b e.swap = src a b e := by
  cases e <;> rfl

/-- [definition] The non-backtracking dart operator: `f` may follow `e` when it leaves the cell
`e` arrives at and is not `e` reversed. -/
def nonBacktracking (a b : E → V) : Matrix (E ⊕ E) (E ⊕ E) ℝ :=
  fun e f => if tgt a b e = src a b f ∧ f ≠ e.swap then 1 else 0

/-- [definition] The adjacency of the cells: the number of darts from `v` to `w`. -/
def adjacency (a b : E → V) : Matrix V V ℝ :=
  fun v w => ((Finset.univ.filter fun e : E ⊕ E => src a b e = v ∧ tgt a b e = w).card : ℝ)

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] Reversal makes the adjacency symmetric. -/
theorem adjacency_isSymm (a b : E → V) : (adjacency a b).IsSymm := by
  refine Matrix.IsSymm.ext fun v w => ?_
  simp only [adjacency]
  congr 1
  apply Finset.card_equiv (Equiv.sumComm E E)
  intro e
  simp [and_comm]

omit [DecidableEq E] in
/-- [proved-derived; formal-checked] The adjacency sums a cell function over the darts leaving a
cell. -/
theorem adjacency_mulVec (a b : E → V) (c : V → ℝ) (v : V) :
    (adjacency a b *ᵥ c) v = ∑ f : E ⊕ E, if src a b f = v then c (tgt a b f) else 0 := by
  simp only [mulVec, dotProduct, adjacency, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : src a b f = v
  · simp [h]
  · simp [h]

/-- [definition] The lift of a state to the darts: `a` at the source plus `b` at the target. -/
def lift (a b : E → V) (x : State V) : E ⊕ E → ℝ :=
  fun e => x.1 (src a b e) + x.2 (tgt a b e)

/-- [proved-derived; formal-checked] **The lift intertwines the dart operator with the move.**
When every cell is the source of `q + 1` darts, the non-backtracking operator on a lifted state is
the lift of the moved state. -/
theorem nonBacktracking_lift (a b : E → V) (q : ℕ)
    (hreg : ∀ v, (Finset.univ.filter fun e : E ⊕ E => src a b e = v).card = q + 1)
    (x : State V) :
    nonBacktracking a b *ᵥ lift a b x = lift a b (move (adjacency a b) (q : ℝ) x) := by
  funext e
  have key : ∀ f : E ⊕ E, nonBacktracking a b e f * lift a b x f =
      (if src a b f = tgt a b e then lift a b x f else 0) -
        (if f = e.swap then lift a b x f else 0) := by
    intro f
    by_cases h1 : f = e.swap
    · subst h1
      simp [nonBacktracking]
    · by_cases h2 : src a b f = tgt a b e
      · simp [nonBacktracking, h1, h2]
      · have h2' : ¬ tgt a b e = src a b f := fun h => h2 h.symm
        simp [nonBacktracking, h1, h2, h2']
  have hsplit : ∀ f : E ⊕ E, (if src a b f = tgt a b e then lift a b x f else 0) =
      (if src a b f = tgt a b e then x.1 (tgt a b e) else 0) +
        (if src a b f = tgt a b e then x.2 (tgt a b f) else 0) := by
    intro f
    by_cases h : src a b f = tgt a b e <;> simp [h, lift]
  have hsum1 : ∑ f : E ⊕ E, (if src a b f = tgt a b e then lift a b x f else 0) =
      ((q : ℝ) + 1) * x.1 (tgt a b e) + (adjacency a b *ᵥ x.2) (tgt a b e) := by
    rw [adjacency_mulVec]
    simp only [hsplit, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter, Finset.sum_const, hreg]
    simp
  have hsum2 : ∑ f : E ⊕ E, (if f = e.swap then lift a b x f else 0) =
      x.1 (tgt a b e) + x.2 (src a b e) := by
    simp [lift]
  have hgoal : (nonBacktracking a b *ᵥ lift a b x) e =
      ∑ f : E ⊕ E, nonBacktracking a b e f * lift a b x f := rfl
  rw [hgoal, Finset.sum_congr rfl (fun f _ => key f), Finset.sum_sub_distrib, hsum1, hsum2]
  simp only [lift, move, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Lift

section Audit

#print axioms area_move
#print axioms normForm_eq_area
#print axioms normForm_move
#print axioms normForm_iterate
#print axioms normForm_eq_square_add
#print axioms normForm_pos_iff
#print axioms cell_normSq_of_le
#print axioms cell_real_roots_of_gt
#print axioms normForm_const_neg
#print axioms normSq_eq_of_normForm_pos
#print axioms normSq_eq_of_tempered
#print axioms eigen_correspondence
#print axioms adjacency_isSymm
#print axioms nonBacktracking_lift

end Audit

end Holonics.Landmarks.RegularGraphNormForm
