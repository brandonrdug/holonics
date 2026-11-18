import Mathlib

/-!
# The closed and co-closed cochains count the holes, and a junction holds a three and one for each pair of its ends

[proved-standard] The source is the record of November 11
(`research/records/2026-11-11_EINSTEINS_FIELD_PROGRAM_ON_THE_COMPLEX_THE_UNIFIED_FIELD_IS_A_TWO_WAY_FLOW_A_GRAIN_GIVES_THE_MASS_AND_A_PROBABILITY_IS_ITS_FLAT_PART.md`,
§5 "a source-free charge is a hole's class", §11 and §14.12; atlas `lorentz.junction-hermitian-times`,
`lorentz.pair-hermitian-signature`).

What is proved.

1. **The count of the closed and co-closed cochains** (§5, §11). On a finite complex over ℝ with boundaries
   `∂₁ : C₁ → C₀` and `∂₂ : C₂ → C₁`, `∂₁∂₂ = 0`, the cochains on edges that are co-closed (`∂₁ f = 0`) and closed
   (`∂₂ᵀ f = 0`) form a space (`harmonic`) of dimension `E − rank ∂₁ − rank ∂₂` (`finrank_harmonic`,
   `finrank_harmonic_eq`). A closed cochain reads zero on every boundary, so its periods stand only on cycles no cell
   fills (`closed_vanishes_on_boundaries`). On a filled complex, every cycle a boundary, there are none
   (`harmonic_eq_bot_of_filled`), and that is the ranks filling the edges (`harmonic_eq_bot_iff`,
   `rank_add_rank_of_filled`). The ruler: a filled triangle holds none (`filled_triangle`), and the hollow one holds the
   circulation (`hollow_triangle`).
2. **A junction's forms** (§14.12). A Hermitian form on a junction of `n` ends has `n² = n + 2·C(n, 2)` real entries
   (`entries_count`). Each pair of ends `(i, j)` reads its own block (`pairBlock`), Hermitian (`pairBlock_isHermitian`),
   whose determinant is a three and one with its own time `t_ij = ½(X_ii + X_jj)` (`pairBlock_det`). A move of that pair
   alone acts on the block as the pair's own move (`pairBlock_move`) and, at determinant one, keeps the block's
   determinant (`pairBlock_det_kept`). The times over the pairs sum to `(n − 1)/2 · tr X`, each end's entry shared by the
   pairs it joins (`sum_times_ordered`, `sum_times`). One amplitude is a null direction in every pair
   (`pairBlock_det_of_amplitude`).

Existing owners, cited and not repeated: `Physics/TwoWayField` holds the pair's own statements (`det_conj_form`,
`det_kept`, `hermitian_det_interval`), of which statement 2 is the reading on each block of a junction;
`Physics/Spacetime/Einstein` holds the Einstein lifts this count stands beside.

Limits. Statement 1 is over ℝ, where the standard pairing is definite; over a field of positive characteristic the
count can differ and is not claimed. The sheet of nine cells of the record is not built here; the ruler is a triangle.
Statement 2 is about the forms of an undivided `n`-fold ratio; that a move of one pair changes the other pairs' blocks
is the record's reading on Gaussian integers and is not stated here, and nothing says a physical event is a junction of
more than two ends.

The computational object is the helical pair interaction: an edge is a pair contact, a cochain on edges a field of
contact readings, and a junction's block is one pair of its ends. Of the winding guide's six general objects this
touches cell holonomy (a harmonic cochain's periods on unfilled cycles) and the pair (each block); the helix, faces and
placement, tube and tower thread stay attached.

Consumers: #410's boxes "On a finite complex the closed and co-closed cochains have dimension `E − rank ∂₁ − rank ∂₂`"
and "A junction's forms"; atlas `lorentz.junction-hermitian-times`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.CochainCount

open Matrix Module

/-! ## 1. The closed and co-closed cochains -/

section Harmonic

variable {V E F : Type*} [Fintype E] [Fintype F]

/-- The cochains on edges that are co-closed (`∂₁ f = 0`) and closed (`∂₂ᵀ f = 0`). -/
def harmonic (d1 : Matrix V E ℝ) (d2 : Matrix E F ℝ) : Submodule ℝ (E → ℝ) :=
  LinearMap.ker d1.mulVecLin ⊓ LinearMap.ker d2ᵀ.mulVecLin

omit [Fintype F] in
/-- [proved-standard] Membership: both the boundary and the coboundary vanish. -/
theorem mem_harmonic {d1 : Matrix V E ℝ} {d2 : Matrix E F ℝ} {f : E → ℝ} :
    f ∈ harmonic d1 d2 ↔ d1 *ᵥ f = 0 ∧ d2ᵀ *ᵥ f = 0 := by
  unfold harmonic
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]

/-- [proved-standard] **A closed cochain reads zero on every boundary**: its periods stand only on cycles no cell
fills. -/
theorem closed_vanishes_on_boundaries (d2 : Matrix E F ℝ) {f : E → ℝ} (hf : d2ᵀ *ᵥ f = 0) (g : F → ℝ) :
    f ⬝ᵥ (d2 *ᵥ g) = 0 := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hf, zero_dotProduct]

private theorem finrank_ker_add_rank {m : Type*} (A : Matrix m E ℝ) :
    finrank ℝ (LinearMap.ker A.mulVecLin) + A.rank = Fintype.card E := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  unfold Matrix.rank
  omega

/-- [proved-standard] **The count of the closed and co-closed cochains**: on a finite complex over ℝ with `∂₁∂₂ = 0`,
their dimension and the two ranks fill the edges, `dim + rank ∂₁ + rank ∂₂ = E`. -/
theorem finrank_harmonic (d1 : Matrix V E ℝ) (d2 : Matrix E F ℝ) (h : d1 * d2 = 0) :
    finrank ℝ (harmonic d1 d2) + d1.rank + d2.rank = Fintype.card E := by
  have hRBle : LinearMap.range d2.mulVecLin ≤ LinearMap.ker d1.mulVecLin := by
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h,
      Matrix.zero_mulVec]
  have hdisj : LinearMap.range d2.mulVecLin ⊓ LinearMap.ker d2ᵀ.mulVecLin = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨⟨g, rfl⟩, hv⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hv
    have hzero : (d2 *ᵥ g) ⬝ᵥ (d2 *ᵥ g) = 0 := closed_vanishes_on_boundaries d2 hv g
    rw [Matrix.mulVecLin_apply]
    exact dotProduct_self_eq_zero.mp hzero
  have hRB : finrank ℝ (LinearMap.range d2.mulVecLin) = d2.rank := rfl
  have hKB := finrank_ker_add_rank d2ᵀ
  rw [Matrix.rank_transpose] at hKB
  have hsum1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range d2.mulVecLin)
    (LinearMap.ker d2ᵀ.mulVecLin)
  rw [hdisj, finrank_bot] at hsum1
  have htop : LinearMap.range d2.mulVecLin ⊔ LinearMap.ker d2ᵀ.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  have hKAKB : LinearMap.ker d1.mulVecLin ⊔ LinearMap.ker d2ᵀ.mulVecLin = ⊤ := by
    apply top_unique
    rw [← htop]
    exact sup_le_sup_right hRBle _
  have hsum2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker d1.mulVecLin)
    (LinearMap.ker d2ᵀ.mulVecLin)
  rw [hKAKB, finrank_top, Module.finrank_fintype_fun_eq_card] at hsum2
  have hKA := finrank_ker_add_rank d1
  unfold harmonic
  omega

/-- [proved-standard] The count as the record writes it: `E − rank ∂₁ − rank ∂₂`. -/
theorem finrank_harmonic_eq (d1 : Matrix V E ℝ) (d2 : Matrix E F ℝ) (h : d1 * d2 = 0) :
    finrank ℝ (harmonic d1 d2) = Fintype.card E - d1.rank - d2.rank := by
  have := finrank_harmonic d1 d2 h
  omega

/-- [proved-standard] **A filled complex holds none**: if every cycle is a boundary, the only closed and co-closed
cochain is zero. -/
theorem harmonic_eq_bot_of_filled (d1 : Matrix V E ℝ) (d2 : Matrix E F ℝ)
    (hfill : ∀ f : E → ℝ, d1 *ᵥ f = 0 → ∃ g, f = d2 *ᵥ g) : harmonic d1 d2 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  obtain ⟨h1, h2⟩ := mem_harmonic.mp hf
  obtain ⟨g, rfl⟩ := hfill f h1
  exact dotProduct_self_eq_zero.mp (closed_vanishes_on_boundaries d2 h2 g)

/-- [proved-standard] There are none exactly when the two ranks fill the edges. -/
theorem harmonic_eq_bot_iff (d1 : Matrix V E ℝ) (d2 : Matrix E F ℝ) (h : d1 * d2 = 0) :
    harmonic d1 d2 = ⊥ ↔ d1.rank + d2.rank = Fintype.card E := by
  have hcount := finrank_harmonic d1 d2 h
  constructor
  · intro hbot
    rw [hbot, finrank_bot] at hcount
    omega
  · intro hr
    apply Submodule.finrank_eq_zero.mp
    omega

/-- [proved-standard] On a filled complex the two ranks fill the edges. -/
theorem rank_add_rank_of_filled (d1 : Matrix V E ℝ) (d2 : Matrix E F ℝ) (h : d1 * d2 = 0)
    (hfill : ∀ f : E → ℝ, d1 *ᵥ f = 0 → ∃ g, f = d2 *ᵥ g) : d1.rank + d2.rank = Fintype.card E :=
  (harmonic_eq_bot_iff d1 d2 h).mp (harmonic_eq_bot_of_filled d1 d2 hfill)

end Harmonic

/-- The triangle's edge boundary: edges `0 → 1`, `1 → 2`, `2 → 0`. -/
def triangleEdges : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 1; 1, -1, 0; 0, 1, -1]

/-- The triangle's one cell, bounded by the three edges in turn. -/
def triangleCell : Matrix (Fin 3) (Fin 1) ℝ := !![1; 1; 1]

/-- [proved-standard] The triangle is a complex: the boundary of the cell's boundary is zero. -/
theorem triangle_complex : triangleEdges * triangleCell = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triangleEdges, triangleCell, Matrix.mul_apply, Fin.sum_univ_three]

/-- [proved-standard] **The filled triangle holds none.** -/
theorem filled_triangle : harmonic triangleEdges triangleCell = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  obtain ⟨h1, h2⟩ := mem_harmonic.mp hf
  have e0 := congrFun h1 0
  have e1 := congrFun h1 1
  have e2 := congrFun h2 0
  simp [triangleEdges, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e0 e1
  simp [triangleCell, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e2
  funext i
  fin_cases i <;> simp <;> linarith

/-- [proved-standard] **The hollow triangle holds the circulation**: with no cell, the cochain that reads one on every
edge is closed and co-closed and is not zero. -/
theorem hollow_triangle :
    (fun _ => 1 : Fin 3 → ℝ) ∈ harmonic triangleEdges (0 : Matrix (Fin 3) (Fin 0) ℝ) ∧
      (fun _ => 1 : Fin 3 → ℝ) ≠ 0 := by
  constructor
  · rw [mem_harmonic]
    constructor
    · funext i
      fin_cases i <;> simp [triangleEdges, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · funext i
      exact i.elim0
  · intro h
    have := congrFun h 0
    norm_num at this

/-! ## 2. A junction's forms -/

/-- [proved-standard] A Hermitian form on `n` ends has `n` real entries on the diagonal and one complex entry for each
pair of ends: `n² = n + 2·C(n, 2)`. -/
theorem entries_count (n : ℕ) : n ^ 2 = n + 2 * n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    nlinarith [ih]

section Junction

variable {n : Type*}

/-- The block a pair of ends `(i, j)` reads. -/
def pairBlock (X : Matrix n n ℂ) (i j : n) : Matrix (Fin 2) (Fin 2) ℂ := X.submatrix ![i, j] ![i, j]

/-- The pair's own time: `t_ij = ½(X_ii + X_jj)`. -/
noncomputable def time (X : Matrix n n ℂ) (i j : n) : ℝ := ((X i i).re + (X j j).re) / 2

/-- The pair's own axis: `z_ij = ½(X_ii − X_jj)`. -/
noncomputable def axis (X : Matrix n n ℂ) (i j : n) : ℝ := ((X i i).re - (X j j).re) / 2

/-- [proved-standard] A pair's block of a Hermitian form is Hermitian. -/
theorem pairBlock_isHermitian {X : Matrix n n ℂ} (hX : X.IsHermitian) (i j : n) : (pairBlock X i j).IsHermitian :=
  hX.submatrix _

private theorem two_det (a b : ℝ) (w : ℂ) :
    (a : ℂ) * b - w * (starRingEnd ℂ) w = (((a + b) / 2) ^ 2 - ((a - b) / 2) ^ 2 - Complex.normSq w : ℝ) := by
  rw [Complex.mul_conj]
  push_cast
  ring

/-- [proved-standard] **Each pair's block is a three and one with its own time**:
`det X_(ij) = t_ij² − z_ij² − |X_ij|²`, `t_ij = ½(X_ii + X_jj)`. -/
theorem pairBlock_det {X : Matrix n n ℂ} (hX : X.IsHermitian) (i j : n) :
    (pairBlock X i j).det = ((time X i j ^ 2 - axis X i j ^ 2 - Complex.normSq (X i j) : ℝ) : ℂ) := by
  have hii : ((X i i).re : ℂ) = X i i := Complex.conj_eq_iff_re.mp (hX.apply i i)
  have hjj : ((X j j).re : ℂ) = X j j := Complex.conj_eq_iff_re.mp (hX.apply j j)
  have hji : (starRingEnd ℂ) (X i j) = X j i := hX.apply j i
  have h := two_det (X i i).re (X j j).re (X i j)
  rw [hii, hjj, hji] at h
  rw [Matrix.det_fin_two]
  unfold pairBlock time axis
  simpa using h

/-- [proved-standard] **One amplitude is a null direction in every pair**: for `X = ψψ*` every block's determinant is
zero. -/
theorem pairBlock_det_of_amplitude (ψ : n → ℂ) (i j : n) :
    (pairBlock (Matrix.vecMulVec ψ (star ψ)) i j).det = 0 := by
  rw [Matrix.det_fin_two]
  unfold pairBlock
  simp [Matrix.vecMulVec_apply]
  ring

variable [Fintype n]

/-- [proved-standard] **A move of one pair alone acts on that pair's block as the pair's own move**: if the columns of
`A` at the pair's ends are supported on those ends, where they read `A₂`, the block of `Aᴴ X A` is `A₂ᴴ X_(ij) A₂`. -/
theorem pairBlock_move (e : Fin 2 → n) (he : Function.Injective e) (A X : Matrix n n ℂ)
    (A₂ : Matrix (Fin 2) (Fin 2) ℂ) (hblock : ∀ a b, A (e a) (e b) = A₂ a b)
    (hoff : ∀ k, k ∉ Set.range e → ∀ b, A k (e b) = 0) :
    (Aᴴ * X * A).submatrix e e = A₂ᴴ * X.submatrix e e * A₂ := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  symm
  apply Fintype.sum_of_injective e he
  · intro l hl
    rw [hoff l hl b, mul_zero]
  · intro d
    rw [hblock]
    congr 1
    apply Fintype.sum_of_injective e he
    · intro k hk
      rw [hoff k hk a, star_zero, zero_mul]
    · intro c
      rw [hblock]

/-- [proved-standard] **A pair's move of determinant one keeps that pair's three and one.** -/
theorem pairBlock_det_kept (e : Fin 2 → n) (he : Function.Injective e) (A X : Matrix n n ℂ)
    (A₂ : Matrix (Fin 2) (Fin 2) ℂ) (hblock : ∀ a b, A (e a) (e b) = A₂ a b)
    (hoff : ∀ k, k ∉ Set.range e → ∀ b, A k (e b) = 0) (hdet : A₂.det = 1) :
    ((Aᴴ * X * A).submatrix e e).det = (X.submatrix e e).det := by
  rw [pairBlock_move e he A X A₂ hblock hoff, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdet]
  simp

variable [DecidableEq n]

/-- [proved-standard] Over the ordered pairs of distinct ends the times sum to `(n − 1)·tr X`. -/
theorem sum_times_ordered (X : Matrix n n ℂ) :
    ∑ i, ∑ j, (if i ≠ j then time X i j else 0) = ((Fintype.card n : ℝ) - 1) * (X.trace).re := by
  have hinner : ∀ i, ∑ j, (if i ≠ j then time X i j else 0) =
      ((Fintype.card n : ℝ) * (X i i).re + ∑ j, (X j j).re) / 2 - (X i i).re := by
    intro i
    have hsplit : ∀ j, (if i ≠ j then time X i j else 0) = time X i j - (if i = j then time X i j else 0) := by
      intro j
      by_cases hij : i = j <;> simp [hij]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    unfold time
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have htr : (X.trace).re = ∑ j, (X j j).re := by
    unfold Matrix.trace
    rw [Complex.re_sum]
    rfl
  rw [htr]
  ring

/-- [proved-standard] **The times sum to `(n − 1)/2 · tr X`**: each end's entry is shared by the pairs it joins. -/
theorem sum_times [LinearOrder n] (X : Matrix n n ℂ) :
    ∑ i, ∑ j, (if i < j then time X i j else 0) = ((Fintype.card n : ℝ) - 1) / 2 * (X.trace).re := by
  have hsymm : ∀ i j, time X i j = time X j i := by
    intro i j
    unfold time
    ring
  have hswap : ∑ i, ∑ j, (if i < j then time X i j else 0) = ∑ i, ∑ j, (if j < i then time X i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm]
  have hboth : ∑ i, ∑ j, (if i < j then time X i j else 0) + ∑ i, ∑ j, (if j < i then time X i j else 0) =
      ∑ i, ∑ j, (if i ≠ j then time X i j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h]
  have hord := sum_times_ordered X
  rw [← hboth, ← hswap] at hord
  linarith

end Junction

end Holonics.Physics.CochainCount
