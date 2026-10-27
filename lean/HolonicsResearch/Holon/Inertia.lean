import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Pulling a constitution back through a map can only lose inertia

#410 owes the inertia of a constitution: the pull-back bound `n₊(PᵀAP) ≤ n₊(A)`,
`n₋(PᵀAP) ≤ n₋(A)` (atlas row `inertia.pullback-bound`) and the rank–trace defect
`2c·tr A − ‖A‖²_F = Σ(c² − (c − λ_i)²)` (`inertia.rank-trace-defect`). Both were checked only by the
retired Rust `inertia.rs`, which computed Sylvester's triple by symmetric elimination over the
rationals.

[definition] The **positive index** `n₊(A)` of a square matrix over an ordered field is the largest
dimension of a subspace on which `A` is positive, `wᵀ A w > 0` for every nonzero `w` in it
(`PosOn`, `posIndex`); the **negative index** is `n₋(A) = n₊(−A)` (`negIndex`). This reading needs
no diagonalization, so the count is a property of the form, never of an elimination's pivot
order.

[proved-standard; formal-checked] What is proved.

1. **The pull-back bound** (`quad_pullback`, `posIndex_pullback`, `negIndex_pullback`): for `A` of
   size `m` and `P` of any shape `m × n`, `n₊(PᵀAP) ≤ n₊(A)` and `n₋(PᵀAP) ≤ n₋(A)`. A subspace
   `W` on which `PᵀAP` is positive meets `ker P` only in `0`, since `wᵀPᵀAPw = (Pw)ᵀA(Pw)`, so `P`
   carries it injectively onto a subspace `PW` of the same dimension on which `A` is positive.
2. **The kernel lies in the radical** (`pullback_mulVec_of_ker`): `Pv = 0` gives `PᵀAPv = 0`.
3. **Sylvester's law** (`posIndex_congr`, `negIndex_congr`): for invertible `P` the bound runs both
   ways, through `P⁻¹`, so the indices are invariant under every change of basis.
4. **A rank-one collapse loses both signs** (`splitForm`, `collapse`, `collapse_example`,
   `collapse_drops_both`): with `A = diag(1, −1)` and `P = [[1, 1], [1, 1]]`, `PᵀAP = 0`, so `n₊`
   and `n₋` both fall from at least `1` to `0` (`posIndex_zero`, `negIndex_zero`,
   `one_le_posIndex_example`, `one_le_negIndex_example`).
5. **The rank–trace defect** (`defect_shift`, `frobenius_sq_eq_trace`, `trace_mul_self_eq_sum_sq`,
   `rank_trace_defect`): for any square `A` over a commutative ring,
   `2c·tr A − ‖A‖²_F = |n|·c² − ‖c·1 − A‖²_F`; for a real symmetric `A` with eigenvalues `λ_i`,
   `‖A‖²_F = tr(A²) = Σ λ_i²` and `tr A = Σ λ_i`, so the defect is `Σ_i (c² − (c − λ_i)²)`. The
   defect at a shift `c` is read from the entries, without computing the spectrum.

The computational object is the helical pair interaction read through its constitution: `A` is the
material law a coholon meets, `P` the incidence through which a receiver reads it, and the indices
count the storage directions of each sign that survive the reading. Of the winding guide's six
general objects this touches faces and placement (a pull-back is a placement of the form) and the
pair (`PᵀAP` is the pair-rate form's shape); the helix, the cell holonomy, the tube and the tower
thread stay attached.

Consumers: the atlas rows `inertia.pullback-bound` and `inertia.rank-trace-defect`, and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Holon.Inertia

open Matrix Module

/-! ## 1. The indices -/

section Index

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {m n : Type*} [Fintype m] [Fintype n]

/-- [definition] `A` is positive on `W`: `wᵀ A w > 0` for every nonzero `w ∈ W`. -/
def PosOn (A : Matrix n n K) (W : Submodule K (n → K)) : Prop :=
  ∀ w ∈ W, w ≠ 0 → 0 < w ⬝ᵥ (A *ᵥ w)

/-- [definition] The positive index `n₊(A)`: the largest dimension of a subspace on which `A` is
positive. -/
def posIndex (A : Matrix n n K) : ℕ :=
  sSup {d | ∃ W : Submodule K (n → K), PosOn A W ∧ finrank K W = d}

/-- [definition] The negative index `n₋(A) = n₊(−A)`. -/
def negIndex (A : Matrix n n K) : ℕ := posIndex (-A)

theorem posOn_bot (A : Matrix n n K) : PosOn A ⊥ := fun _ hw hw0 =>
  absurd ((Submodule.mem_bot K).mp hw) hw0

theorem bddAbove_index (A : Matrix n n K) :
    BddAbove {d | ∃ W : Submodule K (n → K), PosOn A W ∧ finrank K W = d} := by
  refine ⟨Fintype.card n, fun d ⟨W, _, hd⟩ => ?_⟩
  rw [← hd, ← Module.finrank_fintype_fun_eq_card K]
  exact Submodule.finrank_le W

/-- [proved-standard; formal-checked] A subspace on which `A` is positive has dimension at most
`n₊(A)`. -/
theorem le_posIndex {A : Matrix n n K} {W : Submodule K (n → K)} (h : PosOn A W) :
    finrank K W ≤ posIndex A :=
  le_csSup (bddAbove_index A) ⟨W, h, rfl⟩

theorem posIndex_le {A : Matrix n n K} {d : ℕ}
    (h : ∀ W : Submodule K (n → K), PosOn A W → finrank K W ≤ d) : posIndex A ≤ d :=
  csSup_le ⟨0, ⊥, posOn_bot A, by simp⟩ fun _ ⟨W, hW, hd⟩ => by
    rw [← hd]
    exact h W hW

/-! ## 2. The pull-back bound -/

/-- [proved-standard; formal-checked] `wᵀ(PᵀAP)w = (Pw)ᵀA(Pw)`. -/
theorem quad_pullback (A : Matrix m m K) (P : Matrix m n K) (w : n → K) :
    w ⬝ᵥ ((Pᵀ * A * P) *ᵥ w) = (P *ᵥ w) ⬝ᵥ (A *ᵥ (P *ᵥ w)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec w Pᵀ, vecMul_transpose]

/-- [proved-standard; formal-checked] **The pull-back bound for the positive index**:
`n₊(PᵀAP) ≤ n₊(A)` for `P` of any shape. -/
theorem posIndex_pullback (A : Matrix m m K) (P : Matrix m n K) :
    posIndex (Pᵀ * A * P) ≤ posIndex A := by
  refine posIndex_le fun W hW => ?_
  let f : W →ₗ[K] (m → K) := (mulVecLin P).domRestrict W
  have hfw : ∀ w : W, f w = P *ᵥ (w : n → K) := fun _ => rfl
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hpos := hW w w.2 fun h => hne (Submodule.coe_eq_zero.mp h)
    rw [hfw] at hw
    rw [quad_pullback, hw, mulVec_zero, dotProduct_zero] at hpos
    exact lt_irrefl _ hpos
  have hpos : PosOn A (LinearMap.range f) := by
    intro y hy hne
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hy
    have hw0 : (w : n → K) ≠ 0 := fun h => hne (by rw [hfw, h, mulVec_zero])
    have := hW w w.2 hw0
    rw [quad_pullback] at this
    rw [hfw]
    exact this
  calc finrank K W = finrank K (LinearMap.range f) := (LinearMap.finrank_range_of_inj hf).symm
    _ ≤ posIndex A := le_posIndex hpos

/-- [proved-standard; formal-checked] **The pull-back bound for the negative index**:
`n₋(PᵀAP) ≤ n₋(A)` for `P` of any shape. -/
theorem negIndex_pullback (A : Matrix m m K) (P : Matrix m n K) :
    negIndex (Pᵀ * A * P) ≤ negIndex A := by
  unfold negIndex
  rw [show -(Pᵀ * A * P) = Pᵀ * -A * P by rw [Matrix.mul_neg, Matrix.neg_mul]]
  exact posIndex_pullback (-A) P

/-- [proved-standard; formal-checked] **The kernel lies in the radical**: `Pv = 0` gives
`PᵀAPv = 0`. -/
theorem pullback_mulVec_of_ker (A : Matrix m m K) (P : Matrix m n K) {v : n → K}
    (hv : P *ᵥ v = 0) : (Pᵀ * A * P) *ᵥ v = 0 := by
  rw [← mulVec_mulVec, hv, mulVec_zero]

/-! ## 3. Sylvester's law -/

theorem inv_transpose_pullback [DecidableEq n] (A : Matrix n n K) {P : Matrix n n K}
    (hP : IsUnit P.det) : (P⁻¹)ᵀ * (Pᵀ * A * P) * P⁻¹ = A := by
  have h1 : (P⁻¹)ᵀ * Pᵀ = 1 := by
    rw [← transpose_mul, mul_nonsing_inv P hP, transpose_one]
  calc (P⁻¹)ᵀ * (Pᵀ * A * P) * P⁻¹ = ((P⁻¹)ᵀ * Pᵀ) * A * (P * P⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [h1, mul_nonsing_inv P hP, Matrix.one_mul, Matrix.mul_one]

/-- [proved-standard; formal-checked] **Sylvester's law of inertia, positive index**: an invertible
change of basis keeps `n₊`. -/
theorem posIndex_congr [DecidableEq n] (A : Matrix n n K) {P : Matrix n n K}
    (hP : IsUnit P.det) : posIndex (Pᵀ * A * P) = posIndex A := by
  refine le_antisymm (posIndex_pullback A P) ?_
  have h := posIndex_pullback (Pᵀ * A * P) P⁻¹
  rwa [inv_transpose_pullback A hP] at h

/-- [proved-standard; formal-checked] **Sylvester's law of inertia, negative index**. -/
theorem negIndex_congr [DecidableEq n] (A : Matrix n n K) {P : Matrix n n K}
    (hP : IsUnit P.det) : negIndex (Pᵀ * A * P) = negIndex A := by
  refine le_antisymm (negIndex_pullback A P) ?_
  have h := negIndex_pullback (Pᵀ * A * P) P⁻¹
  rwa [inv_transpose_pullback A hP] at h

/-! ## 4. A rank-one collapse loses both signs -/

theorem posIndex_zero : posIndex (0 : Matrix n n K) = 0 := by
  refine Nat.eq_zero_of_le_zero (posIndex_le fun W hW => ?_)
  rw [Nat.le_zero, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
  intro w hw
  by_contra h
  have := hW w hw h
  simp at this

theorem negIndex_zero : negIndex (0 : Matrix n n K) = 0 := by
  rw [negIndex, neg_zero, posIndex_zero]

/-- [definition] The form `diag(1, −1)`. -/
def splitForm : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -1]

/-- [definition] The rank-one map `[[1, 1], [1, 1]]`. -/
def collapse : Matrix (Fin 2) (Fin 2) K := !![1, 1; 1, 1]

/-- [counterexample; formal-checked] `A = diag(1, −1)`, `P = [[1, 1], [1, 1]]`: `PᵀAP = 0`. -/
theorem collapse_example : (collapse : Matrix (Fin 2) (Fin 2) K)ᵀ * splitForm * collapse = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [collapse, splitForm, Matrix.mul_apply, Fin.sum_univ_two]

theorem one_le_posIndex_example : 1 ≤ posIndex (splitForm : Matrix (Fin 2) (Fin 2) K) := by
  have hv : (Pi.single 0 1 : Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  rw [← finrank_span_singleton hv]
  refine le_posIndex fun w hw hw0 => ?_
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hw0
  have e : (a • Pi.single 0 1 : Fin 2 → K) ⬝ᵥ
      ((splitForm : Matrix (Fin 2) (Fin 2) K) *ᵥ (a • Pi.single 0 1)) = a * a := by
    simp [splitForm, dotProduct, mulVec, Fin.sum_univ_two]
  rw [e]
  exact mul_self_pos.mpr ha

theorem one_le_negIndex_example : 1 ≤ negIndex (splitForm : Matrix (Fin 2) (Fin 2) K) := by
  have hv : (Pi.single 1 1 : Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  rw [negIndex, ← finrank_span_singleton hv]
  refine le_posIndex fun w hw hw0 => ?_
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hw0
  have e : (a • Pi.single 1 1 : Fin 2 → K) ⬝ᵥ
      ((-splitForm : Matrix (Fin 2) (Fin 2) K) *ᵥ (a • Pi.single 1 1)) = a * a := by
    simp [splitForm, dotProduct, mulVec, Fin.sum_univ_two]
  rw [e]
  exact mul_self_pos.mpr ha

/-- [counterexample; formal-checked] **The collapse drops both indices**: `PᵀAP = 0` has
`n₊ = n₋ = 0`, while `A = diag(1, −1)` has `n₊ ≥ 1` and `n₋ ≥ 1`. -/
theorem collapse_drops_both :
    posIndex ((collapse : Matrix (Fin 2) (Fin 2) K)ᵀ * splitForm * collapse) <
        posIndex (splitForm : Matrix (Fin 2) (Fin 2) K) ∧
      negIndex ((collapse : Matrix (Fin 2) (Fin 2) K)ᵀ * splitForm * collapse) <
        negIndex (splitForm : Matrix (Fin 2) (Fin 2) K) := by
  rw [collapse_example, posIndex_zero, negIndex_zero]
  exact ⟨one_le_posIndex_example, one_le_negIndex_example⟩

end Index

/-! ## 5. The rank–trace defect -/

section Defect

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-standard; formal-checked] **The defect at a shift, read from the entries**: for any
square `A` over a commutative ring, `2c·tr A − ‖A‖²_F = |n|·c² − ‖c·1 − A‖²_F`. -/
theorem defect_shift {R : Type*} [CommRing R] (A : Matrix n n R) (c : R) :
    2 * c * A.trace - ∑ i, ∑ j, A i j ^ 2 =
      Fintype.card n * c ^ 2 - ∑ i, ∑ j, (c • (1 : Matrix n n R) - A) i j ^ 2 := by
  have hrow : ∀ i, ∑ j, (c • (1 : Matrix n n R) - A) i j ^ 2 =
      c ^ 2 - 2 * c * A i i + ∑ j, A i j ^ 2 := by
    intro i
    have e : ∀ j, (c • (1 : Matrix n n R) - A) i j ^ 2 =
        (if i = j then c ^ 2 - 2 * c * A i i else 0) + A i j ^ 2 := by
      intro j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        ring
      · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul,
          mul_zero, zero_sub, neg_sq, if_neg hij, zero_add]
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i)]
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Matrix.trace, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  simp only [Matrix.diag]
  ring

/-- [proved-standard; formal-checked] For a real symmetric `A`, `‖A‖²_F = tr(A²)`. -/
theorem frobenius_sq_eq_trace (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    ∑ i, ∑ j, A i j ^ 2 = (A * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := hA.apply i j
  rw [star_trivial] at h
  rw [sq, h]

/-- [proved-standard; formal-checked] For a real symmetric `A` with eigenvalues `λ_i`,
`tr(A²) = Σ λ_i²` (the spectral theorem). -/
theorem trace_mul_self_eq_sum_sq (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
  have h2 : A * A = conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues : n → ℝ) *
        diagonal (RCLike.ofReal ∘ hA.eigenvalues : n → ℝ)) := by
    rw [map_mul, ← hA.spectral_theorem]
  rw [h2, conjStarAlgAut_apply, trace_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul,
    diagonal_mul_diagonal, trace_diagonal]
  simp [sq, RCLike.ofReal_real_eq_id]

/-- [proved-standard; formal-checked] **The rank–trace defect**: for a real symmetric `A` with
eigenvalues `λ_i` and any shift `c`, `2c·tr A − ‖A‖²_F = Σ_i (c² − (c − λ_i)²)`. -/
theorem rank_trace_defect (A : Matrix n n ℝ) (hA : A.IsHermitian) (c : ℝ) :
    2 * c * A.trace - ∑ i, ∑ j, A i j ^ 2 = ∑ i, (c ^ 2 - (c - hA.eigenvalues i) ^ 2) := by
  rw [frobenius_sq_eq_trace A hA, trace_mul_self_eq_sum_sq A hA, hA.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Defect

end Holonics.Holon.Inertia
