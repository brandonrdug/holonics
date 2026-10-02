import Holonics.Holon.Law
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

/-!
# Holon.Law.Fisher: the locks' Fisher form on a move's plane

[definition] The owed statement of the October 1 record
`THE_MOVES_METRIC_IS_ITS_WITNESSS_THE_LOCKS_FISHER_FORM_ON_THE_MOVES_PLANE` (§2; #62). Each lock
`j` reads its sheets through the normalized face `θ_j`; its log mass has Hessian
`J_θ = diag θ − θθᵀ` (`Holon/Law.softmaxJacobian`). A plane of moves `τ` (the record's unit move of
`E` and the modulus `ρ`) changes lock `j`'s log readings by `D_j v`, the resting sheet's row zero.
The locks join by direct sum:

```text
G = Σ_j D_jᵀ J_θj D_j,     g = Σ_j D_jᵀ (θ_j − e_tj),     step = −G⁻¹ g
```

[proved-derived; formal-checked] What is proved.

1. **The variance identity** (`softmaxJacobian_quadratic`, `softmaxJacobian_quadratic_eq_variance`,
   `lockFisher_quadratic`): `vᵀGv = Σ_j Var_θj(D_j v)`. `G` is symmetric (`lockFisher_transpose`)
   and positive semidefinite (`lockFisher_quadratic_nonneg`).
2. **The kernel** (`lockFisher_quadratic_eq_zero_iff`, `lockFisher_mulVec_eq_zero_iff`): with
   positive faces and a resting sheet whose row is zero, `Gv = 0` exactly when every lock reads
   nothing of `v`, `ker G = ∩_j ker D_j`. A variance vanishes exactly on constants
   (`softmaxJacobian_quadratic_eq_zero_iff`), and the resting sheet pins the constant to zero.
3. **The step's domain** (`lockFisher_posDef_iff`, `lockStep_solves`, `lockStep_unique`,
   `lockStep_undetermined`): `G ≻ 0` exactly when no nonzero plane direction is unread by every
   lock; there `−G⁻¹g` is the one solution of `G x = −g`. Where some direction is unread, any
   solution can be moved along it: the step is not determined.
4. **Chart invariance** (`lockFisher_rechart`, `lockScore_rechart`, `lockStep_rechart`,
   `lockStep_reading_rechart`, `reading_rechart`). An invertible change of plane coordinates `S`
   (`D_j ↦ D_j S`) moves `G` to `SᵀGS`, `g` to `Sᵀg` and the step to `S⁻¹·step`: a rescaled plane
   direction rescales its coordinate inversely, and the move each lock reads, `D_j·step`, is
   unchanged. A storage rechart `z′ = Bz` with the covector carried as `B⁻ᵀĝ` leaves every reading
   `⟨ĝ, Δz⟩`, so it leaves `D`, `G`, `g` and the step.

Scope: `G` is the Gauss–Newton (Fisher) pullback, not the comparison's full Hessian, which adds
`Σ_j Σ_x (θ_x − [x = t]) Hess(u_x)`. The Fisher form here is the lock's quadratic measurement of
its readings; it is not a mass.

No `axiom`, no `sorry`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HolonCore

open Matrix

/-! ## 1. The variance identity of `J_θ` -/

section Variance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [proved-derived; formal-checked] `wᵀ J_p w = Σ p w² − (Σ p w)²`. -/
theorem softmaxJacobian_quadratic (p w : ι → ℝ) :
    w ⬝ᵥ (softmaxJacobian p *ᵥ w) = ∑ i, p i * w i ^ 2 - (∑ i, p i * w i) ^ 2 := by
  have h : softmaxJacobian p *ᵥ w = fun i => p i * w i - p i * ∑ j, p j * w j := by
    funext i
    simp [softmaxJacobian, mulVec, dotProduct, Matrix.sub_apply, Matrix.diagonal_apply,
      Matrix.vecMulVec_apply, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [h]
  simp only [dotProduct, mul_sub, Finset.sum_sub_distrib, sq]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- [proved-derived; formal-checked] **On the simplex `wᵀ J_p w` is the variance of `w` under
`p`.** -/
theorem softmaxJacobian_quadratic_eq_variance (p w : ι → ℝ) (h1 : ∑ i, p i = 1) :
    w ⬝ᵥ (softmaxJacobian p *ᵥ w) = ∑ i, p i * (w i - ∑ j, p j * w j) ^ 2 := by
  rw [softmaxJacobian_quadratic]
  set m := ∑ j, p j * w j
  have : ∑ i, p i * (w i - m) ^ 2 = ∑ i, p i * w i ^ 2 - 2 * m * m + m ^ 2 * ∑ i, p i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this, h1]
  ring

theorem softmaxJacobian_quadratic_nonneg (p w : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    0 ≤ w ⬝ᵥ (softmaxJacobian p *ᵥ w) := by
  rw [softmaxJacobian_quadratic_eq_variance p w h1]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)

/-- [proved-derived; formal-checked] **A variance vanishes exactly on constants** (positive face). -/
theorem softmaxJacobian_quadratic_eq_zero_iff (p w : ι → ℝ) (hp : ∀ i, 0 < p i)
    (h1 : ∑ i, p i = 1) :
    w ⬝ᵥ (softmaxJacobian p *ᵥ w) = 0 ↔ ∀ i j, w i = w j := by
  rw [softmaxJacobian_quadratic_eq_variance p w h1]
  set m := ∑ j, p j * w j with hm
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hp i).le (sq_nonneg (w i - m)))).1 h
    have hw : ∀ i, w i = m := by
      intro i
      have := hz i (Finset.mem_univ i)
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 (hp i).ne'
      · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
    intro i j
    rw [hw i, hw j]
  · intro hw
    obtain ⟨i₀⟩ : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at h1
    have hmw : m = w i₀ := by
      rw [hm]
      calc ∑ j, p j * w j = ∑ j, p j * w i₀ := Finset.sum_congr rfl fun j _ => by rw [hw j i₀]
        _ = w i₀ := by rw [← Finset.sum_mul, h1, one_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hmw, hw i i₀, sub_self]
    ring

end Variance

/-! ## 2. The locks joined on a move's plane -/

section Lock

variable {κ τ : Type*} [Fintype κ] [Fintype τ] [DecidableEq τ] {σ : κ → Type*}
  [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]

/-- [definition] **The locks' Fisher form on the plane `τ`**: `G = Σ_j D_jᵀ J_θj D_j`. -/
def lockFisher (θ : ∀ j, σ j → ℝ) (D : ∀ j, Matrix (σ j) τ ℝ) : Matrix τ τ ℝ :=
  ∑ j, (D j)ᵀ * softmaxJacobian (θ j) * D j

/-- [definition] **The locks' score on the plane**: `g = Σ_j D_jᵀ (θ_j − e_tj)`, `t_j` the lock's
target sheet. -/
def lockScore (θ : ∀ j, σ j → ℝ) (t : ∀ j, σ j) (D : ∀ j, Matrix (σ j) τ ℝ) : τ → ℝ :=
  ∑ j, (D j)ᵀ *ᵥ (θ j - Pi.single (t j) 1)

/-- [definition] **The step** `−G⁻¹ g`. It is the step only where `G ≻ 0` (`lockStep_solves`). -/
def lockStep (θ : ∀ j, σ j → ℝ) (t : ∀ j, σ j) (D : ∀ j, Matrix (σ j) τ ℝ) : τ → ℝ :=
  -((lockFisher θ D)⁻¹ *ᵥ lockScore θ t D)

theorem lockFisher_transpose (θ : ∀ j, σ j → ℝ) (D : ∀ j, Matrix (σ j) τ ℝ) :
    (lockFisher θ D)ᵀ = lockFisher θ D := by
  simp only [lockFisher, transpose_sum, transpose_mul, transpose_transpose,
    softmaxJacobian_transpose, Matrix.mul_assoc]

/-- [proved-derived; formal-checked] **The variance identity.** `vᵀ G v = Σ_j (D_j v)ᵀ J_θj (D_j v)`,
the sum over locks of the variance of the log readings `D_j v` (`softmaxJacobian_quadratic_eq_variance`). -/
theorem lockFisher_quadratic (θ : ∀ j, σ j → ℝ) (D : ∀ j, Matrix (σ j) τ ℝ) (v : τ → ℝ) :
    v ⬝ᵥ (lockFisher θ D *ᵥ v) =
      ∑ j, (D j *ᵥ v) ⬝ᵥ (softmaxJacobian (θ j) *ᵥ (D j *ᵥ v)) := by
  simp only [lockFisher, sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem lockFisher_quadratic_nonneg (θ : ∀ j, σ j → ℝ) (D : ∀ j, Matrix (σ j) τ ℝ)
    (hθ : ∀ j x, 0 ≤ θ j x) (h1 : ∀ j, ∑ x, θ j x = 1) (v : τ → ℝ) :
    0 ≤ v ⬝ᵥ (lockFisher θ D *ᵥ v) := by
  rw [lockFisher_quadratic]
  exact Finset.sum_nonneg fun j _ => softmaxJacobian_quadratic_nonneg _ _ (hθ j) (h1 j)

/-- [proved-derived; formal-checked] **The kernel of the quadratic form.** With positive faces and
a resting sheet `rest j` whose row is zero, `vᵀGv = 0` exactly when every lock reads nothing of `v`. -/
theorem lockFisher_quadratic_eq_zero_iff (θ : ∀ j, σ j → ℝ) (D : ∀ j, Matrix (σ j) τ ℝ)
    (hθ : ∀ j x, 0 < θ j x) (h1 : ∀ j, ∑ x, θ j x = 1) (rest : ∀ j, σ j)
    (hrest : ∀ j k, D j (rest j) k = 0) (v : τ → ℝ) :
    v ⬝ᵥ (lockFisher θ D *ᵥ v) = 0 ↔ ∀ j, D j *ᵥ v = 0 := by
  rw [lockFisher_quadratic]
  constructor
  · intro h j
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      softmaxJacobian_quadratic_nonneg (θ j) (D j *ᵥ v) (fun x => (hθ j x).le) (h1 j)).1 h j
      (Finset.mem_univ j)
    have hc := (softmaxJacobian_quadratic_eq_zero_iff (θ j) (D j *ᵥ v) (hθ j) (h1 j)).1 hz
    have h0 : (D j *ᵥ v) (rest j) = 0 := by
      simp [mulVec, dotProduct, hrest]
    funext x
    rw [hc x (rest j), h0]
    rfl
  · intro h
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h j]
    simp

/-- [proved-derived; formal-checked] **The kernel**: `G v = 0` exactly when `D_j v = 0` for every
lock, `ker G = ∩_j ker D_j`. -/
theorem lockFisher_mulVec_eq_zero_iff (θ : ∀ j, σ j → ℝ) (D : ∀ j, Matrix (σ j) τ ℝ)
    (hθ : ∀ j x, 0 < θ j x) (h1 : ∀ j, ∑ x, θ j x = 1) (rest : ∀ j, σ j)
    (hrest : ∀ j k, D j (rest j) k = 0) (v : τ → ℝ) :
    lockFisher θ D *ᵥ v = 0 ↔ ∀ j, D j *ᵥ v = 0 := by
  constructor
  · intro h
    refine (lockFisher_quadratic_eq_zero_iff θ D hθ h1 rest hrest v).1 ?_
    rw [h, dotProduct_zero]
  · intro h
    simp only [lockFisher, sum_mulVec]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mulVec_mulVec, h j, mulVec_zero]

/-- [proved-derived; formal-checked] **The step's domain.** `G ≻ 0` exactly when no nonzero plane
direction is unread by every lock. -/
theorem lockFisher_posDef_iff (θ : ∀ j, σ j → ℝ) (D : ∀ j, Matrix (σ j) τ ℝ)
    (hθ : ∀ j x, 0 < θ j x) (h1 : ∀ j, ∑ x, θ j x = 1) (rest : ∀ j, σ j)
    (hrest : ∀ j k, D j (rest j) k = 0) :
    (lockFisher θ D).PosDef ↔ ∀ v : τ → ℝ, (∀ j, D j *ᵥ v = 0) → v = 0 := by
  have hherm : (lockFisher θ D).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, lockFisher_transpose]
  rw [posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨_, hpos⟩ v hv
    by_contra hne
    have := hpos hne
    rw [star_trivial, (lockFisher_quadratic_eq_zero_iff θ D hθ h1 rest hrest v).2 hv] at this
    exact lt_irrefl _ this
  · intro hk
    refine ⟨hherm, fun v hv => ?_⟩
    rw [star_trivial]
    rcases (lockFisher_quadratic_nonneg θ D (fun j x => (hθ j x).le) h1 v).lt_or_eq with h | h
    · exact h
    · exact absurd (hk v ((lockFisher_quadratic_eq_zero_iff θ D hθ h1 rest hrest v).1 h.symm)) hv

/-- [proved-derived; formal-checked] **Where `G ≻ 0` the step solves `G x = −g`.** -/
theorem lockStep_solves (θ : ∀ j, σ j → ℝ) (t : ∀ j, σ j) (D : ∀ j, Matrix (σ j) τ ℝ)
    (hG : (lockFisher θ D).PosDef) :
    lockFisher θ D *ᵥ lockStep θ t D = -lockScore θ t D := by
  have hu : IsUnit (lockFisher θ D).det := (hG.det_pos).ne'.isUnit
  rw [lockStep, mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]

/-- [proved-derived; formal-checked] **…and it is the only solution.** -/
theorem lockStep_unique (θ : ∀ j, σ j → ℝ) (t : ∀ j, σ j) (D : ∀ j, Matrix (σ j) τ ℝ)
    (hG : (lockFisher θ D).PosDef) (x : τ → ℝ) (hx : lockFisher θ D *ᵥ x = -lockScore θ t D) :
    x = lockStep θ t D := by
  have hu : IsUnit (lockFisher θ D).det := (hG.det_pos).ne'.isUnit
  rw [lockStep, ← mulVec_neg, ← hx, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

/-- [proved-derived; formal-checked] **Off the domain the step is undetermined.** If a nonzero
direction `v` is unread by every lock, any solution of `G x = −g` moved along `v` is another. -/
theorem lockStep_undetermined (θ : ∀ j, σ j → ℝ) (t : ∀ j, σ j) (D : ∀ j, Matrix (σ j) τ ℝ)
    (hθ : ∀ j x, 0 < θ j x) (h1 : ∀ j, ∑ x, θ j x = 1) (rest : ∀ j, σ j)
    (hrest : ∀ j k, D j (rest j) k = 0) (v : τ → ℝ) (hv : ∀ j, D j *ᵥ v = 0)
    (x : τ → ℝ) (hx : lockFisher θ D *ᵥ x = -lockScore θ t D) :
    lockFisher θ D *ᵥ (x + v) = -lockScore θ t D := by
  rw [mulVec_add, hx, (lockFisher_mulVec_eq_zero_iff θ D hθ h1 rest hrest v).2 hv, add_zero]

/-! ## 3. Chart invariance -/

/-- [proved-derived; formal-checked] A change of plane coordinates `S` moves `G` to `SᵀGS`. -/
theorem lockFisher_rechart (θ : ∀ j, σ j → ℝ) (D : ∀ j, Matrix (σ j) τ ℝ) (S : Matrix τ τ ℝ) :
    lockFisher θ (fun j => D j * S) = Sᵀ * lockFisher θ D * S := by
  simp only [lockFisher, Finset.mul_sum, Finset.sum_mul, transpose_mul, Matrix.mul_assoc]

/-- [proved-derived; formal-checked] …and `g` to `Sᵀ g`. -/
theorem lockScore_rechart (θ : ∀ j, σ j → ℝ) (t : ∀ j, σ j) (D : ∀ j, Matrix (σ j) τ ℝ)
    (S : Matrix τ τ ℝ) :
    lockScore θ t (fun j => D j * S) = Sᵀ *ᵥ lockScore θ t D := by
  simp only [lockScore, mulVec_sum, transpose_mul, mulVec_mulVec]

/-- [proved-derived; formal-checked] **A rescaled plane direction rescales its coordinate
inversely**: under an invertible `S`, the step becomes `S⁻¹·step`. -/
theorem lockStep_rechart (θ : ∀ j, σ j → ℝ) (t : ∀ j, σ j) (D : ∀ j, Matrix (σ j) τ ℝ)
    (S : Matrix τ τ ℝ) (hS : IsUnit S.det) :
    lockStep θ t (fun j => D j * S) = S⁻¹ *ᵥ lockStep θ t D := by
  have hST : IsUnit Sᵀ.det := by rwa [det_transpose]
  rw [lockStep, lockStep, lockFisher_rechart, lockScore_rechart, mul_inv_rev, mul_inv_rev,
    mulVec_neg, mulVec_mulVec, mulVec_mulVec]
  congr 2
  simp only [Matrix.mul_assoc, nonsing_inv_mul _ hST, Matrix.mul_one]

/-- [proved-derived; formal-checked] **The move each lock reads is chart-free**:
`(D_j S)·step′ = D_j·step`. -/
theorem lockStep_reading_rechart (θ : ∀ j, σ j → ℝ) (t : ∀ j, σ j) (D : ∀ j, Matrix (σ j) τ ℝ)
    (S : Matrix τ τ ℝ) (hS : IsUnit S.det) (j : κ) :
    (D j * S) *ᵥ lockStep θ t (fun j => D j * S) = D j *ᵥ lockStep θ t D := by
  rw [lockStep_rechart θ t D S hS, mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ hS,
    Matrix.mul_one]

/-- [proved-derived; formal-checked] **A storage rechart leaves every reading.** With `z′ = Bz` and
the covector carried as `B⁻ᵀĝ`, `⟨B⁻ᵀĝ, B Δz⟩ = ⟨ĝ, Δz⟩`; the readings `D`, hence `G`, `g` and
the step, do not see the storage chart. -/
theorem reading_rechart {μ : Type*} [Fintype μ] [DecidableEq μ] (B : Matrix μ μ ℝ)
    (hB : IsUnit B.det) (ghat dz : μ → ℝ) :
    ((B⁻¹)ᵀ *ᵥ ghat) ⬝ᵥ (B *ᵥ dz) = ghat ⬝ᵥ dz := by
  rw [dotProduct_mulVec, ← vecMul_transpose, transpose_transpose, vecMul_vecMul,
    nonsing_inv_mul _ hB, vecMul_one]

end Lock

section Audit

#print axioms softmaxJacobian_quadratic
#print axioms softmaxJacobian_quadratic_eq_variance
#print axioms softmaxJacobian_quadratic_eq_zero_iff
#print axioms lockFisher_quadratic
#print axioms lockFisher_quadratic_eq_zero_iff
#print axioms lockFisher_mulVec_eq_zero_iff
#print axioms lockFisher_posDef_iff
#print axioms lockStep_solves
#print axioms lockStep_unique
#print axioms lockStep_undetermined
#print axioms lockFisher_rechart
#print axioms lockScore_rechart
#print axioms lockStep_rechart
#print axioms lockStep_reading_rechart
#print axioms reading_rechart

end Audit

end Holonics.HolonCore
