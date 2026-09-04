import ElementaryHolonics.Millennium.HolonicConnectionVariation

/-!
# The Yang--Mills flow direction and the Weitzenböck evolution of curvature

The Yang--Mills flow moves a connection in the direction `G_j = Σ_k D_k F_{kj}`.  By the first
variation of curvature, the curvature then moves at first order by `(D_A G)_ij`, and the Bianchi
and Ricci identities expand this into the covariant Laplacian plus commutators:

```text
(D_A G)_ij = Σ_k ( D_k D_k F_ij + [F_ik, F_kj] + [F_ik, F_kj] ).
```

Every step is a pointwise identity for a `C³` connection.  In the holonic reading the flow is the
gradient descent of the face defect, and the evolution says that the defect diffuses through the
covariant Laplacian and interacts with itself only through the commutator of adjacent faces.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.HolonicYangMillsFlow

open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-! ## Smoothness bookkeeping -/

theorem contDiff_differential {f : Base n → 𝔤} {m : ℕ} (hf : ContDiff ℝ (m + 1) f) (i : Fin n) :
    ContDiff ℝ m (differential i f) := by
  have h := hf.fderiv_right (m := m) (by norm_cast)
  exact h.clm_apply contDiff_const

theorem contDiff_bracket {f g : Base n → 𝔤} {m : ℕ} (hf : ContDiff ℝ m f) (hg : ContDiff ℝ m g) :
    ContDiff ℝ m (fun x => bracket (f x) (g x)) := by
  simp only [bracket]
  exact (hf.mul hg).sub (hg.mul hf)

theorem contDiff_curvature (A : Connection n 𝔤) {m : ℕ} (hA : ∀ i, ContDiff ℝ (m + 1) (A i))
    (i j : Fin n) : ContDiff ℝ m (curvature A i j) := by
  have hi : ContDiff ℝ m (A i) := (hA i).of_le (by exact_mod_cast Nat.le_succ m)
  have hj : ContDiff ℝ m (A j) := (hA j).of_le (by exact_mod_cast Nat.le_succ m)
  exact ((contDiff_differential (hA j) i).sub (contDiff_differential (hA i) j)).add
    (contDiff_bracket hi hj)

theorem contDiff_covariantDerivative (A : Connection n 𝔤) {m : ℕ}
    (hA : ∀ i, ContDiff ℝ (m + 1) (A i)) {X : Base n → 𝔤} (hX : ContDiff ℝ (m + 1) X)
    (i : Fin n) : ContDiff ℝ m (covariantDerivative A i X) := by
  have hi : ContDiff ℝ m (A i) := (hA i).of_le (by exact_mod_cast Nat.le_succ m)
  have hX' : ContDiff ℝ m X := hX.of_le (by exact_mod_cast Nat.le_succ m)
  exact (contDiff_differential hX i).add (contDiff_bracket hi hX')

theorem differentiableAt_of_contDiff_one {f : Base n → 𝔤} (hf : ContDiff ℝ 1 f) (x : Base n) :
    DifferentiableAt ℝ f x :=
  (hf.differentiable (by norm_num)).differentiableAt

/-! ## Linearity of the covariant derivative -/

theorem covariantDerivative_neg_sub (A : Connection n 𝔤) (i : Fin n) {X Y : Base n → 𝔤}
    {x : Base n} (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) :
    covariantDerivative A i (fun y => -X y - Y y) x =
      -covariantDerivative A i X x - covariantDerivative A i Y x := by
  simp only [covariantDerivative]
  have h : differential i (fun y => -X y - Y y) x = (-fderiv ℝ X x - fderiv ℝ Y x) (direction i) :=
    differential_eq_hasFDerivAt (hX.hasFDerivAt.neg.sub hY.hasFDerivAt) i
  rw [h]
  simp only [differential, sub_apply, neg_apply, bracket]
  noncomm_ring

theorem covariantDerivative_neg (A : Connection n 𝔤) (i : Fin n) {X : Base n → 𝔤} {x : Base n}
    (hX : DifferentiableAt ℝ X x) :
    covariantDerivative A i (fun y => -X y) x = -covariantDerivative A i X x := by
  simp only [covariantDerivative]
  have h : differential i (fun y => -X y) x = (-fderiv ℝ X x) (direction i) :=
    differential_eq_hasFDerivAt hX.hasFDerivAt.neg i
  rw [h]
  simp only [differential, neg_apply, bracket]
  noncomm_ring

theorem covariantDerivative_finsetSum (A : Connection n 𝔤) (i : Fin n) {ι : Type*}
    (s : Finset ι) (X : ι → Base n → 𝔤) {x : Base n} (hX : ∀ k, DifferentiableAt ℝ (X k) x) :
    covariantDerivative A i (fun y => ∑ k ∈ s, X k y) x =
      ∑ k ∈ s, covariantDerivative A i (X k) x := by
  simp only [covariantDerivative]
  have hfun : (fun y => ∑ k ∈ s, X k y) = ∑ k ∈ s, X k := by
    funext y
    simp [Finset.sum_apply]
  rw [hfun]
  have h := differential_eq_hasFDerivAt (HasFDerivAt.sum (u := s) fun k _ => (hX k).hasFDerivAt) i
  rw [h]
  simp only [differential, sum_apply, bracket, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-! ## The flow direction and the Weitzenböck evolution -/

/-- The Yang--Mills flow direction `G_j = Σ_k D_k F_{kj}`. -/
def yangMillsDirection (A : Connection n 𝔤) (j : Fin n) : Base n → 𝔤 :=
  fun x => ∑ k, covariantDerivative A k (curvature A k j) x

/-- **The Weitzenböck evolution**: along the Yang--Mills direction the curvature moves by its
covariant Laplacian plus twice the commutator of adjacent faces. -/
theorem covariantVariation_yangMillsDirection (A : Connection n 𝔤)
    (hA : ∀ i, ContDiff ℝ 3 (A i)) (i j : Fin n) (x : Base n) :
    covariantVariation A (yangMillsDirection A) i j x =
      ∑ k, (covariantDerivative A k (covariantDerivative A k (curvature A i j)) x +
        (bracket (curvature A i k x) (curvature A k j x) +
          bracket (curvature A i k x) (curvature A k j x))) := by
  have hA2 : ∀ i, ContDiff ℝ 2 (A i) := fun i => (hA i).of_le (by norm_num)
  have hA1 : ∀ i x, DifferentiableAt ℝ (A i) x := fun i x => differentiableAt_of_contDiff (hA2 i) x
  have hF2 : ∀ k l, ContDiff ℝ 2 (curvature A k l) := fun k l => contDiff_curvature A hA k l
  have hDF1 : ∀ l k m (y : Base n), DifferentiableAt ℝ (covariantDerivative A l (curvature A k m)) y :=
    fun l k m y => differentiableAt_of_contDiff_one (contDiff_covariantDerivative A hA2 (hF2 k m) l) y
  -- Bianchi as identities of sections
  have hB : ∀ a b c, covariantDerivative A a (curvature A b c) =
      fun y => -covariantDerivative A b (curvature A c a) y - covariantDerivative A c (curvature A a b) y := by
    intro a b c
    funext y
    have h := bianchi A hA2 a b c y
    calc covariantDerivative A a (curvature A b c) y
        = covariantDerivative A a (curvature A b c) y +
          (covariantDerivative A b (curvature A c a) y + covariantDerivative A c (curvature A a b) y) -
          (covariantDerivative A b (curvature A c a) y + covariantDerivative A c (curvature A a b) y) := by
          abel
      _ = _ := by rw [← add_assoc, h]; abel
  -- antisymmetry as identities of sections
  have hAnti : ∀ a b, curvature A b a = fun y => -curvature A a b y := by
    intro a b
    funext y
    exact curvature_antisymm A a b y
  have hDanti : ∀ l a b, covariantDerivative A l (curvature A b a) =
      fun y => -covariantDerivative A l (curvature A a b) y := by
    intro l a b
    funext y
    rw [hAnti a b]
    exact covariantDerivative_neg A l (differentiableAt_of_contDiff (hF2 a b) y)
  unfold covariantVariation yangMillsDirection
  rw [covariantDerivative_finsetSum A i Finset.univ _ (fun k => hDF1 k k j x),
    covariantDerivative_finsetSum A j Finset.univ _ (fun k => hDF1 k k i x),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- Ricci on both orders
  have e1 := ricci A hA1 (curvature A k j) (hF2 k j) i k x
  have e4 := ricci A hA1 (curvature A k i) (hF2 k i) j k x
  -- D_k D_i F_kj  and  D_k D_j F_ki through Bianchi
  have e2 : covariantDerivative A k (covariantDerivative A i (curvature A k j)) x =
      -covariantDerivative A k (covariantDerivative A k (curvature A j i)) x -
        covariantDerivative A k (covariantDerivative A j (curvature A i k)) x := by
    rw [hB i k j]
    exact covariantDerivative_neg_sub A k (hDF1 k j i x) (hDF1 j i k x)
  have e5 : covariantDerivative A k (covariantDerivative A j (curvature A k i)) x =
      -covariantDerivative A k (covariantDerivative A k (curvature A i j)) x -
        covariantDerivative A k (covariantDerivative A i (curvature A j k)) x := by
    rw [hB j k i]
    exact covariantDerivative_neg_sub A k (hDF1 k i j x) (hDF1 i j k x)
  -- D_k D_k F_ji = − D_k D_k F_ij
  have e3 : covariantDerivative A k (covariantDerivative A k (curvature A j i)) x =
      -covariantDerivative A k (covariantDerivative A k (curvature A i j)) x := by
    rw [hDanti k i j]
    exact covariantDerivative_neg A k (hDF1 k i j x)
  -- D_k D_i F_jk − D_k D_j F_ik = − D_k D_k F_ij
  have e6 : covariantDerivative A k (covariantDerivative A i (curvature A j k)) x -
      covariantDerivative A k (covariantDerivative A j (curvature A i k)) x =
      -covariantDerivative A k (covariantDerivative A k (curvature A i j)) x := by
    have hfun : covariantDerivative A i (curvature A j k) =
        fun y => -covariantDerivative A j (curvature A k i) y - covariantDerivative A k (curvature A i j) y :=
      hB i j k
    have hfun' : covariantDerivative A j (curvature A k i) =
        fun y => -covariantDerivative A j (curvature A i k) y := hDanti j i k
    rw [hfun, covariantDerivative_neg_sub A k (hDF1 j k i x) (hDF1 k i j x), hfun',
      covariantDerivative_neg A k (hDF1 j i k x)]
    abel
  -- the commutators
  have e7 : bracket (curvature A j k x) (curvature A k i x) =
      -bracket (curvature A i k x) (curvature A k j x) := by
    rw [curvature_antisymm A k j, curvature_antisymm A i k]
    simp only [bracket]
    noncomm_ring
  have e1' : covariantDerivative A i (covariantDerivative A k (curvature A k j)) x =
      covariantDerivative A k (covariantDerivative A i (curvature A k j)) x +
        bracket (curvature A i k x) (curvature A k j x) := sub_eq_iff_eq_add'.mp e1
  have e4' : covariantDerivative A j (covariantDerivative A k (curvature A k i)) x =
      covariantDerivative A k (covariantDerivative A j (curvature A k i)) x +
        bracket (curvature A j k x) (curvature A k i x) := sub_eq_iff_eq_add'.mp e4
  have e6' : covariantDerivative A k (covariantDerivative A i (curvature A j k)) x =
      -covariantDerivative A k (covariantDerivative A k (curvature A i j)) x +
        covariantDerivative A k (covariantDerivative A j (curvature A i k)) x :=
    sub_eq_iff_eq_add.mp e6
  rw [e1', e4', e2, e5, e3, e7, e6']
  abel

section Audit

#print axioms covariantVariation_yangMillsDirection

end Audit

end Soma.Holonics.Millennium.HolonicYangMillsFlow
