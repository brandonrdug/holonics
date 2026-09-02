import ElementaryHolonics.Millennium.HolonicYangMillsFlow

/-!
# The local Yang--Mills energy identity

Under an ad-invariant pairing `B` on the algebra, `B([a, x], y) + B(x, [a, y]) = 0`, the covariant
derivative is metric: `∂_i B(X, Y) = B(D_i X, Y) + B(X, D_i Y)`.  Along the Yang--Mills direction
`G_j = Σ_k D_k F_kj` the pairing of the first variation of curvature with the curvature is then

```text
Σ_{ij} B((D_A G)_ij, F_ij) = 2 Σ_{ij} ∂_i B(G_j, F_ij) − 2 Σ_j B(G_j, G_j) :
```

a divergence minus twice the squared flow direction, pointwise.  On a base without boundary the
divergence integrates to zero and the Yang--Mills energy decreases exactly by the squared flow.
No integration is used here; the identity is exact at every point.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.HolonicYangMillsEnergy

open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation
open Soma.Holonics.Millennium.HolonicYangMillsFlow

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- An ad-invariant pairing on the algebra. -/
structure InvariantPairing (𝔤 : Type*) [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤] where
  B : 𝔤 →L[ℝ] 𝔤 →L[ℝ] ℝ
  invariant : ∀ a x y, B (bracket a x) y + B x (bracket a y) = 0

/-- The differential of a pairing of sections. -/
theorem differential_pairing (P : InvariantPairing 𝔤) {X Y : Base n → 𝔤} {x : Base n}
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) (i : Fin n) :
    differential i (fun y => P.B (X y) (Y y)) x =
      P.B (differential i X x) (Y x) + P.B (X x) (differential i Y x) := by
  have h : HasFDerivAt (fun y => P.B (X y) (Y y)) _ x :=
    (P.B.hasFDerivAt.comp x hX.hasFDerivAt).clm_apply hY.hasFDerivAt
  rw [differential_eq_hasFDerivAt h i]
  simp [differential, add_comm]

/-- **The covariant derivative is metric** for an ad-invariant pairing. -/
theorem differential_pairing_eq_covariant (P : InvariantPairing 𝔤) (A : Connection n 𝔤)
    (i : Fin n) {X Y : Base n → 𝔤} {x : Base n} (hX : DifferentiableAt ℝ X x)
    (hY : DifferentiableAt ℝ Y x) :
    differential i (fun y => P.B (X y) (Y y)) x =
      P.B (covariantDerivative A i X x) (Y x) + P.B (X x) (covariantDerivative A i Y x) := by
  rw [differential_pairing P hX hY i]
  simp only [covariantDerivative, map_add, add_apply]
  have := P.invariant (A i x) (X x) (Y x)
  linarith

/-- **The local energy identity along the Yang--Mills direction.** -/
theorem sum_pairing_covariantVariation_yangMillsDirection (P : InvariantPairing 𝔤)
    (A : Connection n 𝔤) (hA : ∀ i, ContDiff ℝ 3 (A i)) (x : Base n) :
    ∑ i, ∑ j, P.B (covariantVariation A (yangMillsDirection A) i j x) (curvature A i j x) =
      2 * (∑ i, ∑ j, differential i
          (fun y => P.B (yangMillsDirection A j y) (curvature A i j y)) x) -
        2 * ∑ j, P.B (yangMillsDirection A j x) (yangMillsDirection A j x) := by
  have hA2 : ∀ i, ContDiff ℝ 2 (A i) := fun i => (hA i).of_le (by norm_num)
  have hF2 : ∀ k l, ContDiff ℝ 2 (curvature A k l) := fun k l => contDiff_curvature A hA k l
  have hF1 : ∀ k l (y : Base n), DifferentiableAt ℝ (curvature A k l) y :=
    fun k l y => differentiableAt_of_contDiff (hF2 k l) y
  have hDF1 : ∀ l k m (y : Base n),
      DifferentiableAt ℝ (covariantDerivative A l (curvature A k m)) y :=
    fun l k m y =>
      differentiableAt_of_contDiff_one (contDiff_covariantDerivative A hA2 (hF2 k m) l) y
  have hG1 : ∀ j (y : Base n), DifferentiableAt ℝ (yangMillsDirection A j) y := by
    intro j y
    unfold yangMillsDirection
    have hfun : (fun x => ∑ k, covariantDerivative A k (curvature A k j) x) =
        ∑ k, covariantDerivative A k (curvature A k j) := by
      funext z
      simp [Finset.sum_apply]
    rw [hfun]
    exact (HasFDerivAt.sum (u := Finset.univ) fun k _ => (hDF1 k k j y).hasFDerivAt).differentiableAt
  -- the swapped double sum is the negative of the direct one
  have hswap : ∑ i, ∑ j, P.B (covariantDerivative A j (yangMillsDirection A i) x)
      (curvature A i j x) =
      -∑ i, ∑ j, P.B (covariantDerivative A i (yangMillsDirection A j) x) (curvature A i j x) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [curvature_antisymm A i j x, map_neg, neg_neg]
  -- metric compatibility termwise
  have hmetric : ∀ i j, P.B (covariantDerivative A i (yangMillsDirection A j) x) (curvature A i j x) =
      differential i (fun y => P.B (yangMillsDirection A j y) (curvature A i j y)) x -
        P.B (yangMillsDirection A j x) (covariantDerivative A i (curvature A i j) x) := by
    intro i j
    rw [differential_pairing_eq_covariant P A i (hG1 j x) (hF1 i j x)]
    ring
  -- the inner sum of the second term is the squared direction
  have hsq : ∀ j, ∑ i, P.B (yangMillsDirection A j x) (covariantDerivative A i (curvature A i j) x) =
      P.B (yangMillsDirection A j x) (yangMillsDirection A j x) := by
    intro j
    rw [← map_sum]
    rfl
  -- assemble
  have hexpand : ∑ i, ∑ j, P.B (covariantVariation A (yangMillsDirection A) i j x) (curvature A i j x) =
      (∑ i, ∑ j, P.B (covariantDerivative A i (yangMillsDirection A j) x) (curvature A i j x)) -
        ∑ i, ∑ j, P.B (covariantDerivative A j (yangMillsDirection A i) x) (curvature A i j x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [covariantVariation, map_sub, sub_apply]
  have hmain : ∑ i, ∑ j, P.B (covariantDerivative A i (yangMillsDirection A j) x) (curvature A i j x) =
      (∑ i, ∑ j, differential i (fun y => P.B (yangMillsDirection A j y) (curvature A i j y)) x) -
        ∑ j, P.B (yangMillsDirection A j x) (yangMillsDirection A j x) := by
    simp only [hmetric, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => P.B (yangMillsDirection A j x)
      (covariantDerivative A i (curvature A i j) x))]
    simp only [hsq]
  rw [hexpand, hswap, hmain]
  ring

section Audit

#print axioms differential_pairing_eq_covariant
#print axioms sum_pairing_covariantVariation_yangMillsDirection

end Audit

end Soma.Holonics.Millennium.HolonicYangMillsEnergy
