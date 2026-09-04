import ElementaryHolonics.Millennium.Pivots

/-!
# The Hodge pivot, instantiated: one plus, and the minus is the anchor

`hodgeForm e` is `v ↦ 2⟪e,v⟫² − ‖v‖²`, built from any chosen unit direction — the ample class.
Its signature is `(1, n−1)`, and the three facts that matter are all one line each:

* `theAmpleDirectionIsPositive` — the chosen direction returns `+1`.
* `theComplementIsNegativeDefinite` — everything orthogonal to it returns `−‖v‖²`.
* `theNegativePartIsTheAnchor` — **and on that complement the negated form *is* the Euclidean
  inner product.**

The third is the point.  The minus half of the Hodge index signature is not a second phenomenon
needing its own account: it is the anchor of `Pivots`, realized on the primitive part.  **One
realizer carries both halves** — the plus on the ample direction, the minus on everything
orthogonal — which is why the two cannot be separated, and why it is the *ample* class that pays
rather than merely an effective one.

`theHodgeFormIsNotPositive` then refuses positivity the same way `Pivots` refused the hyperbolic
plane: `e + w` and `e − w` are both null and their sum is not, so the null cone is not a subspace.
The two cones cannot merge without passing through zero, and **that split is the invariant** while
which side is called positive is a hand.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.Millennium.HodgeIndex

open Soma.Holonics.Millennium.MillenniumCoupling
open Soma.Holonics.Millennium.MillenniumCoupling.ReceiverForm
open Soma.Holonics.Millennium.Pivots

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Hodge-index operator built from a chosen unit direction: `T v = 2⟪e,v⟫e − v`. -/
def hodgeOp (e : V) : V →L[ℝ] V :=
  (2 : ℝ) • (ContinuousLinearMap.smulRight (innerSL ℝ e) e) - ContinuousLinearMap.id ℝ V

@[simp] theorem theHodgeOpApply (e v : V) : hodgeOp e v = (2 * inner ℝ e v) • e - v := by
  simp [hodgeOp, smul_smul]

/-- The form of signature `(1, n−1)`: one positive direction, everything orthogonal negative. -/
def hodgeForm (e : V) : ReceiverForm V where
  T := hodgeOp e
  selfAdjoint := by
    intro x y
    simp only [theHodgeOpApply, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm x e]
    ring

theorem theHodgeReading (e v : V) :
    (hodgeForm e).B v v = 2 * (inner ℝ e v : ℝ) ^ 2 - ‖v‖ ^ 2 := by
  simp only [ReceiverForm.B, hodgeForm, theHodgeOpApply, inner_sub_left, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq]
  ring

/-- **THE CHOSEN DIRECTION IS POSITIVE** — the ample class. -/
theorem theAmpleDirectionIsPositive {e : V} (he : ‖e‖ = 1) : (hodgeForm e).B e e = 1 := by
  rw [theHodgeReading, real_inner_self_eq_norm_sq, he]
  norm_num

/-- **AND THE FORM IS NEGATIVE DEFINITE ON ITS ORTHOGONAL COMPLEMENT.**  This is the Hodge index
theorem's linear content: signature `(1, ρ−1)`, the ample direction alone carrying the plus. -/
theorem theComplementIsNegativeDefinite {e v : V} (hv : (inner ℝ e v : ℝ) = 0) :
    (hodgeForm e).B v v = -‖v‖ ^ 2 := by
  rw [theHodgeReading, hv]
  ring

/-- **AND ON THAT COMPLEMENT THE NEGATED FORM *IS* THE ANCHOR.**  So the minus half of the Hodge
index signature is not a second phenomenon: it is the Euclidean inner product itself, realized on
the primitive part.  One realizer carries both halves — the plus on the ample direction, the minus
on everything orthogonal to it — which is why the two cannot be separated and why the ample class
is what pays. -/
theorem theNegativePartIsTheAnchor {e v : V} (hv : (inner ℝ e v : ℝ) = 0) :
    (-(hodgeForm e)).B v v = (euclidean V).B v v := by
  rw [theNegReading, theComplementIsNegativeDefinite hv, theEuclideanReading,
    real_inner_self_eq_norm_sq]
  ring

/-- **THE HODGE FORM IS NOT POSITIVE**, whenever there is anything orthogonal to the ample
direction: `e + w` and `e − w` are both null and their sum is not, and a positive form's null cone
is a subspace.  The two cones cannot merge — that is the split, and it is the invariant. -/
theorem theHodgeFormIsNotPositive {e w : V} (he : ‖e‖ = 1) (hw : ‖w‖ = 1)
    (horth : (inner ℝ e w : ℝ) = 0) : ¬ (hodgeForm e).IsPositive := by
  intro hpos
  have hnull : ∀ s : ℝ, s ^ 2 = 1 → (hodgeForm e).B (e + s • w) (e + s • w) = 0 := by
    intro s hs
    have hwe : (inner ℝ w e : ℝ) = 0 := by rw [real_inner_comm]; exact horth
    rw [theHodgeReading, inner_add_right, real_inner_smul_right, horth,
      real_inner_self_eq_norm_sq, he]
    have hn : ‖e + s • w‖ ^ 2 = 1 + s ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_add_self]
      simp only [real_inner_smul_left, real_inner_smul_right, horth, hwe,
        real_inner_self_eq_norm_sq, he, hw]
      rw [norm_smul, Real.norm_eq_abs, hw, mul_one, sq_abs]
      ring
    rw [hn, hs]
    ring
  have h1 := hnull 1 (by norm_num)
  have h2 := hnull (-1) (by norm_num)
  have horth2 := (hodgeForm e).theNullDirectionIsOrthogonal hpos h1 (e + (-1 : ℝ) • w)
  have hval : (hodgeForm e).B (e + (1:ℝ) • w) (e + (-1:ℝ) • w) = 2 := by
    have hwe : (inner ℝ w e : ℝ) = 0 := by rw [real_inner_comm]; exact horth
    simp only [ReceiverForm.B, hodgeForm, theHodgeOpApply, inner_sub_left, real_inner_smul_left,
      inner_add_right, inner_add_left, real_inner_smul_right, inner_neg_right, inner_neg_left,
      horth, hwe, real_inner_self_eq_norm_sq, he, hw, one_smul, neg_one_smul]
    ring
  rw [hval] at horth2
  norm_num at horth2

end Soma.Holonics.Millennium.HodgeIndex
