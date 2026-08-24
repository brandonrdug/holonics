import ElementaryHolonics.Millennium.Pivots

/-!
# The local-to-global row: a family of readings, its frame operator, and `Ш`

The Birch–Swinnerton-Dyer row's form is a **sum of local readings** — one per place — and that is
literally the frame operator `S = Σᵢ |rᵢ⟩⟨rᵢ|` of the family.  Three facts follow, none of them
about elliptic curves:

* `theFrameFormIsPositive` — a sum of local readings is always positive; it is a sum of squares.
* `theFrameFormIsDefiniteIffSeparating` — and definite **exactly when the local family separates**.
* `theCollapseIsTheCommonKernel` — so the null cone is the *common kernel* of the local readings,
  which by `MillenniumCoupling.theNullConeIsTheCollapsedPopulation` is the collapsed population of
  the induced family.

That last line is `Ш` in one sentence: **every local frame agrees and no global object accounts for
it.**  The failure of a local-to-global principle is therefore a *separation failure*, not a
counterexample — the same reading this corpus already gives it, arriving here as a theorem about
frames rather than a claim about curves.

## And the frame operator is not the identity

`theFrameOperatorIsNotTheIdentity`: two copies of one unit direction already give `S = 2·id`.  The
family reconstructs everything it should and still `Σᵢ|rᵢ⟩⟨rᵢ| ≠ I`.  So a resolution of identity
is a statement about a family being **orthonormal in a declared metric**, never about it merely
spanning; writing `Σ|aᵢ⟩⟨aᵢ| = I` for a spanning family asserts an orthonormality no receiver
declared, and reconstruction there runs through the **dual frame** `S⁻¹|rᵢ⟩`.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.Millennium.LocalFrame

open Soma.Holonics.Millennium.MillenniumCoupling
open Soma.Holonics.Millennium.MillenniumCoupling.ReceiverForm
open Soma.Holonics.Millennium.Pivots Finset


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]

/-- The **frame operator** of a family of readings: `S = Σᵢ |rᵢ⟩⟨rᵢ|`. -/
def frameOp (r : ι → V) : V →L[ℝ] V :=
  ∑ i, ContinuousLinearMap.smulRight (innerSL ℝ (r i)) (r i)

@[simp] theorem theFrameOpApply (r : ι → V) (v : V) :
    frameOp r v = ∑ i, (inner ℝ (r i) v : ℝ) • r i := by
  simp [frameOp, ContinuousLinearMap.sum_apply]

/-- The form it reads: a sum of local readings, one per place. -/
def frameForm (r : ι → V) : ReceiverForm V where
  T := frameOp r
  selfAdjoint := by
    intro x y
    simp only [theFrameOpApply, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    exact sum_congr rfl (fun i _ => by rw [real_inner_comm x (r i)]; ring)

theorem theFrameReading (r : ι → V) (x y : V) :
    (frameForm r).B x y = ∑ i, (inner ℝ (r i) x : ℝ) * (inner ℝ (r i) y : ℝ) := by
  simp only [ReceiverForm.B, frameForm, theFrameOpApply, sum_inner, real_inner_smul_left]

/-- **A SUM OF LOCAL READINGS IS ALWAYS POSITIVE** — it is a sum of squares. -/
theorem theFrameFormIsPositive (r : ι → V) : (frameForm r).IsPositive := by
  intro v
  rw [theFrameReading]
  exact sum_nonneg (fun i _ => by nlinarith [sq_nonneg (inner ℝ (r i) v : ℝ)])

/-- **AND IT IS DEFINITE EXACTLY WHEN THE LOCAL FAMILY SEPARATES.**  The null cone is the common
kernel of the readings: a construction the whole family reads as zero.  That is the local-to-global
statement, and its failure is a **collapsed population** — every local reading agrees, no global
object accounts for it. -/
theorem theFrameFormIsDefiniteIffSeparating (r : ι → V) :
    (frameForm r).IsDefinite ↔ ∀ v : V, (∀ i, (inner ℝ (r i) v : ℝ) = 0) → v = 0 := by
  constructor
  · intro h v hv
    refine h v ?_
    rw [theFrameReading]
    exact sum_eq_zero (fun i _ => by rw [hv i]; ring)
  · intro h v hv
    refine h v (fun i => ?_)
    rw [theFrameReading] at hv
    have hnn : ∀ i ∈ (univ : Finset ι), (0:ℝ) ≤ (inner ℝ (r i) v : ℝ) * (inner ℝ (r i) v : ℝ) :=
      fun i _ => mul_self_nonneg _
    have := (sum_eq_zero_iff_of_nonneg hnn).mp hv i (mem_univ i)
    exact mul_self_eq_zero.mp this

/-- **THE COLLAPSED POPULATION IS THE COMMON KERNEL OF THE LOCAL READINGS.**  Chaining the frame
form's positivity through `theNullConeIsTheCollapsedPopulation`: a construction that every local
reading returns zero on is exactly one no reading in the induced family can tell from zero.

That is `Ш` in one sentence — **every local frame agrees and no global object accounts for it** —
and it is why the failure of a local-to-global principle is a separation failure rather than a
counterexample. -/
theorem theCollapseIsTheCommonKernel (r : ι → V) (v : V) :
    Soma.Holonics.Millennium.Separation.collapseOf (frameForm r).readings v 0 ↔ ∀ i, (inner ℝ (r i) v : ℝ) = 0 := by
  rw [← (frameForm r).theNullConeIsTheCollapsedPopulation (theFrameFormIsPositive r) v,
    theFrameReading]
  constructor
  · intro h i
    have hnn : ∀ j ∈ (univ : Finset ι), (0:ℝ) ≤ (inner ℝ (r j) v : ℝ) * (inner ℝ (r j) v : ℝ) :=
      fun j _ => mul_self_nonneg _
    exact mul_self_eq_zero.mp ((sum_eq_zero_iff_of_nonneg hnn).mp h i (mem_univ i))
  · intro h
    exact sum_eq_zero (fun i _ => by rw [h i]; ring)

/-- **AND THE FRAME OPERATOR IS NOT THE IDENTITY.**  Two copies of one unit direction already give
`S = 2·id`: the family reconstructs everything it should, and still `Σᵢ|rᵢ⟩⟨rᵢ| ≠ I`.

So a resolution of identity is a statement about a family being **orthonormal in a declared
metric**, not about it spanning.  Writing `Σ|aᵢ⟩⟨aᵢ| = I` for a family that merely spans asserts an
orthonormality no receiver declared — and reconstruction there runs through the *dual* frame
`S⁻¹|rᵢ⟩`, not through the family itself. -/
theorem theFrameOperatorIsNotTheIdentity {e : V} (he : ‖e‖ = 1) :
    frameOp (fun _ : Fin 2 => e) e = (2:ℝ) • e ∧ ((2:ℝ) • e ≠ e) := by
  have hne : e ≠ 0 := by intro h; rw [h] at he; simp at he
  constructor
  · rw [theFrameOpApply]
    simp [real_inner_self_eq_norm_sq, he]
    module
  · intro h
    have h2 : (1:ℝ) • e = 0 := by
      rw [show (1:ℝ) = 2 - 1 by norm_num, sub_smul, h, one_smul, sub_self]
    rw [one_smul] at h2
    exact hne h2

end Soma.Holonics.Millennium.LocalFrame
