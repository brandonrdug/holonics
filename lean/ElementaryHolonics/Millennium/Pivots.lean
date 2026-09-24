import ElementaryHolonics.Millennium.MillenniumCoupling

/-!
# The pivots, instantiated: realization causes placement

`Coupling` proves what is shared across the six rows.  This file gives transport something to run
**from**, and the anchor is the plainest object available: **the inner product itself, read as a
receiver form.**  It is coercive with gap one, hence positive, hence definite — and every
positivity result in the frame is a pullback of that single fact.

## Realization causes placement

`theRealizedFormIsDefinite`: a form that is the pullback of an inner product along an injection is
definite.  Placement is not obtained *beside* realization; it is derived from it.  That is the
Castelnuovo shape in its linear shell — an ample class supplies the embedding, and positivity of
the Rosati involution follows rather than being assumed.  The strengthening is where the mass
lives: `theRealizationBoundedBelowGivesTheGap` says a realizer that merely exists gives placement,
while a realizer that is **quantitatively faithful** gives the gap.  Existence versus a bound is
exactly definite versus coercive, one level up.

## The indefinite witness, and it costs no eigenvalue

`hyperbolicForm` is `v₀² − v₁²` — the Hodge index signature `(1,1)` at rank two.  It is refused by
the frame directly: `(1,1)` and `(1,−1)` both return nothing while their sum returns four, and
`Coupling.theNullDirectionIsOrthogonal` says a positive form's null cone **is** a subspace.  So two
null directions with a non-null sum refuse positivity outright — **no eigenvalue computed, no
diagonalisation, no characteristic polynomial.**  The obstruction is read off the cone's failure
to be linear, which is the corpus's own reading: the split is the invariant, and the two cones
cannot merge without passing through zero.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.Millennium.Pivots

open Soma.Holonics.Millennium.MillenniumCoupling
open Soma.Holonics.Millennium.MillenniumCoupling.ReceiverForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The anchor: the inner product itself, read as a receiver form. -/
def euclidean (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] : ReceiverForm V where
  T := ContinuousLinearMap.id ℝ V
  selfAdjoint := fun _ _ => rfl

@[simp] theorem theEuclideanReading (x y : V) : (euclidean V).B x y = inner ℝ x y := rfl

/-- **THE ANCHOR IS COERCIVE, WITH GAP ONE.**  Every transport of positivity in the frame runs
back to this. -/
theorem theEuclideanFormIsCoercive : (euclidean V).IsCoercive := by
  refine ⟨1, one_pos, fun v => ?_⟩
  rw [theEuclideanReading, real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

theorem theEuclideanFormIsPositive : (euclidean V).IsPositive :=
  theGapForcesPositivity _ theEuclideanFormIsCoercive

theorem theEuclideanFormIsDefinite : (euclidean V).IsDefinite :=
  theGapForcesDefiniteness _ theEuclideanFormIsCoercive

/-! ## Realization causes placement -/

section Realization
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **REALIZATION CAUSES PLACEMENT.**  A form that is the pullback of an inner product along an
injection is definite — placement is not obtained beside realization, it is derived from it.
This is the Castelnuovo shape in its linear shell: an ample class supplies the embedding, and
positivity of the Rosati involution follows rather than being assumed. -/
theorem theRealizedFormIsDefinite (G : ReceiverForm W) (f : W →L[ℝ] V)
    (hpres : ∀ x y : W, inner ℝ (f x) (f y) = G.B x y)
    (hinj : ∀ x : W, f x = 0 → x = 0) : G.IsDefinite :=
  theDefinitenessTransports (euclidean V) G f (fun x y => hpres x y) hinj
    theEuclideanFormIsDefinite

/-- The same realization gives positivity. -/
theorem theRealizedFormIsPositive (G : ReceiverForm W) (f : W →L[ℝ] V)
    (hpres : ∀ x y : W, inner ℝ (f x) (f y) = G.B x y) : G.IsPositive :=
  thePositivityTransports (euclidean V) G f (fun x y => hpres x y) theEuclideanFormIsPositive

/-- **AND A REALIZATION BOUNDED BELOW SUPPLIES THE GAP.**  A realizer that merely exists gives
placement; a realizer that is *quantitatively* faithful gives the mass. -/
theorem theRealizationBoundedBelowGivesTheGap (G : ReceiverForm W) (f : W →L[ℝ] V) {c : ℝ}
    (hc : 0 < c) (hbelow : ∀ x : W, c * ‖x‖ ≤ ‖f x‖)
    (hpres : ∀ x y : W, inner ℝ (f x) (f y) = G.B x y) : G.IsCoercive :=
  theGapTransports (euclidean V) G f hc hbelow (fun x y => hpres x y) theEuclideanFormIsCoercive

end Realization

/-! ## The indefinite witness: a null cone that is not a subspace -/

/-- The signature-`(1,1)` operator on the plane — the Hodge index shape in its smallest instance. -/
def hyperbolic : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := WithLp.toLp 2 (fun i => if i = 0 then x.ofLp i else -x.ofLp i)
  map_add' := by
    intro x y; ext i; by_cases h : i = 0 <;> simp [h] <;> ring
  map_smul' := by
    intro c x; ext i; by_cases h : i = 0 <;> simp [h] <;> ring

@[simp] theorem theHyperbolicApply (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (hyperbolic x).ofLp i = if i = 0 then x.ofLp i else -x.ofLp i := rfl

/-- As a receiver form. -/
def hyperbolicForm : ReceiverForm (EuclideanSpace ℝ (Fin 2)) where
  T := LinearMap.toContinuousLinearMap hyperbolic
  selfAdjoint := by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    simp

/-- Its reading is `v₀² − v₁²`. -/
theorem theHyperbolicReading (v : EuclideanSpace ℝ (Fin 2)) :
    hyperbolicForm.B v v = v.ofLp 0 ^ 2 - v.ofLp 1 ^ 2 := by
  rw [ReceiverForm.B, PiLp.inner_apply, Fin.sum_univ_two]
  simp [hyperbolicForm]
  ring

/-- **THE NULL CONE IS NOT A SUBSPACE, SO THE FORM IS NOT POSITIVE.**  `(1,1)` and `(1,−1)` both
return nothing; their sum `(2,0)` returns four.  By `theNullDirectionIsOrthogonal` a positive
form's null cone *is* a subspace, so exhibiting two null directions with a non-null sum refuses
positivity outright — no eigenvalue computed, no diagonalisation. -/
theorem theHyperbolicFormIsNotPositive : ¬ hyperbolicForm.IsPositive := by
  intro hpos
  set u : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 1] with hu
  set w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, -1] with hw
  have hun : hyperbolicForm.B u u = 0 := by rw [theHyperbolicReading]; simp [hu]
  have hwn : hyperbolicForm.B w w = 0 := by rw [theHyperbolicReading]; simp [hw]
  have horth : hyperbolicForm.B u w = 0 :=
    hyperbolicForm.theNullDirectionIsOrthogonal hpos hun w
  have hval : hyperbolicForm.B u w = 2 := by
    rw [ReceiverForm.B, PiLp.inner_apply, Fin.sum_univ_two]
    simp [hyperbolicForm, hu, hw]
    norm_num
  rw [hval] at horth
  norm_num at horth

/-! ## A finer receiver sees what the diagonal cannot -/

/-- A rotation: antisymmetric, hence invisible on the diagonal. -/
def rotate : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := WithLp.toLp 2 (fun i => if i = 0 then x.ofLp 1 else -x.ofLp 0)
  map_add' := by intro x y; ext i; by_cases h : i = 0 <;> simp [h] <;> ring
  map_smul' := by intro c x; ext i; by_cases h : i = 0 <;> simp [h] <;> ring

theorem theRotationIsAntisymmetric (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (rotate x) y = -inner ℝ x (rotate y) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [rotate]

/-- A strictly graded receiver — the finer reading. -/
def graded : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := WithLp.toLp 2 (fun i => if i = 0 then x.ofLp 0 else 2 * x.ofLp 1)
  map_add' := by intro x y; ext i; by_cases h : i = 0 <;> simp [h] <;> ring
  map_smul' := by intro c x; ext i; by_cases h : i = 0 <;> simp [h] <;> ring

/-- **THE ANTISYMMETRIC PART IS INVISIBLE TO ONE RECEIVER AND VISIBLE TO A FINER ONE.**  The
rotation returns nothing against the plain diagonal — that is `theAntisymmetricPartIsInvisible` —
yet returns `−1` against the graded reading at `(1,1)`.

**So whether the nonlinearity is visible is a property of the receiver, not of the term.**  That is
why an energy estimate cannot decide the Navier–Stokes row: `⟪(u·∇)u, u⟫ = 0` is an identity about
the *reading*, and the term that would break regularity sits precisely where that reading is
blind.  Converting an invisible structure into a visible one by grading the receiver is the same
move as phase contrast — the object never changed, the aperture did. -/
theorem theFinerReceiverSeesTheRotation :
    inner ℝ (rotate (WithLp.toLp 2 ![1, 1])) (graded (WithLp.toLp 2 ![1, 1])) = (-1 : ℝ) ∧
      inner ℝ (rotate (WithLp.toLp 2 ![1, 1])) (WithLp.toLp 2 ![1, 1] : EuclideanSpace ℝ (Fin 2))
        = (0 : ℝ) := by
  constructor
  · rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [rotate, graded]
    norm_num
  · exact Soma.Holonics.Millennium.MillenniumCoupling.ReceiverForm.theAntisymmetricPartIsInvisible
      (LinearMap.toContinuousLinearMap rotate) (fun x y => theRotationIsAntisymmetric x y) _

end Soma.Holonics.Millennium.Pivots