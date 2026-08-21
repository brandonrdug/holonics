import ElementaryHolonics.Millennium.Coupling
import ElementaryHolonics.Millennium.Paying

/-!
# The theta complex — a filled cell and a surviving loop at once

Every previous instance had one or the other.  The hollow triangle had a nonzero homology and a
trivial realized population; the filled triangle would have a nonzero realized population and no
homology.  **The theta complex has both**: two vertices joined by three edges, with one of the
three loops filled.

So it is the first object on which the descent criterion holds with a **nonzero** realized
population — the boundary of the filled cell — and the population comes from the complex rather
than being picked by hand.

It also settles something by negation: **the boundary-pullback form vanishes on every cycle**, so
it can never be faithful on a homology.  A form that pays on a homology has to come from somewhere
other than a boundary.

Every `theorem` here is discharged.
-/

namespace Soma.Holonics.Millennium.Theta

open Soma.Holonics.Millennium Soma.Holonics.Millennium.Coupling
open Soma.Holonics.Millennium.Paying

/-- Coefficients on the three edges. -/
abbrev Edges : Type := ℤ × ℤ × ℤ
/-- Coefficients on the two vertices. -/
abbrev Verts : Type := ℤ × ℤ
/-- Coefficients on the single filled cell. -/
abbrev Faces : Type := ℤ

/-- The **edge boundary**.  All three edges run from the first vertex to the second. -/
def d1 : Edges →+ Verts where
  toFun e := (-(e.1 + e.2.1 + e.2.2), e.1 + e.2.1 + e.2.2)
  map_zero' := rfl
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

@[simp] theorem d1_apply (e : Edges) :
    d1 e = (-(e.1 + e.2.1 + e.2.2), e.1 + e.2.1 + e.2.2) := rfl

/-- The **face boundary**: the filled cell spans the first two edges. -/
def d2 : Faces →+ Edges where
  toFun n := (n, -n, 0)
  map_zero' := rfl
  map_add' a b := by
    simp only [Prod.mk_add_mk, neg_add, add_zero]

@[simp] theorem d2_apply (n : Faces) : d2 n = (n, -n, 0) := rfl

/-- **The composite returns nothing** — the boundary of a boundary vanishes. -/
theorem d1_comp_d2 (n : Faces) : d1 (d2 n) = 0 := by
  simp [d1, d2]

/-- The **theta chain**: fill one loop, then take the edge boundary. -/
def thetaChain : TransportChain Faces Edges Verts where
  into := d2
  outOf := d1
  composite_zero := d1_comp_d2

/-! ## Both conditions, on one object -/

/-- **The realized population is not zero.**  The filled cell has a boundary and it is a real
edge chain. -/
theorem theRealizedIsNonzero :
    ((1, -1, 0) : Edges) ∈ thetaChain.realized ∧ ((1, -1, 0) : Edges) ≠ 0 := by
  refine ⟨⟨1, rfl⟩, ?_⟩
  intro h
  exact one_ne_zero (congrArg Prod.fst h)

/-- **And a loop survives it.**  The second and third edges close a cycle that no face fills. -/
theorem theSurvivingLoopIsRetained : ((0, 1, -1) : Edges) ∈ thetaChain.retained := by
  show d1 ((0, 1, -1) : Edges) = 0
  simp [d1]

theorem theSurvivingLoopIsNotRealized : ((0, 1, -1) : Edges) ∉ thetaChain.realized := by
  rintro ⟨n, hn⟩
  have h : (0 : ℤ) = -1 := congrArg (fun p : Edges => p.2.2) hn
  omega

/-- **So the theta chain does not glue, and its homology is not trivial.**  This is the first
object in the development carrying a nonzero realized population *and* a nonzero homology. -/
theorem theThetaChainDoesNotGlue : ¬ thetaChain.toPassage.Glues := fun h =>
  theSurvivingLoopIsNotRealized (h theSurvivingLoopIsRetained)

theorem theThetaHomologyIsNontrivial :
    ¬ Subsingleton thetaChain.toPassage.ObstructionGroup := fun h =>
  theThetaChainDoesNotGlue ((AdditivePassage.glues_iff_obstruction_subsingleton _).mpr h)

/-! ## The boundary-pullback form, and the criterion satisfied with a nonzero realized population -/

/-- The standard pairing on vertex chains, one slot fixed. -/
def pair2On (a : Verts) : Verts →+ ℚ :=
  AddMonoidHom.mk' (fun b => ((a.1 * b.1 + a.2 * b.2 : ℤ) : ℚ)) (by
    intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    push_cast
    ring)

/-- The standard pairing on vertex chains. -/
def pair2 : Verts →+ (Verts →+ ℚ) :=
  AddMonoidHom.mk' pair2On (by
    intro a b
    ext c
    simp only [AddMonoidHom.add_apply, pair2On, AddMonoidHom.mk'_apply, Prod.fst_add, Prod.snd_add]
    push_cast
    ring)

@[simp] theorem pair2_apply (a b : Verts) :
    pair2 a b = ((a.1 * b.1 + a.2 * b.2 : ℤ) : ℚ) := rfl

/-- The **boundary-pullback form** on edge chains. -/
def thetaForm : Edges →+ (Edges →+ ℚ) :=
  AddMonoidHom.mk' (fun e => (pair2 (d1 e)).comp d1) (by
    intro a b
    ext f
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_add, pair2_apply, d1_apply,
      ])

@[simp] theorem thetaForm_apply (e f : Edges) : thetaForm e f = pair2 (d1 e) (d1 f) := rfl

/-- **The theta complex under the boundary-pullback form**, everything retained. -/
def thetaDatum : CompressedPositivity Edges where
  form := thetaForm
  form_symm := by
    intro a b
    simp only [thetaForm_apply, pair2_apply]
    push_cast
    ring
  cutoff := ⊥
  remainder := ⊤
  orthogonal := by
    intro c hc v _
    rw [AddSubgroup.mem_bot] at hc
    subst hc
    show thetaForm 0 v = 0
    rw [map_zero]
    rfl
  sign := 1
  sign_unit := Or.inl rfl
  definite := by
    intro v _
    simp only [one_mul, thetaForm_apply, pair2_apply]
    have : (0 : ℤ) ≤ (d1 v).1 * (d1 v).1 + (d1 v).2 * (d1 v).2 := by
      nlinarith [mul_self_nonneg (d1 v).1, mul_self_nonneg (d1 v).2]
    exact_mod_cast this

/-- **The pullback form vanishes on every cycle.** -/
theorem thePullbackVanishesOnCycles {x : Edges} (hx : d1 x = 0) (y : Edges) :
    thetaDatum.form x y = 0 := by
  show thetaForm x y = 0
  rw [thetaForm_apply, hx, map_zero]
  rfl

/-- **The criterion holds, with a nonzero realized population that the complex supplied.**

The filled cell's boundary is a cycle, so it lies in the radical, so the form descends onto the
homology.  Unlike the hollow triangle, the population quotiented out here is not zero, and unlike
the doubled loop of the previous iteration it was not picked by hand — it is what the complex
realizes. -/
theorem theNonzeroRealizedLiesInTheRadical :
    ∀ r ∈ thetaChain.realized, ∀ w ∈ thetaDatum.remainder, thetaDatum.form r w = 0 := by
  rintro r ⟨n, rfl⟩ w _
  exact thePullbackVanishesOnCycles (d1_comp_d2 n) w

/-- **And therefore the form descends onto the theta complex's homology.** -/
theorem theFormDescendsOntoTheThetaHomology :
    ∀ v ∈ thetaDatum.remainder, ∀ r ∈ thetaChain.realized, ∀ w ∈ thetaDatum.remainder,
      thetaDatum.form (v + r) w = thetaDatum.form v w :=
  (thetaDatum.theFormDescendsIffTheQuotientedIsInTheRadical thetaChain.realized le_top).mpr
    theNonzeroRealizedLiesInTheRadical

/-- **But it can never be faithful there.**

Every cycle is null under a boundary pullback, and a homology class is a cycle.  So the descended
form has null classes wherever the homology is nonzero — which it is here, witnessed by the
surviving loop.

**A form that pays on a homology cannot be a boundary pullback.** It has to come from somewhere
else. -/
theorem theDescendedFormIsNotFaithful :
    thetaDatum.sign * thetaDatum.form ((0, 1, -1) : Edges) ((0, 1, -1) : Edges) = 0
      ∧ ((0, 1, -1) : Edges) ∉ thetaChain.realized := by
  refine ⟨?_, theSurvivingLoopIsNotRealized⟩
  show (1 : ℚ) * thetaForm ((0, 1, -1) : Edges) ((0, 1, -1) : Edges) = 0
  rw [one_mul]
  exact thePullbackVanishesOnCycles theSurvivingLoopIsRetained _

end Soma.Holonics.Millennium.Theta
