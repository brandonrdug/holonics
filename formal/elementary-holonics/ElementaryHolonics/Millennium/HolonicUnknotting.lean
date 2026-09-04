import ElementaryHolonics.Millennium.Gluing
import ElementaryHolonics.Millennium.HolonicComposition
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Algebra.Quandle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Unknotting station zero: swing transport, null difference, and irreducibility

This file closes the algebraic entrance to the unknotting ladder.  Mathlib's rack and quandle
owners already contain the coloring equations underlying the three Reidemeister moves:

* a quandle pivot fixes itself;
* a rack action and its inverse cancel;
* self-distributivity transports a crossing through a crossing; and
* the action of a transported pivot is conjugate to the original actions.

Those are exact local transport laws, not yet a planar knot diagram or Reidemeister theorem.  The
file also formalizes two distinctions needed by the larger ladder.  First, a faithful receiver form
makes a nonzero difference exactly a non-null self-reading.  Second, “prime” means a nonunit whose
every binary factorization has a unit factor.  Calling that unit the unknot requires an actual knot
monoid, which the repository does not yet construct.
-/

namespace Soma.Holonics.Millennium.HolonicUnknotting

open Quandles

/-! ## 1. Quandle swing transport -/

/-- A pivot acts on every rack color by an invertible swing. -/
def rackSwing {R : Type*} [Rack R] (pivot : R) : Equiv.Perm R := Rack.act' pivot

/-- The inverse swing cancels the forward swing. This is the algebraic R-II coloring law. -/
theorem inverseSwing_cancels {R : Type*} [Rack R] (pivot color : R) :
    (rackSwing pivot).symm (rackSwing pivot color) = color := by
  exact (rackSwing pivot).left_inv color

/-- The forward swing cancels the inverse swing, in the opposite order. -/
theorem swing_cancelsInverse {R : Type*} [Rack R] (pivot color : R) :
    rackSwing pivot ((rackSwing pivot).symm color) = color := by
  exact (rackSwing pivot).right_inv color

/-- A quandle pivot fixes its own color. This is the algebraic R-I coloring law. -/
theorem pivotSwing_fixesPivot {Q : Type*} [Quandle Q] (pivot : Q) :
    rackSwing pivot pivot = pivot := by
  exact Quandle.fix

/-- Moving one pivot through another conjugates its complete transport action. -/
theorem transportedPivotSwing_isConjugate {R : Type*} [Rack R] (x y : R) :
    rackSwing (x ◃ y) = rackSwing x * rackSwing y * (rackSwing x)⁻¹ := by
  exact Rack.ad_conj x y

/-- Self-distributivity is the algebraic R-III coloring law. -/
theorem crossingTransport_interchanges {R : Type*} [Rack R] (x y z : R) :
    x ◃ y ◃ z = (x ◃ y) ◃ x ◃ z := by
  exact Shelf.self_distrib

/-! ## 2. The null is null exactly when a faithful receiver sees every difference -/

/-- For a faithful receiver pairing whose zero self-reading is actually zero, unequal source
occurrences are exactly those with a non-null self-reading of their additive difference. -/
theorem difference_ne_iff_differenceSelfPair_ne_zero
    {A : Type*} [AddCommGroup A] (F : PayingPairing A) (hzero : F.pair 0 0 = 0)
    (a b : A) :
    a ≠ b ↔ F.pair (a - b) (a - b) ≠ 0 := by
  constructor
  · intro hab hnull
    exact hab (sub_eq_zero.mp (F.null_cone_is_a_point (a - b) hnull))
  · intro hnonnull hab
    apply hnonnull
    rw [hab, sub_self, hzero]

/-! ## 3. Prime means irreducible relative to the unit -/

/-- The generic factorization law shared by arithmetic primes and prime knots: a prime object is a
nonunit and every binary factorization has a unit factor. -/
theorem irreducibleFactorizationLaw {M : Type*} [Monoid M] {p : M} (hp : Irreducible p) :
    ¬ IsUnit p ∧ ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b := by
  exact irreducible_iff.mp hp

/-- When the factorization monoid has only the identity as a unit, every factorization of an
irreducible object contains the identity.  In a future knot-class monoid that identity is the
unknot; no knot-specific instance is asserted here. -/
theorem irreducibleSplit_containsIdentity
    {M : Type*} [Monoid M] (units_trivial : ∀ u : M, IsUnit u → u = 1)
    {p a b : M} (hp : Irreducible p) (hsplit : p = a * b) :
    a = 1 ∨ b = 1 := by
  rcases hp.isUnit_or_isUnit hsplit with ha | hb
  · exact Or.inl (units_trivial a ha)
  · exact Or.inr (units_trivial b hb)

/-! ## 4. The obvious Euler phase is a maximally collapsed writhe receiver -/

/-- The full-turn exponential receiver on an integer ledger. -/
noncomputable def fullTurnPhase (writhe : ℤ) : ℂ :=
  Complex.exp (writhe * (2 * Real.pi * Complex.I))

/-- Every integer writhe has the same full-turn phase. This receiver therefore carries no verdict
about writhe, framing, a Reidemeister orbit, or unknotting. -/
theorem fullTurnPhase_collapsesEveryInteger (writhe : ℤ) :
    fullTurnPhase writhe = 1 := by
  exact Complex.exp_int_mul_two_pi_mul_I writhe

end Soma.Holonics.Millennium.HolonicUnknotting

#print axioms Soma.Holonics.Millennium.HolonicUnknotting.inverseSwing_cancels
#print axioms Soma.Holonics.Millennium.HolonicUnknotting.pivotSwing_fixesPivot
#print axioms Soma.Holonics.Millennium.HolonicUnknotting.transportedPivotSwing_isConjugate
#print axioms Soma.Holonics.Millennium.HolonicUnknotting.crossingTransport_interchanges
#print axioms Soma.Holonics.Millennium.HolonicUnknotting.difference_ne_iff_differenceSelfPair_ne_zero
#print axioms Soma.Holonics.Millennium.HolonicUnknotting.irreducibleSplit_containsIdentity
#print axioms Soma.Holonics.Millennium.HolonicUnknotting.fullTurnPhase_collapsesEveryInteger
