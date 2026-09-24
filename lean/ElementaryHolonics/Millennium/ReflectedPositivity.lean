import ElementaryHolonics.Millennium.Paying

/-!
# The reflection is the first slot of the form

The standing positivity datum in `Paying.lean` carries a form, a declared subspace it is positive
on, a cutoff and a sign.  What it has never carried is an **involution relating them** — and that
involution is the missing field of the classical object this development has been circling.

The classical statement (aside labels: Osterwalder–Schrader; in the statistical-mechanics form,
Osterwalder–Seiler and Fröhlich–Israel–Lieb–Simon) is:

```text
closed subspace H+ ; unitary involution Theta
RP:  <f, Theta f>  >=  0   for all f in H+   ==>   H_Theta  ==  H+ / N_Theta
```

**The whole content of this file is that the reflection is not a new organ beside the form.  It is
the form's first slot.**  Fold it in and the round trip *is* a `CompressedPositivity`, its null
population *is* `Paying.radical`, and the two standing theorems about descent and faithfulness
apply to it by projection with nothing reproved.

What this file establishes, and nothing beyond it:

* the two candidate compatibilities — a form-isometry and self-adjointness — are **one condition**
  for an involution, and that condition is exactly what makes the round trip symmetric;
* folding the reflection in yields a `CompressedPositivity`, so `N_Theta = Paying.radical`;
* the fixed and anti-fixed faces of the reflection **cannot see each other**;
* and, on one carrier with one form and one declared half, **two legal reflections, one of which
  pays and one of which does not.**

That last item is the reason the file exists.  This project's standing positivity organ computes
`x^T (M^T M) x = |M x|^2 >= 0`, which cannot fail for any integer matrix and any probe, and by the
project's own rule a check that cannot fail carries no evidence.  The pair in section 6 varies the
reflection alone — same carrier, same form, same half — and the positivity moves.

**What this file does NOT establish**, stated once and carried as named `Prop`s in section 7:
the classical reflection **exchanges** the two halves rather than preserving one; the classical
`Theta` is an antilinear anti-morphism, and over an `AddCommGroup` with rational values there is
no conjugation, so this is the real-symmetric special case; and the quotient `H+/N_Theta` is
characterised here by a criterion rather than constructed as a group.

Every `theorem` here is discharged.  Nothing here is a claim about any named conjecture, and the
phrase "mass gap" appears nowhere as a claim.
-/

namespace Soma.Holonics.Millennium.Reflected

open Soma.Holonics.Millennium.Paying

universe u

variable {V : Type u} [AddCommGroup V]

/-! ## 1. The structure -/

/-- A **reflected positivity datum**: a symmetric form, an involution the form cannot tell from its
own adjoint, a declared half, and the condition that the round trip pays on that half. -/
structure ReflectedPositivity (V : Type u) [AddCommGroup V] where
  /-- The form. -/
  form : V →+ V →+ ℚ
  /-- It is symmetric. -/
  form_symm : ∀ a b, form a b = form b a
  /-- The reflection. -/
  reflection : V →+ V
  /-- It is an involution. -/
  reflection_involutive : ∀ v, reflection (reflection v) = v
  /-- The form cannot tell the reflection from its adjoint.  Section 2 shows this is the same
  condition as the reflection being a form-isometry, and section 3 shows it is exactly what makes
  the round trip symmetric. -/
  reflection_selfAdjoint : ∀ a b, form (reflection a) b = form a (reflection b)
  /-- The declared half.  It is a **declaration**: the set on which a form is non-negative is not
  in general a subgroup, so which half is retained is not read off the form. -/
  half : AddSubgroup V
  /-- **The condition.**  The round trip pays on the half. -/
  roundTrip_nonneg : ∀ f ∈ half, 0 ≤ form (reflection f) f

namespace ReflectedPositivity

variable (R : ReflectedPositivity V)

/-! ## 2. The two compatibilities are one condition -/

/-- **For an involution, being a form-isometry and being self-adjoint are the same condition.**

Both directions are the same substitution — replace one argument by its reflection and use
`theta (theta v) = v` — which is why the equivalence spends the involutivity and would fail
without it. -/
theorem theIsometryIsExactlyTheSelfAdjointness (form : V →+ V →+ ℚ) (theta : V →+ V)
    (hinv : ∀ v, theta (theta v) = v) :
    (∀ a b, form (theta a) (theta b) = form a b)
      ↔ (∀ a b, form (theta a) b = form a (theta b)) := by
  constructor
  · intro h a b
    have hb := h a (theta b)
    rwa [hinv b] at hb
  · intro h a b
    have hb := h a (theta b)
    rwa [hinv b] at hb

/-- **So the datum's reflection is a form-isometry**, obtained from the field rather than assumed
beside it. -/
theorem theReflectionIsAnIsometry (a b : V) :
    R.form (R.reflection a) (R.reflection b) = R.form a b :=
  (theIsometryIsExactlyTheSelfAdjointness R.form R.reflection R.reflection_involutive).mpr
    R.reflection_selfAdjoint a b

/-! ## 3. The round trip, and where self-adjointness is spent -/

/-- The **round-trip form**: the form with the reflection folded into its first slot.

**DEFINITIONAL — this is `form.comp reflection` and naming it proves nothing.**  The content is
that it is symmetric (next) and that it is therefore a `CompressedPositivity` form (section 4). -/
def roundTripForm : V →+ V →+ ℚ := R.form.comp R.reflection

/-- **DEFINITIONAL — `rfl`.** -/
@[simp] theorem roundTripForm_apply (a b : V) :
    R.roundTripForm a b = R.form (R.reflection a) b := rfl

/-- **The round trip is symmetric, and this is exactly where self-adjointness is spent.**

Without it the round trip is not a symmetric form, the standing structure will not accept it, and
the descent question cannot even be posed. -/
theorem theRoundTripIsSymmetric (a b : V) : R.roundTripForm a b = R.roundTripForm b a := by
  simp only [roundTripForm_apply]
  rw [R.reflection_selfAdjoint a b]
  exact R.form_symm a (R.reflection b)

/-! ## 4. The composition — the reflection enters the standing structure -/

/-- **The datum is a compressed positivity datum with the reflection folded in.**

This is the composition the development was missing.  The reflection is not an organ beside the
form; it is the form's first slot.  Everything `Paying` proves therefore holds of the round trip
with no further argument. -/
def toCompressedPositivity : CompressedPositivity V where
  form := R.roundTripForm
  form_symm := R.theRoundTripIsSymmetric
  cutoff := ⊥
  remainder := R.half
  orthogonal := by
    intro c hc v _
    have hc' : c ∈ (⊥ : AddSubgroup V) := hc
    rw [AddSubgroup.mem_bot] at hc'
    subst hc'
    simp
  sign := 1
  sign_unit := Or.inl rfl
  definite := by
    intro v hv
    rw [one_mul]
    exact R.roundTrip_nonneg v hv

/-- **The null population of the round trip IS the standing radical.**

**DEFINITIONAL — `Iff.rfl`.**  It is recorded because the identification is the point: `N_Theta`
is not a new object to be built, it is `Paying.radical` of the composed datum. -/
theorem theNullSetIsTheRadical (v : V) :
    v ∈ R.toCompressedPositivity.radical
      ↔ (v ∈ R.half ∧ ∀ w ∈ R.half, R.form (R.reflection v) w = 0) := Iff.rfl

/-- **The null cone of the round trip is its radical**, inherited by projection.

A vector of the half that pairs with itself to nothing under the round trip pairs with the whole
half to nothing.  The integer Cauchy–Schwarz argument that proves it lives in `Paying` and is not
repeated. -/
theorem theRoundTripNullConeIsTheRadical {v : V} (hv : v ∈ R.half)
    (hnull : R.form (R.reflection v) v = 0) : v ∈ R.toCompressedPositivity.radical :=
  R.toCompressedPositivity.theNullOnTheRemainderIsTheRadical hv (by
    show (1 : ℚ) * R.form (R.reflection v) v = 0
    rw [one_mul]; exact hnull)

/-- **The quotient is faithful exactly when what is quotiented out is the whole null population.**

Inherited by projection from the standing trichotomy: outside the radical the form does not
descend, strictly inside it the quotient keeps null classes, at the radical it is faithful. -/
theorem theReflectionQuotientIsFaithfulIffItDividesByTheWholeNullSet
    (N : AddSubgroup V) (hN : N ≤ R.toCompressedPositivity.radical) :
    (∀ v ∈ R.half, R.form (R.reflection v) v = 0 → v ∈ N)
      ↔ R.toCompressedPositivity.radical ≤ N := by
  have h := R.toCompressedPositivity.theQuotientIsFaithfulIffTheRealizedIsTheWholeRadical N hN
  constructor
  · intro hf
    refine h.mp ?_
    intro v hv hnull
    refine hf v hv ?_
    have hn : (1 : ℚ) * R.form (R.reflection v) v = 0 := hnull
    linarith
  · intro hr v hv hnull
    refine h.mpr hr v hv ?_
    show (1 : ℚ) * R.form (R.reflection v) v = 0
    rw [one_mul]; exact hnull

/-! ## 5. The two faces of the reflection cannot see each other -/

/-- What the reflection fixes. -/
def fixedFace : AddSubgroup V where
  carrier := {v | R.reflection v = v}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    have ha' : R.reflection a = a := ha
    have hb' : R.reflection b = b := hb
    show R.reflection (a + b) = a + b
    rw [map_add, ha', hb']
  neg_mem' := by
    intro a ha
    have ha' : R.reflection a = a := ha
    show R.reflection (-a) = -a
    rw [map_neg, ha']

/-- What the reflection reverses. -/
def antiFixedFace : AddSubgroup V where
  carrier := {v | R.reflection v = -v}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    have ha' : R.reflection a = -a := ha
    have hb' : R.reflection b = -b := hb
    show R.reflection (a + b) = -(a + b)
    rw [map_add, ha', hb', neg_add]
  neg_mem' := by
    intro a ha
    have ha' : R.reflection a = -a := ha
    show R.reflection (-a) = -(-a)
    rw [map_neg, ha']

/-- **A cross-pairing is its own negative.**

`form a b = form (θa) (θb) = form a (−b) = −form a b`.  That is the whole mechanism. -/
theorem theCrossPairingIsItsOwnNegative {a b : V} (ha : a ∈ R.fixedFace)
    (hb : b ∈ R.antiFixedFace) : R.form a b = - R.form a b := by
  have ea : R.reflection a = a := ha
  have eb : R.reflection b = -b := hb
  have h := R.theReflectionIsAnIsometry a b
  rw [ea, eb, map_neg] at h
  linarith

/-- **The cross-pairing vanishes: the two faces cannot see each other.**

Two is invertible in the *values* even though it is not invertible in the carrier, which is why
this is available here while the halved eigenprojectors are not.

An exact numerical check of this statement already runs in the Rust body — the θ-isometric metric
pairing there returns the cross term as exactly zero.  This is that check as a theorem. -/
theorem theCrossPairingVanishes {a b : V} (ha : a ∈ R.fixedFace)
    (hb : b ∈ R.antiFixedFace) : R.form a b = 0 := by
  have h := R.theCrossPairingIsItsOwnNegative ha hb
  linarith

end ReflectedPositivity

/-! ## 6. One carrier, one form, one half — and two legal reflections that disagree

The carrier is four sites in a row.  The form is `2I + A(P4)`, the path graph's kernel, which is
positive definite.  The half retains the two right-hand sites.

Both reflections below are involutions and both are self-adjoint for that form, so both are legal
inputs to the structure above.  **One pays and one does not.**  Every other declared input is held
fixed, so the failure is attributable to the reflection alone. -/

/-- Four sites in a row. -/
abbrev Sites : Type := ℤ × ℤ × ℤ × ℤ

/-- The kernel `2I + A(P4)` on those sites. -/
def gram (e f : Sites) : ℤ :=
  2 * (e.1 * f.1 + e.2.1 * f.2.1 + e.2.2.1 * f.2.2.1 + e.2.2.2 * f.2.2.2)
    + (e.1 * f.2.1 + e.2.1 * f.1)
    + (e.2.1 * f.2.2.1 + e.2.2.1 * f.2.1)
    + (e.2.2.1 * f.2.2.2 + e.2.2.2 * f.2.2.1)

/-- **The kernel's self-pairing is a sum of five squares**, so the form is positive definite and
the failures below cannot be blamed on it. -/
theorem theChainKernelIsFiveSquares (s : Sites) :
    gram s s = s.1 * s.1 + (s.1 + s.2.1) * (s.1 + s.2.1)
      + (s.2.1 + s.2.2.1) * (s.2.1 + s.2.2.1)
      + (s.2.2.1 + s.2.2.2) * (s.2.2.1 + s.2.2.2) + s.2.2.2 * s.2.2.2 := by
  obtain ⟨a, b, c, d⟩ := s
  simp only [gram]
  ring

/-- The **reflection across the central bond**: the row read backwards. -/
def bond (s : Sites) : Sites := (s.2.2.2, s.2.2.1, s.2.1, s.1)

/-- The **shear reflection**: the third site absorbs its two neighbours. -/
def shear (s : Sites) : Sites := (s.1, s.2.1, -s.2.1 - s.2.2.1 - s.2.2.2, s.2.2.2)

theorem bondIsInvolutive (s : Sites) : bond (bond s) = s := by
  obtain ⟨a, b, c, d⟩ := s; rfl

theorem shearIsInvolutive (s : Sites) : shear (shear s) = s := by
  obtain ⟨a, b, c, d⟩ := s
  simp only [shear, Prod.mk.injEq]
  exact ⟨trivial, trivial, by ring, trivial⟩

theorem bondIsSelfAdjoint (e f : Sites) : gram (bond e) f = gram e (bond f) := by
  obtain ⟨a, b, c, d⟩ := e; obtain ⟨p, q, r, t⟩ := f
  simp only [bond, gram]; ring

theorem shearIsSelfAdjoint (e f : Sites) : gram (shear e) f = gram e (shear f) := by
  obtain ⟨a, b, c, d⟩ := e; obtain ⟨p, q, r, t⟩ := f
  simp only [shear, gram]; ring

/-- **The bond reflection pays**: on the half its round trip is a square. -/
theorem theBondRoundTripIsASquare (u v : ℤ) :
    gram (bond (0, 0, u, v)) (0, 0, u, v) = u * u := by
  simp only [bond, gram]; ring

theorem theBondPaysOnTheHalf (u v : ℤ) :
    0 ≤ gram (bond (0, 0, u, v)) (0, 0, u, v) := by
  rw [theBondRoundTripIsASquare]; exact mul_self_nonneg u

/-- **The shear reflection does not pay**: on the same half its round trip is an indefinite
quadratic. -/
theorem theShearRoundTripIsIndefinite (u v : ℤ) :
    gram (shear (0, 0, u, v)) (0, 0, u, v) = -2 * u * u - 2 * u * v + v * v := by
  simp only [shear, gram]; ring

/-- **The positivity fails, on a reflection that is every bit as legal as the one that pays.**

Same carrier, same form, same declared half; both reflections involutive and both self-adjoint for
the form.  The only input that varies is the reflection, and the sign moves with it.

*This is the form whose positivity can fail that the standing organ could not supply, because
`|M x|^2 >= 0` holds for every integer matrix and every probe.* -/
theorem theShearFailsAtTheInnerSite :
    gram (shear (0, 0, 1, 0)) ((0, 0, 1, 0) : Sites) < 0 := by
  simp only [shear, gram]; norm_num

/-- **And the two disagree at one site**, which is the whole witness in one line. -/
theorem theTwoReflectionsDisagreeOnTheSameVector :
    0 ≤ gram (bond (0, 0, 1, 0)) ((0, 0, 1, 0) : Sites)
      ∧ gram (shear (0, 0, 1, 0)) ((0, 0, 1, 0) : Sites) < 0 := by
  refine ⟨?_, theShearFailsAtTheInnerSite⟩
  simp only [bond, gram]; norm_num

/-! ## 6b. The exchange, and the witness that survives it

**CORRECTION, 2026-08-20, and it is against section 6 above.** The classical involution carries the
negative half to the positive one.  The shear does not: `shear (0,0,u,v) = (0,0,-u-v,v)` lands back
in the declared half, so it **preserves** that half rather than exchanging it.  Under the classical
exchange requirement the bond/shear pair therefore stops separating, and the section 6 witness is a
witness about the weaker structure stated here — exactly what `TheHalfExchangeIsNotRequired` below
named as its own falsifier.

**The separation survives, under a different second reflection.**  `twist` exchanges the two halves,
is involutive, is self-adjoint for the same form, and its round trip on the same half is negative.
So the pair below separates under the *stronger* statement, which section 6's pair does not. -/

/-- The left half: the two left-hand sites. -/
def leftPair (s : Sites) : Prop := s.2.2.1 = 0 ∧ s.2.2.2 = 0

/-- The right half: the two right-hand sites.  This is the half section 6 declares. -/
def rightPair (s : Sites) : Prop := s.1 = 0 ∧ s.2.1 = 0

/-- **The shear preserves the half instead of exchanging it.**

This is the correction: it is not an admissible reflection for the classical statement at all. -/
theorem theShearPreservesTheHalf (u v : ℤ) : rightPair (shear (0, 0, u, v)) := by
  constructor <;> rfl

/-- The **twist**: `(a,b,c,d) ↦ (c+d, −c, −b, a+b)`. -/
def twist (s : Sites) : Sites := (s.2.2.1 + s.2.2.2, -s.2.2.1, -s.2.1, s.1 + s.2.1)

theorem twistIsInvolutive (s : Sites) : twist (twist s) = s := by
  obtain ⟨a, b, c, d⟩ := s
  simp only [twist, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem twistIsSelfAdjoint (e f : Sites) : gram (twist e) f = gram e (twist f) := by
  obtain ⟨a, b, c, d⟩ := e; obtain ⟨p, q, r, t⟩ := f
  simp only [twist, gram]; ring

/-- **The twist exchanges the halves**, which the shear does not. -/
theorem theTwistExchangesTheHalves (u v : ℤ) : leftPair (twist (0, 0, u, v)) := by
  constructor <;> rfl

theorem theBondExchangesTheHalves (u v : ℤ) : leftPair (bond (0, 0, u, v)) := by
  constructor <;> rfl

/-- **The twist's round trip on the half is the negated square.** -/
theorem theTwistRoundTripIsNegative (u v : ℤ) :
    gram (twist (0, 0, u, v)) (0, 0, u, v) = -(u * u) := by
  simp only [twist, gram]; ring

/-- **The separation survives the exchange requirement.**

One carrier, one positive-definite form, one declared half.  Two reflections, both involutive, both
self-adjoint for the form, and **both carrying the declared half into the complementary one** — so
both are admissible for the classical statement, not merely for the weaker one above.  The bond pays
and the twist does not.

*This replaces the section 6 pair as the load-bearing witness; that pair remains true of the weaker
structure and is retained to mark the difference.* -/
theorem theExchangingReflectionsDisagree :
    leftPair (bond (0, 0, 1, 0)) ∧ leftPair (twist (0, 0, 1, 0))
      ∧ 0 ≤ gram (bond (0, 0, 1, 0)) ((0, 0, 1, 0) : Sites)
      ∧ gram (twist (0, 0, 1, 0)) ((0, 0, 1, 0) : Sites) < 0 := by
  refine ⟨theBondExchangesTheHalves 1 0, theTwistExchangesTheHalves 1 0, ?_, ?_⟩
  · simp only [bond, gram]; norm_num
  · simp only [twist, gram]; norm_num

/-! ## 7. What is not established here

Each is a named `Prop` with its falsifier, never an axiom and never a `sorry`. -/

/-- **The classical reflection exchanges the halves; this structure only requires a half.**

Osterwalder–Seiler's `Theta` carries the negative-time algebra to the positive-time one, so the
round trip leaves the half.  Nothing in `ReflectedPositivity` requires the reflection to move the
half at all, and a datum whose reflection fixes its half pointwise satisfies every field while
carrying no reflection content.

*Falsifier: a field relating the reflection to the half under which the section 6 witness pair
still separates.  If the pair does not survive the added field, the witness is about the structure
rather than about reflection positivity.* -/
def TheHalfExchangeIsNotRequired : Prop :=
  ∀ (V : Type) (_ : AddCommGroup V) (_ : ReflectedPositivity V), True

/-- **The classical involution is an antilinear anti-morphism.**

Over an `AddCommGroup` with rational values there is no conjugation and no multiplication, so
everything above is the real-symmetric special case.

*Falsifier: a statement of the round-trip condition over a carrier with a conjugation under which
`theRoundTripIsSymmetric` fails, showing the real case is not a special case but a different
statement.* -/
def TheAntilinearCaseIsNotCovered : Prop := True

/-- **The physical space `H+/N_Theta` is characterised here, not constructed.**

Section 4 gives the criterion naming which quotiented population leaves no null classes.  It does
not build the quotient group, the induced form, or a descended transport.

*Falsifier: a constructed quotient carrying an induced form that is not faithful where the
criterion says it is.* -/
def TheQuotientIsNotConstructed : Prop := True

end Soma.Holonics.Millennium.Reflected
