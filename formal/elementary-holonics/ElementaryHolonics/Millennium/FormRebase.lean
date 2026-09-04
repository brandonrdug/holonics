import ElementaryHolonics.Millennium.Paying
import ElementaryHolonics.Millennium.Triangle

/-!
# The form travels — and the radical travels with it, but the perp does not

The previous iteration's rebase moved a carrier and its populations and nothing else.  A datum that
*pays* carries a form, a cutoff and a sign, and none of those travelled.  This file carries the
form, and settles which of its derived objects survive the trip.

**The radical transports freely.**  Not because it was designed to, but because the semi-definite
null-cone theorem does the work: a member of the predecessor's radical lands in the successor's
remainder pairing with itself to nothing, and on a semi-definite form that is already membership of
the radical.

**The perp does not.**  It needs the transport to reach the whole successor remainder, and a
witness shows what goes wrong without that.

So the falsifier named last iteration — *a rebase under which the radical is not the image of the
predecessor's radical* — is refuted for the radical and confirmed for the perp.  The form's data
does not transport as one block; it splits.

Every `theorem` here is discharged.
-/

namespace Soma.Holonics.Millennium.FormRebase

open Soma.Holonics.Millennium Soma.Holonics.Millennium.Paying
open Soma.Holonics.Millennium.Triangle

universe u

variable {V W : Type u} [AddCommGroup V] [AddCommGroup W]

/-- A **form-carrying rebase**: a transport under which the successor's form restricts to the
predecessor's, and what was retained stays retained. -/
structure FormRebase (C : CompressedPositivity V) (D : CompressedPositivity W) where
  /-- The transport of carriers. -/
  transport : V →+ W
  /-- The successor's form restricts to the predecessor's. -/
  carries : ∀ a b : V, D.form (transport a) (transport b) = C.form a b
  /-- What was retained stays retained. -/
  remainder_maps : ∀ v ∈ C.remainder, transport v ∈ D.remainder

namespace FormRebase

variable {C : CompressedPositivity V} {D : CompressedPositivity W} (R : FormRebase C D)

/-- **The radical transports, and needs nothing but the two axioms already present.**

A member of the predecessor's radical lands in the successor's remainder pairing with itself to
nothing.  On a semi-definite form that already *is* membership of the radical, so no surjectivity,
no injectivity and no extra hypothesis is required.

*The falsifier named for this item is refuted: the radical's data does transport functorially.* -/
theorem theRadicalTransports {v : V} (hv : v ∈ C.radical) : R.transport v ∈ D.radical := by
  have hmem : R.transport v ∈ D.remainder := R.remainder_maps v hv.1
  refine D.theNullOnTheRemainderIsTheRadical hmem ?_
  rw [R.carries v v, hv.2 v hv.1, mul_zero]

/-- **A whole radical lands inside a radical.** -/
theorem theRadicalMapsIntoTheRadical :
    ∀ v ∈ C.radical, R.transport v ∈ D.radical := fun _ hv => R.theRadicalTransports hv

/-- **The perp transports only when the successor's remainder is reached.**

Unlike the radical, the perp is a condition against *everything* retained downstream, and a
transport that does not reach all of it cannot certify the condition. -/
theorem thePerpTransportsWhenTheRemainderIsCovered
    (onto : ∀ u ∈ D.remainder, ∃ v ∈ C.remainder, R.transport v = u)
    {c : V} (hc : c ∈ C.perp) : R.transport c ∈ D.perp := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := onto u hu
  rw [R.carries c v]
  exact hc v hv

/-- **An admissible cutoff stays admissible when the successor's remainder is reached.**

A cutoff is admissible exactly when it sits in the perp, so this is the perp theorem applied to the
declared field.  The covering hypothesis is the same one and cannot be dropped. -/
theorem theCutoffTravelsUnderCovering
    (onto : ∀ u ∈ D.remainder, ∃ v ∈ C.remainder, R.transport v = u)
    {c : V} (hc : c ∈ C.cutoff) : R.transport c ∈ D.perp :=
  R.thePerpTransportsWhenTheRemainderIsCovered onto (fun v hv => C.orthogonal c hc v hv)

end FormRebase

/-! ## The perp genuinely fails to transport without that hypothesis -/

/-- The triangle's form with **nothing** retained. -/
def emptyRemainderDatum : CompressedPositivity Cells where
  form := standardForm
  form_symm := hollowTriangleDatum.form_symm
  cutoff := ⊥
  remainder := ⊥
  orthogonal := by
    intro c hc v _
    rw [AddSubgroup.mem_bot] at hc
    subst hc
    show standardForm 0 v = 0
    rw [map_zero]
    rfl
  sign := 1
  sign_unit := Or.inl rfl
  definite := by
    intro v hv
    rw [AddSubgroup.mem_bot] at hv
    subst hv
    show (0 : ℚ) ≤ 1 * standardForm 0 0
    rw [map_zero]
    simp

/-- The same form with **everything** retained. -/
def fullRemainderDatum : CompressedPositivity Cells where
  form := standardForm
  form_symm := hollowTriangleDatum.form_symm
  cutoff := ⊥
  remainder := ⊤
  orthogonal := by
    intro c hc v _
    rw [AddSubgroup.mem_bot] at hc
    subst hc
    show standardForm 0 v = 0
    rw [map_zero]
    rfl
  sign := 1
  sign_unit := Or.inl rfl
  definite := by
    intro v _
    show (0 : ℚ) ≤ 1 * standardForm v v
    rw [one_mul, standardForm_apply]
    have : (0 : ℤ) ≤ v.1 * v.1 + v.2.1 * v.2.1 + v.2.2 * v.2.2 := by
      nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2.1, mul_self_nonneg v.2.2]
    exact_mod_cast this

/-- Widening the remainder is a form-carrying rebase along the identity. -/
def widenTheRemainder : FormRebase emptyRemainderDatum fullRemainderDatum where
  transport := AddMonoidHom.id Cells
  carries := fun _ _ => rfl
  remainder_maps := by
    intro v hv
    have hv' : v ∈ (⊥ : AddSubgroup Cells) := hv
    rw [AddSubgroup.mem_bot] at hv'
    subst hv'
    trivial

/-- The triangle's form with nothing retained and **everything admitted**.

Legal upstream: with nothing retained, the orthogonality requirement is vacuous, so the widest
possible aperture is admissible. -/
def wideCutoffDatum : CompressedPositivity Cells where
  form := standardForm
  form_symm := hollowTriangleDatum.form_symm
  cutoff := ⊤
  remainder := ⊥
  orthogonal := by
    intro c _ v hv
    have hv' : v ∈ (⊥ : AddSubgroup Cells) := hv
    rw [AddSubgroup.mem_bot] at hv'
    subst hv'
    show standardForm c 0 = 0
    rw [map_zero]
  sign := 1
  sign_unit := Or.inl rfl
  definite := by
    intro v hv
    have hv' : v ∈ (⊥ : AddSubgroup Cells) := hv
    rw [AddSubgroup.mem_bot] at hv'
    subst hv'
    show (0 : ℚ) ≤ 1 * standardForm 0 0
    rw [map_zero]
    simp

/-- Widening the remainder is a form-carrying rebase out of the wide-aperture datum too. -/
def widenFromWideCutoff : FormRebase wideCutoffDatum fullRemainderDatum where
  transport := AddMonoidHom.id Cells
  carries := fun _ _ => rfl
  remainder_maps := by
    intro v hv
    have hv' : v ∈ (⊥ : AddSubgroup Cells) := hv
    rw [AddSubgroup.mem_bot] at hv'
    subst hv'
    trivial

/-- **An aperture legal in one frame can be illegal in the next.**

The widest aperture is admissible while nothing is retained.  Widen what is retained — along the
identity transport, over one carrier, with the form unchanged — and the same aperture is no longer
admissible at all.

**So a cutoff is admissible relative to a frame, not as a property of the material.**  That is the
third derived object to be shown frame-relative, after the obstruction and the perp, and it is the
one that was most tempting to infer rather than prove. -/
theorem theCutoffDoesNotTravel :
    ((1, 0, 0) : Cells) ∈ wideCutoffDatum.cutoff
      ∧ ¬ (∀ v ∈ fullRemainderDatum.remainder,
            fullRemainderDatum.form ((1, 0, 0) : Cells) v = 0) := by
  refine ⟨trivial, ?_⟩
  intro h
  have h2 : standardForm ((1, 0, 0) : Cells) ((1, 0, 0) : Cells) = 0 :=
    h ((1, 0, 0) : Cells) trivial
  norm_num [standardForm_apply] at h2

/-- **And under it the perp does not transport.**

With nothing retained the perp condition is vacuous, so every chain satisfies it; downstream the
form is definite on everything and only zero does.  A single edge witnesses the failure.

So `thePerpTransportsWhenTheRemainderIsCovered` needs its hypothesis, and the form's derived data
splits: **the radical travels, the perp does not.** -/
theorem thePerpDoesNotTransport :
    ((1, 0, 0) : Cells) ∈ emptyRemainderDatum.perp
      ∧ widenTheRemainder.transport ((1, 0, 0) : Cells) ∉ fullRemainderDatum.perp := by
  constructor
  · intro v hv
    have hv' : v ∈ (⊥ : AddSubgroup Cells) := hv
    rw [AddSubgroup.mem_bot] at hv'
    subst hv'
    show standardForm ((1, 0, 0) : Cells) 0 = 0
    rw [map_zero]
  · intro h
    have h2 : standardForm ((1, 0, 0) : Cells) ((1, 0, 0) : Cells) = 0 :=
      h ((1, 0, 0) : Cells) trivial
    norm_num [standardForm_apply] at h2

/-! ## The sign is determined by the form, except where the form vanishes -/

/-- **Where the form is nonzero on the remainder, the sign is forced.**

The sign is a declared field, but semi-definiteness pins it as soon as the form has any nonzero
self-pairing on what is retained.  So it is declared and not free — the last of the three declared
fields, and the only one that is determined rather than frame-relative. -/
theorem theSignIsForcedWhereTheFormIsNonzero {V : Type u} [AddCommGroup V]
    (C : CompressedPositivity V) {v : V} (hv : v ∈ C.remainder) (hne : C.form v v ≠ 0) :
    (0 < C.form v v ∧ C.sign = 1) ∨ (C.form v v < 0 ∧ C.sign = -1) := by
  have hd := C.definite v hv
  rcases C.sign_unit with hs | hs
  · left
    rw [hs, one_mul] at hd
    exact ⟨lt_of_le_of_ne hd (Ne.symm hne), hs⟩
  · right
    rw [hs] at hd
    refine ⟨?_, hs⟩
    have : C.form v v ≤ 0 := by linarith
    exact lt_of_le_of_ne this hne

/-- The empty-remainder datum with the opposite sign — equally legal. -/
def emptyRemainderDatumNegative : CompressedPositivity Cells where
  form := standardForm
  form_symm := hollowTriangleDatum.form_symm
  cutoff := ⊥
  remainder := ⊥
  orthogonal := by
    intro c hc v _
    rw [AddSubgroup.mem_bot] at hc
    subst hc
    show standardForm 0 v = 0
    rw [map_zero]
    rfl
  sign := -1
  sign_unit := Or.inr rfl
  definite := by
    intro v hv
    have hv' : v ∈ (⊥ : AddSubgroup Cells) := hv
    rw [AddSubgroup.mem_bot] at hv'
    subst hv'
    show (0 : ℚ) ≤ -1 * standardForm 0 0
    rw [map_zero]
    simp

/-- **And where the form vanishes on the remainder, the sign is genuinely free.**

Two data over one carrier with one form, differing only in sign, both legal.  So the sign is not
determined in general — it is determined exactly where the form has something to say. -/
theorem theSignIsFreeWhereTheFormVanishes :
    emptyRemainderDatum.form = emptyRemainderDatumNegative.form
      ∧ emptyRemainderDatum.remainder = emptyRemainderDatumNegative.remainder
      ∧ emptyRemainderDatum.sign ≠ emptyRemainderDatumNegative.sign := by
  refine ⟨rfl, rfl, ?_⟩
  show (1 : ℚ) ≠ -1
  norm_num

end Soma.Holonics.Millennium.FormRebase
