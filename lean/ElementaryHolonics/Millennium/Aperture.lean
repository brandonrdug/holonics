import ElementaryHolonics.Millennium.Separation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-!
# The separation row: a lower bound is a statement about aperture size

The other five rows of the coupling ask whether a form is positive.  This one asks whether a
family **separates**, and `MillenniumCoupling.theDefinitenessIsSeparation` already proves those are
the same property.  What is owed here is the mechanism, and it is pigeonhole:

```text
|Y|^{|F|} < |X|   ⟹   some pair collapses
```

The joint reading of a finite family lands in `Y^F`; if that codomain is smaller than the
population, two constructions share a reading and **no member of the family tells them apart**
(`theFamilyTooSmallCollapses`).  Contrapositive: a family that separates the whole population must
satisfy `|X| ≤ |Y|^{|F|}` — so a lower bound on the population is a lower bound on the aperture,
and *that is what a circuit lower bound is* (`theSeparatingFamilyIsLargeEnough`).

`theBooleanPopulationDemandsAnExponentialAperture` makes it concrete: the Boolean functions on `n`
inputs number `2^{2^n}`, a family of `k` binary readings distinguishes at most `2^k` classes, so the
aperture must reach `2^n` before separation is even possible.

The reading that matters: **the exponential is not a difficulty about any particular function.**  It
is the size of the aperture the population demands, and the family is not defeated by the hardness
of what it reads but by its own size against it.  That is the same sentence as every other row —
the receiver decides what is separable.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.Millennium.Aperture

open Soma.Holonics.Millennium.Separation Finset

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The joint reading of a finite receiver family: what the whole family returns at a point. -/
def jointReading (F : Finset (X → Y)) (x : X) : F → Y := fun f => f.val x

/-- **A RECEIVER FAMILY TOO SMALL FOR ITS POPULATION MUST COLLAPSE A PAIR.**  The joint reading
lands in `Y^F`; if that is smaller than the population, two constructions share a reading and no
member of the family tells them apart.

This is the counting lower bound in its exact form — **`|Y|^{|F|} < |X|` forces a collapse** — and
it says the obstruction is an *aperture* one.  A family is not defeated by the difficulty of the
population but by its own size against it, which is the same statement as everywhere else in the
frame: the receiver decides what is separable. -/
theorem theFamilyTooSmallCollapses (F : Finset (X → Y))
    (h : Fintype.card Y ^ F.card < Fintype.card X) :
    ∃ a b : X, a ≠ b ∧ collapseOf (↑F : Set (X → Y)) a b := by
  have hcard : Fintype.card (F → Y) < Fintype.card X := by
    rw [Fintype.card_fun, Fintype.card_coe]
    exact h
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (jointReading F) hcard
  refine ⟨a, b, hne, fun f hf => ?_⟩
  have := congrFun heq ⟨f, hf⟩
  simpa [jointReading] using this

/-- **AND CONVERSELY, A FAMILY THAT SEPARATES MUST BE BIG ENOUGH.**  Contrapositive: separating the
whole population forces `|X| ≤ |Y|^{|F|}`, so a lower bound on the population is a lower bound on
the aperture.  That is what a circuit lower bound *is*. -/
theorem theSeparatingFamilyIsLargeEnough (F : Finset (X → Y))
    (hsep : ∀ a b : X, collapseOf (↑F : Set (X → Y)) a b → a = b) :
    Fintype.card X ≤ Fintype.card Y ^ F.card := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, b, hne, hc⟩ := theFamilyTooSmallCollapses F hlt
  exact hne (hsep a b hc)

/-! ## The Boolean instance: the aperture bound is exponential -/

/-- **FEWER THAN `2^n` READINGS CANNOT SEPARATE THE BOOLEAN FUNCTIONS ON `n` INPUTS.**  The
population has size `2^{2^n}` and a family of `k` binary readings distinguishes at most `2^k`
classes, so the aperture must reach `2^n` before separation is even possible.

That exponential is not a difficulty about any particular function — it is the **size of the
aperture** the population demands, and every lower-bound programme is an attempt to show a
declared family sits below it. -/
theorem theBooleanPopulationDemandsAnExponentialAperture (n : ℕ)
    (F : Finset (((Fin n → Bool) → Bool) → Bool)) (h : F.card < 2 ^ n) :
    ∃ a b : (Fin n → Bool) → Bool, a ≠ b ∧
      collapseOf (↑F : Set (((Fin n → Bool) → Bool) → Bool)) a b := by
  refine theFamilyTooSmallCollapses F ?_
  have hX : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
    simp [Fintype.card_fun]
  have hY : Fintype.card Bool = 2 := rfl
  rw [hX, hY]
  exact Nat.pow_lt_pow_right (by norm_num) h

end Soma.Holonics.Millennium.Aperture
