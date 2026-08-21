import ElementaryHolonics.Millennium.Gluing
import ElementaryHolonics.Millennium.Triangle

/-!
# The rebase — an obstruction belongs to a frame, not to a carrier

The July authority record on the arithmetic line rejects the picture every structure in this
development assumes: an ambient carrier held fixed while populations are compared inside it.  Its
words are that such a picture *"lets an observer stand outside the arithmetic process, freeze the
former manifold, append a new coordinate, and compare both inside one supposed total field."*

This file supplies the minimal correction and one witness.  A **rebase** carries one passage to
another; and **the same carrier under a different realization has a different obstruction**, so an
obstruction group is an invariant of the material *and its frame* and never of the material alone.

That is the no-absolute-frame law arriving inside this development rather than being quoted at it.

Every `theorem` here is discharged.
-/

namespace Soma.Holonics.Millennium.Rebase

open Soma.Holonics.Millennium Soma.Holonics.Millennium.Triangle

/-- A **rebase**: a transport of carriers under which each population lands inside its successor. -/
structure PassageRebase (A B : AdditivePassage.{0}) where
  /-- The transport of carriers. -/
  transport : A.Candidate →+ B.Candidate
  /-- What was realized stays realized. -/
  realized_maps : AddSubgroup.map transport A.Realized ≤ B.Realized
  /-- What was admissible stays admissible. -/
  admissible_maps : AddSubgroup.map transport A.LocallyAdmissible ≤ B.LocallyAdmissible

/-- The hollow triangle's passage: the loop is admissible and nothing realizes it. -/
def hollowPassage : AdditivePassage.{0} where
  Candidate := Cells
  Realized := ⊥
  LocallyAdmissible := boundary.ker
  realized_le := bot_le

/-- The same carrier once the face is filled: the loop is now realized. -/
def filledPassage : AdditivePassage.{0} where
  Candidate := Cells
  Realized := boundary.ker
  LocallyAdmissible := boundary.ker
  realized_le := le_rfl

/-- **Filling the face is a rebase along the identity transport.**

Nothing about the carrier moves.  What moves is which population is realized — which is exactly the
change the static picture cannot represent, because it holds the former block intact. -/
def fillTheFace : PassageRebase hollowPassage filledPassage where
  transport := AddMonoidHom.id Cells
  realized_maps := by
    simp only [hollowPassage, filledPassage, AddSubgroup.map_bot]
    exact bot_le
  admissible_maps := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hy

/-- **The hollow passage does not glue.** -/
theorem theHollowPassageDoesNotGlue : ¬ hollowPassage.Glues := by
  intro h
  have h2 : ((1, 1, 1) : Cells) ∈ hollowPassage.Realized := h theLoopIsInhabited
  rw [show hollowPassage.Realized = ⊥ from rfl, AddSubgroup.mem_bot] at h2
  exact one_ne_zero (congrArg Prod.fst h2)

/-- **The filled passage glues.** -/
theorem theFilledPassageGlues : filledPassage.Glues := le_rfl

/-- **Gluing does not transport.**

One carrier, one rebase along the identity, and the obstruction goes from inhabited to empty.  So
gluing is not a property the transport carries, and **an obstruction group is an invariant of the
material together with its frame — never of the material alone.**

This is the concrete form of the July correction: you cannot freeze the former manifold and compare
inside one supposed total field, because the same field with a different realization answers
differently. -/
theorem gluingDoesNotTransport :
    ∃ B : PassageRebase hollowPassage filledPassage,
      ¬ hollowPassage.Glues ∧ filledPassage.Glues :=
  ⟨fillTheFace, theHollowPassageDoesNotGlue, theFilledPassageGlues⟩

/-- **And therefore the obstruction group is not an invariant of the carrier.**

Both passages have the same `Candidate`.  One has an inhabited obstruction and the other does not. -/
theorem theObstructionIsNotAnInvariantOfTheCarrier :
    hollowPassage.Candidate = filledPassage.Candidate
      ∧ ¬ Subsingleton hollowPassage.ObstructionGroup
      ∧ Subsingleton filledPassage.ObstructionGroup := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    exact theHollowPassageDoesNotGlue
      ((AdditivePassage.glues_iff_obstruction_subsingleton _).mpr h)
  · exact (AdditivePassage.glues_iff_obstruction_subsingleton _).mp theFilledPassageGlues

/-- **A rebase composes.**  Rebasing is a transport and transports chain, so a lineage of foundings
is a lineage of rebases rather than a sequence of unrelated frames. -/
def PassageRebase.comp {A B C : AdditivePassage.{0}}
    (f : PassageRebase A B) (g : PassageRebase B C) : PassageRebase A C where
  transport := g.transport.comp f.transport
  realized_maps := by
    rw [← AddSubgroup.map_map]
    exact le_trans (AddSubgroup.map_mono f.realized_maps) g.realized_maps
  admissible_maps := by
    rw [← AddSubgroup.map_map]
    exact le_trans (AddSubgroup.map_mono f.admissible_maps) g.admissible_maps

/-- **And the identity is a rebase**, so every passage is its own frame and the lineage starts
somewhere. -/
def PassageRebase.id (A : AdditivePassage.{0}) : PassageRebase A A where
  transport := AddMonoidHom.id A.Candidate
  realized_maps := by intro x hx; obtain ⟨y, hy, rfl⟩ := hx; exact hy
  admissible_maps := by intro x hx; obtain ⟨y, hy, rfl⟩ := hx; exact hy

end Soma.Holonics.Millennium.Rebase
