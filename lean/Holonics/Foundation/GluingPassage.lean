import Mathlib.Logic.IsEmpty.Basic

/-!
# Gluing passages

A **gluing passage** is the situation in which local data is available, a population of
*realizers* is available, and the question is whether every locally admissible candidate is
*carried* by a realizer. This is a generic carrier for the obstruction population shared by
continuing towers and the research passages that instantiate it.

The single axiom is that realization lands inside local admissibility. The content of a specific
passage is whether the converse holds; this generic owner does not assume it.
-/

namespace Holonics.Millennium

universe u v

/-! ## The passage itself -/

/-- A **gluing passage**: local admissibility, a realizer population, and the realization map
that carries a realizer to the candidate it pays for.

The single axiom is that realization lands inside local admissibility — *a realized candidate
is always locally admissible*. The content of every open question of this shape is the converse,
which is not assumed here and cannot be. -/
structure GluingPassage where
  /-- What may be asked for. -/
  Candidate : Type u
  /-- What can be built. -/
  Realizer : Type v
  /-- Building it. -/
  realize : Realizer → Candidate
  /-- What the local receivers can already see. -/
  LocallyAdmissible : Candidate → Prop
  /-- Realization pays: what is built is locally admissible. -/
  realized_is_admissible : ∀ r : Realizer, LocallyAdmissible (realize r)

namespace GluingPassage

variable (P : GluingPassage.{u, v})

/-- A candidate is **carried** when some realizer realizes it. -/
def Carried (c : P.Candidate) : Prop := ∃ r : P.Realizer, P.realize r = c

/-- Realization pays, restated on candidates. This direction is free. -/
theorem carried_is_admissible {c : P.Candidate} (h : P.Carried c) :
    P.LocallyAdmissible c := by
  obtain ⟨r, rfl⟩ := h
  exact P.realized_is_admissible r

/-- The **obstruction population**: locally admissible candidates that nothing carries. -/
def Obstruction : Type u := { c : P.Candidate // P.LocallyAdmissible c ∧ ¬ P.Carried c }

/-- The passage **glues** when local admissibility already forces a realizer. -/
def Glues : Prop := ∀ c : P.Candidate, P.LocallyAdmissible c → P.Carried c

/-- **Gluing is exactly the emptiness of the obstruction population.** -/
theorem glues_iff_obstruction_isEmpty : P.Glues ↔ IsEmpty P.Obstruction := by
  constructor
  · intro h
    exact ⟨fun x => x.2.2 (h x.1 x.2.1)⟩
  · intro h c hc
    exact Classical.byContradiction fun hnc => h.false ⟨c, hc, hnc⟩

/-- A witness against gluing is an inhabitant of the obstruction, and conversely. -/
theorem not_glues_iff_obstruction_nonempty : ¬ P.Glues ↔ Nonempty P.Obstruction := by
  rw [glues_iff_obstruction_isEmpty, not_isEmpty_iff]

end GluingPassage
end Holonics.Millennium
