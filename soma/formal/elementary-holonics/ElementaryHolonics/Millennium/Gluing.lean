import Mathlib.Algebra.Order.Field.Rat
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The gluing passage — the shape every open placement question shares

A **gluing passage** is the situation in which local data is available, a population of
*realizers* is available, and the question is whether every locally admissible candidate is
*carried* by a realizer.  This file factors that shape out once so that the named lines in
`Millennium/Lines.lean` are configurations of one structure rather than six unrelated
statements.

The vocabulary is composed rather than eponymous, per the naming discipline: a name should let
its mechanism be read off it and rebuilt from it by a reader who holds no shared history.  The
classical label is carried as an aside on each declaration and never as the name.

Every `theorem` in this file is discharged.  Nothing here is assumed.
-/

namespace Soma.Holonics.Millennium

universe u v

/-! ## 1. The passage itself -/

/-- A **gluing passage**: local admissibility, a realizer population, and the realization map
that carries a realizer to the candidate it pays for.

The single axiom is that realization lands inside local admissibility — *a realized candidate
is always locally admissible*.  The content of every open question of this shape is the
converse, which is not assumed here and cannot be. -/
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

/-- Realization pays, restated on candidates.  This direction is free. -/
theorem carried_is_admissible {c : P.Candidate} (h : P.Carried c) :
    P.LocallyAdmissible c := by
  obtain ⟨r, rfl⟩ := h
  exact P.realized_is_admissible r

/-- The **obstruction population**: locally admissible candidates that nothing carries.
This is the object every open line in this family is missing a handle on. -/
def Obstruction : Type u := { c : P.Candidate // P.LocallyAdmissible c ∧ ¬ P.Carried c }

/-- The passage **glues** when local admissibility already forces a realizer. -/
def Glues : Prop := ∀ c : P.Candidate, P.LocallyAdmissible c → P.Carried c

/-- **Gluing is exactly the emptiness of the obstruction population.**

This is the sentence the six named lines share.  It is trivial as mathematics and it is the
point: it says the content of each line is *a population*, so the useful question is never
"does it glue" but "what inhabits the obstruction, and what separates one inhabitant from
another". -/
theorem glues_iff_obstruction_isEmpty : P.Glues ↔ IsEmpty P.Obstruction := by
  constructor
  · intro h
    exact ⟨fun x => x.2.2 (h x.1 x.2.1)⟩
  · intro h c hc
    by_contra hnc
    exact h.false ⟨c, hc, hnc⟩

/-- A witness against gluing is an inhabitant of the obstruction, and conversely.  Stated so a
counterexample search has a type to return into. -/
theorem not_glues_iff_obstruction_nonempty : ¬ P.Glues ↔ Nonempty P.Obstruction := by
  rw [glues_iff_obstruction_isEmpty, not_isEmpty_iff]

end GluingPassage

/-! ## 2. When the candidates add, the obstruction is a group

The passages that have been *closed* historically are the ones whose obstruction carries group
structure, because a group can be computed with, bounded, and shown finite.  The passage that
has resisted longest — the verify-to-search gap — is precisely the one for which no obstruction
group is known.  This section makes "the obstruction is a group" a definition rather than a
remark. -/

/-- An **additive passage**: the candidates form an abelian group, and both the realized
population and the locally admissible population are subgroups of it. -/
structure AdditivePassage where
  /-- What may be asked for. -/
  Candidate : Type u
  /-- The candidates add. -/
  [addCommGroup : AddCommGroup Candidate]
  /-- What some realizer pays for. -/
  Realized : AddSubgroup Candidate
  /-- What the local receivers admit. -/
  LocallyAdmissible : AddSubgroup Candidate
  /-- Realization pays. -/
  realized_le : Realized ≤ LocallyAdmissible

namespace AdditivePassage

attribute [instance] AdditivePassage.addCommGroup

variable (A : AdditivePassage.{u})

/-- The passage **glues** when the two populations coincide. -/
def Glues : Prop := A.LocallyAdmissible ≤ A.Realized

/-- The **obstruction group**: locally admissible modulo realized.  Every closed line in this
family closed by getting a handle on this group. -/
abbrev ObstructionGroup : Type u :=
  A.LocallyAdmissible ⧸ (A.Realized.addSubgroupOf A.LocallyAdmissible)

/-- **Gluing is exactly the triviality of the obstruction group.** -/
theorem glues_iff_obstruction_subsingleton :
    A.Glues ↔ Subsingleton A.ObstructionGroup := by
  constructor
  · intro h
    refine ⟨fun x y => ?_⟩
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      induction y using QuotientAddGroup.induction_on with
      | H b =>
        refine QuotientAddGroup.eq.mpr ?_
        simpa [AddSubgroup.mem_addSubgroupOf] using h (by simpa using (-a + b).2)
  · intro h c hc
    have : (QuotientAddGroup.mk (⟨c, hc⟩ : A.LocallyAdmissible)
              : A.ObstructionGroup) = QuotientAddGroup.mk 0 := Subsingleton.elim _ _
    have := QuotientAddGroup.eq.mp this
    simpa [AddSubgroup.mem_addSubgroupOf] using this

/-- A candidate **reached only in multiple `k`**: `k` copies of it are paid for and it is not.

This is the faithful finite model of an integral-realization failure — the cokernel of the
realization map has a class of order dividing `k`.  It is a statement about the *integral*
question only; after tensoring with the rationals such a class is carried, and nothing here
may be reported as an obstruction to a rational line.

*Aside: the classical instances are the torsion counterexamples of Atiyah–Hirzebruch and the
non-torsion ones of Kollár.* -/
def ReachedOnlyInMultiple (k : ℕ) (c : A.Candidate) : Prop :=
  c ∈ A.LocallyAdmissible ∧ (k • c) ∈ A.Realized ∧ c ∉ A.Realized

/-- A candidate reached only in multiple `k` is an inhabitant of the obstruction, and its class
is killed by `k`.  **The multiple is the order of the obstruction class.** -/
theorem reachedOnlyInMultiple_is_torsion_class
    {k : ℕ} {c : A.Candidate} (h : A.ReachedOnlyInMultiple k c) :
    k • (QuotientAddGroup.mk (⟨c, h.1⟩ : A.LocallyAdmissible) : A.ObstructionGroup) = 0 ∧
      (QuotientAddGroup.mk (⟨c, h.1⟩ : A.LocallyAdmissible) : A.ObstructionGroup) ≠ 0 := by
  obtain ⟨hc, hk, hn⟩ := h
  constructor
  · rw [← QuotientAddGroup.mk_nsmul]
    refine QuotientAddGroup.eq_zero_iff _ |>.mpr ?_
    simpa [AddSubgroup.mem_addSubgroupOf] using hk
  · intro hzero
    exact hn (by simpa [AddSubgroup.mem_addSubgroupOf] using
      (QuotientAddGroup.eq_zero_iff _ |>.mp hzero))

end AdditivePassage

/-! ## 3. What a positive realizer supplies that an available one does not

A realizer that merely *exists* pays for nothing.  What pays is a realizer carrying a pairing
whose **null cone is a single point** — no nonzero object self-pairs to nothing.  This section
states that condition and derives the separation it buys.

*Aside: this is the content of the positivity of the Rosati involution, and the reason an
ample class and not merely an effective one is required.  An effective class can self-pair
negatively; the standard example is a curve of self-intersection −1.* -/

/-- A pairing on a realizer population whose **null cone is a single point**. -/
structure PayingPairing (R : Type u) [AddCommGroup R] where
  /-- The form. -/
  pair : R → R → ℚ
  /-- It is symmetric. -/
  pair_symm : ∀ a b, pair a b = pair b a
  /-- Self-pairings are never negative. -/
  pair_self_nonneg : ∀ a, 0 ≤ pair a a
  /-- **Only the zero object self-pairs to nothing.** -/
  null_cone_is_a_point : ∀ a, pair a a = 0 → a = 0

namespace PayingPairing

variable {R : Type u} [AddCommGroup R] (F : PayingPairing R)

/-- **A paying pairing separates: every nonzero object is seen by some pairing, namely with
itself.**  This is the whole force of positivity, and it is what a realizer that merely exists
does not supply. -/
theorem separates {a : R} (ha : a ≠ 0) : ∃ b, F.pair a b ≠ 0 :=
  ⟨a, fun h => ha (F.null_cone_is_a_point a h)⟩

/-- Restated as the placement sentence: **no nonzero object pairs to nothing against
everything.** -/
theorem no_object_is_invisible {a : R} (h : ∀ b, F.pair a b = 0) : a = 0 :=
  F.null_cone_is_a_point a (h a)

end PayingPairing

end Soma.Holonics.Millennium

-- Audit: every theorem above is discharged from the standard axioms only.
section Audit
open Soma.Holonics.Millennium
#print axioms GluingPassage.glues_iff_obstruction_isEmpty
#print axioms GluingPassage.not_glues_iff_obstruction_nonempty
#print axioms AdditivePassage.glues_iff_obstruction_subsingleton
#print axioms AdditivePassage.reachedOnlyInMultiple_is_torsion_class
#print axioms PayingPairing.separates
#print axioms PayingPairing.no_object_is_invisible
end Audit
