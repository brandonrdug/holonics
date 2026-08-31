import ElementaryHolonics.Millennium.HodgeSmoothProjectiveReceiver

/-!
# Hodge source-construction finish line

[definition] The existing `SourceDeterminedHodgeTheory.Conclusion` is the primitive-algebraicity
receiver once the classical analytic/Hodge/cycle-class current has been constructed.  It is not,
by itself, a closed finish line: a caller still supplies that current.

[established-bounded; source-audit] Mathlib presently has no canonical complex analytification,
pure Hodge decomposition, or algebraic-cycle fundamental-class construction for arbitrary smooth
projective complex schemes.  This file therefore does **not** claim a formal statement equivalent
to the official Hodge conjecture.  It makes the missing standard source construction an explicit
existential boundary and keeps its return separate from the conjectural algebraicity field.

[definition] The closed proposition `HodgeSourceConstructionFinishLine` asks for both:

* [definition] one universal source construction, carrying analytification, Hodge decomposition, fundamental
  classes and Poincare duality for every represented smooth projective complex scheme; and
* [definition] the existing primitive-algebraicity conclusion for the same construction.

[proved-derived; formal-checked] An empty official predicate cannot make this receiver true, and
the conjectural conclusion is not stored in the source-construction object itself.

[open] The fields of `SourceDeterminedHodgeTheory` are the strongest source contract currently
expressed by this Lean line, but the absent canonical comparison library prevents proving that an
inhabitant is the unique classical construction rather than another coherent model of that
contract.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeOfficialReceiver

open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver

/-- [definition] The nonconjectural source-construction return.

The wrapper adds no data and, in particular, no algebraicity proof.  Its purpose is to make the
standard analytic/Hodge/fundamental-class construction a different port from the primitive Hodge
surjectivity receiver. -/
structure ClassicalHodgeSourceConstruction where
  theory : SourceDeterminedHodgeTheory

namespace ClassicalHodgeSourceConstruction

/-- [definition] Primitive algebraicity for the exact theory returned by this source
construction. -/
def PrimitiveAlgebraicity (source : ClassicalHodgeSourceConstruction) : Prop :=
  source.theory.Conclusion

/-- [proved-derived; formal-checked] A source-construction/algebraicity pair terminates literally
in the existing source-determined receiver. -/
theorem to_sourceDeterminedConclusion
    (source : ClassicalHodgeSourceConstruction)
    (halgebraic : source.PrimitiveAlgebraicity) :
    source.theory.Conclusion :=
  halgebraic

/-- [proved-derived; formal-checked] The same return reaches the existing realization-family
receiver selected by the source current. -/
theorem to_theHodgeConjecture
    (source : ClassicalHodgeSourceConstruction)
    (halgebraic : source.PrimitiveAlgebraicity) :
    TheHodgeConjecture source.theory.Canonical :=
  source.theory.conclusion_iff_theHodgeConjecture.mp halgebraic

end ClassicalHodgeSourceConstruction

/-- [definition] The repository's closed Hodge construction target.

This is deliberately named a *source-construction finish line*, not the official theorem.  A term
must construct the missing classical source current and then prove primitive algebraicity for that
same current. -/
def HodgeSourceConstructionFinishLine : Prop :=
  ∃ source : ClassicalHodgeSourceConstruction, source.PrimitiveAlgebraicity

namespace HodgeSourceConstructionFinishLine

/-- [proved-derived; formal-checked] The finish line exposes its nonconjectural source
construction separately from the conjectural return. -/
theorem returns_source_and_algebraicity
    (h : HodgeSourceConstructionFinishLine) :
    ∃ source : ClassicalHodgeSourceConstruction,
      source.theory.Conclusion :=
  h

/-- [proved-derived; formal-checked] Every completed construction returns a concrete existing
`SourceDeterminedHodgeTheory.Conclusion`; no arbitrary official-family predicate is introduced. -/
theorem to_sourceDeterminedConclusion
    (h : HodgeSourceConstructionFinishLine) :
    ∃ theory : SourceDeterminedHodgeTheory, theory.Conclusion := by
  obtain ⟨source, halgebraic⟩ := h
  exact ⟨source.theory, source.to_sourceDeterminedConclusion halgebraic⟩

/-- [proved-derived; formal-checked] The construction also reaches the earlier realization-family
receiver for the exact source current it returned.  This is an adapter, not an equivalence with a
parameter-free classical theorem. -/
theorem to_sourceSelectedTheHodgeConjecture
    (h : HodgeSourceConstructionFinishLine) :
    ∃ theory : SourceDeterminedHodgeTheory,
      TheHodgeConjecture theory.Canonical := by
  obtain ⟨source, halgebraic⟩ := h
  exact ⟨source.theory, source.to_theHodgeConjecture halgebraic⟩

end HodgeSourceConstructionFinishLine

/-- [proved-derived; formal-checked] A separately constructed standard source and a proof of its
primitive algebraicity fill the closed repository receiver. -/
theorem hodgeSourceConstructionFinishLine_of
    (source : ClassicalHodgeSourceConstruction)
    (halgebraic : source.theory.Conclusion) :
    HodgeSourceConstructionFinishLine :=
  ⟨source, halgebraic⟩

end Soma.Holonics.Millennium.HodgeOfficialReceiver
