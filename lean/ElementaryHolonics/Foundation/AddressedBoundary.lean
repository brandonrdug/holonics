import ElementaryHolonics.Foundation.Lineage
import Mathlib.Data.Finsupp.Basic

/-!
# The additive boundary of an addressed occurrence

An occurrence contributes `-source` at its incoming face and `+target` at its outgoing face.
For heterogeneous passages these live in different free abelian groups.  A serial join therefore
returns three typed faces; its middle face cancels because the pullback occurrence owns the exact
joining equality.  This is edge-boundary cancellation, not a claim that a higher boundary squares
to zero and not a dynamic conservation law.
-/

namespace Soma.Holonics

universe u v w x

namespace AddressedPassage

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type x}

/-- The free additive face carried by one boundary population. -/
abbrev AdditiveFace (X : Type u) := X →₀ ℤ

/-- The incoming endpoint of an occurrence, with its causal orientation. -/
noncomputable def incomingBoundary (P : AddressedPassage X Y) (carried : P.Occurrence) : AdditiveFace X :=
  -Finsupp.single (P.source carried) 1

/-- The outgoing endpoint of an occurrence, with its causal orientation. -/
noncomputable def outgoingBoundary (P : AddressedPassage X Y) (carried : P.Occurrence) : AdditiveFace Y :=
  Finsupp.single (P.target carried) 1

/-- The two typed exterior faces of one carrying occurrence. -/
noncomputable def additiveBoundary (P : AddressedPassage X Y) (carried : P.Occurrence) :
    AdditiveFace X × AdditiveFace Y :=
  (P.incomingBoundary carried, P.outgoingBoundary carried)

/-- The shared face exposed before a serial join is condensed. -/
noncomputable def joinedMiddleBoundary (P : AddressedPassage X Y) (Q : AddressedPassage Y Z)
    (joined : Join P Q) : AdditiveFace Y :=
  P.outgoingBoundary joined.left + Q.incomingBoundary joined.right

/-- Pullback incidence is exactly the witness which cancels the joined middle face. -/
theorem boundary_join (P : AddressedPassage X Y) (Q : AddressedPassage Y Z)
    (joined : Join P Q) : joinedMiddleBoundary P Q joined = 0 := by
  unfold joinedMiddleBoundary outgoingBoundary incomingBoundary
  rw [joined.joins]
  simp

/-- Composition retains the incoming face of the first occurrence and outgoing face of the last. -/
theorem boundary_comp (P : AddressedPassage X Y) (Q : AddressedPassage Y Z)
    (joined : (comp Q P).Occurrence) :
    (comp Q P).additiveBoundary joined =
      (P.incomingBoundary joined.left, Q.outgoingBoundary joined.right) := rfl

/-- Rebracketing a triple join preserves both exterior additive faces. -/
theorem boundary_compAssociator (P : AddressedPassage X Y) (Q : AddressedPassage Y Z)
    (R : AddressedPassage Z W) (joined : (comp R (comp Q P)).Occurrence) :
    (comp (comp R Q) P).additiveBoundary
        ((compAssociator R Q P).occurrence joined) =
      (comp R (comp Q P)).additiveBoundary joined := rfl

/-- Passage equivalence transports the additive boundary without identifying occurrences. -/
theorem boundary_passageEquiv {P Q : AddressedPassage X Y}
    (equivalent : PassageEquiv P Q) (carried : P.Occurrence) :
    Q.additiveBoundary (equivalent.occurrence carried) = P.additiveBoundary carried := by
  apply Prod.ext
  · unfold additiveBoundary incomingBoundary
    simp only
    rw [equivalent.source_exact carried]
  · unfold additiveBoundary outgoingBoundary
    simp only
    rw [equivalent.target_exact carried]

/-- The relational composite is precisely the quotient which forgets the joined occurrence. -/
theorem additiveBoundary_shadow_forgets_the_carrier
    (P : AddressedPassage X Y) (Q : AddressedPassage Y Z) :
    shadow (comp Q P) = Rel.comp (shadow Q) (shadow P) := shadow_comp Q P

end AddressedPassage

end Soma.Holonics

section Audit
open Soma.Holonics
#print axioms AddressedPassage.boundary_join
#print axioms AddressedPassage.boundary_comp
#print axioms AddressedPassage.boundary_compAssociator
#print axioms AddressedPassage.boundary_passageEquiv
#print axioms AddressedPassage.additiveBoundary_shadow_forgets_the_carrier
end Audit
