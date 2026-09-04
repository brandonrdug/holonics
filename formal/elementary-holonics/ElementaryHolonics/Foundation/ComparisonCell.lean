import ElementaryHolonics.Foundation.AddressedBoundary

/-!
# Addressed comparison cells

A comparison cell retains two parallel carrying occurrences and the common source at which their
routes can genuinely be compared.  Exact target commutation and receiver-relative commutation are
properties derived from that data.  They are not constructor fields.
-/

namespace Soma.Holonics

universe u v w x

namespace AddressedPassage

variable {X : Type u} {Y : Type v}

/-- Two parallel route occurrences placed at one exact source address. -/
structure ComparisonCell (P Q : AddressedPassage X Y) where
  left : P.Occurrence
  right : Q.Occurrence
  source_exact : P.source left = Q.source right

namespace ComparisonCell

variable {P Q : AddressedPassage X Y}

/-- Exact commutation is equality of the two returned target faces. -/
def Commutes (cell : ComparisonCell P Q) : Prop :=
  P.target cell.left = Q.target cell.right

/-- A declared receiver may see a commuting face even when the targets remain distinct. -/
def CommutesAt (cell : ComparisonCell P Q) {Face : Type x} (receiver : Y → Face) : Prop :=
  receiver (P.target cell.left) = receiver (Q.target cell.right)

/-- A functional receiver exposes both route faces and a proof that they differ. -/
structure ReceiverDefect (cell : ComparisonCell P Q) (Face : Type x) (receiver : Y → Face) where
  separates : receiver (P.target cell.left) ≠ receiver (Q.target cell.right)

/-- The left route's returned receiver face. -/
def ReceiverDefect.leftFace {cell : ComparisonCell P Q} {Face : Type x}
    {receiver : Y → Face} (_defect : ReceiverDefect cell Face receiver) : Face :=
  receiver (P.target cell.left)

/-- The right route's returned receiver face. -/
def ReceiverDefect.rightFace {cell : ComparisonCell P Q} {Face : Type x}
    {receiver : Y → Face} (_defect : ReceiverDefect cell Face receiver) : Face :=
  receiver (Q.target cell.right)

/-- Exact target commutation implies commutation at every dependent receiver. -/
theorem commutesAt_of_commutes (cell : ComparisonCell P Q) (h : cell.Commutes)
    {Face : Type x} (receiver : Y → Face) : cell.CommutesAt receiver := by
  unfold CommutesAt
  exact congrArg receiver h

/-- A receiver defect constructively refuses exact commutation. -/
theorem not_commutes_of_receiverDefect (cell : ComparisonCell P Q)
    {Face : Type x} {receiver : Y → Face} (defect : cell.ReceiverDefect Face receiver) :
    ¬ cell.Commutes := by
  intro h
  exact defect.separates (congrArg receiver h)

end ComparisonCell

end AddressedPassage

end Soma.Holonics

section Audit
open Soma.Holonics
#print axioms AddressedPassage.ComparisonCell.commutesAt_of_commutes
#print axioms AddressedPassage.ComparisonCell.not_commutes_of_receiverDefect
end Audit
