import ElementaryHolonics.Foundation.ComparisonCell
import Mathlib.Algebra.Group.Hom.Basic

/-!
# Loss reads a situated comparison

A loss gauge reads the two receiver faces of an existing addressed comparison cell. Its value
need not be scalar, symmetric, nonnegative, or zero on agreement. The complete comparison and
its oriented difference remain available before that gauge is applied. A statistical entropy,
mechanical mismatch or model discrepancy can instantiate this same interface.
-/

namespace Soma.Holonics.AddressedPassage.ComparisonCell

variable {X Y Face Value : Type*} {P Q : AddressedPassage X Y}

/-- Both compared faces remain tied to their actual parallel source passages. -/
def observedPair (cell : ComparisonCell P Q) (receiver : Y → Face) : Face × Face :=
  (receiver (P.target cell.left), receiver (Q.target cell.right))

/-- A declared measurement of the comparison, with no machine-learning restriction. -/
def loss (cell : ComparisonCell P Q) (receiver : Y → Face) (gauge : Face → Face → Value) : Value :=
  gauge (cell.observedPair receiver).1 (cell.observedPair receiver).2

/-- Agreement returns the gauge's actual diagonal baseline; zero is an additional property. -/
theorem loss_of_receiver_agreement (cell : ComparisonCell P Q) (receiver : Y → Face)
    (gauge : Face → Face → Value) (agrees : cell.CommutesAt receiver) :
    cell.loss receiver gauge = gauge (receiver (P.target cell.left))
      (receiver (P.target cell.left)) := by
  change gauge (receiver (P.target cell.left)) (receiver (Q.target cell.right)) = _
  rw [show receiver (Q.target cell.right) = receiver (P.target cell.left) from agrees.symm]

/-- The signed difference precedes a norm, energy, or other scalar receiver. -/
def orientedDifference [AddCommGroup Face] (cell : ComparisonCell P Q) (receiver : Y → Face) : Face :=
  receiver (Q.target cell.right) - receiver (P.target cell.left)

theorem orientedDifference_zero_iff [AddCommGroup Face]
    (cell : ComparisonCell P Q) (receiver : Y → Face) :
    cell.orientedDifference receiver = 0 ↔ cell.CommutesAt receiver := by
  change receiver (Q.target cell.right) - receiver (P.target cell.left) = 0 ↔
    receiver (P.target cell.left) = receiver (Q.target cell.right)
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    exact sub_eq_zero.mpr h.symm

/-- A chart change preserves the comparison measurement when it carries the gauge as well. -/
theorem loss_rechart {OtherFace : Type*} (cell : ComparisonCell P Q) (receiver : Y → Face)
    (chart : Face → OtherFace) (gauge : Face → Face → Value)
    (otherGauge : OtherFace → OtherFace → Value)
    (compatible : ∀ left right, otherGauge (chart left) (chart right) = gauge left right) :
    cell.loss (chart ∘ receiver) otherGauge = cell.loss receiver gauge :=
  compatible _ _

#print axioms loss_of_receiver_agreement
#print axioms orientedDifference_zero_iff
#print axioms loss_rechart

end Soma.Holonics.AddressedPassage.ComparisonCell
