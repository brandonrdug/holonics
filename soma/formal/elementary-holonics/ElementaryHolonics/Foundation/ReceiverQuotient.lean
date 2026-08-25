import ElementaryHolonics.Foundation.MeasuredDifferenceReceiver
import ElementaryHolonics.Foundation.TransportLift

/-!
# Receiver quotients retain their complete predecessor fibres

This file composes the existing static receiver-exact `Compression` owner with the transport-lift
owner.  A quotient face is therefore never assigned an invented inverse: its inverse image is a
typed reconstruction fibre, and a chosen section is additional structure.

The final section does not introduce a new softmax model.  It places the existing holonic binary
exponential adaptation from `MeasuredDifferenceReceiver` into the receiver-quotient owner.  The
quotient is the oriented potential difference; a common shift stays in one fibre; the normalized
exponential is the already-proved receiver factor.
-/

namespace Soma.Holonics.Foundation.ReceiverCompression

open Soma.Holonics
open Soma.Holonics.Foundation.MeasuredDifferenceReceiver
open Soma.Holonics.Foundation.Lift

universe u v w x

/-- [definition] The established receiver-exact compression, named at its quotient role. -/
abbrev ReceiverQuotient (Receiver : Type u) (Source : Type v)
    (Quotient : Type w) (Face : Type x) :=
  Compression Receiver Source Quotient Face

/-- [definition] The complete predecessor population behind one quotient face. -/
def reconstructionFibre {Receiver : Type u} {Source : Type v}
    {Quotient : Type w} {Face : Type x}
    (C : ReceiverQuotient Receiver Source Quotient Face) (quotient : Quotient) : Type v :=
  TransportLift C.quotient quotient

/-- Equal quotient faces exhibit both sources inside one complete reconstruction fibre. -/
def quotient_eq_places_both_in_one_fibre
    {Receiver : Type u} {Source : Type v} {Quotient : Type w} {Face : Type x}
    (C : ReceiverQuotient Receiver Source Quotient Face) {left right : Source}
    (same : C.quotient left = C.quotient right) :
    reconstructionFibre C (C.quotient left) × reconstructionFibre C (C.quotient left) :=
  (⟨left, rfl⟩, ⟨right, same.symm⟩)

/-- [definition] A section is extra structure selecting one source in every quotient fibre. -/
structure QuotientSection
    {Receiver : Type u} {Source : Type v} {Quotient : Type w} {Face : Type x}
    (C : ReceiverQuotient Receiver Source Quotient Face) where
  choice : Quotient → Source
  rightInverse : ∀ quotient, C.quotient (choice quotient) = quotient

/-- A declared section exhibits an inhabitant of every quotient fibre; it does not make that
fibre a singleton. -/
def QuotientSection.lift
    {Receiver : Type u} {Source : Type v} {Quotient : Type w} {Face : Type x}
    {C : ReceiverQuotient Receiver Source Quotient Face}
    (chosen : QuotientSection C) (quotient : Quotient) :
    reconstructionFibre C quotient :=
  ⟨chosen.choice quotient, chosen.rightInverse quotient⟩

/-! ## The established binary exponential chart as a receiver quotient -/

noncomputable section

/-- [proved-derived; formal-checked] The existing binary exponential face factors through the
oriented potential difference as a receiver-exact quotient. -/
def binaryExponentialQuotient : ReceiverQuotient Unit (ℝ × ℝ) ℝ ℝ where
  quotient potentials := potentials.2 - potentials.1
  receiver _ potentials := binaryExponentialFace potentials.1 potentials.2
  factor _ := logisticDifference
  exact _ potentials :=
    (binaryExponentialFace_eq_logisticDifference potentials.1 potentials.2).symm

/-- A common additive potential is exactly a direction inside one quotient fibre. -/
theorem binaryExponentialQuotient_common_shift
    (first second common : ℝ) :
    binaryExponentialQuotient.quotient (first + common, second + common) =
      binaryExponentialQuotient.quotient (first, second) := by
  dsimp [binaryExponentialQuotient]
  ring

/-- Consequently the complete binary exponential receiver cannot distinguish a common shift. -/
theorem binaryExponentialReceiver_common_shift
    (first second common : ℝ) :
    binaryExponentialQuotient.receiver () (first + common, second + common) =
      binaryExponentialQuotient.receiver () (first, second) := by
  exact binaryExponentialQuotient.receiver_eq_of_quotient_eq
    (binaryExponentialQuotient_common_shift first second common) ()

/-- Both shifted potential pairs are returned in one explicit reconstruction fibre. -/
def binaryCommonShiftFibre (first second common : ℝ) :
    reconstructionFibre binaryExponentialQuotient (second - first) ×
      reconstructionFibre binaryExponentialQuotient (second - first) :=
  (⟨(first, second), rfl⟩,
   ⟨(first + common, second + common), by
      dsimp [binaryExponentialQuotient]
      ring⟩)

end

section Audit

#print axioms quotient_eq_places_both_in_one_fibre
#print axioms binaryExponentialQuotient_common_shift
#print axioms binaryExponentialReceiver_common_shift

end Audit

end Soma.Holonics.Foundation.ReceiverCompression
