import ElementaryHolonics.Millennium.LineageCompression

/-!
# Receiver-history identity

The executable finite quotient computes the coarsest stable receiver/history relation.  The
existing `ReceiverHistoryCompression` proves soundness: equal quotient faces force every future
receiver face to agree.  This file names the converse obligation required for native identity and
derives the exact equivalence and constructive separating-history law.

Nothing here treats a token window, prompt hash, transcript, or proof language as state.
-/

namespace Soma.Holonics.Millennium.ReceiverHistory

open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.LineageCompression

universe u v w x y

/-- A receiver/history compression which is also complete for its declared future family. -/
structure CompleteReceiverHistoryQuotient
    (Generator : Type u) (Receiver : Type v)
    (Source : Type w) (Quotient : Type x) (Face : Type y)
    extends ReceiverHistoryCompression Generator Receiver Source Quotient Face where
  complete : ∀ {left right : Source},
    (∀ receiver word,
      toReceiverHistoryCompression.present.receiver receiver
          (transportWord toReceiverHistoryCompression.sourceTransport word left) =
        toReceiverHistoryCompression.present.receiver receiver
          (transportWord toReceiverHistoryCompression.sourceTransport word right)) →
    toReceiverHistoryCompression.present.quotient left =
      toReceiverHistoryCompression.present.quotient right

namespace CompleteReceiverHistoryQuotient

variable {Generator : Type u} {Receiver : Type v}
  {Source : Type w} {Quotient : Type x} {Face : Type y}
  (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face)

/-- The rich causal signature is the complete receiver face after every ordered transport word. -/
def causalSignature (source : Source) : Receiver → List Generator → Face :=
  fun receiver word =>
    C.present.receiver receiver (transportWord C.sourceTransport word source)

/-- Native equality is exactly equality of the complete declared causal signatures. -/
theorem quotientEq_iff_causalSignatureEq {left right : Source} :
    C.present.quotient left = C.present.quotient right ↔
      C.causalSignature left = C.causalSignature right := by
  constructor
  · intro h
    funext receiver word
    exact C.toReceiverHistoryCompression.quotientEqForcesEverySuccessorFace h receiver word
  · intro h
    apply C.complete
    intro receiver word
    exact congrFun (congrFun h receiver) word

/-- Unequal native states return an explicit receiver and ordered history which separates them. -/
theorem quotientNe_returnsSeparatingReceiverHistory {left right : Source}
    (h : C.present.quotient left ≠ C.present.quotient right) :
    ∃ receiver word,
      C.causalSignature left receiver word ≠ C.causalSignature right receiver word := by
  classical
  by_contra noSeparator
  apply h
  apply C.complete
  intro receiver word
  by_contra separated
  exact noSeparator ⟨receiver, word, separated⟩

/-- Literal source occurrences remain plural even when their native state is equal. -/
theorem quotientEqualityRetainsBothOccurrences {left right : Source}
    (h : C.present.quotient left = C.present.quotient right) :
    ∃ leftIn rightIn : C.toReceiverHistoryCompression.preimageFibre
        (C.present.quotient left),
      leftIn.1 = left ∧ rightIn.1 = right :=
  C.toReceiverHistoryCompression.quotientEqPlacesBothOccurrencesInOneFibre h

end CompleteReceiverHistoryQuotient

end Soma.Holonics.Millennium.ReceiverHistory

section Audit
open Soma.Holonics.Millennium.ReceiverHistory
#print axioms CompleteReceiverHistoryQuotient.quotientEq_iff_causalSignatureEq
#print axioms CompleteReceiverHistoryQuotient.quotientNe_returnsSeparatingReceiverHistory
#print axioms CompleteReceiverHistoryQuotient.quotientEqualityRetainsBothOccurrences
end Audit
