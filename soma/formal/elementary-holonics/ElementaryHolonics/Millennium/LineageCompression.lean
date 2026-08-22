import ElementaryHolonics.Foundation.Lineage
import ElementaryHolonics.Millennium.Chronology

/-!
# Receiver-history compression over ordered transport words

`Foundation.Receiver.Compression` states exact factorization for a declared receiver family at one
cut.  That is intentionally static.  A holonic compression must survive the admitted continuations:
after any ordered word of source transports, every declared receiver must still factor through the
quotient.

The additional law is not another loss function.  It is generator-wise transport equivariance.
`Chronology.generatorEquivarianceExtendsToEveryTransportWord` then proves the whole successor
family at once, with noncommuting order retained.  A future receiver that separates a proposed
quotient fibre is therefore a constructive falsifier of that compression.

The finite control in section 3 shows why the extension is necessary: two occurrences can agree
under a static receiver and quotient, then separate after one successor transport.  Every theorem
is discharged.  Nothing here asserts a result about a named Millennium problem.
-/

namespace Soma.Holonics.Millennium.LineageCompression

open Soma.Holonics
open Soma.Holonics.Millennium.Chronology

universe u v w x y

/--
A receiver-exact quotient whose source and quotient transports commute on every generator.

The quotient is not called a decoder: its full inverse image is retained as the reconstruction
fibre below.  A codec compression additionally owes an exterior presentation and decoder cost.
-/
structure ReceiverHistoryCompression
    (Generator : Type u) (Receiver : Type v)
    (Source : Type w) (Quotient : Type x) (Face : Type y) where
  /-- Exact factorization at the present receiver cut. -/
  present : Compression Receiver Source Quotient Face
  /-- The admitted source transport generators. -/
  sourceTransport : Generator → Source → Source
  /-- Their proposed transports on the quotient. -/
  quotientTransport : Generator → Quotient → Quotient
  /-- The quotient commutes with every generator. -/
  generatorExact : ∀ generator source,
    present.quotient (sourceTransport generator source) =
      quotientTransport generator (present.quotient source)

namespace ReceiverHistoryCompression

variable {Generator : Type u} {Receiver : Type v}
  {Source : Type w} {Quotient : Type x} {Face : Type y}
  (C : ReceiverHistoryCompression Generator Receiver Source Quotient Face)

/-- The complete predecessor population retained behind one quotient face. -/
def reconstructionFibre (quotient : Quotient) : Type _ :=
  { source : Source // C.present.quotient source = quotient }

/-- Equal quotient faces place two occurrences in one retained reconstruction fibre. -/
theorem quotientEqPlacesBothOccurrencesInOneFibre {left right : Source}
    (h : C.present.quotient left = C.present.quotient right) :
    ∃ leftIn rightIn : C.reconstructionFibre (C.present.quotient left),
      leftIn.1 = left ∧ rightIn.1 = right :=
  ⟨⟨left, rfl⟩, ⟨right, h.symm⟩, rfl, rfl⟩

/-- Generator-wise exactness extends to every ordered, possibly noncommuting transport word. -/
theorem quotientCommutesWithEveryOrderedWord (word : List Generator) (source : Source) :
    C.present.quotient (transportWord C.sourceTransport word source) =
      transportWord C.quotientTransport word (C.present.quotient source) :=
  generatorEquivarianceExtendsToEveryTransportWord
    C.sourceTransport C.quotientTransport C.present.quotient C.generatorExact word source

/-- The receiver family enlarged by every admitted successor word. -/
def futureReceiver : (Receiver × List Generator) → Source → Face
  | (receiver, word), source =>
      C.present.receiver receiver (transportWord C.sourceTransport word source)

/-- The corresponding factor on the quotient, with the same ordered word. -/
def futureFactor : (Receiver × List Generator) → Quotient → Face
  | (receiver, word), quotient =>
      C.present.factor receiver (transportWord C.quotientTransport word quotient)

/--
The quotient is exact for the complete declared receiver/history family.

This is the pure factorization theorem behind holonic compression: the infinite word family is
paid for by the local generator commuting law, not by enumerating successor histories.
-/
def allSuccessorHistories :
    Compression (Receiver × List Generator) Source Quotient Face where
  quotient := C.present.quotient
  receiver := C.futureReceiver
  factor := C.futureFactor
  exact := by
    rintro ⟨receiver, word⟩ source
    simp only [futureFactor, futureReceiver]
    rw [← C.quotientCommutesWithEveryOrderedWord word source]
    exact C.present.exact receiver (transportWord C.sourceTransport word source)

/-- Equal quotient faces remain equal under every admitted receiver and successor history. -/
theorem quotientEqForcesEverySuccessorFace {left right : Source}
    (h : C.present.quotient left = C.present.quotient right)
    (receiver : Receiver) (word : List Generator) :
    C.present.receiver receiver (transportWord C.sourceTransport word left) =
      C.present.receiver receiver (transportWord C.sourceTransport word right) := by
  exact (C.allSuccessorHistories.receiver_eq_of_quotient_eq h) (receiver, word)

/--
A single separating successor is a witness that the two occurrences cannot lawfully be collapsed.
-/
theorem separatingSuccessorReopensTheProposedQuotient {left right : Source}
    (receiver : Receiver) (word : List Generator)
    (separates :
      C.present.receiver receiver (transportWord C.sourceTransport word left) ≠
        C.present.receiver receiver (transportWord C.sourceTransport word right)) :
    C.present.quotient left ≠ C.present.quotient right := by
  intro h
  exact separates (C.quotientEqForcesEverySuccessorFace h receiver word)

/-! ## A finite control: a present receiver can collapse what one successor reopens -/

namespace StaticControl

/-- The present quotient retains only the first coordinate. -/
def firstCoordinateCompression : Compression Unit (Bool × Bool) Bool Bool where
  quotient := Prod.fst
  receiver _ := Prod.fst
  factor _ := _root_.id
  exact _ _ := rfl

/-- A successor transport exposes the previously hidden second coordinate. -/
def exchangeCoordinates : Bool × Bool → Bool × Bool
  | (left, right) => (right, left)

/--
Static receiver exactness does not imply exactness under successors.

The two occurrences have the same present quotient and receiver face, but one successor separates
them.  Therefore a static `Compression` cannot by itself establish holonic compression.
-/
theorem aStaticCompressionCanReopenUnderOneSuccessor :
    firstCoordinateCompression.quotient (false, false) =
        firstCoordinateCompression.quotient (false, true)
      ∧ firstCoordinateCompression.receiver () (false, false) =
        firstCoordinateCompression.receiver () (false, true)
      ∧ firstCoordinateCompression.receiver () (exchangeCoordinates (false, false)) ≠
        firstCoordinateCompression.receiver () (exchangeCoordinates (false, true)) := by
  decide

end StaticControl

end ReceiverHistoryCompression

end Soma.Holonics.Millennium.LineageCompression

section Audit
open Soma.Holonics.Millennium.LineageCompression
#print axioms ReceiverHistoryCompression.quotientCommutesWithEveryOrderedWord
#print axioms ReceiverHistoryCompression.quotientEqForcesEverySuccessorFace
#print axioms ReceiverHistoryCompression.separatingSuccessorReopensTheProposedQuotient
#print axioms ReceiverHistoryCompression.StaticControl.aStaticCompressionCanReopenUnderOneSuccessor
end Audit
