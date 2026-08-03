import ElementaryHolonics.Foundation.Receiver

/-!
# Occurrence, presentation, and receiver face

An occurrence may be carried by a presentation and observed through a receiver.
Equality at any one of these cuts is not silently promoted to equality at the
others.  This is the exact core retained from the Holobrochos bit-purity work.
-/

namespace Soma.Holonics

universe u v w z

/-- Equality after one declared receiver has observed two occurrences. -/
def FaceEq {X : Type u} {Y : Type v} (receiver : X → Y) (x y : X) : Prop :=
  receiver x = receiver y

/-- A receiver factors through a carrier map without changing its value. -/
def FactorsThrough {X : Type u} {Q : Type v} {Y : Type w}
    (carrier : X → Q) (receiver : X → Y) : Prop :=
  ∃ received : Q → Y, ∀ x, received (carrier x) = receiver x

theorem faceEq_of_occurrenceEq
    {X : Type u} {Y : Type v} (receiver : X → Y) {x y : X}
    (h : x = y) :
    FaceEq receiver x y := by
  simpa [FaceEq] using congrArg receiver h

theorem faceEq_of_carrierEq
    {X : Type u} {Q : Type v} {Y : Type w}
    {carrier : X → Q} {receiver : X → Y}
    (hfactor : FactorsThrough carrier receiver) {x y : X}
    (hcarrier : carrier x = carrier y) :
    FaceEq receiver x y := by
  rcases hfactor with ⟨received, hexact⟩
  unfold FaceEq
  rw [← hexact x, ← hexact y, hcarrier]

/--
Equal receiver faces need not identify source occurrences.  This finite witness
prevents presentation equality from being promoted to occurrence identity.
-/
theorem equal_face_does_not_force_occurrence_identity :
    FaceEq (fun _ : Bool ↦ Unit.unit) false true ∧
      (false : Bool) ≠ true := by
  constructor
  · rfl
  · decide

/--
A comparison is situated by a frame.  It is not intrinsically a binary
operation on two supposedly context-free objects.
-/
abbrev SituatedComparison
    (Frame : Type u) (X : Type v) (Face : Type w) :=
  Frame → X → X → Face

/--
Presentation and denotation are carried separately.  Different presentations
may denote the same value while remaining distinct occurrences.
-/
structure Presented
    (Presentation : Type u) (Value : Type v) where
  presentation : Presentation
  value : Value

end Soma.Holonics
