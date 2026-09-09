import ElementaryHolonics.Foundation.ReceiverHistoryCompression
import ElementaryHolonics.Millennium.Receiver

/-!
# Canonical joint receiver descent

An additive receiver family has a canonical quotient: the carrier modulo the subgroup which the
complete family cannot distinguish.  This owner composes that quotient with the existing ordered
history compression owner.

The quotient retains the full inverse image of every joint face.  It does not choose a source
representative and it does not claim an executable decoder.  Admitted additive generators descend
when they preserve the collapsed subgroup; the existing generator-word theorem then supplies
receiver exactness for every finite ordered successor history.
-/

namespace Soma.Holonics.Foundation.JointReceiverDescent

open Soma.Holonics
open Soma.Holonics.Millennium.Receiver
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.LineageCompression

universe u

/-- The existing receiver-transformer criterion becomes exactly invariance of the joint blind
subgroup for an additive generator. Thus the preservation receipt below is also necessary for
this declared joint receiver, rather than a freely added sufficient condition. -/
theorem joint_generator_descends_iff
    {Receiver X V : Type u} [AddCommGroup X] [AddCommGroup V]
    (read : Receiver → (X →+ V)) (transport : X →+ X) :
    Nonempty (ReceiverTransformer (jointReading read)
      (fun source ↦ jointReading read (transport source))) ↔
      ∀ source, source ∈ collapsedPopulation read → transport source ∈ collapsedPopulation read := by
  rw [receiverTransformer_exists_iff]
  constructor
  · intro descends source hsource
    have equal : jointReading read source = jointReading read 0 := by
      funext receiver
      exact ((AddSubgroup.mem_iInf.mp hsource) receiver).trans (map_zero (read receiver)).symm
    have returned := descends source 0 equal
    apply AddSubgroup.mem_iInf.mpr
    intro receiver
    have h := congrFun returned receiver
    simpa using h
  · intro preserves left right equal
    have difference : right - left ∈ collapsedPopulation read :=
      (unseparatedIffDifferenceCollapsed read left right).mp (fun receiver ↦ congrFun equal receiver)
    have returned := preserves (right - left) difference
    funext receiver
    have h := (AddSubgroup.mem_iInf.mp returned) receiver
    change read receiver (transport (right - left)) = 0 at h
    rw [map_sub, map_sub] at h
    exact (sub_eq_zero.mp h).symm

/-- An additive receiver family together with source generators that preserve its blind
population. -/
structure JointReceiverHistory
    (Generator : Type u) (Receiver : Type u)
    (X : Type u) (V : Type u)
    [AddCommGroup X] [AddCommGroup V] where
  /-- The complete declared additive receiver family. -/
  read : Receiver → (X →+ V)
  /-- The admitted additive source transports. -/
  transport : Generator → (X →+ X)
  /-- Every source generator preserves what the complete receiver family cannot distinguish. -/
  preservesCollapsed : ∀ generator x,
    x ∈ Soma.Holonics.Millennium.Receiver.collapsedPopulation read →
      transport generator x ∈ Soma.Holonics.Millennium.Receiver.collapsedPopulation read

namespace JointReceiverHistory

variable {Generator : Type u} {Receiver : Type u}
  {X : Type u} {V : Type u} [AddCommGroup X] [AddCommGroup V]
  (J : JointReceiverHistory Generator Receiver X V)

/-- The canonical blind subgroup of the complete receiver family. -/
abbrev collapsed : AddSubgroup X :=
  Soma.Holonics.Millennium.Receiver.collapsedPopulation J.read

/-- The canonical joint receiver quotient. -/
abbrev JointQuotient := X ⧸ collapsed J

/-- The quotient map retains the quotient face and leaves its complete predecessor fibre implicit
in the quotient type. -/
def quotient : X → JointQuotient J := QuotientAddGroup.mk' (collapsed J)

/-- One receiver factors through the canonical joint quotient. -/
def factor (receiver : Receiver) : JointQuotient J →+ V :=
  QuotientAddGroup.lift (collapsed J) (J.read receiver) (by
    intro x hx
    exact (AddSubgroup.mem_iInf.mp hx) receiver)

@[simp] theorem factor_quotient (receiver : Receiver) (x : X) :
    factor J receiver (quotient J x) = J.read receiver x := by
  rfl

/-- The canonical quotient identifies exactly the pairs with equal complete receiver readings. -/
theorem quotient_eq_iff_joint_readings_eq (left right : X) :
    quotient J left = quotient J right ↔
      ∀ receiver, J.read receiver left = J.read receiver right := by
  constructor
  · intro same
    apply (unseparatedIffDifferenceCollapsed J.read left right).mpr
    have hdifference : -left + right ∈ collapsed J :=
      (QuotientAddGroup.eq.mp same)
    simpa [sub_eq_add_neg, add_comm] using hdifference
  · intro same
    apply QuotientAddGroup.eq.mpr
    have hdifference : right - left ∈ collapsed J :=
      (unseparatedIffDifferenceCollapsed J.read left right).mp same
    simpa [sub_eq_add_neg, add_comm] using hdifference

/-- The present receiver compression induced by the complete family. -/
def presentCompression : Compression Receiver X (JointQuotient J) V where
  quotient := quotient J
  receiver := fun receiver x => J.read receiver x
  factor := fun receiver q => factor J receiver q
  exact := by
    intro receiver x
    exact factor_quotient J receiver x

/-- The complete predecessor population behind a canonical quotient face. -/
abbrev preimageFibre (face : JointQuotient J) : Type u :=
  { source : X // quotient J source = face }

/-- Equal quotient faces retain both source occurrences in one complete inverse-image fibre. -/
def quotient_eq_places_both_in_one_fibre {left right : X}
    (same : quotient J left = quotient J right) :
    preimageFibre J (quotient J left) × preimageFibre J (quotient J left) :=
  (⟨left, rfl⟩, ⟨right, same.symm⟩)

/-- The additive generator induced on the canonical quotient. -/
def quotientTransport (generator : Generator) : JointQuotient J →+ JointQuotient J :=
  QuotientAddGroup.lift (collapsed J)
    ((QuotientAddGroup.mk' (collapsed J)).comp (J.transport generator)) (by
      intro x hx
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        (J.preservesCollapsed generator x hx))

@[simp] theorem quotientTransport_quotient (generator : Generator) (x : X) :
    quotientTransport J generator (quotient J x) =
      quotient J (J.transport generator x) := by
  rfl

/-- The canonical quotient as an instance of the existing ordered-history compression owner. -/
def historyCompression : ReceiverHistoryCompression
    Generator Receiver X (JointQuotient J) V where
  present := presentCompression J
  sourceTransport generator := fun x => J.transport generator x
  quotientTransport generator := fun q => quotientTransport J generator q
  generatorExact := by
    intro generator source
    exact quotientTransport_quotient J generator source

/-- Exact factorization for every receiver and every finite ordered successor word. -/
def allSuccessorHistories : Compression
    (Receiver × List Generator) X (JointQuotient J) V :=
  ReceiverHistoryCompression.allSuccessorHistories (historyCompression J)

theorem quotient_eq_forces_every_successor_face {left right : X}
    (same : quotient J left = quotient J right)
    (receiver : Receiver) (word : List Generator) :
    J.read receiver
        (transportWord (fun generator x => J.transport generator x) word left) =
      J.read receiver
        (transportWord (fun generator x => J.transport generator x) word right) := by
  exact ReceiverHistoryCompression.quotientEqForcesEverySuccessorFace
    (historyCompression J) same receiver word

theorem separating_successor_reopens_quotient {left right : X}
    (receiver : Receiver) (word : List Generator)
    (separates : J.read receiver
        (transportWord (fun generator x => J.transport generator x) word left) ≠
      J.read receiver
        (transportWord (fun generator x => J.transport generator x) word right)) :
    quotient J left ≠ quotient J right := by
  exact ReceiverHistoryCompression.separatingSuccessorReopensTheProposedQuotient
    (historyCompression J) receiver word separates

end JointReceiverHistory

end Soma.Holonics.Foundation.JointReceiverDescent

section Audit
open Soma.Holonics.Foundation.JointReceiverDescent
#print axioms joint_generator_descends_iff
#print axioms JointReceiverHistory.factor_quotient
#print axioms JointReceiverHistory.quotient_eq_iff_joint_readings_eq
#print axioms JointReceiverHistory.quotientTransport_quotient
#print axioms JointReceiverHistory.quotient_eq_forces_every_successor_face
#print axioms JointReceiverHistory.separating_successor_reopens_quotient
end Audit
