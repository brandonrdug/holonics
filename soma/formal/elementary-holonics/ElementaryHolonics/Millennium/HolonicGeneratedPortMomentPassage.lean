import ElementaryHolonics.Millennium.HolonicPortResolvedBoundaryTransport
import ElementaryHolonics.Millennium.HolonicQuadraticMomentCondensation

/-!
# Generator-addressed port moments and forced native chronology

**[proved-derived]** A plural generator action must remain addressed through the membrane
restriction and receiver.  If `C` is the continuing quadratic current, the native higher face is

`C_(p,g) = D_p (T_g C T_gᵀ) D_p`.

The exterior port quotient occurs only after these `(port, generator)` occurrences exist.  A
receiver-returned set `S` therefore continues as the exact selected sum

`C_next = sum_(p,g in S) C_(p,g)`.

This file also records the source-neutral chronology law used by Athena ingress.  Ordered exterior
current is an input term of the recurrence, not a byte-labelled native state and not a commutative
bag formed before transport.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicGeneratedPortMomentPassage

open scoped BigOperators
open Soma.Holonics.Millennium.HolonicQuadraticMomentCondensation

variable {Scalar Cell Generator Port : Type*}
  {Support : Type*} [CommRing Scalar] [Fintype Support] [Fintype Cell]
  [Fintype Generator] [Fintype Port]

/-- One complete native higher face.  Generator and port are both occurrence addresses; neither
is reconstructed after an aggregate receiver. -/
def generatedPortMoment
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : Port → Cell → Scalar)
    (moment : Matrix Cell Cell Scalar) (port : Port) (generatorFace : Generator) :
    Matrix Cell Cell Scalar :=
  restrictMoment (restriction port) (transportMoment (generator generatorFace) moment)

/-- The complete generator/port population before receiver selection. -/
def completeGeneratedPortFront
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : Port → Cell → Scalar)
    (moment : Matrix Cell Cell Scalar) :
    Port → Generator → Matrix Cell Cell Scalar :=
  fun port generatorFace => generatedPortMoment generator restriction moment port generatorFace

/-- The rank-one carrier of one addressed higher face.  This is the native executable chart of
`D_p T_g x_s`; its quadratic moment reconstructs the ambient pair field exactly, so the latter is
not a residency obligation. -/
def generatedPortCurrent
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : Port → Cell → Scalar)
    (current : Support → Cell → Scalar) (port : Port) (generatorFace : Generator) :
    Support → Cell → Scalar :=
  fun support cell =>
    restriction port cell * (generator generatorFace).mulVec (current support) cell

/-- One generator-addressed port moment is exactly the quadratic moment of its restricted,
transported rank-one family.  Thus preserving the addressed family preserves the complete pair
receiver while avoiding an ambient `Cell × Cell` carrier. -/
theorem quadraticMoment_generatedPortCurrent_eq_generatedPortMoment
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : Port → Cell → Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar)
    (port : Port) (generatorFace : Generator) :
    quadraticMoment weight
        (generatedPortCurrent generator restriction current port generatorFace) =
      generatedPortMoment generator restriction (quadraticMoment weight current)
        port generatorFace := by
  rw [generatedPortMoment, ← quadraticMoment_generated_eq_transportMoment]
  ext left right
  simp only [quadraticMoment, generatedPortCurrent, restrictMoment]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro support _
  ring

/-- Exact continuation through a receiver-returned addressed subset.  False faces remain in the
reconstruction fibre; this sum is not permission to discard their boundary testimony. -/
def selectedGeneratedPortMoment
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : Port → Cell → Scalar)
    (selected : Port → Generator → Bool)
    (moment : Matrix Cell Cell Scalar) : Matrix Cell Cell Scalar :=
  ∑ port, ∑ generatorFace,
    if selected port generatorFace
    then generatedPortMoment generator restriction moment port generatorFace
    else 0

@[simp] theorem generatedPortMoment_eq_restrict_transport
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : Port → Cell → Scalar)
    (moment : Matrix Cell Cell Scalar) (port : Port) (generatorFace : Generator) :
    generatedPortMoment generator restriction moment port generatorFace =
      restrictMoment (restriction port) (transportMoment (generator generatorFace) moment) := rfl

/-- Selecting every addressed face reduces only after port and generator incidence have both been
retained. -/
theorem selectedGeneratedPortMoment_all
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : Port → Cell → Scalar)
    (moment : Matrix Cell Cell Scalar) :
    selectedGeneratedPortMoment generator restriction (fun _ _ => true) moment =
      ∑ port, ∑ generatorFace,
        generatedPortMoment generator restriction moment port generatorFace := by
  simp [selectedGeneratedPortMoment]

/-- The selected continuation remains an exact addressed rank-one family.  Its ambient pair sum
is a receiver reconstruction, not the hot state population. -/
theorem selectedGeneratedPortMoment_eq_sum_quadraticMoment
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : Port → Cell → Scalar)
    (selected : Port → Generator → Bool)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    selectedGeneratedPortMoment generator restriction selected
        (quadraticMoment weight current) =
      ∑ port, ∑ generatorFace,
        if selected port generatorFace
        then quadraticMoment weight
          (generatedPortCurrent generator restriction current port generatorFace)
        else 0 := by
  apply Finset.sum_congr rfl
  intro port _
  apply Finset.sum_congr rfl
  intro generatorFace _
  by_cases chosen : selected port generatorFace = true
  · simp [selectedGeneratedPortMoment, chosen,
      quadraticMoment_generatedPortCurrent_eq_generatedPortMoment]
  · have notChosen : selected port generatorFace = false := Bool.eq_false_of_not_eq_true chosen
    simp [selectedGeneratedPortMoment, notChosen]

/-- One causal ingress occurrence is a native current added after the existing stored moment has
crossed every addressed generator.  The input is a current section; its exterior spelling is not
part of this law. -/
def forcedMomentStep
    (generator : Generator → Matrix Cell Cell Scalar)
    (stored incoming : Matrix Cell Cell Scalar) : Matrix Cell Cell Scalar :=
  (∑ generatorFace, transportMoment (generator generatorFace) stored) + incoming

/-- Ordered input chronology.  Reordering is not admitted by this definition: every later input
meets the standing deposited by its exact predecessor list. -/
def forcedMomentChronology
    (generator : Generator → Matrix Cell Cell Scalar) :
    List (Matrix Cell Cell Scalar) → Matrix Cell Cell Scalar → Matrix Cell Cell Scalar
  | [], stored => stored
  | incoming :: later, stored =>
      forcedMomentChronology generator later (forcedMomentStep generator stored incoming)

@[simp] theorem forcedMomentChronology_nil
    (generator : Generator → Matrix Cell Cell Scalar)
    (stored : Matrix Cell Cell Scalar) :
    forcedMomentChronology generator [] stored = stored := rfl

@[simp] theorem forcedMomentChronology_cons
    (generator : Generator → Matrix Cell Cell Scalar)
    (incoming : Matrix Cell Cell Scalar)
    (later : List (Matrix Cell Cell Scalar))
    (stored : Matrix Cell Cell Scalar) :
    forcedMomentChronology generator (incoming :: later) stored =
      forcedMomentChronology generator later
        (forcedMomentStep generator stored incoming) := rfl

/-- The one-step local ledger: the deposited difference is exactly the transported standing plus
the admitted incoming current. -/
theorem forcedMomentStep_sub_transport_eq_incoming
    (generator : Generator → Matrix Cell Cell Scalar)
    (stored incoming : Matrix Cell Cell Scalar) :
    forcedMomentStep generator stored incoming -
        (∑ generatorFace, transportMoment (generator generatorFace) stored) = incoming := by
  simp [forcedMomentStep]

section Audit

#print axioms generatedPortMoment_eq_restrict_transport
#print axioms selectedGeneratedPortMoment_all
#print axioms quadraticMoment_generatedPortCurrent_eq_generatedPortMoment
#print axioms selectedGeneratedPortMoment_eq_sum_quadraticMoment
#print axioms forcedMomentChronology_cons
#print axioms forcedMomentStep_sub_transport_eq_incoming

end Audit

end Soma.Holonics.Millennium.HolonicGeneratedPortMomentPassage
