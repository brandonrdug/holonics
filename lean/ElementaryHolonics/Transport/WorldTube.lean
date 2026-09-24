import ElementaryHolonics.Foundation.Holon
import ElementaryHolonics.Millennium.HolonicDirectedPassage
import ElementaryHolonics.Foundation.ReceiverHistoryCompression
import ElementaryHolonics.Millennium.SituatedReturnedDifference

/-!
# Addressed world-tubes, clocks, and returned interaction

This file composes standing owners.  It adds no material-specific organ.  A carried exterior span
retains its occurrence population, both boundary maps, exact local-clock face, receiver face, and
obstruction.  Serial contact remains the existing pullback join.  Resegmentation therefore changes
only the presentation of an already joined occurrence; a missing joining equality is an open gap.

The same occurrence enters the existing addressed membrane contact.  Its constitutive current is
restricted to an outward receiver.  Membership in that receiver's kernel is lawful exterior
silence, while a section outside the kernel has nonzero radiation.  World consequence and later
return form a complete situated difference whose causal adjoint changes the one continuing rest.
The standing dynamic-compression law then carries that rest through every finite ordered successor
word.

All introduced carriers are `[definition]`.  Every theorem is
`[proved-derived; formal-checked]`; the two finite controls are
`[counterexample; formal-checked]` relative to the declared fixtures.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicSensoryWorldTube

open Soma.Holonics
open Soma.Holonics.Millennium.LineageCompression
open Soma.Holonics.Millennium.SituatedReturnedDifference

/-! ## Exact local clocks remain addressed -/

/-- One exact affine local-clock chart.  Its address is part of the chart and is not reconstructed
from a displayed coordinate. -/
structure ExactLocalClock (ClockAddress : Type*) where
  address : ClockAddress
  origin : ℚ
  rate : ℚ
  rate_ne_zero : rate ≠ 0

namespace ExactLocalClock

/-- The exact coordinate returned by one local clock at one local tick. -/
def coordinate {ClockAddress : Type*}
    (clock : ExactLocalClock ClockAddress) (tick : ℚ) : ℚ :=
  clock.origin + clock.rate * tick

/-- An exact affine clock passage is admitted only with its commuting coordinate square. -/
structure Passage {SourceAddress TargetAddress : Type*}
    (source : ExactLocalClock SourceAddress) (target : ExactLocalClock TargetAddress) where
  scale : ℚ
  offset : ℚ
  scale_ne_zero : scale ≠ 0
  commutes : ∀ tick,
    target.coordinate (scale * tick + offset) = source.coordinate tick

/-- The identity local-clock passage. -/
def Passage.identity {ClockAddress : Type*}
    (clock : ExactLocalClock ClockAddress) : Passage clock clock where
  scale := 1
  offset := 0
  scale_ne_zero := one_ne_zero
  commutes tick := by simp [coordinate]

/-- Equal displayed coordinates do not identify local clocks: two addressed charts may return the
same coordinate at one tick while remaining distinct charts. -/
theorem equal_coordinate_does_not_identify_clock_address :
    let left : ExactLocalClock Bool := ⟨false, 0, 1, one_ne_zero⟩
    let right : ExactLocalClock Bool := ⟨true, 0, 1, one_ne_zero⟩
    left.coordinate 0 = right.coordinate 0 ∧ left.address ≠ right.address := by
  norm_num [coordinate]

end ExactLocalClock

/-- One situated clock face retains both the exact chart and the local tick. -/
structure SituatedClockFace (ClockAddress : Type*) where
  chart : ExactLocalClock ClockAddress
  tick : ℚ

namespace SituatedClockFace

/-- The displayed coordinate is a receiver face of the retained chart/tick pair. -/
def coordinate {ClockAddress : Type*} (face : SituatedClockFace ClockAddress) : ℚ :=
  face.chart.coordinate face.tick

end SituatedClockFace

universe uSpanSource uSpanTarget uSpanClock uSpanFace uSpanObstruction uSpanOccurrence

/-! ## Addressed spans, pullback composition, and resegmentation -/

/-- An addressed exterior span with chronology, returned face, and obstruction attached to every
carrying occurrence.  `ClockFace`, `Face`, and `Obstruction` remain arbitrary typed carriers. -/
structure ClockedSpan
    (Source : Type uSpanSource) (Target : Type uSpanTarget)
    (ClockFace : Type uSpanClock) (Face : Type uSpanFace)
    (Obstruction : Type uSpanObstruction) (Occurrence : Type uSpanOccurrence) where
  source : Occurrence → Source
  target : Occurrence → Target
  clock : Occurrence → ClockFace
  receive : Occurrence → Face
  obstruction : Occurrence → Obstruction

namespace ClockedSpan

variable {X Y Z ClockLeft ClockRight FaceLeft FaceRight ObstructionLeft ObstructionRight
  LeftOccurrence RightOccurrence : Type*}

/-- The standing addressed-passage face of a clocked span. -/
def toPassage
    (span : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence) :
    AddressedPassage X Y where
  Occurrence := LeftOccurrence
  source := span.source
  target := span.target

/-- The complete receiver face of one carried span occurrence. -/
def completeFace
    (span : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (occurrence : LeftOccurrence) : ClockLeft × FaceLeft × ObstructionLeft :=
  (span.clock occurrence, span.receive occurrence, span.obstruction occurrence)

/-- Serial span composition is the standing pullback composition.  Both clock faces, receiver
faces, and obstructions remain paired; none is selected or merged. -/
def comp
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence) :
    ClockedSpan X Z (ClockLeft × ClockRight) (FaceLeft × FaceRight)
      (ObstructionLeft × ObstructionRight)
      (AddressedPassage.Join left.toPassage right.toPassage) where
  source joined := left.source joined.left
  target joined := right.target joined.right
  clock joined := (left.clock joined.left, right.clock joined.right)
  receive joined := (left.receive joined.left, right.receive joined.right)
  obstruction joined :=
    (left.obstruction joined.left, right.obstruction joined.right)

/-- Splitting and rejoining an already composable occurrence preserves its complete face.  This
is resegmentation naturality: only the cover changes. -/
theorem split_rejoin_preserves_completeFace
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    {source : X} {target : Z}
    (carried : (AddressedPassage.comp right.toPassage left.toPassage).Fibre source target) :
    (comp right left).completeFace
        (AddressedPassage.joinCompositeFibre right.toPassage left.toPassage
          (AddressedPassage.splitCompositeFibre right.toPassage left.toPassage carried)).1 =
      (comp right left).completeFace carried.1 := by
  rw [AddressedPassage.join_split]

/-- Every later receiver of the complete span face also commutes with lawful split/rejoin. -/
theorem resegmentation_natural
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    {source : X} {target : Z}
    (carried : (AddressedPassage.comp right.toPassage left.toPassage).Fibre source target)
    {Reading : Type*}
    (receiver : ((ClockLeft × ClockRight) × (FaceLeft × FaceRight) ×
      (ObstructionLeft × ObstructionRight)) → Reading) :
    receiver ((comp right left).completeFace
        (AddressedPassage.joinCompositeFibre right.toPassage left.toPassage
          (AddressedPassage.splitCompositeFibre right.toPassage left.toPassage carried)).1) =
      receiver ((comp right left).completeFace carried.1) := by
  rw [split_rejoin_preserves_completeFace]

/-- An actual open gap says that no predecessor target equals any successor source. -/
def HasOpenGap
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence) : Prop :=
  ∀ predecessor successor,
    left.target predecessor ≠ right.source successor

/-- A gap has no pullback occurrence.  It cannot be treated as another segmentation of a joined
world-line. -/
theorem openGap_has_no_joined_occurrence
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (gap : HasOpenGap left right) :
    IsEmpty (AddressedPassage.Join left.toPassage right.toPassage) := by
  constructor
  intro joined
  exact gap joined.left joined.right joined.joins

end ClockedSpan

/-! ## One membrane, one outward receiver, one world return -/

/-- The singular world-tube composition.  The span occurrence itself addresses membrane ingress;
outward restriction, world consequence, later return, causal adjoint, and dynamic condensation all
belong to the same continuing body. -/
structure WorldTube
    (ExteriorBoundary InteriorBoundary ClockFace Face Obstruction Occurrence
      InteriorCurrent ExteriorCurrent World Morphology
      Generator Receiver Quotient ReceiverFace : Type*)
    [AddCommGroup InteriorCurrent] [AddCommGroup ExteriorCurrent]
    [AddCommGroup Morphology] where
  span : ClockedSpan ExteriorBoundary InteriorBoundary ClockFace Face Obstruction Occurrence
  /-- Current returned by the standing addressed membrane owner at this exact span occurrence. -/
  membraneIngress : Occurrence → InteriorCurrent
  outward : InteriorCurrent →+ ExteriorCurrent
  worldConsequence : ExteriorCurrent → World
  laterReturn : World → ExteriorCurrent
  causalAdjoint : ExteriorCurrent →+ Morphology
  rest : Morphology
  history : ReceiverHistoryCompression Generator Receiver Morphology Quotient ReceiverFace

namespace WorldTube

variable
    {ExteriorBoundary InteriorBoundary ClockFace Face Obstruction Occurrence
      InteriorCurrent ExteriorCurrent World Morphology
      Generator Receiver Quotient ReceiverFace : Type*}
    [AddCommGroup InteriorCurrent] [AddCommGroup ExteriorCurrent]
    [AddCommGroup Morphology]

variable (tube : WorldTube ExteriorBoundary InteriorBoundary ClockFace Face Obstruction Occurrence
  InteriorCurrent ExteriorCurrent World Morphology
  Generator Receiver Quotient ReceiverFace)

/-- The complete constitutive current entering the interior at one addressed occurrence. -/
def interiorCurrent (occurrence : Occurrence) : InteriorCurrent :=
  tube.membraneIngress occurrence

/-- Native outward radiation is restriction of the complete interior current. -/
def radiation (occurrence : Occurrence) : ExteriorCurrent :=
  tube.outward (tube.interiorCurrent occurrence)

/-- The outward receiver radical is the exact population whose exterior restriction is zero. -/
def outwardRadical : AddSubgroup InteriorCurrent := tube.outward.ker

/-- Lawful exterior silence retains nonzero interior conduct inside the outward radical. -/
def IsLawfulSilence (occurrence : Occurrence) : Prop :=
  tube.interiorCurrent occurrence ≠ 0 ∧ tube.interiorCurrent occurrence ∈ tube.outwardRadical

/-- Lawful silence is exactly nonzero interior conduct with zero outward radiation. -/
theorem lawfulSilence_iff_nonzero_and_radiation_zero
    (occurrence : Occurrence) :
    tube.IsLawfulSilence occurrence ↔
      tube.interiorCurrent occurrence ≠ 0 ∧ tube.radiation occurrence = 0 := by
  rfl

/-- A section outside the outward radical has nonzero radiation; it cannot be silently withheld. -/
theorem nonradical_must_radiate
    (occurrence : Occurrence)
    (notRadical : tube.interiorCurrent occurrence ∉ tube.outwardRadical) :
    tube.radiation occurrence ≠ 0 := by
  exact notRadical

/-- The exterior consequence returns through the world into the same exterior-current fibre. -/
def returnedSection (occurrence : Occurrence) : ExteriorCurrent :=
  tube.laterReturn (tube.worldConsequence (tube.radiation occurrence))

/-- World return is measured by the standing situated-difference law, with the identity connection
because emission and return occupy the same declared exterior-current fibre here. -/
def returnedDifference (occurrence : Occurrence) : ExteriorCurrent :=
  dependentReturnedDifference (AddEquiv.refl ExteriorCurrent)
    (tube.radiation occurrence) (tube.returnedSection occurrence)

/-- The causal adjoint deposits the complete returned difference into the one continuing rest. -/
def cultivatedRest (occurrence : Occurrence) : Morphology :=
  tube.rest + tube.causalAdjoint (tube.returnedDifference occurrence)

/-- Cultivation changes morphology by exactly the causal-adjoint return, with no scalar score. -/
theorem cultivatedRest_sub_rest
    (occurrence : Occurrence) :
    tube.cultivatedRest occurrence - tube.rest =
      tube.causalAdjoint (tube.returnedDifference occurrence) := by
  simp [cultivatedRest]

/-- The admitted generator square carries the cultivated rest through every finite ordered
successor word. -/
theorem cultivatedRest_descends_every_finite_successor_word
    (occurrence : Occurrence) (word : List Generator) :
    tube.history.present.quotient
        (Chronology.transportWord tube.history.sourceTransport word
          (tube.cultivatedRest occurrence)) =
      Chronology.transportWord tube.history.quotientTransport word
        (tube.history.present.quotient (tube.cultivatedRest occurrence)) :=
  tube.history.quotientCommutesWithEveryOrderedWord word (tube.cultivatedRest occurrence)

end WorldTube

/-! ## Finite radical control -/

/-- Projection to the first coordinate is an exact outward receiver. -/
def firstCoordinateOutward : (ℤ × ℤ) →+ ℤ where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A nonzero interior section can be lawfully silent for one declared outward receiver. -/
theorem nonzero_interior_section_can_lie_in_outward_radical :
    (0, 1) ≠ (0 : ℤ × ℤ) ∧ (0, 1) ∈ firstCoordinateOutward.ker := by
  constructor
  · intro equal
    have := congrArg Prod.snd equal
    norm_num at this
  · rfl

/-- A section not in the outward radical returns nonzero exterior radiation. -/
theorem finite_nonradical_section_cannot_be_silent :
    (1, 0) ∉ firstCoordinateOutward.ker ∧ firstCoordinateOutward (1, 0) ≠ 0 := by
  norm_num [firstCoordinateOutward]

section Audit

#print axioms ExactLocalClock.Passage.identity
#print axioms ExactLocalClock.equal_coordinate_does_not_identify_clock_address
#print axioms ClockedSpan.split_rejoin_preserves_completeFace
#print axioms ClockedSpan.resegmentation_natural
#print axioms ClockedSpan.openGap_has_no_joined_occurrence
#print axioms WorldTube.lawfulSilence_iff_nonzero_and_radiation_zero
#print axioms WorldTube.nonradical_must_radiate
#print axioms WorldTube.cultivatedRest_sub_rest
#print axioms WorldTube.cultivatedRest_descends_every_finite_successor_word
#print axioms nonzero_interior_section_can_lie_in_outward_radical
#print axioms finite_nonradical_section_cannot_be_silent

end Audit

end Soma.Holonics.Millennium.HolonicSensoryWorldTube
