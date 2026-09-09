import ElementaryHolonics.Transport.WorldTube
import ElementaryHolonics.Transport.ReceiverPotential
import ElementaryHolonics.Foundation.BoundaryScalePassage
import Mathlib.Data.Set.Image

/-!
# Clocked world-tube resegmentation and boundary-family images

This owner packages the existing addressed split/join and associator equivalences at the level of
the complete clock, receiver, and obstruction face.  Future images remain receiver-relative and
retain their full source fibres; an ordered occurrence transport is supplied by the caller when a
history is required.  The boundary section adds the corresponding forward image law for a lawful
scale passage and its serial composition.

No inverse, surjectivity, or singleton source fibre is introduced.
-/

namespace Soma.Holonics.Transport.WorldTubePotential

open Soma.Holonics
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.HolonicSensoryWorldTube
open Soma.Holonics.Transport.ReceiverPotential

/-! ## Exact split/rejoin equivalence for a clocked composite -/

universe uX uY uZ uClockLeft uClockRight uFaceLeft uFaceRight
  uObstructionLeft uObstructionRight uLeftOccurrence uRightOccurrence

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
  {ClockLeft : Type uClockLeft} {ClockRight : Type uClockRight}
  {FaceLeft : Type uFaceLeft} {FaceRight : Type uFaceRight}
  {ObstructionLeft : Type uObstructionLeft} {ObstructionRight : Type uObstructionRight}
  {LeftOccurrence : Type uLeftOccurrence} {RightOccurrence : Type uRightOccurrence}

abbrev CompositeFibre
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (source : X) (target : Z) :=
  (right.comp left).toPassage.Fibre source target

abbrev SplitFibre
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (source : X) (target : Z) :=
  Σ middle : Y,
    left.toPassage.Fibre source middle × right.toPassage.Fibre middle target

/-- The exact split/rejoin equivalence of a clocked composite fibre. -/
def splitRejoinEquiv
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    {source : X} {target : Z} :
    CompositeFibre right left source target ≃ SplitFibre right left source target where
  toFun carried := AddressedPassage.splitCompositeFibre
    right.toPassage left.toPassage carried
  invFun pieces := AddressedPassage.joinCompositeFibre
    right.toPassage left.toPassage pieces
  left_inv carried := AddressedPassage.join_split right.toPassage left.toPassage carried
  right_inv pieces := AddressedPassage.split_join right.toPassage left.toPassage pieces

/-- The split presentation reconstructs the complete clock/face/obstruction face exactly. -/
theorem splitRejoin_completeFace
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    {source : X} {target : Z} (carried : CompositeFibre right left source target) :
    (right.comp left).completeFace
        ((AddressedPassage.joinCompositeFibre right.toPassage left.toPassage
          (splitRejoinEquiv right left carried)).1) =
      (right.comp left).completeFace carried.1 := by
  exact ClockedSpan.split_rejoin_preserves_completeFace right left carried

/-- Every receiver of the complete face is invariant under split/rejoin. -/
theorem splitRejoin_receiver_natural
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    {source : X} {target : Z} (carried : CompositeFibre right left source target)
    {Reading : Type*}
    (receiver : ((ClockLeft × ClockRight) × (FaceLeft × FaceRight) ×
      (ObstructionLeft × ObstructionRight)) → Reading) :
    receiver ((right.comp left).completeFace
      ((AddressedPassage.joinCompositeFibre right.toPassage left.toPassage
        (splitRejoinEquiv right left carried)).1)) =
      receiver ((right.comp left).completeFace carried.1) := by
  exact ClockedSpan.resegmentation_natural right left carried receiver

/-! ## Three-way complete-face associator -/

universe uClockMiddle uFaceMiddle uObstructionMiddle uMiddleOccurrence

variable {ClockMiddle : Type uClockMiddle} {FaceMiddle : Type uFaceMiddle}
  {ObstructionMiddle : Type uObstructionMiddle} {MiddleOccurrence : Type uMiddleOccurrence}

/-- The product reassociation carried by the three-way clocked associator. -/
def associatorFaceEquiv
    (ClockLeft : Type*) (ClockMiddle : Type*) (ClockRight : Type*)
    (FaceLeft : Type*) (FaceMiddle : Type*) (FaceRight : Type*)
    (ObstructionLeft : Type*) (ObstructionMiddle : Type*) (ObstructionRight : Type*) :
    (((ClockLeft × ClockMiddle) × ClockRight) ×
      (((FaceLeft × FaceMiddle) × FaceRight) ×
        ((ObstructionLeft × ObstructionMiddle) × ObstructionRight))) ≃
    ((ClockLeft × (ClockMiddle × ClockRight)) ×
      ((FaceLeft × (FaceMiddle × FaceRight)) ×
        (ObstructionLeft × (ObstructionMiddle × ObstructionRight)))) :=
  Equiv.prodCongr
    (Equiv.prodAssoc ClockLeft ClockMiddle ClockRight)
    (Equiv.prodCongr
      (Equiv.prodAssoc FaceLeft FaceMiddle FaceRight)
      (Equiv.prodAssoc ObstructionLeft ObstructionMiddle ObstructionRight))

/-- The occurrence equivalence supplied by the addressed associator. -/
def associatorOccurrenceEquiv
    {W : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    :
    (third.comp (second.comp first)).toPassage.Occurrence ≃
      ((third.comp second).comp first).toPassage.Occurrence :=
  (AddressedPassage.compAssociator third.toPassage second.toPassage first.toPassage).occurrence

theorem associator_source_natural
    {W : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (occurrence : (third.comp (second.comp first)).toPassage.Occurrence) :
    ((third.comp second).comp first).source
        (associatorOccurrenceEquiv third second first occurrence) =
      (third.comp (second.comp first)).source occurrence := by
  exact (AddressedPassage.compAssociator third.toPassage second.toPassage first.toPassage)
    |>.source_exact occurrence

theorem associator_target_natural
    {W : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (occurrence : (third.comp (second.comp first)).toPassage.Occurrence) :
    ((third.comp second).comp first).target
        (associatorOccurrenceEquiv third second first occurrence) =
      (third.comp (second.comp first)).target occurrence := by
  exact (AddressedPassage.compAssociator third.toPassage second.toPassage first.toPassage)
    |>.target_exact occurrence

theorem associator_clock_natural
    {W : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (occurrence : (third.comp (second.comp first)).toPassage.Occurrence) :
    Equiv.prodAssoc ClockLeft ClockMiddle ClockRight
        ((third.comp (second.comp first)).clock occurrence) =
      ((third.comp second).comp first).clock
        (associatorOccurrenceEquiv third second first occurrence) := by
  rcases occurrence with ⟨⟨left, middle, left_join⟩, right, right_join⟩
  rfl

theorem associator_face_natural
    {W : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (occurrence : (third.comp (second.comp first)).toPassage.Occurrence) :
    Equiv.prodAssoc FaceLeft FaceMiddle FaceRight
        ((third.comp (second.comp first)).receive occurrence) =
      ((third.comp second).comp first).receive
        (associatorOccurrenceEquiv third second first occurrence) := by
  rcases occurrence with ⟨⟨left, middle, left_join⟩, right, right_join⟩
  rfl

theorem associator_obstruction_natural
    {W : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (occurrence : (third.comp (second.comp first)).toPassage.Occurrence) :
    Equiv.prodAssoc ObstructionLeft ObstructionMiddle ObstructionRight
        ((third.comp (second.comp first)).obstruction occurrence) =
      ((third.comp second).comp first).obstruction
        (associatorOccurrenceEquiv third second first occurrence) := by
  rcases occurrence with ⟨⟨left, middle, left_join⟩, right, right_join⟩
  rfl

/-- The three-way associator preserves every component of the complete clocked face after product
reassociation. -/
theorem associator_completeFace_natural
    {W : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (occurrence : (third.comp (second.comp first)).toPassage.Occurrence) :
    associatorFaceEquiv ClockLeft ClockMiddle ClockRight FaceLeft FaceMiddle FaceRight
      ObstructionLeft ObstructionMiddle ObstructionRight
      ((third.comp (second.comp first)).completeFace occurrence) =
      ((third.comp second).comp first).completeFace
        (associatorOccurrenceEquiv third second first occurrence) := by
  rcases occurrence with ⟨⟨left, middle, left_join⟩, right, right_join⟩
  rfl

theorem associator_receiver_natural
    {W Reading : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (occurrence : (third.comp (second.comp first)).toPassage.Occurrence)
    (receiver :
      (ClockLeft × (ClockMiddle × ClockRight)) ×
        ((FaceLeft × (FaceMiddle × FaceRight)) ×
          (ObstructionLeft × (ObstructionMiddle × ObstructionRight))) → Reading) :
    receiver (associatorFaceEquiv ClockLeft ClockMiddle ClockRight FaceLeft FaceMiddle FaceRight
      ObstructionLeft ObstructionMiddle ObstructionRight
      ((third.comp (second.comp first)).completeFace occurrence)) =
      receiver (((third.comp second).comp first).completeFace
        (associatorOccurrenceEquiv third second first occurrence)) := by
  rw [associator_completeFace_natural]

/-! ## Receiver-potential histories over the actual resegmentations -/

theorem split_historyOutcomes_rebase
    {Observation Generator Result : Type*}
    (right : ClockedSpan Y Z ClockRight FaceRight ObstructionRight RightOccurrence)
    (left : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    {source : X} {target : Z}
    (entering : CompositeFibre right left source target → Observation)
    (observed : Set.range entering)
    (transport : Generator → CompositeFibre right left source target →
      CompositeFibre right left source target)
    (word : List Generator)
    (receiver : CompositeFibre right left source target → Result) :
    historyOutcomes (entering ∘ (splitRejoinEquiv right left).symm)
      (rebaseObservation (splitRejoinEquiv right left) entering observed)
      (rebaseTransport (splitRejoinEquiv right left) transport) word
      (receiver ∘ (splitRejoinEquiv right left).symm) =
      historyOutcomes entering observed transport word receiver := by
  exact historyOutcomes_rebase (splitRejoinEquiv right left)
    entering observed transport word receiver

theorem associator_historyOutcomes_rebase
    {W Observation Generator Result : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (entering : (third.comp (second.comp first)).toPassage.Occurrence → Observation)
    (observed : Set.range entering)
    (transport : Generator →
      (third.comp (second.comp first)).toPassage.Occurrence →
      (third.comp (second.comp first)).toPassage.Occurrence)
    (word : List Generator)
    (receiver : (third.comp (second.comp first)).toPassage.Occurrence → Result) :
    historyOutcomes (entering ∘ (associatorOccurrenceEquiv third second first).symm)
      (rebaseObservation (associatorOccurrenceEquiv third second first) entering observed)
      (rebaseTransport (associatorOccurrenceEquiv third second first) transport) word
      (receiver ∘ (associatorOccurrenceEquiv third second first).symm) =
      historyOutcomes entering observed transport word receiver := by
  exact historyOutcomes_rebase (associatorOccurrenceEquiv third second first)
    entering observed transport word receiver

/-! ## Boundary-scale family images -/

open Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation

theorem boundaryScale_boundary_image_natural
    {Scalar FineInterior FineBoundary CoarseInterior CoarseBoundary : Type*}
    [Semiring Scalar]
    [AddCommMonoid FineInterior] [Module Scalar FineInterior]
    [AddCommMonoid FineBoundary] [Module Scalar FineBoundary]
    [AddCommMonoid CoarseInterior] [Module Scalar CoarseInterior]
    [AddCommMonoid CoarseBoundary] [Module Scalar CoarseBoundary]
    (passage : BoundaryScalePassage Scalar FineInterior FineBoundary
      CoarseInterior CoarseBoundary)
    (family : Set FineInterior) :
    passage.coarseBoundary '' (passage.interiorTransport '' family) =
      passage.boundaryTransport '' (passage.fineBoundary '' family) := by
  ext boundary
  constructor
  · rintro ⟨_, ⟨current, hcurrent, rfl⟩, rfl⟩
    exact ⟨passage.fineBoundary current,
      ⟨current, hcurrent, rfl⟩, (passage.transport_boundary current).symm⟩
  · rintro ⟨_, ⟨current, hcurrent, rfl⟩, rfl⟩
    exact ⟨passage.interiorTransport current,
      ⟨current, hcurrent, rfl⟩, passage.transport_boundary current⟩

theorem boundaryScale_comp_boundary_image_natural
    {Scalar FineInterior FineBoundary MiddleInterior MiddleBoundary
      CoarseInterior CoarseBoundary : Type*}
    [Semiring Scalar]
    [AddCommMonoid FineInterior] [Module Scalar FineInterior]
    [AddCommMonoid FineBoundary] [Module Scalar FineBoundary]
    [AddCommMonoid MiddleInterior] [Module Scalar MiddleInterior]
    [AddCommMonoid MiddleBoundary] [Module Scalar MiddleBoundary]
    [AddCommMonoid CoarseInterior] [Module Scalar CoarseInterior]
    [AddCommMonoid CoarseBoundary] [Module Scalar CoarseBoundary]
    (fineToMiddle : BoundaryScalePassage Scalar FineInterior FineBoundary
      MiddleInterior MiddleBoundary)
    (middleToCoarse : BoundaryScalePassage Scalar MiddleInterior MiddleBoundary
      CoarseInterior CoarseBoundary)
    (middleBoundary_agrees :
      middleToCoarse.fineBoundary = fineToMiddle.coarseBoundary)
    (family : Set FineInterior) :
    middleToCoarse.coarseBoundary ''
        (middleToCoarse.interiorTransport ''
          (fineToMiddle.interiorTransport '' family)) =
      middleToCoarse.boundaryTransport ''
        (fineToMiddle.boundaryTransport ''
          (fineToMiddle.fineBoundary '' family)) := by
  ext boundary
  constructor
  · rintro ⟨_, ⟨_, ⟨current, hcurrent, rfl⟩, rfl⟩, rfl⟩
    refine ⟨fineToMiddle.boundaryTransport (fineToMiddle.fineBoundary current),
      ⟨fineToMiddle.fineBoundary current, ⟨current, hcurrent, rfl⟩, rfl⟩, ?_⟩
    rw [middleToCoarse.transport_boundary, middleBoundary_agrees]
    rw [fineToMiddle.transport_boundary]
  · rintro ⟨_, ⟨_, ⟨current, hcurrent, rfl⟩, rfl⟩, rfl⟩
    refine ⟨middleToCoarse.interiorTransport (fineToMiddle.interiorTransport current),
      ⟨fineToMiddle.interiorTransport current, ⟨current, hcurrent, rfl⟩, rfl⟩, ?_⟩
    rw [middleToCoarse.transport_boundary, middleBoundary_agrees]
    rw [fineToMiddle.transport_boundary]

section Audit

#print axioms splitRejoinEquiv
#print axioms splitRejoin_completeFace
#print axioms associator_completeFace_natural
#print axioms split_historyOutcomes_rebase
#print axioms associator_historyOutcomes_rebase
#print axioms boundaryScale_boundary_image_natural
#print axioms boundaryScale_comp_boundary_image_natural

end Audit

end Soma.Holonics.Transport.WorldTubePotential
