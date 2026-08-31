import ElementaryHolonics.Foundation.AddressedBoundary
import Mathlib.Tactic

/-!
# The elementary occurrence-bearing holon

An elementary holon is the smallest existing intersection of three already admitted owners:

* an `AddressedPassage`, which retains the occurrence population and its oriented source and
  target ports;
* a receiver current on each occurrence; and
* for a `BoundaryHolon`, a constitutive boundary map proving that the returned current realizes
  the oriented difference `target - source`.

This is not a universal wrapper and it does not identify all objects which share a receiver face.
Serial composition remains the pullback composition of addressed passages, so the composite
occurrence retains both component occurrences and their exact joining equality.  The paired
receiver is lossless at that boundary.  Additive boundary holons may additionally compose their
currents; the joining face then cancels by the retained pullback witness.

The finite-population theorem at the end is the elementary local-to-global law: summing the
currents of one occurrence population and then taking its boundary is exactly the sum of outgoing
faces minus the sum of incoming faces.  It does not assume geometric cancellation, independence,
or conservation beyond the declared constitutive law.
-/

namespace Soma.Holonics

universe u v w x

/-- An addressed occurrence population together with the current returned by its receiver. -/
structure Holon (Source : Type u) (Target : Type v) (Face : Type w) where
  /-- The complete occurrence population. -/
  Occurrence : Type x
  /-- The oriented incoming port. -/
  source : Occurrence → Source
  /-- The oriented outgoing port. -/
  target : Occurrence → Target
  /-- The receiver face returned by each carrying occurrence. -/
  receive : Occurrence → Face

namespace Holon

variable {Source : Type u} {Middle : Type v} {Target : Type w}
variable {LeftFace RightFace : Type x}

/-- The addressed-passage owner underlying a holon. -/
def toPassage (holon : Holon Source Target LeftFace) : AddressedPassage Source Target where
  Occurrence := holon.Occurrence
  source := holon.source
  target := holon.target

/-- Every occurrence retained behind one returned receiver face. -/
def ReconstructionFibre (holon : Holon Source Target LeftFace) (face : LeftFace) : Type _ :=
  { occurrence : holon.Occurrence // holon.receive occurrence = face }

/-- Contact between serial holons is the exact pullback witness, not co-presence. -/
abbrev Interaction (left : Holon Source Middle LeftFace)
    (right : Holon Middle Target RightFace) :=
  AddressedPassage.Join left.toPassage right.toPassage

/-- Serial composition retains both currents as an ordered receiver pair. -/
def comp (right : Holon Middle Target RightFace)
    (left : Holon Source Middle LeftFace) :
    Holon Source Target (LeftFace × RightFace) where
  Occurrence := AddressedPassage.Join left.toPassage right.toPassage
  source joined := left.source joined.left
  target joined := right.target joined.right
  receive joined := (left.receive joined.left, right.receive joined.right)

/--
The Cartesian interaction body of two holons.  This constructs the complete pair population and
makes no execution-independence claim; an interchange or resource theorem is still required before
an apparatus may read it as parallel execution.
-/
def cartesian
    {Source' Target' Face' : Type*}
    (left : Holon Source Target LeftFace)
    (right : Holon Source' Target' Face') :
    Holon (Source × Source') (Target × Target') (LeftFace × Face') where
  Occurrence := left.Occurrence × right.Occurrence
  source pair := (left.source pair.1, right.source pair.2)
  target pair := (left.target pair.1, right.target pair.2)
  receive pair := (left.receive pair.1, right.receive pair.2)

/-- The reconstruction fibre of a Cartesian interaction retains both component fibres exactly. -/
def cartesianReconstructionFibreEquiv
    {Source' Target' Face' : Type*}
    (left : Holon Source Target LeftFace)
    (right : Holon Source' Target' Face')
    (face : LeftFace × Face') :
    (cartesian left right).ReconstructionFibre face ≃
      left.ReconstructionFibre face.1 × right.ReconstructionFibre face.2 where
  toFun occurrence :=
    (⟨occurrence.1.1, congrArg Prod.fst occurrence.2⟩,
      ⟨occurrence.1.2, congrArg Prod.snd occurrence.2⟩)
  invFun occurrence :=
    ⟨(occurrence.1.1, occurrence.2.1),
      Prod.ext occurrence.1.2 occurrence.2.2⟩
  left_inv occurrence := by
    cases occurrence with
    | mk occurrence receiverEq =>
      cases occurrence
      rfl
  right_inv occurrence := by
    cases occurrence with
    | mk left right =>
      cases left
      cases right
      rfl

/--
The self-diagonal of a holon.  One occurrence is presented simultaneously on two axes; unlike the
Cartesian body it does not invent an independent second occurrence.
-/
def diagonal (holon : Holon Source Target LeftFace) :
    Holon (Source × Source) (Target × Target) (LeftFace × LeftFace) where
  Occurrence := holon.Occurrence
  source occurrence := (holon.source occurrence, holon.source occurrence)
  target occurrence := (holon.target occurrence, holon.target occurrence)
  receive occurrence := (holon.receive occurrence, holon.receive occurrence)

/-- The off-diagonal pair population keeps the proof that its two occurrences differ. -/
def offDiagonal (holon : Holon Source Target LeftFace) :
    Holon (Source × Source) (Target × Target) (LeftFace × LeftFace) where
  Occurrence := { pair : holon.Occurrence × holon.Occurrence // pair.1 ≠ pair.2 }
  source occurrence :=
    (holon.source occurrence.1.1, holon.source occurrence.1.2)
  target occurrence :=
    (holon.target occurrence.1.1, holon.target occurrence.1.2)
  receive occurrence :=
    (holon.receive occurrence.1.1, holon.receive occurrence.1.2)

/-- The fully reconstructed fibre of a paired composite receiver. -/
def CompositeReconstructionFibre
    (right : Holon Middle Target RightFace)
    (left : Holon Source Middle LeftFace)
    (face : LeftFace × RightFace) : Type _ :=
  Σ leftOccurrence : left.ReconstructionFibre face.1,
    { rightOccurrence : right.ReconstructionFibre face.2 //
      left.target leftOccurrence.1 = right.source rightOccurrence.1 }

/--
The paired receiver of a serial composite retains exactly both component fibres and the boundary
equality by which they interact.
-/
def compReconstructionFibreEquiv
    (right : Holon Middle Target RightFace)
    (left : Holon Source Middle LeftFace)
    (face : LeftFace × RightFace) :
    (comp right left).ReconstructionFibre face ≃
      CompositeReconstructionFibre right left face where
  toFun carried :=
    ⟨⟨carried.1.left, congrArg Prod.fst carried.2⟩,
      ⟨⟨carried.1.right, congrArg Prod.snd carried.2⟩, carried.1.joins⟩⟩
  invFun pieces :=
    ⟨⟨pieces.1.1, pieces.2.1.1, pieces.2.2⟩,
      Prod.ext pieces.1.2 pieces.2.1.2⟩
  left_inv carried := by
    rcases carried with ⟨⟨leftOccurrence, rightOccurrence, joins⟩, receiverEq⟩
    rfl
  right_inv pieces := by
    rcases pieces with ⟨⟨leftOccurrence, leftReceiverEq⟩,
      ⟨⟨rightOccurrence, rightReceiverEq⟩, joins⟩⟩
    rfl

/-- The joined middle additive face of a holonic interaction cancels exactly. -/
theorem interaction_middle_boundary
    (left : Holon Source Middle LeftFace)
    (right : Holon Middle Target RightFace)
    (interaction : Interaction left right) :
    AddressedPassage.joinedMiddleBoundary left.toPassage right.toPassage interaction = 0 :=
  AddressedPassage.boundary_join left.toPassage right.toPassage interaction

end Holon

universe uC uI uO

/--
A holon whose returned current has an additive boundary realizing its oriented port difference.
-/
structure BoundaryHolon (Chain : Type uC) (Current : Type uI)
    [AddCommGroup Chain] [AddCommMonoid Current] where
  /-- The complete occurrence population. -/
  Occurrence : Type uO
  /-- The incoming chain face of an occurrence. -/
  source : Occurrence → Chain
  /-- The outgoing chain face of an occurrence. -/
  target : Occurrence → Chain
  /-- The current received from an occurrence. -/
  receive : Occurrence → Current
  /-- The constitutive boundary map for the returned current. -/
  boundary : Current →+ Chain
  /-- Every local current returns its exact outgoing-minus-incoming difference. -/
  returnsBoundary : ∀ occurrence,
    boundary (receive occurrence) = target occurrence - source occurrence

namespace BoundaryHolon

variable {Chain : Type uC} {Current : Type uI}
variable [AddCommGroup Chain] [AddCommMonoid Current]

/-- Transport a boundary holon through declared additive receiver maps.  The commuting law is the
exact constitutive receipt required to reinterpret the current; equal displayed endpoints alone do
not authorize this passage. -/
def map
    {Chain' Current' : Type*}
    [AddCommGroup Chain'] [AddCommMonoid Current']
    (holon : BoundaryHolon Chain Current)
    (chainMap : Chain →+ Chain')
    (currentMap : Current →+ Current')
    (boundary' : Current' →+ Chain')
    (commutes : ∀ current,
      boundary' (currentMap current) = chainMap (holon.boundary current)) :
    BoundaryHolon Chain' Current' where
  Occurrence := holon.Occurrence
  source occurrence := chainMap (holon.source occurrence)
  target occurrence := chainMap (holon.target occurrence)
  receive occurrence := currentMap (holon.receive occurrence)
  boundary := boundary'
  returnsBoundary := by
    intro occurrence
    rw [commutes, holon.returnsBoundary, map_sub]

/-- Forget only the constitutive boundary law while retaining the complete holon. -/
def toHolon (holon : BoundaryHolon Chain Current) : Holon Chain Chain Current where
  Occurrence := holon.Occurrence
  source := holon.source
  target := holon.target
  receive := holon.receive

/-- Serial boundary-holon composition adds the currents and retains the exact join occurrence. -/
def comp (right left : BoundaryHolon Chain Current)
    (sameBoundary : right.boundary = left.boundary) : BoundaryHolon Chain Current where
  Occurrence := Holon.Interaction left.toHolon right.toHolon
  source joined := left.source joined.left
  target joined := right.target joined.right
  receive joined := left.receive joined.left + right.receive joined.right
  boundary := left.boundary
  returnsBoundary := by
    intro joined
    rw [map_add, left.returnsBoundary joined.left]
    have hright := right.returnsBoundary joined.right
    rw [sameBoundary] at hright
    have hjoin : left.target joined.left = right.source joined.right := by
      exact joined.joins
    rw [hright, hjoin]
    abel

/-- The complete current returned by a finite occurrence population. -/
noncomputable def totalCurrent (holon : BoundaryHolon Chain Current)
    [Fintype holon.Occurrence] : Current :=
  ∑ occurrence, holon.receive occurrence

/-- The complete incoming face of a finite occurrence population. -/
noncomputable def totalSource (holon : BoundaryHolon Chain Current)
    [Fintype holon.Occurrence] : Chain :=
  ∑ occurrence, holon.source occurrence

/-- The complete outgoing face of a finite occurrence population. -/
noncomputable def totalTarget (holon : BoundaryHolon Chain Current)
    [Fintype holon.Occurrence] : Chain :=
  ∑ occurrence, holon.target occurrence

/--
The generic exact local-to-global law for a finite holonic occurrence population.
-/
theorem boundary_totalCurrent (holon : BoundaryHolon Chain Current)
    [Fintype holon.Occurrence] :
    holon.boundary holon.totalCurrent = holon.totalTarget - holon.totalSource := by
  rw [totalCurrent, totalTarget, totalSource, map_sum]
  simp_rw [holon.returnsBoundary]
  simpa using
    (Finset.sum_sub_distrib (s := Finset.univ) holon.target holon.source)

end BoundaryHolon

end Soma.Holonics

section Audit
open Soma.Holonics
#print axioms Holon.compReconstructionFibreEquiv
#print axioms Holon.cartesianReconstructionFibreEquiv
#print axioms Holon.interaction_middle_boundary
#print axioms BoundaryHolon.comp
#print axioms BoundaryHolon.map
#print axioms BoundaryHolon.boundary_totalCurrent
end Audit
