import ElementaryHolonics.Foundation.CausalNaturalHolon
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Tensor lenses, tensor faces, and the artifact passage

A `TensorFace` is a dependent tensor product over a declared finite axis family. A `TensorLens` is
a receiver map into such faces. Neither is a holon: occurrence population and oriented ports remain
owned by `Holon`.

The theorem in this file is deliberately narrower than general coordinate covariance. It says
that, for a homogeneous `Fin order` tensor power, a coherent permutation of equal slots which lifts
to occurrences and preserves both ports transports the complete preimage fibre.
-/

namespace Soma.Holonics

open scoped TensorProduct

universe uSource uTarget uCarrier uR uAxis uAxis' uSlot
universe uMorphology uArtifact uReceiver

/-- A dependent tensor receiver face over one declared finite axis family. -/
abbrev TensorFace (R : Type uR) {Axis : Type uAxis} [Fintype Axis]
    (Slot : Axis → Type uSlot) [CommSemiring R]
    [∀ axis, AddCommMonoid (Slot axis)] [∀ axis, Module R (Slot axis)] : Type _ :=
  PiTensorProduct R Slot

/-- A receiver from a carrier into one heterogeneous finite tensor face. -/
structure TensorLens (Carrier : Type uCarrier) (R : Type uR)
    (Axis : Type uAxis) [Fintype Axis] (Slot : Axis → Type uSlot)
    [CommSemiring R] [∀ axis, AddCommMonoid (Slot axis)]
    [∀ axis, Module R (Slot axis)] where
  project : Carrier → TensorFace R Slot

namespace TensorLens

variable {Carrier : Type uCarrier} {R : Type uR} {Axis : Type uAxis}
variable [Fintype Axis] {Slot : Axis → Type uSlot}
variable [CommSemiring R] [∀ axis, AddCommMonoid (Slot axis)]
variable [∀ axis, Module R (Slot axis)]

/-- Apply a heterogeneous tensor lens only at the receiver boundary. -/
def applyToHolon {Source : Type uSource} {Target : Type uTarget}
    (lens : TensorLens Carrier R Axis Slot) (holon : Holon Source Target Carrier) :
    Holon Source Target (TensorFace R Slot) where
  Occurrence := holon.Occurrence
  source := holon.source
  target := holon.target
  receive occurrence := lens.project (holon.receive occurrence)

/-- The literal preimage population behind one heterogeneous tensor face. -/
def PreimageFibre {Source : Type uSource} {Target : Type uTarget}
    (lens : TensorLens Carrier R Axis Slot) (holon : Holon Source Target Carrier)
    (face : TensorFace R Slot) : Type _ :=
  (lens.applyToHolon holon).PreimageFibre face

end TensorLens

/-- Reindex a heterogeneous finite axis family through an equivalence of its axis types. -/
noncomputable def dependentAxisReindex
    {R : Type uR} {Axis : Type uAxis} {Axis' : Type uAxis'}
    [Fintype Axis] [Fintype Axis'] (Slot : Axis → Type uSlot)
    [CommSemiring R] [∀ axis, AddCommMonoid (Slot axis)]
    [∀ axis, Module R (Slot axis)] (reindex : Axis ≃ Axis') :
    TensorFace R Slot ≃ₗ[R] TensorFace R (fun axis' ↦ Slot (reindex.symm axis')) :=
  PiTensorProduct.reindex R Slot reindex

/-- The homogeneous specialization used only for equal slot carriers indexed by `Fin order`. -/
abbrev HomogeneousTensorFace (R : Type uR) (order : ℕ) (V : Type uSlot)
    [CommSemiring R] [AddCommMonoid V] [Module R V] : Type _ :=
  TensorFace R (fun _ : Fin order ↦ V)

namespace Holon

variable {R : Type uR} {V : Type uSlot}
variable [CommSemiring R] [AddCommMonoid V] [Module R V]
variable {Source : Type uSource} {Target : Type uTarget} {order : ℕ}

/--
Coherent naturality only for permutations of equal `Fin order` slots. This does not claim
naturality for heterogeneous axes, variance changes, basis changes, or arbitrary coordinates.
-/
structure HomogeneousSlotNaturality
    (holon : Holon Source Target (HomogeneousTensorFace R order V)) where
  occurrenceReindex : Equiv.Perm (Fin order) → holon.Occurrence ≃ holon.Occurrence
  occurrence_refl :
    occurrenceReindex (Equiv.refl (Fin order)) = Equiv.refl holon.Occurrence
  occurrence_trans : ∀ first second,
    occurrenceReindex (first.trans second) =
      (occurrenceReindex first).trans (occurrenceReindex second)
  source_natural : ∀ reindex occurrence,
    holon.source occurrence = holon.source (occurrenceReindex reindex occurrence)
  target_natural : ∀ reindex occurrence,
    holon.target occurrence = holon.target (occurrenceReindex reindex occurrence)
  receive_natural : ∀ reindex occurrence,
    PiTensorProduct.reindex R (fun _ : Fin order ↦ V) reindex
        (holon.receive occurrence) =
      holon.receive (occurrenceReindex reindex occurrence)

/-- One homogeneous slot permutation supplies an equivalence of elementary holon diagrams. -/
noncomputable def HomogeneousSlotNaturality.rebase
    {holon : Holon Source Target (HomogeneousTensorFace R order V)}
    (naturality : HomogeneousSlotNaturality holon)
    (reindex : Equiv.Perm (Fin order)) : Rebase holon holon where
  occurrenceEquiv := naturality.occurrenceReindex reindex
  sourceEquiv := Equiv.refl Source
  targetEquiv := Equiv.refl Target
  faceEquiv :=
    (PiTensorProduct.reindex R (fun _ : Fin order ↦ V) reindex).toEquiv
  source_natural := naturality.source_natural reindex
  target_natural := naturality.target_natural reindex
  receive_natural := naturality.receive_natural reindex

/-- A homogeneous slot permutation transports the complete preimage, not only the face. -/
noncomputable def HomogeneousSlotNaturality.preimageFibreEquiv
    {holon : Holon Source Target (HomogeneousTensorFace R order V)}
    (naturality : HomogeneousSlotNaturality holon)
    (reindex : Equiv.Perm (Fin order))
    (face : HomogeneousTensorFace R order V) :
    holon.PreimageFibre face ≃
      holon.PreimageFibre
        (PiTensorProduct.reindex R (fun _ : Fin order ↦ V) reindex face) :=
  (naturality.rebase reindex).preimageFibreEquiv face

end Holon

/-! ## The contract required before a durable carrier earns the artifact name -/

/--
A morphology artifact passage validates every rested carrier and remounts the same morphology.
The artifact name belongs to carriers returned by such a passage, not to every serializable value.
-/
structure MorphologyArtifactPassage
    (Morphology : Type uMorphology) (Artifact : Type uArtifact) where
  rest : Morphology → Artifact
  validates : Artifact → Prop
  remount : Artifact → Option Morphology
  rest_valid : ∀ morphology, validates (rest morphology)
  remount_exact : ∀ morphology, remount (rest morphology) = some morphology

namespace MorphologyArtifactPassage

variable {Morphology : Type uMorphology} {Artifact : Type uArtifact}

/-- Exact remount recovers every later receiver consequence. -/
theorem receiver_after_remount (passage : MorphologyArtifactPassage Morphology Artifact)
    {Receiver : Type uReceiver} (receiver : Morphology → Receiver) (morphology : Morphology) :
    Option.map receiver (passage.remount (passage.rest morphology)) = some (receiver morphology) := by
  rw [passage.remount_exact]
  rfl

end MorphologyArtifactPassage

end Soma.Holonics

section Audit
open Soma.Holonics
#print axioms dependentAxisReindex
#print axioms TensorLens.applyToHolon
#print axioms Holon.HomogeneousSlotNaturality.preimageFibreEquiv
#print axioms MorphologyArtifactPassage.receiver_after_remount
end Audit
