import ElementaryHolonics.Computation.HolonicIntelligenceLifecycle
import Mathlib.Tactic

/-!
# Native transport scaffolds and repeated inference circulation

Soulkiller returns inherited transport scaffolding, not a compressed copy of a foreign model and
not Athena's permanent intelligence.  A scaffold packages already-profiled native holons,
winding/generator families, lawful compositions, and open obligations.  Repeated inference joins
each emitted occurrence to the next actual ingress while morphology remains fixed at every
inference cut.  A later cultivation may make the inherited scaffold removable while preserving a
declared receiver family.

The bounded-dispersion control keeps supplied, retained, and emitted current distinct.  Equal
total supply does not identify boundary return; the result is algebraic and makes no universal
thermodynamic or biological assertion.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicIntelligence

universe uHolon uProfile uWinding uComposition uScaffoldOpen

/--
The productive, source-neutral assembly returned by a foreign-realization lift.

`Profile` is instantiated by the existing intrinsic-holon profile.  `Winding` is instantiated by
an already-founded reusable spool/generator family.  The scaffold owns neither foreign names nor a
callable exterior executor.
-/
structure NativeTransportScaffold
    (Holon : Type uHolon) (Profile : Type uProfile) (Winding : Type uWinding)
    (Composition : Type uComposition) (OpenObligation : Type uScaffoldOpen) where
  profiledHolons : List (Holon × Profile)
  windings : List Winding
  compositions : List Composition
  openObligations : List OpenObligation
  profiledHolons_nonempty : profiledHolons ≠ []
  windings_nonempty : windings ≠ []

namespace NativeTransportScaffold

variable
    {Holon : Type uHolon} {Profile : Type uProfile} {Winding : Type uWinding}
    {Composition : Type uComposition} {OpenObligation : Type uScaffoldOpen}

abbrev Scaffold :=
  NativeTransportScaffold Holon Profile Winding Composition OpenObligation

/-- Productive admission consumes the scaffold itself and no cold coordinate. -/
def identityAdmission
    (Holon : Type uHolon) (Profile : Type uProfile) (Winding : Type uWinding)
    (Composition : Type uComposition) (OpenObligation : Type uScaffoldOpen) :
    ProductiveAdmission
      (NativeTransportScaffold Holon Profile Winding Composition OpenObligation)
      (NativeTransportScaffold Holon Profile Winding Composition OpenObligation) where
  admit := _root_.id

universe uCold uInsufficiency

/-- Replacing all cold ancestry cannot change the admitted native scaffold. -/
theorem coldWitness_cannot_change_admission
    {ColdWitness : Type uCold} {Insufficiency : Type uInsufficiency}
    (returned : DismantlingReturn Scaffold ColdWitness Insufficiency)
    (replacement : ColdWitness) :
    DismantlingReturn.admitted
        (identityAdmission Holon Profile Winding Composition OpenObligation)
        (returned.replaceColdWitness replacement) =
      DismantlingReturn.admitted
        (identityAdmission Holon Profile Winding Composition OpenObligation) returned := by
  exact DismantlingReturn.admitted_replaceColdWitness
    (identityAdmission Holon Profile Winding Composition OpenObligation) returned replacement

end NativeTransportScaffold

universe uDispersionCarrier uBoundaryFace

/-- One bounded current balance and the boundary face through which its emission is observed. -/
structure BoundaryDispersionPassage
    (Carrier : Type uDispersionCarrier) (Face : Type uBoundaryFace)
    [AddCommMonoid Carrier] where
  supplied : Carrier
  retained : Carrier
  emitted : Carrier
  balance : supplied = retained + emitted
  receiver : Carrier → Face
  boundaryFace : Face
  boundaryFaceExact : boundaryFace = receiver emitted

/-- Equal total supply with a receiver-visible boundary separation. -/
structure EqualSupplyBoundarySeparation
    (Carrier : Type uDispersionCarrier) (Face : Type uBoundaryFace)
    [AddCommMonoid Carrier] where
  scaffolded : BoundaryDispersionPassage Carrier Face
  direct : BoundaryDispersionPassage Carrier Face
  sameSupply : scaffolded.supplied = direct.supplied
  boundarySeparates : scaffolded.boundaryFace ≠ direct.boundaryFace

namespace EqualSupplyBoundarySeparation

variable
    {Carrier : Type uDispersionCarrier} {Face : Type uBoundaryFace}
    [AddCommMonoid Carrier]
    (control : EqualSupplyBoundarySeparation Carrier Face)

/-- The same supplied current coexists with unequal boundary returns. -/
theorem sameSupply_does_not_identify_boundary :
    control.scaffolded.supplied = control.direct.supplied ∧
      control.scaffolded.boundaryFace ≠ control.direct.boundaryFace :=
  ⟨control.sameSupply, control.boundarySeparates⟩

/-- A concrete additive control: the scaffold retains one unit while the direct body emits both. -/
def naturalControl : EqualSupplyBoundarySeparation ℕ ℕ where
  scaffolded := {
    supplied := 2
    retained := 1
    emitted := 1
    balance := by norm_num
    receiver := _root_.id
    boundaryFace := 1
    boundaryFaceExact := rfl
  }
  direct := {
    supplied := 2
    retained := 0
    emitted := 2
    balance := by norm_num
    receiver := _root_.id
    boundaryFace := 2
    boundaryFaceExact := rfl
  }
  sameSupply := rfl
  boundarySeparates := by decide

@[simp] theorem naturalControl_sameSupply :
    naturalControl.scaffolded.supplied = naturalControl.direct.supplied := rfl

theorem naturalControl_boundarySeparates :
    naturalControl.scaffolded.boundaryFace ≠ naturalControl.direct.boundaryFace := by
  decide

end EqualSupplyBoundarySeparation

universe uRepeatedMorphology uRepeatedOccurrence uRepeatedActive uRepeatedConducted
  uRepeatedReceiver uRepeatedFace uRepeatedLineage uRepeatedFibre uRepeatedOpen

abbrev InferenceCut
    (Morphology : Type uRepeatedMorphology) (Occurrence : Type uRepeatedOccurrence)
    (ActiveSection : Type uRepeatedActive) (ConductedSection : Type uRepeatedConducted)
    (Receiver : Type uRepeatedReceiver) (Face : Type uRepeatedFace)
    (Lineage : Type uRepeatedLineage) (Reconstruction : Type uRepeatedFibre)
    (OpenObligation : Type uRepeatedOpen) :=
  InferenceCirculationReturn Morphology Occurrence ActiveSection ConductedSection Occurrence
    Receiver Face Lineage Reconstruction OpenObligation

/-- Every neighboring cut is joined by equality of emission and actual later ingress. -/
def EmissionIngressJoined
    {Morphology : Type uRepeatedMorphology} {Occurrence : Type uRepeatedOccurrence}
    {ActiveSection : Type uRepeatedActive} {ConductedSection : Type uRepeatedConducted}
    {Receiver : Type uRepeatedReceiver} {Face : Type uRepeatedFace}
    {Lineage : Type uRepeatedLineage} {Reconstruction : Type uRepeatedFibre}
    {OpenObligation : Type uRepeatedOpen} :
    List (InferenceCut Morphology Occurrence ActiveSection ConductedSection Receiver Face
      Lineage Reconstruction OpenObligation) → Prop
  | [] => True
  | [_] => True
  | left :: right :: rest =>
      left.emittedOccurrence = right.enteringOccurrence ∧
        EmissionIngressJoined (right :: rest)

/-- A nonempty family of inference cuts connected by actual occurrence lineage. -/
structure RepeatedInferenceCirculation
    (Morphology : Type uRepeatedMorphology) (Occurrence : Type uRepeatedOccurrence)
    (ActiveSection : Type uRepeatedActive) (ConductedSection : Type uRepeatedConducted)
    (Receiver : Type uRepeatedReceiver) (Face : Type uRepeatedFace)
    (Lineage : Type uRepeatedLineage) (Reconstruction : Type uRepeatedFibre)
    (OpenObligation : Type uRepeatedOpen) where
  cuts : List (InferenceCut Morphology Occurrence ActiveSection ConductedSection Receiver Face
    Lineage Reconstruction OpenObligation)
  cuts_nonempty : cuts ≠ []
  joined : EmissionIngressJoined cuts

namespace RepeatedInferenceCirculation

variable
    {Morphology : Type uRepeatedMorphology} {Occurrence : Type uRepeatedOccurrence}
    {ActiveSection : Type uRepeatedActive} {ConductedSection : Type uRepeatedConducted}
    {Receiver : Type uRepeatedReceiver} {Face : Type uRepeatedFace}
    {Lineage : Type uRepeatedLineage} {Reconstruction : Type uRepeatedFibre}
    {OpenObligation : Type uRepeatedOpen}
    (circulation : RepeatedInferenceCirculation Morphology Occurrence ActiveSection
      ConductedSection Receiver Face Lineage Reconstruction OpenObligation)

/-- Every member remains an inference cut with fixed reusable morphology. -/
theorem everyCut_isInferenceCut :
    ∀ cut ∈ circulation.cuts, cut.IsInferenceCut := by
  intro cut _
  exact cut.isInferenceCut

/-- The complete adjacent joining law is returned by the repeated circulation. -/
theorem everyAdjacentEmission_isActualIngress :
    EmissionIngressJoined circulation.cuts :=
  circulation.joined

end RepeatedInferenceCirculation

universe uReleaseHolon uReleaseProfile uReleaseWinding uReleaseComposition uReleaseOpen
  uReleaseMorphology uReleaseDifference uReleaseDelta uReleaseProbe uReleaseFace uReleaseRest
  uReleaseOccurrence uDetachedRest

/--
One cultivation in which inherited transport is initially load-bearing and later removable.

The source-detached morphology is remounted independently.  Every declared receiver probe agrees
with the cultivated successor after scaffold withdrawal, while at least one probe still separates
the source-detached result from the pre-scaffold predecessor.
-/
structure ScaffoldReleasePassage
    (Holon : Type uReleaseHolon) (Profile : Type uReleaseProfile)
    (Winding : Type uReleaseWinding) (Composition : Type uReleaseComposition)
    (OpenObligation : Type uReleaseOpen) (Morphology : Type uReleaseMorphology)
    (Difference : Type uReleaseDifference) (Delta : Type uReleaseDelta)
    (Probe : Type uReleaseProbe) (Face : Type uReleaseFace)
    (RestIdentity : Type uReleaseRest) (Occurrence : Type uReleaseOccurrence)
    (DetachedRest : Type uDetachedRest) where
  scaffold : NativeTransportScaffold Holon Profile Winding Composition OpenObligation
  predecessor : Morphology
  mountScaffold :
    NativeTransportScaffold Holon Profile Winding Composition OpenObligation →
      Morphology → Morphology
  mounted : Morphology
  mountedExact : mounted = mountScaffold scaffold predecessor
  cultivation : CultivationPassage Morphology Difference Delta Probe Face RestIdentity Occurrence
  cultivationBeginsAtMounted : cultivation.predecessor = mounted
  declaredProbes : List Probe
  declaredProbes_nonempty : declaredProbes ≠ []
  scaffoldInitiallyLoadBearing :
    ∃ probe ∈ declaredProbes,
      cultivation.conduct mounted probe ≠ cultivation.conduct predecessor probe
  withdrawScaffold :
    NativeTransportScaffold Holon Profile Winding Composition OpenObligation →
      Morphology → Morphology
  sourceDetached : Morphology
  sourceDetachedExact :
    sourceDetached = withdrawScaffold scaffold cultivation.successor
  detachedRest : Morphology → DetachedRest
  detachedRemount : DetachedRest → Morphology
  detachedRemountExact : detachedRemount (detachedRest sourceDetached) = sourceDetached
  declaredConductPreserved :
    ∀ probe ∈ declaredProbes,
      cultivation.conduct sourceDetached probe = cultivation.conduct cultivation.successor probe
  nativeChangeSurvivesWithdrawal :
    ∃ probe ∈ declaredProbes,
      cultivation.conduct sourceDetached probe ≠ cultivation.conduct predecessor probe

namespace ScaffoldReleasePassage

variable
    {Holon : Type uReleaseHolon} {Profile : Type uReleaseProfile}
    {Winding : Type uReleaseWinding} {Composition : Type uReleaseComposition}
    {OpenObligation : Type uReleaseOpen} {Morphology : Type uReleaseMorphology}
    {Difference : Type uReleaseDifference} {Delta : Type uReleaseDelta}
    {Probe : Type uReleaseProbe} {Face : Type uReleaseFace}
    {RestIdentity : Type uReleaseRest} {Occurrence : Type uReleaseOccurrence}
    {DetachedRest : Type uDetachedRest}
    (passage : ScaffoldReleasePassage Holon Profile Winding Composition OpenObligation
      Morphology Difference Delta Probe Face RestIdentity Occurrence DetachedRest)

/-- The complete training-wheel law: load-bearing first, receiver-exact after withdrawal. -/
theorem loadBearing_then_receiverExactAfterWithdrawal :
    (∃ probe ∈ passage.declaredProbes,
      passage.cultivation.conduct passage.mounted probe ≠
        passage.cultivation.conduct passage.predecessor probe) ∧
    (∀ probe ∈ passage.declaredProbes,
      passage.cultivation.conduct passage.sourceDetached probe =
        passage.cultivation.conduct passage.cultivation.successor probe) ∧
    passage.detachedRemount (passage.detachedRest passage.sourceDetached) =
      passage.sourceDetached :=
  ⟨passage.scaffoldInitiallyLoadBearing, passage.declaredConductPreserved,
    passage.detachedRemountExact⟩

/-- Source-detached native conduct still separates from the pre-scaffold body. -/
theorem nativeChange_survives_scaffoldWithdrawal :
    ∃ probe ∈ passage.declaredProbes,
      passage.cultivation.conduct passage.sourceDetached probe ≠
        passage.cultivation.conduct passage.predecessor probe :=
  passage.nativeChangeSurvivesWithdrawal

end ScaffoldReleasePassage

section Audit

#print axioms NativeTransportScaffold.coldWitness_cannot_change_admission
#print axioms EqualSupplyBoundarySeparation.sameSupply_does_not_identify_boundary
#print axioms EqualSupplyBoundarySeparation.naturalControl_boundarySeparates
#print axioms RepeatedInferenceCirculation.everyCut_isInferenceCut
#print axioms RepeatedInferenceCirculation.everyAdjacentEmission_isActualIngress
#print axioms ScaffoldReleasePassage.loadBearing_then_receiverExactAfterWithdrawal
#print axioms ScaffoldReleasePassage.nativeChange_survives_scaffoldWithdrawal

end Audit

end Soma.Holonics.Computation.HolonicIntelligence
