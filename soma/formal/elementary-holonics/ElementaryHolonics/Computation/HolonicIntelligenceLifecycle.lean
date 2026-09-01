import ElementaryHolonics.Computation.IntrinsicHolonProfile
import ElementaryHolonics.Computation.HolonicNeuralEcology
import Mathlib.Tactic

/-!
# Neutral dismantling, inference, and cultivation lifecycle

These structures package relations already present in the formal machine-learning line.  Product
and campaign names are absent: a named implementation may instantiate these contracts, but it
does not define them.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicIntelligence

open Soma.Holonics.Computation.HolonicNeuralEcology

universe uSite uCarrier uMorphology uGenerator uReceiver uFace uRest uIngress uEgress

/-- One rested, remountable transport ecology over the common local-current owner. -/
structure RestedTransportEcology
    (Site : Type uSite) (Carrier : Type uCarrier) (Morphology : Type uMorphology)
    (Generator : Type uGenerator) (Receiver : Type uReceiver) (Face : Type uFace)
    (RestIdentity : Type uRest) (Ingress : Type uIngress) (Egress : Type uEgress)
    [Fintype Site] [AddCommMonoid Carrier] where
  body : FiniteLocalCurrentEcology Site Carrier Morphology Generator Receiver Face
  restingMorphology : Morphology
  restingState : Site → Carrier
  restIdentity : RestIdentity
  remount : RestIdentity → Morphology × (Site → Carrier)
  remountExact : remount restIdentity = (restingMorphology, restingState)
  ingress : Ingress → Generator × (Site → Carrier)
  egress : (Site → Carrier) → Egress

namespace RestedTransportEcology

variable
    {Site : Type uSite} {Carrier : Type uCarrier} {Morphology : Type uMorphology}
    {Generator : Type uGenerator} {Receiver : Type uReceiver} {Face : Type uFace}
    {RestIdentity : Type uRest} {Ingress : Type uIngress} {Egress : Type uEgress}
    [Fintype Site] [AddCommMonoid Carrier]
    (ecology : RestedTransportEcology Site Carrier Morphology Generator Receiver Face
      RestIdentity Ingress Egress)

/-- Ordered native conduct through one unchanged rest. -/
def conductWord (word : List Generator) : Site → Carrier :=
  ecology.body.inferWord ecology.restingMorphology word ecology.restingState

/-- Exact remount reproduces the complete rested conduct section. -/
theorem conductWord_after_remount (word : List Generator) :
    ecology.body.inferWord (ecology.remount ecology.restIdentity).1 word
      (ecology.remount ecology.restIdentity).2 = ecology.conductWord word := by
  rw [ecology.remountExact]
  rfl

/-- One exterior occurrence enters the same body through its typed ingress passage. -/
def conductIngress (occurrence : Ingress) : Site → Carrier :=
  let mounted := ecology.ingress occurrence
  ecology.body.step ecology.restingMorphology mounted.1 mounted.2

end RestedTransportEcology

universe uProductive uCold uInsufficiency uAdmitted

/-- The physically split return of one foreign-realization dismantling boundary. -/
structure DismantlingReturn
    (Productive : Type uProductive) (ColdWitness : Type uCold)
    (Insufficiency : Type uInsufficiency) where
  productive : Productive
  coldWitness : ColdWitness
  insufficiency : Insufficiency

/-- Admission into a native ecology reads only the productive return. -/
structure ProductiveAdmission (Productive : Type uProductive) (Admitted : Type uAdmitted) where
  admit : Productive → Admitted

namespace DismantlingReturn

variable
    {Productive : Type uProductive} {ColdWitness : Type uCold}
    {Insufficiency : Type uInsufficiency} {Admitted : Type uAdmitted}

def admitted (admission : ProductiveAdmission Productive Admitted)
    (returned : DismantlingReturn Productive ColdWitness Insufficiency) : Admitted :=
  admission.admit returned.productive

def replaceColdWitness (returned : DismantlingReturn Productive ColdWitness Insufficiency)
    (witness : ColdWitness) : DismantlingReturn Productive ColdWitness Insufficiency where
  productive := returned.productive
  coldWitness := witness
  insufficiency := returned.insufficiency

/-- Cold ancestry is structurally unable to change productive native admission. -/
@[simp] theorem admitted_replaceColdWitness
    (admission : ProductiveAdmission Productive Admitted)
    (returned : DismantlingReturn Productive ColdWitness Insufficiency)
    (witness : ColdWitness) :
    admitted admission (returned.replaceColdWitness witness) = admitted admission returned := by
  rfl

end DismantlingReturn

universe uInferenceMorphology uInferenceOccurrence uActive uConducted uEmission uInferenceReceiver
  uInferenceFace uLineage uFibre uOpen

/-- One complete inference cut: emission occurs while reusable morphology remains fixed. -/
structure InferenceCirculationReturn
    (Morphology : Type uInferenceMorphology) (Occurrence : Type uInferenceOccurrence)
    (ActiveSection : Type uActive) (ConductedSection : Type uConducted)
    (Emission : Type uEmission)
    (Receiver : Type uInferenceReceiver) (Face : Type uInferenceFace)
    (Lineage : Type uLineage) (Reconstruction : Type uFibre)
    (OpenObligation : Type uOpen) where
  predecessorMorphology : Morphology
  enteringOccurrence : Occurrence
  mount : Morphology → Occurrence → ActiveSection
  activeSection : ActiveSection
  activeSectionExact : activeSection = mount predecessorMorphology enteringOccurrence
  conduct : Morphology → ActiveSection → ConductedSection
  conductedSection : ConductedSection
  conductedSectionExact : conductedSection = conduct predecessorMorphology activeSection
  receiver : Receiver
  condense : Receiver → ConductedSection → Face
  face : Face
  faceExact : face = condense receiver conductedSection
  emit : Face → Emission
  emittedOccurrence : Emission
  emittedOccurrenceExact : emittedOccurrence = emit face
  lineage : Lineage
  reconstruction : Reconstruction
  successorMorphology : Morphology
  morphologyFixed : successorMorphology = predecessorMorphology
  openObligations : List OpenObligation

namespace InferenceCirculationReturn

variable
    {Morphology : Type uInferenceMorphology} {Occurrence : Type uInferenceOccurrence}
    {ActiveSection : Type uActive} {ConductedSection : Type uConducted}
    {Emission : Type uEmission}
    {Receiver : Type uInferenceReceiver} {Face : Type uInferenceFace}
    {Lineage : Type uLineage} {Reconstruction : Type uFibre}
    {OpenObligation : Type uOpen}
    (returned : InferenceCirculationReturn Morphology Occurrence ActiveSection ConductedSection Emission
      Receiver Face Lineage Reconstruction OpenObligation)

def IsInferenceCut : Prop := returned.successorMorphology = returned.predecessorMorphology

/-- The packaged inference return exposes its fixed-morphology law directly. -/
theorem isInferenceCut : returned.IsInferenceCut := returned.morphologyFixed

/-- The emitted occurrence is definitionally downstream of mount, conduct, and receiver collapse. -/
theorem emission_is_downstream :
    returned.emittedOccurrence =
      returned.emit
        (returned.condense returned.receiver
          (returned.conduct returned.predecessorMorphology
            (returned.mount returned.predecessorMorphology returned.enteringOccurrence))) := by
  rw [returned.emittedOccurrenceExact, returned.faceExact,
    returned.conductedSectionExact, returned.activeSectionExact]

end InferenceCirculationReturn

universe uCultivationMorphology uDifference uDelta uProbe uCultivationFace uCultivationRest
  uCultivationOccurrence

/--
One complete cultivation passage.  The returned difference proposes a delta; a committed child
must remount, change later conduct, and withdraw exactly to its predecessor.
-/
structure CultivationPassage
    (Morphology : Type uCultivationMorphology) (Difference : Type uDifference)
    (Delta : Type uDelta) (Probe : Type uProbe) (Face : Type uCultivationFace)
    (RestIdentity : Type uCultivationRest) (Occurrence : Type uCultivationOccurrence) where
  predecessor : Morphology
  emittedOccurrence : Occurrence
  returnedOccurrence : Occurrence
  precedes : Occurrence → Occurrence → Prop
  precedesIrreflexive : ∀ occurrence, ¬ precedes occurrence occurrence
  returnIsLater : precedes emittedOccurrence returnedOccurrence
  difference : Occurrence → Occurrence → Difference
  returnedDifference : Difference
  returnedDifferenceExact :
    returnedDifference = difference emittedOccurrence returnedOccurrence
  causalAdjoint : Difference → Delta
  applyDelta : Morphology → Delta → Morphology
  successor : Morphology
  successorIsReturn :
    successor = applyDelta predecessor (causalAdjoint returnedDifference)
  morphologyChanged : successor ≠ predecessor
  conduct : Morphology → Probe → Face
  witnessProbe : Probe
  changedLaterConduct : conduct successor witnessProbe ≠ conduct predecessor witnessProbe
  rest : Morphology → RestIdentity
  remount : RestIdentity → Morphology
  remountExact : remount (rest successor) = successor
  withdraw : Difference → Morphology → Morphology
  withdrawalExact : withdraw returnedDifference successor = predecessor

namespace CultivationPassage

variable
    {Morphology : Type uCultivationMorphology} {Difference : Type uDifference}
    {Delta : Type uDelta} {Probe : Type uProbe} {Face : Type uCultivationFace}
    {RestIdentity : Type uCultivationRest} {Occurrence : Type uCultivationOccurrence}
    (passage : CultivationPassage Morphology Difference Delta Probe Face RestIdentity Occurrence)

def IsInferenceCut : Prop := passage.successor = passage.predecessor

/-- A witnessed morphology change cannot simultaneously be an inference cut. -/
theorem cultivation_excludes_inference : ¬ passage.IsInferenceCut :=
  passage.morphologyChanged

/-- Emission and return are distinct occurrences because the return is genuinely later. -/
theorem emitted_ne_returned : passage.emittedOccurrence ≠ passage.returnedOccurrence := by
  intro equal
  have later := passage.returnIsLater
  rw [← equal] at later
  exact passage.precedesIrreflexive passage.emittedOccurrence later

/-- The cultivation return carries a concrete later-conduct separator. -/
theorem has_later_conduct_separator :
    ∃ probe, passage.conduct passage.successor probe ≠
      passage.conduct passage.predecessor probe :=
  ⟨passage.witnessProbe, passage.changedLaterConduct⟩

/-- Source-detached remount reproduces the committed successor morphology. -/
theorem remount_returns_successor :
    passage.remount (passage.rest passage.successor) = passage.successor :=
  passage.remountExact

/-- Targeted withdrawal returns the exact predecessor morphology. -/
theorem withdrawal_returns_predecessor :
    passage.withdraw passage.returnedDifference passage.successor = passage.predecessor :=
  passage.withdrawalExact

end CultivationPassage

section Audit

#print axioms RestedTransportEcology.conductWord_after_remount
#print axioms DismantlingReturn.admitted_replaceColdWitness
#print axioms InferenceCirculationReturn.isInferenceCut
#print axioms InferenceCirculationReturn.emission_is_downstream
#print axioms CultivationPassage.cultivation_excludes_inference
#print axioms CultivationPassage.emitted_ne_returned
#print axioms CultivationPassage.has_later_conduct_separator
#print axioms CultivationPassage.remount_returns_successor
#print axioms CultivationPassage.withdrawal_returns_predecessor

end Audit

end Soma.Holonics.Computation.HolonicIntelligence
