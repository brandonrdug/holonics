import ElementaryHolonics.Computation.HolonicDiffusionCharts
import ElementaryHolonics.Millennium.HolonicComplexParametron

/-!
# Eros cultivation and Athena rest over one holonic neural ecology

Athena is one rested source-neutral ecology, not a transformer or a serialized checkpoint.  Eros
is a returned cultivation passage over that ecology, not a trainer cabinet.  Soulkiller witness is
kept cold and separate from source-neutral spools; changing witness cannot change spool admission.
-/

noncomputable section

namespace Soma.Holonics.Computation.ErosAthenaNeuralObjects

open Soma.Holonics.Computation.HolonicNeuralEcology

universe uSite uCarrier uMorphology uGenerator uReceiver uFace
  uRest uIngress uEgress uDifference uSpool uWitness uInsufficiency

/-- One rested Athena body.  Codec or modality labels do not occur: every ingress occurrence is
translated at the typed exterior port into a generator and a native local section. -/
structure AthenaRestedEcology
    (Site : Type uSite) (Carrier : Type uCarrier) (Morphology : Type uMorphology)
    (Generator : Type uGenerator) (Receiver : Type uReceiver) (Face : Type uFace)
    (RestIdentity : Type uRest) (Ingress : Type uIngress) (Egress : Type uEgress)
    [Fintype Site] [AddCommMonoid Carrier] where
  body : FiniteLocalCurrentEcology Site Carrier Morphology Generator Receiver Face
  restingMorphology : Morphology
  restingState : Site → Carrier
  restIdentity : RestIdentity
  remount : RestIdentity → Morphology × (Site → Carrier)
  remount_exact : remount restIdentity = (restingMorphology, restingState)
  ingress : Ingress → Generator × (Site → Carrier)
  egress : (Site → Carrier) → Egress

namespace AthenaRestedEcology

variable
    {Site : Type uSite} {Carrier : Type uCarrier} {Morphology : Type uMorphology}
    {Generator : Type uGenerator} {Receiver : Type uReceiver} {Face : Type uFace}
    {RestIdentity : Type uRest} {Ingress : Type uIngress} {Egress : Type uEgress}
    [Fintype Site] [AddCommMonoid Carrier]
    (A : AthenaRestedEcology Site Carrier Morphology Generator Receiver Face
      RestIdentity Ingress Egress)

def infer (word : List Generator) : Site → Carrier :=
  A.body.inferWord A.restingMorphology word A.restingState

/-- Source-detached remount reproduces the exact rested inference section. -/
theorem infer_after_remount (word : List Generator) :
    A.body.inferWord (A.remount A.restIdentity).1 word
      (A.remount A.restIdentity).2 = A.infer word := by
  rw [A.remount_exact]
  rfl

/-- Every exterior ingress uses the same ecology body and differs only by its caused occurrence. -/
def conductIngress (occurrence : Ingress) : Site → Carrier :=
  let mounted := A.ingress occurrence
  A.body.step A.restingMorphology mounted.1 mounted.2

end AthenaRestedEcology

/-! ## Soulkiller ends at source-neutral spools plus separate cold testimony -/

structure SoulkillerReturn
    (Spool : Type uSpool) (Witness : Type uWitness) (Insufficiency : Type uInsufficiency) where
  spools : List Spool
  coldWitness : Witness
  insufficiency : Insufficiency

structure SpoolAdmission (Spool : Type uSpool) (Generator : Type uGenerator) where
  admit : Spool → Generator

namespace SoulkillerReturn

variable {Spool : Type uSpool} {Witness : Type uWitness}
  {Insufficiency : Type uInsufficiency} {Generator : Type uGenerator}

def admitted (admission : SpoolAdmission Spool Generator)
    (returned : SoulkillerReturn Spool Witness Insufficiency) : List Generator :=
  returned.spools.map admission.admit

def replaceWitness (returned : SoulkillerReturn Spool Witness Insufficiency)
    (witness : Witness) : SoulkillerReturn Spool Witness Insufficiency where
  spools := returned.spools
  coldWitness := witness
  insufficiency := returned.insufficiency

/-- Cold foreign witness is structurally unable to determine the admitted native generators. -/
@[simp] theorem admitted_replaceWitness
    (admission : SpoolAdmission Spool Generator)
    (returned : SoulkillerReturn Spool Witness Insufficiency) (witness : Witness) :
    admitted admission (returned.replaceWitness witness) = admitted admission returned := rfl

end SoulkillerReturn

/-! ## Eros is a returned morphology passage with behavioral and ablation testimony -/

structure ErosCultivationPassage
    {Site : Type uSite} {Carrier : Type uCarrier} {Morphology : Type uMorphology}
    {Generator : Type uGenerator} {Receiver : Type uReceiver} {Face : Type uFace}
    {RestIdentity : Type uRest} {Ingress : Type uIngress} {Egress : Type uEgress}
    [Fintype Site] [AddCommMonoid Carrier]
    (parent : AthenaRestedEcology Site Carrier Morphology Generator Receiver Face
      RestIdentity Ingress Egress)
    (Difference : Type uDifference) where
  returnedDifference : Difference
  returnMorphology : Difference → Morphology → Morphology
  childMorphology : Morphology
  child_is_return :
    childMorphology = returnMorphology returnedDifference parent.restingMorphology
  morphology_changed : childMorphology ≠ parent.restingMorphology
  childIdentity : RestIdentity
  witnessGenerator : Generator
  witnessReceiver : Receiver
  witnessState : Site → Carrier
  changed_later_conduct :
    parent.body.observe witnessReceiver
      (parent.body.step childMorphology witnessGenerator witnessState) ≠
    parent.body.observe witnessReceiver
      (parent.body.step parent.restingMorphology witnessGenerator witnessState)
  ablate : Difference → Morphology → Morphology
  ablation_exact : ablate returnedDifference childMorphology = parent.restingMorphology

namespace ErosCultivationPassage

variable
    {Site : Type uSite} {Carrier : Type uCarrier} {Morphology : Type uMorphology}
    {Generator : Type uGenerator} {Receiver : Type uReceiver} {Face : Type uFace}
    {RestIdentity : Type uRest} {Ingress : Type uIngress} {Egress : Type uEgress}
    [Fintype Site] [AddCommMonoid Carrier]
    {parent : AthenaRestedEcology Site Carrier Morphology Generator Receiver Face
      RestIdentity Ingress Egress}
    {Difference : Type uDifference}
    (passage : ErosCultivationPassage parent Difference)

/-- The child is the same ecology and boundary apparatus at a returned rest. -/
def child : AthenaRestedEcology Site Carrier Morphology Generator Receiver Face
    RestIdentity Ingress Egress where
  body := parent.body
  restingMorphology := passage.childMorphology
  restingState := parent.restingState
  restIdentity := passage.childIdentity
  remount _ := (passage.childMorphology, parent.restingState)
  remount_exact := rfl
  ingress := parent.ingress
  egress := parent.egress

@[simp] theorem child_body : passage.child.body = parent.body := rfl

theorem child_rest_changed : passage.child.restingMorphology ≠ parent.restingMorphology :=
  passage.morphology_changed

theorem ablation_returns_parent_rest :
    passage.ablate passage.returnedDifference passage.child.restingMorphology =
      parent.restingMorphology := passage.ablation_exact

/-- A training receipt necessarily contains a later-conduct separator, not merely a changed file
or scalar score. -/
theorem cultivation_has_behavioral_separator :
    ∃ generator receiver state,
      parent.body.observe receiver
        (parent.body.step passage.childMorphology generator state) ≠
      parent.body.observe receiver
        (parent.body.step parent.restingMorphology generator state) :=
  ⟨passage.witnessGenerator, passage.witnessReceiver, passage.witnessState,
    passage.changed_later_conduct⟩

end ErosCultivationPassage

/-! ## Complex Parametron current is one carrier realization, not a separate neural species -/

def complexParametronEcology
    (Site : Type uSite) [Fintype Site]
    (Morphology : Type uMorphology) (Generator : Type uGenerator)
    (Receiver : Type uReceiver) (Face : Type uFace)
    (current : Morphology → Generator → (Site → ℂ) → Site → Site → ℂ)
    (constitutive : Morphology → Generator → Site → ℂ → ℂ)
    (observe : Receiver → (Site → ℂ) → Face) :
    FiniteLocalCurrentEcology Site ℂ Morphology Generator Receiver Face where
  localCurrent := current
  reaction := constitutive
  observe := observe

theorem complexParametronEcology_step
    {Site : Type uSite} [Fintype Site]
    {Morphology : Type uMorphology} {Generator : Type uGenerator}
    {Receiver : Type uReceiver} {Face : Type uFace}
    (current : Morphology → Generator → (Site → ℂ) → Site → Site → ℂ)
    (constitutive : Morphology → Generator → Site → ℂ → ℂ)
    (observe : Receiver → (Site → ℂ) → Face)
    (morphology : Morphology) (generator : Generator) (state : Site → ℂ) (target : Site) :
    (complexParametronEcology Site Morphology Generator Receiver Face
      current constitutive observe).step morphology generator state target =
      constitutive morphology generator target
        (∑ source, current morphology generator state target source) := rfl

section Audit

#print axioms AthenaRestedEcology.infer_after_remount
#print axioms SoulkillerReturn.admitted_replaceWitness
#print axioms ErosCultivationPassage.child_body
#print axioms ErosCultivationPassage.ablation_returns_parent_rest
#print axioms ErosCultivationPassage.cultivation_has_behavioral_separator
#print axioms complexParametronEcology_step

end Audit

end Soma.Holonics.Computation.ErosAthenaNeuralObjects
