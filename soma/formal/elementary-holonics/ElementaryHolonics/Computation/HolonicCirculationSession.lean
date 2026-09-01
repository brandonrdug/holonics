import ElementaryHolonics.Computation.HolonicDiffusionCharts
import ElementaryHolonics.Computation.NativeMorphologyVariant
import Mathlib.Tactic

/-!
# Live circulation sessions, parented commits, and diffusive boundaries

This owner is the neutral AAC0 foundation.  It composes the existing fixed-morphology inference,
genuinely later cultivation, repeated-circulation, morphology-package, and exact-diffusion laws.
It does not introduce a model, trainer, scheduler, application ontology, or surface-selected
continuation.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicCirculationSession

open Soma.Holonics.Computation.HolonicIntelligence
open Soma.Holonics.Computation.HolonicDiffusionCharts

/-! ## One live rested session -/

/-- A move-owned rested morphology together with its exact snapshot/remount law.

`conduct` is deliberately generic.  A concrete runtime may instantiate it with native inference,
diffusion, or another already-founded local law; the session does not select a semantic phase.
-/
structure LiveCirculationSession
    (Morphology RestIdentity Ingress Face Generation : Type*) where
  morphology : Morphology
  generation : Generation
  rest : Morphology → RestIdentity
  remount : RestIdentity → Morphology
  remountExact : remount (rest morphology) = morphology
  conduct : Morphology → Ingress → Face

namespace LiveCirculationSession

variable {Morphology RestIdentity Ingress Face Generation : Type*}
    (session : LiveCirculationSession Morphology RestIdentity Ingress Face Generation)

/-- Snapshot/remount preserves every later conduct admitted by the session. -/
theorem conduct_after_remount (ingress : Ingress) :
    session.conduct (session.remount (session.rest session.morphology)) ingress =
      session.conduct session.morphology ingress := by
  rw [session.remountExact]

end LiveCirculationSession

/-! ## Owned circulation boundaries -/

/-- Discrete successor conduct and constituted diffusion are two laws returning the same boundary
envelope.  The tag is testimony about the enacted law, not a native reasoning ontology. -/
inductive CirculationTransportKind where
  | addressedSuccessor
  | constitutedDiffusion
deriving DecidableEq

/-- The owned exterior boundary common to discrete and diffusive conduct. -/
structure CirculationBoundary
    (Morphology Ingress Emission Lineage Reconstruction Configuration OpenObligation : Type*) where
  transportKind : CirculationTransportKind
  predecessorMorphology : Morphology
  ingress : Ingress
  emission : Emission
  lineage : Lineage
  reconstruction : Reconstruction
  configuration : Configuration
  openObligations : List OpenObligation
  successorMorphology : Morphology
  morphologyFixed : successorMorphology = predecessorMorphology

namespace CirculationBoundary

variable
    {Morphology Ingress Emission Lineage Reconstruction Configuration OpenObligation : Type*}
    (boundary : CirculationBoundary Morphology Ingress Emission Lineage Reconstruction
      Configuration OpenObligation)

/-- Every conduct boundary is an inference cut: reusable morphology cannot change while the
emission which may later cause a return is being produced. -/
theorem isInferenceCut : boundary.successorMorphology = boundary.predecessorMorphology :=
  boundary.morphologyFixed

end CirculationBoundary

/-! ## Commit and decline -/

/-- One genuinely later cultivation committed as the parent of the next inference boundary. -/
structure ParentedMorphologyCommit
    (Morphology Difference Delta Probe Face RestIdentity Occurrence Generation
      ActiveSection ConductedSection Emission Receiver InferenceFace Lineage Reconstruction
      OpenObligation : Type*) where
  cultivation :
    CultivationPassage Morphology Difference Delta Probe Face RestIdentity Occurrence
  predecessorGeneration : Generation
  nextGeneration : Generation → Generation
  successorGeneration : Generation
  generationExact : successorGeneration = nextGeneration predecessorGeneration
  nextCut :
    InferenceCirculationReturn Morphology Occurrence ActiveSection ConductedSection Emission
      Receiver InferenceFace Lineage Reconstruction OpenObligation
  nextCutBeginsAtSuccessor :
    nextCut.predecessorMorphology = cultivation.successor

namespace ParentedMorphologyCommit

variable
    {Morphology Difference Delta Probe Face RestIdentity Occurrence Generation ActiveSection
      ConductedSection Emission Receiver InferenceFace Lineage Reconstruction OpenObligation : Type*}
    (commit : ParentedMorphologyCommit Morphology Difference Delta Probe Face RestIdentity Occurrence
      Generation ActiveSection ConductedSection Emission Receiver InferenceFace Lineage
      Reconstruction OpenObligation)

/-- The committed child is caused by a genuinely later occurrence and cannot be the inference cut
which emitted it. -/
theorem return_is_later_and_changes_morphology :
    commit.cultivation.precedes commit.cultivation.emittedOccurrence
        commit.cultivation.returnedOccurrence ∧
      commit.cultivation.successor ≠ commit.cultivation.predecessor :=
  ⟨commit.cultivation.returnIsLater, commit.cultivation.morphologyChanged⟩

/-- The first inference cut of the next generation begins at the committed successor and keeps
that successor fixed while it conducts. -/
theorem next_cut_uses_committed_successor :
    commit.nextCut.predecessorMorphology = commit.cultivation.successor ∧
      commit.nextCut.successorMorphology = commit.cultivation.successor := by
  constructor
  · exact commit.nextCutBeginsAtSuccessor
  · calc
      commit.nextCut.successorMorphology = commit.nextCut.predecessorMorphology :=
        commit.nextCut.morphologyFixed
      _ = commit.cultivation.successor := commit.nextCutBeginsAtSuccessor

/-- The committed generation is the declared child of exactly its predecessor generation. -/
theorem generation_is_parented :
    commit.successorGeneration = commit.nextGeneration commit.predecessorGeneration :=
  commit.generationExact

/-- A committed successor remains exact after durable rest/remount. -/
theorem successor_remounts_exactly :
    commit.cultivation.remount (commit.cultivation.rest commit.cultivation.successor) =
      commit.cultivation.successor :=
  commit.cultivation.remountExact

end ParentedMorphologyCommit

/-- Declining a candidate morphology difference returns the same owner and generation. -/
structure DeclinedMorphologyCandidate (Morphology Generation Candidate : Type*) where
  predecessorMorphology : Morphology
  candidate : Candidate
  successorMorphology : Morphology
  unchanged : successorMorphology = predecessorMorphology
  predecessorGeneration : Generation
  successorGeneration : Generation
  generationUnchanged : successorGeneration = predecessorGeneration

namespace DeclinedMorphologyCandidate

variable {Morphology Generation Candidate : Type*}
    (declined : DeclinedMorphologyCandidate Morphology Generation Candidate)

theorem preserves_owner_and_generation :
    declined.successorMorphology = declined.predecessorMorphology ∧
      declined.successorGeneration = declined.predecessorGeneration :=
  ⟨declined.unchanged, declined.generationUnchanged⟩

end DeclinedMorphologyCandidate

/-! ## Snapshot and remount -/

/-- A complete exterior snapshot of one live session.  The stored chart is not runtime topology;
its law is exact remount of the owned morphology and its later receiver conduct. -/
structure SnapshotRemountPassage
    (Morphology Snapshot Ingress Face : Type*) where
  snapshot : Morphology → Snapshot
  remount : Snapshot → Morphology
  conduct : Morphology → Ingress → Face
  morphology : Morphology
  remountExact : remount (snapshot morphology) = morphology

namespace SnapshotRemountPassage

variable {Morphology Snapshot Ingress Face : Type*}
    (passage : SnapshotRemountPassage Morphology Snapshot Ingress Face)

theorem later_conduct_exact (ingress : Ingress) :
    passage.conduct (passage.remount (passage.snapshot passage.morphology)) ingress =
      passage.conduct passage.morphology ingress := by
  rw [passage.remountExact]

end SnapshotRemountPassage

/-! ## Exact diffusion through the common boundary -/

/-- One constituted diffusion deed whose receiver face and emission are exterior consequences of
the exact implicit balance.  Morphology remains fixed at this conduct boundary. -/
structure DiffusiveCirculationPassage
    (Morphology Occurrence State Input Receiver Face Emission Lineage Reconstruction Configuration
      OpenObligation : Type*) [AddCommGroup State] [Module ℝ State] where
  morphology : Morphology
  occurrence : Occurrence
  diffusion : ImplicitDiffusionChart State Input
  stateBefore : State
  input : Input
  stateAfter : State
  stateAfterExact : stateAfter = diffusion.advance stateBefore input
  receiver : Receiver
  condense : Receiver → State → Face
  face : Face
  faceExact : face = condense receiver stateAfter
  emit : Face → Emission
  emission : Emission
  emissionExact : emission = emit face
  lineage : Lineage
  reconstruction : Reconstruction
  configuration : Configuration
  openObligations : List OpenObligation
  successorMorphology : Morphology
  morphologyFixed : successorMorphology = morphology

namespace DiffusiveCirculationPassage

variable
    {Morphology Occurrence State Input Receiver Face Emission Lineage Reconstruction Configuration
      OpenObligation : Type*} [AddCommGroup State] [Module ℝ State]
    (passage : DiffusiveCirculationPassage Morphology Occurrence State Input Receiver Face Emission
      Lineage Reconstruction Configuration OpenObligation)

/-- The returned diffusive state satisfies its constituted capacity/Laplacian balance exactly. -/
theorem constituted_balance :
    passage.diffusion.capacity passage.stateAfter +
        passage.diffusion.timestep • passage.diffusion.laplacian passage.stateAfter =
      passage.diffusion.capacity passage.stateBefore + passage.diffusion.source passage.input := by
  rw [passage.stateAfterExact]
  exact passage.diffusion.advance_balance passage.stateBefore passage.input

/-- Receiver condensation and emission are definitionally downstream of exact diffusion. -/
theorem emission_is_downstream :
    passage.emission =
      passage.emit
        (passage.condense passage.receiver
          (passage.diffusion.advance passage.stateBefore passage.input)) := by
  rw [passage.emissionExact, passage.faceExact, passage.stateAfterExact]

/-- Diffusive conduct is an inference cut with the same fixed-morphology law as discrete conduct. -/
theorem morphology_is_fixed : passage.successorMorphology = passage.morphology :=
  passage.morphologyFixed

/-- A diffusive deed enters the common owned boundary envelope without losing lineage,
reconstruction, configuration, or open exterior. -/
def boundary :
    CirculationBoundary Morphology Occurrence Emission Lineage Reconstruction Configuration
      OpenObligation where
  transportKind := .constitutedDiffusion
  predecessorMorphology := passage.morphology
  ingress := passage.occurrence
  emission := passage.emission
  lineage := passage.lineage
  reconstruction := passage.reconstruction
  configuration := passage.configuration
  openObligations := passage.openObligations
  successorMorphology := passage.successorMorphology
  morphologyFixed := passage.morphologyFixed

@[simp] theorem boundary_emission : passage.boundary.emission = passage.emission := rfl

@[simp] theorem boundary_isInferenceCut :
    passage.boundary.successorMorphology = passage.boundary.predecessorMorphology :=
  passage.morphologyFixed

end DiffusiveCirculationPassage

section Audit

#print axioms LiveCirculationSession.conduct_after_remount
#print axioms CirculationBoundary.isInferenceCut
#print axioms ParentedMorphologyCommit.return_is_later_and_changes_morphology
#print axioms ParentedMorphologyCommit.next_cut_uses_committed_successor
#print axioms ParentedMorphologyCommit.generation_is_parented
#print axioms ParentedMorphologyCommit.successor_remounts_exactly
#print axioms DeclinedMorphologyCandidate.preserves_owner_and_generation
#print axioms SnapshotRemountPassage.later_conduct_exact
#print axioms DiffusiveCirculationPassage.constituted_balance
#print axioms DiffusiveCirculationPassage.emission_is_downstream
#print axioms DiffusiveCirculationPassage.boundary_isInferenceCut

end Audit

end Soma.Holonics.Computation.HolonicCirculationSession
