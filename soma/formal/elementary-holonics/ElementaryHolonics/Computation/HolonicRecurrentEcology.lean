import ElementaryHolonics.Computation.HolonicNeuralEcology
import ElementaryHolonics.Foundation.CausalNaturalHolon
import Mathlib.Tactic

/-!
# One recurrent ecology operation

The primitive is one operation from a contemporary ecology and one occurrence to an emission,
an exact trace, and the successor ecology.  The successor is the state used by the next operation.
Self-reentry and application-produced occurrences use the same port; neither is a privileged
learning return.

`FiniteRecurrentOperation` instantiates that primitive over the existing finite local-current
ecology.  Local current, aggregation, reaction, emission, morphology advance, chronology, and
lineage are returned by one function.  Exact rest, ablation, source access, and exterior provenance
remain possible receivers of this recurrence and are not fields of the primitive.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicRecurrentEcology

open Soma.Holonics
open Soma.Holonics.Computation.HolonicNeuralEcology

universe uEcology uOccurrence uEmission uTrace

/-- One exact operation on one contemporary ecology. -/
structure OperationStep
    (Ecology : Type uEcology) (Occurrence : Type uOccurrence)
    (Emission : Type uEmission) (Trace : Type uTrace) where
  operate : Ecology → Occurrence → Emission × Trace × Ecology
  predecessor : Ecology
  occurrence : Occurrence
  emission : Emission
  trace : Trace
  successor : Ecology
  exact : operate predecessor occurrence = (emission, trace, successor)

namespace OperationStep

variable {Ecology : Type uEcology} {Occurrence : Type uOccurrence}
  {Emission : Type uEmission} {Trace : Type uTrace}

/-- Package the actual result of an operation without introducing a second return law. -/
def of (operate : Ecology → Occurrence → Emission × Trace × Ecology)
    (predecessor : Ecology) (occurrence : Occurrence) :
    OperationStep Ecology Occurrence Emission Trace where
  operate := operate
  predecessor := predecessor
  occurrence := occurrence
  emission := (operate predecessor occurrence).1
  trace := (operate predecessor occurrence).2.1
  successor := (operate predecessor occurrence).2.2
  exact := rfl

@[simp] theorem operate_emission (step : OperationStep Ecology Occurrence Emission Trace) :
    (step.operate step.predecessor step.occurrence).1 = step.emission := by
  rw [step.exact]

@[simp] theorem operate_trace (step : OperationStep Ecology Occurrence Emission Trace) :
    (step.operate step.predecessor step.occurrence).2.1 = step.trace := by
  rw [step.exact]

@[simp] theorem operate_successor (step : OperationStep Ecology Occurrence Emission Trace) :
    (step.operate step.predecessor step.occurrence).2.2 = step.successor := by
  rw [step.exact]

end OperationStep

/-- A complete recurrence driven by one operation owner. -/
structure Recurrence
    {Ecology : Type uEcology} {Occurrence : Type uOccurrence}
    {Emission : Type uEmission} {Trace : Type uTrace}
    (operate : Ecology → Occurrence → Emission × Trace × Ecology) where
  state : ℕ → Ecology
  occurrence : ℕ → Occurrence
  emission : ℕ → Emission
  trace : ℕ → Trace
  exact : ∀ time,
    operate (state time) (occurrence time) =
      (emission time, trace time, state (time + 1))

namespace Recurrence

variable {Ecology : Type uEcology} {Occurrence : Type uOccurrence}
  {Emission : Type uEmission} {Trace : Type uTrace}
  {operate : Ecology → Occurrence → Emission × Trace × Ecology}

/-- The actual operation at one time in the recurrence. -/
def stepAt (recurrence : Recurrence operate) (time : ℕ) :
    OperationStep Ecology Occurrence Emission Trace where
  operate := operate
  predecessor := recurrence.state time
  occurrence := recurrence.occurrence time
  emission := recurrence.emission time
  trace := recurrence.trace time
  successor := recurrence.state (time + 1)
  exact := recurrence.exact time

/-- The next operation consumes exactly the preceding successor ecology. -/
theorem successor_joins_next_predecessor (recurrence : Recurrence operate) (time : ℕ) :
    (recurrence.stepAt time).successor =
      (recurrence.stepAt (time + 1)).predecessor := rfl

/-- Emission is a receiver of operation occurrences; equal faces do not identify two times. -/
def operationHolon (recurrence : Recurrence operate) : Holon ℕ ℕ Emission where
  Occurrence := ℕ
  source := id
  target := Nat.succ
  receive := recurrence.emission

/-- A receiver equality can retain two causally distinct operation occurrences. -/
theorem equal_emission_retains_distinct_occurrences
    (recurrence : Recurrence operate) {left right : ℕ}
    (distinct : left ≠ right)
    (sameFace : recurrence.emission left = recurrence.emission right) :
    ∃ first second : (recurrence.operationHolon).Occurrence,
      first ≠ second ∧
        (recurrence.operationHolon).receive first =
          (recurrence.operationHolon).receive second :=
  ⟨left, right, distinct, sameFace⟩

end Recurrence

universe uApplication

/-- Provenance of the next ordinary occurrence.  Both constructors enter the same operation. -/
inductive NextOccurrenceSource (Emission : Type uEmission) (Application : Type uApplication) where
  | selfReentry (emission : Emission)
  | application (value : Application)

/-- One occurrence port shared by self-reentry and application-produced material. -/
structure OccurrencePort
    (Occurrence : Type uOccurrence) (Emission : Type uEmission)
    (Application : Type uApplication) where
  fromEmission : Emission → Occurrence
  fromApplication : Application → Occurrence

namespace OccurrencePort

variable {Ecology : Type uEcology} {Occurrence : Type uOccurrence}
  {Emission : Type uEmission} {Trace : Type uTrace} {Application : Type uApplication}

def receive (port : OccurrencePort Occurrence Emission Application) :
    NextOccurrenceSource Emission Application → Occurrence
  | .selfReentry emission => port.fromEmission emission
  | .application value => port.fromApplication value

/-- Self and application provenance feed the same operation owner and result type. -/
def operateFrom (port : OccurrencePort Occurrence Emission Application)
    (operate : Ecology → Occurrence → Emission × Trace × Ecology)
    (ecology : Ecology) (source : NextOccurrenceSource Emission Application) :
    Emission × Trace × Ecology :=
  operate ecology (port.receive source)

@[simp] theorem operateFrom_self
    (port : OccurrencePort Occurrence Emission Application)
    (operate : Ecology → Occurrence → Emission × Trace × Ecology)
    (ecology : Ecology) (emission : Emission) :
    port.operateFrom operate ecology (.selfReentry emission) =
      operate ecology (port.fromEmission emission) := rfl

@[simp] theorem operateFrom_application
    (port : OccurrencePort Occurrence Emission Application)
    (operate : Ecology → Occurrence → Emission × Trace × Ecology)
    (ecology : Ecology) (value : Application) :
    port.operateFrom operate ecology (.application value) =
      operate ecology (port.fromApplication value) := rfl

end OccurrencePort

universe uSite uCarrier uMorphology uGenerator uReceiver uFace

/-- Complete contemporary state used by a finite local-current operation. -/
structure FiniteEcologyState
    (Site : Type uSite) (Carrier : Type uCarrier)
    (Morphology : Type uMorphology) (Occurrence : Type uOccurrence) where
  morphology : Morphology
  carrier : Site → Carrier
  chronology : List Occurrence

/-- Exact operation trace before any application receiver renders the emission. -/
structure FiniteOperationTrace
    (Site : Type uSite) (Carrier : Type uCarrier)
    (Generator : Type uGenerator) (Receiver : Type uReceiver)
    (Occurrence : Type uOccurrence) where
  occurrence : Occurrence
  generator : Generator
  receiver : Receiver
  presented : Site → Carrier
  localCurrent : Site → Site → Carrier
  aggregateCurrent : Site → Carrier
  reacted : Site → Carrier

/-- The additional laws needed to make the finite local-current chart one recurrent operation. -/
structure FiniteRecurrentOperation
    {Site : Type uSite} {Carrier : Type uCarrier} {Morphology : Type uMorphology}
    {Generator : Type uGenerator} {Receiver : Type uReceiver} {Face : Type uFace}
    [Fintype Site] [AddCommMonoid Carrier]
    (neural : FiniteLocalCurrentEcology Site Carrier Morphology Generator Receiver Face)
    (Occurrence : Type uOccurrence) where
  present : (Site → Carrier) → Occurrence → Generator × Receiver × (Site → Carrier)
  advanceMorphology :
    Morphology → Occurrence → (Site → Carrier) → (Site → Carrier) → Morphology

namespace FiniteRecurrentOperation

variable {Site : Type uSite} {Carrier : Type uCarrier} {Morphology : Type uMorphology}
  {Generator : Type uGenerator} {Receiver : Type uReceiver} {Face : Type uFace}
  {Occurrence : Type uOccurrence}
  [Fintype Site] [AddCommMonoid Carrier]
  {neural : FiniteLocalCurrentEcology Site Carrier Morphology Generator Receiver Face}
  (operation : FiniteRecurrentOperation neural Occurrence)

/-- One neural operation: present, form every local current, aggregate, react, emit, and advance. -/
def operate (ecology : FiniteEcologyState Site Carrier Morphology Occurrence)
    (occurrence : Occurrence) :
    Face × FiniteOperationTrace Site Carrier Generator Receiver Occurrence ×
      FiniteEcologyState Site Carrier Morphology Occurrence :=
  let mounted := operation.present ecology.carrier occurrence
  let generator := mounted.1
  let receiver := mounted.2.1
  let presented := mounted.2.2
  let reacted := neural.step ecology.morphology generator presented
  let trace : FiniteOperationTrace Site Carrier Generator Receiver Occurrence := {
    occurrence := occurrence
    generator := generator
    receiver := receiver
    presented := presented
    localCurrent := fun target source =>
      neural.localCurrent ecology.morphology generator presented target source
    aggregateCurrent := neural.aggregateCurrent ecology.morphology generator presented
    reacted := reacted
  }
  let successor : FiniteEcologyState Site Carrier Morphology Occurrence := {
    morphology := operation.advanceMorphology ecology.morphology occurrence presented reacted
    carrier := reacted
    chronology := ecology.chronology ++ [occurrence]
  }
  (neural.observe receiver reacted, trace, successor)

@[simp] theorem operate_successor_chronology
    (ecology : FiniteEcologyState Site Carrier Morphology Occurrence)
    (occurrence : Occurrence) :
    (operation.operate ecology occurrence).2.2.chronology =
      ecology.chronology ++ [occurrence] := rfl

@[simp] theorem operate_successor_carrier
    (ecology : FiniteEcologyState Site Carrier Morphology Occurrence)
    (occurrence : Occurrence) :
    (operation.operate ecology occurrence).2.2.carrier =
      neural.step ecology.morphology
        (operation.present ecology.carrier occurrence).1
        (operation.present ecology.carrier occurrence).2.2 := rfl

@[simp] theorem operate_trace_localCurrent
    (ecology : FiniteEcologyState Site Carrier Morphology Occurrence)
    (occurrence : Occurrence)
    (target source : Site) :
    (operation.operate ecology occurrence).2.1.localCurrent target source =
      neural.localCurrent ecology.morphology
        (operation.present ecology.carrier occurrence).1
        (operation.present ecology.carrier occurrence).2.2 target source := rfl

@[simp] theorem operate_trace_reacted
    (ecology : FiniteEcologyState Site Carrier Morphology Occurrence)
    (occurrence : Occurrence) :
    (operation.operate ecology occurrence).2.1.reacted =
      (operation.operate ecology occurrence).2.2.carrier := rfl

@[simp] theorem operate_emission
    (ecology : FiniteEcologyState Site Carrier Morphology Occurrence)
    (occurrence : Occurrence) :
    (operation.operate ecology occurrence).1 =
      neural.observe (operation.present ecology.carrier occurrence).2.1
        (operation.operate ecology occurrence).2.2.carrier := rfl

end FiniteRecurrentOperation

universe uLeftEcology uRightEcology uLeftOccurrence uRightOccurrence
  uLeftEmission uRightEmission uLeftTrace uRightTrace

/-- A rebase transports the complete operation result, not only its emitted receiver face. -/
structure OperationRebase
    {LeftEcology : Type uLeftEcology} {RightEcology : Type uRightEcology}
    {LeftOccurrence : Type uLeftOccurrence} {RightOccurrence : Type uRightOccurrence}
    {LeftEmission : Type uLeftEmission} {RightEmission : Type uRightEmission}
    {LeftTrace : Type uLeftTrace} {RightTrace : Type uRightTrace}
    (leftOperate : LeftEcology → LeftOccurrence → LeftEmission × LeftTrace × LeftEcology)
    (rightOperate : RightEcology → RightOccurrence → RightEmission × RightTrace × RightEcology) where
  ecologyEquiv : LeftEcology ≃ RightEcology
  occurrenceEquiv : LeftOccurrence ≃ RightOccurrence
  emissionEquiv : LeftEmission ≃ RightEmission
  traceEquiv : LeftTrace ≃ RightTrace
  natural : ∀ ecology occurrence,
    rightOperate (ecologyEquiv ecology) (occurrenceEquiv occurrence) =
      (emissionEquiv (leftOperate ecology occurrence).1,
        traceEquiv (leftOperate ecology occurrence).2.1,
        ecologyEquiv (leftOperate ecology occurrence).2.2)

namespace OperationRebase

variable
  {LeftEcology : Type uLeftEcology} {RightEcology : Type uRightEcology}
  {LeftOccurrence : Type uLeftOccurrence} {RightOccurrence : Type uRightOccurrence}
  {LeftEmission : Type uLeftEmission} {RightEmission : Type uRightEmission}
  {LeftTrace : Type uLeftTrace} {RightTrace : Type uRightTrace}
  {leftOperate : LeftEcology → LeftOccurrence → LeftEmission × LeftTrace × LeftEcology}
  {rightOperate : RightEcology → RightOccurrence → RightEmission × RightTrace × RightEcology}

/-- Transport one exact operation step through a complete natural rebase. -/
def step (rebase : OperationRebase leftOperate rightOperate)
    (left : OperationStep LeftEcology LeftOccurrence LeftEmission LeftTrace)
    (owns : left.operate = leftOperate) :
    OperationStep RightEcology RightOccurrence RightEmission RightTrace where
  operate := rightOperate
  predecessor := rebase.ecologyEquiv left.predecessor
  occurrence := rebase.occurrenceEquiv left.occurrence
  emission := rebase.emissionEquiv left.emission
  trace := rebase.traceEquiv left.trace
  successor := rebase.ecologyEquiv left.successor
  exact := by
    rw [rebase.natural]
    have exactLeft :
        leftOperate left.predecessor left.occurrence =
          (left.emission, left.trace, left.successor) := by
      rw [← owns]
      exact left.exact
    rw [exactLeft]

@[simp] theorem step_successor
    (rebase : OperationRebase leftOperate rightOperate)
    (left : OperationStep LeftEcology LeftOccurrence LeftEmission LeftTrace)
    (owns : left.operate = leftOperate) :
    (rebase.step left owns).successor = rebase.ecologyEquiv left.successor := rfl

end OperationRebase

/-! ## One firing control with fixed and changing morphology in the same operation owner -/

namespace Control

def operation : FiniteRecurrentOperation HolonicNeuralEcology.Control.oneSiteEcology Bool where
  present carrier generator := (generator, (), carrier)
  advanceMorphology morphology occurrence _ _ :=
    morphology + if occurrence then 1 else 0

def predecessor : FiniteEcologyState (Fin 1) ℤ ℤ Bool where
  morphology := 2
  carrier := fun _ => 3
  chronology := []

def fixedStep : OperationStep (FiniteEcologyState (Fin 1) ℤ ℤ Bool) Bool ℤ
    (FiniteOperationTrace (Fin 1) ℤ Bool Unit Bool) :=
  OperationStep.of operation.operate predecessor false

def changingStep : OperationStep (FiniteEcologyState (Fin 1) ℤ ℤ Bool) Bool ℤ
    (FiniteOperationTrace (Fin 1) ℤ Bool Unit Bool) :=
  OperationStep.of operation.operate predecessor true

theorem fixed_and_changing_share_one_operation_owner :
    fixedStep.operate = changingStep.operate := rfl

theorem fixedStep_advances_without_changing_morphology :
    fixedStep.successor.morphology = fixedStep.predecessor.morphology ∧
      fixedStep.successor.chronology = [false] := by
  norm_num [fixedStep, OperationStep.of, operation,
    FiniteRecurrentOperation.operate, predecessor]

theorem changingStep_changes_morphology_and_advances :
    changingStep.successor.morphology = changingStep.predecessor.morphology + 1 ∧
      changingStep.successor.chronology = [true] := by
  norm_num [changingStep, OperationStep.of, operation,
    FiniteRecurrentOperation.operate, predecessor]

end Control

section Audit

#print axioms OperationStep.operate_successor
#print axioms Recurrence.successor_joins_next_predecessor
#print axioms Recurrence.equal_emission_retains_distinct_occurrences
#print axioms OccurrencePort.operateFrom_self
#print axioms OccurrencePort.operateFrom_application
#print axioms FiniteRecurrentOperation.operate_successor_chronology
#print axioms FiniteRecurrentOperation.operate_trace_localCurrent
#print axioms FiniteRecurrentOperation.operate_emission
#print axioms OperationRebase.step_successor
#print axioms Control.fixed_and_changing_share_one_operation_owner
#print axioms Control.fixedStep_advances_without_changing_morphology
#print axioms Control.changingStep_changes_morphology_and_advances

end Audit

end Soma.Holonics.Computation.HolonicRecurrentEcology
