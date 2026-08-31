import ElementaryHolonics.Computation.SituatedMachineLearning
import Cslib.Foundations.Semantics.LTS.Execution
import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
# CSLib as an operational receiver of holonic transport

CSLib supplies a precise exterior chart for labelled transitions, finite executions, simulation,
and bisimulation.  It does not supply physical chronology, addressed occurrence lineage, receiver
fibres, or morphology.  This file maps a proved dynamic receiver chart into CSLib and proves the
operational consequences without identifying CSLib's state relation with native causal equality.
-/

namespace Soma.Holonics.Computation.CslibExecutionReceiver

open Soma.Holonics.Computation.MachineLearningChart

universe uG uR uH uC uF

variable {Generator : Type uG} {Receiver : Type uR}
  {Native : Type uH} {Classical : Type uC} {Face : Type uF}
  (C : DynamicReceiverChart Generator Receiver Native Classical Face)

/-- The native transport viewed through CSLib's labelled-transition receiver. -/
def nativeLTS : Cslib.LTS Native Generator where
  Tr native generator successor := C.nativeStep generator native = successor

/-- The fixed classical chart viewed through the same exterior labels. -/
def classicalLTS : Cslib.LTS Classical Generator where
  Tr classical generator successor := C.classicalStep generator classical = successor

/-- CSLib relates a native state to precisely its presented classical receiver face. -/
def quotientRelation (native : Native) (classical : Classical) : Prop :=
  C.quotient native = classical

/-- The dynamic quotient law is exactly a CSLib forward simulation. -/
theorem quotientRelation_isSimulation :
    Cslib.LTS.IsSimulation (nativeLTS C) (classicalLTS C) (quotientRelation C) := by
  intro native classical related generator nativeSuccessor nativeTransition
  refine ⟨C.classicalStep generator classical, rfl, ?_⟩
  unfold quotientRelation
  rw [← nativeTransition, C.generatorExact, related]

/-- Every finite CSLib multistep native trace projects with its complete ordered label word. -/
theorem multistepProjects
    {nativeStart nativeFinish : Native} {word : List Generator}
    (path : (nativeLTS C).MTr nativeStart word nativeFinish) :
    (classicalLTS C).MTr (C.quotient nativeStart) word (C.quotient nativeFinish) := by
  obtain ⟨classicalFinish, classicalPath, related⟩ :=
    (quotientRelation_isSimulation C).sim_trace (by rfl) word nativeFinish path
  unfold quotientRelation at related
  subst classicalFinish
  exact classicalPath

/-- Every finite CSLib execution has a projected classical execution with intermediate states. -/
theorem executionProjects
    {nativeStart nativeFinish : Native} {word : List Generator} {states : List Native}
    (execution : (nativeLTS C).Execution nativeStart word nativeFinish states) :
    ∃ classicalStates : List Classical,
      (classicalLTS C).Execution
        (C.quotient nativeStart) word (C.quotient nativeFinish) classicalStates := by
  have nativePath := Cslib.LTS.Execution.to_mTr execution
  exact Cslib.LTS.Execution.of_mTr (multistepProjects C nativePath)

/--
For total deterministic generator functions, the dynamic quotient relation is also a CSLib
bisimulation.  This remains operational equivalence only; the relation may retain many distinct
native occurrences over one classical state.
-/
theorem quotientRelation_isBisimulation :
    Cslib.LTS.IsBisimulation (nativeLTS C) (classicalLTS C) (quotientRelation C) := by
  intro native classical related generator
  constructor
  · intro nativeSuccessor nativeTransition
    refine ⟨C.classicalStep generator classical, rfl, ?_⟩
    unfold quotientRelation
    rw [← nativeTransition, C.generatorExact, related]
  · intro classicalSuccessor classicalTransition
    refine ⟨C.nativeStep generator native, rfl, ?_⟩
    unfold quotientRelation
    rw [C.generatorExact, related, classicalTransition]

/-! ## CSLib equivalence does not erase addressed source difference -/

namespace Control

open Soma.Holonics.Computation.MachineLearningChart.Control

/--
The two native occurrences are unequal and share one classical state.  The complete dynamic
quotient is a CSLib bisimulation, so even bisimulation is strictly weaker than native occurrence
identity and its reconstruction fibre.
-/
theorem bisimulationRetainsDistinctNativeOccurrences :
    let left : Bool × Bool := (false, false)
    let right : Bool × Bool := (false, true)
    left ≠ right ∧ stableChart.quotient left = stableChart.quotient right ∧
      Cslib.LTS.IsBisimulation
        (nativeLTS stableChart) (classicalLTS stableChart) (quotientRelation stableChart) := by
  refine ⟨by decide, rfl, ?_⟩
  exact quotientRelation_isBisimulation stableChart

end Control

end Soma.Holonics.Computation.CslibExecutionReceiver

section Audit
open Soma.Holonics.Computation.CslibExecutionReceiver
#print axioms quotientRelation_isSimulation
#print axioms multistepProjects
#print axioms executionProjects
#print axioms quotientRelation_isBisimulation
#print axioms Control.bisimulationRetainsDistinctNativeOccurrences
end Audit
