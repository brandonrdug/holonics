import ElementaryHolonics.Computation.DependentMachineLearningCarrier
import ElementaryHolonics.Millennium.ReceiverHistory
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# One finite holonic neural ecology

This file defines the architecture-neutral finite transport object used by the HNN campaign.
Sites carry one chart of local state.  Every addressed generator and rested morphology determines
source-to-target local currents; their junction sum enters one local constitutive reaction.
Architecture names, codecs, and apparatus coordinates do not occur in the object.

The same object supplies a native generator family to `DynamicReceiverChart`.  A classical
architecture is therefore an additional quotient, transition, and receiver factorization, never
the native ontology.  Inference retains one morphology through an ordered transport word;
cultivation is a separately returned passage that changes reusable morphology in that fixed-rest
receiver presentation. This older presentation does not define the general HNA lifecycle:
`HolonicRecurrentEcology` owns the complete operation and its developing successor. In particular,
these fixed-morphology words must not be substituted for native contextual recurrence.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicNeuralEcology

open scoped BigOperators
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Computation.MachineLearningChart

universe uS uC uM uG uR uF uD uE

/-- A finite chart of local holonic current and constitutive response.  `localCurrent` may depend
on the complete contemporary state, so fixed and input-conditioned incidence share one type. -/
structure FiniteLocalCurrentEcology
    (Site : Type uS) (Carrier : Type uC) (Morphology : Type uM)
    (Generator : Type uG) (Receiver : Type uR) (Face : Type uF)
    [Fintype Site] [AddCommMonoid Carrier] where
  localCurrent : Morphology → Generator → (Site → Carrier) → Site → Site → Carrier
  /-- Local standing and arriving current are distinct arguments of the constitutive response. -/
  reaction : Morphology → Generator → Site → Carrier → Carrier → Carrier
  observe : Receiver → (Site → Carrier) → Face

namespace FiniteLocalCurrentEcology

variable {Site : Type uS} {Carrier : Type uC} {Morphology : Type uM}
  {Generator : Type uG} {Receiver : Type uR} {Face : Type uF}
  [Fintype Site] [AddCommMonoid Carrier]
  (N : FiniteLocalCurrentEcology Site Carrier Morphology Generator Receiver Face)

/-- All caused currents entering one addressed site, before local reaction. -/
def aggregateCurrent (morphology : Morphology) (generator : Generator)
    (state : Site → Carrier) (target : Site) : Carrier :=
  ∑ source : Site, N.localCurrent morphology generator state target source

/-- One complete native transport through fixed contemporary morphology. -/
def step (morphology : Morphology) (generator : Generator)
    (state : Site → Carrier) : Site → Carrier :=
  fun target ↦ N.reaction morphology generator target (state target)
    (N.aggregateCurrent morphology generator state target)

@[simp] theorem step_apply (morphology : Morphology) (generator : Generator)
    (state : Site → Carrier) (target : Site) :
    N.step morphology generator state target =
      N.reaction morphology generator target (state target)
        (∑ source : Site, N.localCurrent morphology generator state target source) := rfl

/-- Ordered inference through one rested morphology. -/
def inferWord (morphology : Morphology) (word : List Generator)
    (state : Site → Carrier) : Site → Carrier :=
  transportWord (N.step morphology) word state

@[simp] theorem inferWord_nil (morphology : Morphology) (state : Site → Carrier) :
    N.inferWord morphology [] state = state := rfl

theorem inferWord_append (morphology : Morphology) (left right : List Generator)
    (state : Site → Carrier) :
    N.inferWord morphology (left ++ right) state =
      N.inferWord morphology left (N.inferWord morphology right state) := by
  induction left with
  | nil => rfl
  | cons generator left ih =>
      simp only [List.cons_append, inferWord, transportWord_cons]
      exact congrArg (N.step morphology generator) ih

/-- A proposed classical architecture chart over one rested native ecology. -/
structure ClassicalConfiguration (Classical : Type*) where
  quotient : (Site → Carrier) → Classical
  classicalStep : Generator → Classical → Classical
  classicalObserve : Receiver → Classical → Face
  observeExact : ∀ receiver state,
    classicalObserve receiver (quotient state) = N.observe receiver state
  generatorExact : ∀ morphology generator state,
    quotient (N.step morphology generator state) =
      classicalStep generator (quotient state)

/-- Every classical configuration is exactly an HML dynamic receiver chart for each rest. -/
def ClassicalConfiguration.dynamicChart {Classical : Type*}
    (configuration : N.ClassicalConfiguration Classical) (morphology : Morphology) :
    DynamicReceiverChart Generator Receiver (Site → Carrier) Classical Face where
  quotient := configuration.quotient
  nativeStep := N.step morphology
  classicalStep := configuration.classicalStep
  nativeObserve := N.observe
  classicalObserve := configuration.classicalObserve
  observeExact := configuration.observeExact
  generatorExact := configuration.generatorExact morphology

/-- Consequently the architecture chart commutes with every ordered inference history. -/
theorem ClassicalConfiguration.everyInferenceWordExact {Classical : Type*}
    (configuration : N.ClassicalConfiguration Classical) (morphology : Morphology)
    (word : List Generator) (state : Site → Carrier) :
    configuration.quotient (N.inferWord morphology word state) =
      transportWord configuration.classicalStep word (configuration.quotient state) :=
  (configuration.dynamicChart N morphology).everyOrderedWordExact word state

/-- A complete returned cultivation law is separate from inference conduct. -/
structure ReturningCultivation (Exterior : Type uE) (Difference : Type uD) where
  difference : Morphology → (Site → Carrier) → Exterior → Difference
  returnMorphology : Difference → Morphology → Morphology

namespace ReturningCultivation

variable {Exterior : Type uE} {Difference : Type uD}
  (C : ReturningCultivation (Site := Site) (Carrier := Carrier)
    (Morphology := Morphology) Exterior Difference)

/-- Inference keeps the rested constitutive morphology fixed. -/
def InferenceAt (difference : Difference) (morphology : Morphology) : Prop :=
  C.returnMorphology difference morphology = morphology

/-- Cultivation is a witnessed change of the reusable morphology. -/
def CultivatesAt (difference : Difference) (morphology : Morphology) : Prop :=
  C.returnMorphology difference morphology ≠ morphology

theorem cultivates_iff_not_inference (difference : Difference) (morphology : Morphology) :
    C.CultivatesAt difference morphology ↔ ¬ C.InferenceAt difference morphology := by
  rfl

/-- A complete productive recurrence conducts at the old rest and only afterward returns the
new morphology. -/
def productiveOccurrence (morphology : Morphology) (generator : Generator)
    (state : Site → Carrier) (exterior : Exterior) :
    (Site → Carrier) × Difference × Morphology :=
  let conducted := N.step morphology generator state
  let returned := C.difference morphology conducted exterior
  (conducted, returned, C.returnMorphology returned morphology)

@[simp] theorem productiveOccurrence_conducts_before_return
    (morphology : Morphology) (generator : Generator)
    (state : Site → Carrier) (exterior : Exterior) :
    (C.productiveOccurrence N morphology generator state exterior).1 =
      N.step morphology generator state := rfl

end ReturningCultivation

end FiniteLocalCurrentEcology

/-! ## Controls: fixed, input-conditioned, and sparse currents use the same owner -/

namespace Control

/-- One-site scalar current law with morphology gain. -/
def oneSiteEcology : FiniteLocalCurrentEcology (Fin 1) ℤ ℤ Bool Unit ℤ where
  localCurrent gain generator state _ source :=
    if generator then gain * state source else state source
  reaction _ _ _ _ current := current
  observe _ state := state 0

theorem oneSite_true_step (gain current : ℤ) :
    oneSiteEcology.step gain true (fun _ ↦ current) = fun _ ↦ gain * current := by
  funext target
  simp [FiniteLocalCurrentEcology.step, FiniteLocalCurrentEcology.aggregateCurrent,
    oneSiteEcology]

/-- The same ecology type admits contemporary-state-conditioned current without a new
architecture owner. -/
def conditionedTwoSiteEcology :
    FiniteLocalCurrentEcology (Fin 2) ℤ Unit Unit Unit (Fin 2 → ℤ) where
  localCurrent _ _ state target source :=
    if state target = state source then state source else 0
  reaction _ _ _ _ current := current
  observe _ state := state

theorem conditionedTwoSite_step_uses_contemporary_state (left right : ℤ)
    (hne : left ≠ right) :
    conditionedTwoSiteEcology.step () () ![left, right] = ![left, right] := by
  funext target
  fin_cases target <;>
    simp [FiniteLocalCurrentEcology.step, FiniteLocalCurrentEcology.aggregateCurrent,
      conditionedTwoSiteEcology, hne, Ne.symm hne, Fin.sum_univ_succ]

end Control

end Soma.Holonics.Computation.HolonicNeuralEcology

section Audit
open Soma.Holonics.Computation.HolonicNeuralEcology
#print axioms FiniteLocalCurrentEcology.inferWord_append
#print axioms FiniteLocalCurrentEcology.ClassicalConfiguration.everyInferenceWordExact
#print axioms FiniteLocalCurrentEcology.ReturningCultivation.cultivates_iff_not_inference
#print axioms Control.oneSite_true_step
#print axioms Control.conditionedTwoSite_step_uses_contemporary_state
end Audit
